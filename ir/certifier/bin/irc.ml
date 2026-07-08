(* irc — the Keel certifier (M2.2 prototype).

   Pipeline (ir/SPEC.md; only the *_verified* steps are trusted — they call
   F*-extracted verified code; the parser and prover are untrusted and their
   output is validated):
     1. parse a .kir program + @assert claims               (untrusted)
     2. VERIFIED: Ebpf_CertCheck.accepts  — straight-line safety
     3. for each claim: build the goal from the register's binding term
        (Ebpf_Annot.defterm), synthesize a proof                (untrusted)
     4. VERIFIED: Ebpf_Proof.check_proof  — validate the synthesized proof
     5. VERIFIED: Ebpf_Serialize.serialize_hex — emit real bytecode

   Scope (matches the verified proof-rule core): claims are bounds
   (bvule/bvult/bvuge/distinct-0/=) over registers whose value is built from
   MOV / AND / OR / XOR / ADD / SUB / MUL / constants. DIV (ITE-wrapped) and
   SHIFT (masked amount) claims need proof rules staged in M2.1 (ITE_F /
   substitution / imm-shift definition term) and are reported as
   "unprovable by v0-core prover", not silently accepted. *)

module F = Ebpf_Formula
module A = Ebpf_Ast
module P = Ebpf_Proof
module N = Ebpf_Annot
module CC = Ebpf_CertCheck
module S = Ebpf_Serialize

let z = Z.of_int
let two64 = Z.pow (Z.of_int 2) 64

let reg_name (r: A.reg) : string =
  match r with
  | A.R0 -> "r0" | A.R1 -> "r1" | A.R2 -> "r2" | A.R3 -> "r3" | A.R4 -> "r4"
  | A.R5 -> "r5" | A.R6 -> "r6" | A.R7 -> "r7" | A.R8 -> "r8" | A.R9 -> "r9"
  | A.R10 -> "r10"

let cmp_name (k: F.atomkind) : string =
  match k with F.KUle -> "<=" | F.KUlt -> "<" | F.KUge -> ">=" | F.KEq -> "==" | F.KNe -> "!="

(* ---------- term/atom constructors ---------- *)
let tc (v: Z.t) : F.term = F.TC (z 64, v)
let tci (v: int) : F.term = tc (z v)

(* ---------- parser (minimal .kir subset) ---------- *)
(* Lines: "opNN dst, src" | "@assert (cmp rREG CONST)" | "exit" | "; comment"
   | ".prog"/".mode _"/".keel _" (ignored). Registers r0..r10. src is a
   register or a decimal/0x immediate. *)

type claim = { after: int; kind: F.atomkind; reg: A.reg; bound: Z.t }

exception Parse_error of string

let reg_of (s: string) : A.reg =
  match s with
  | "r0" -> A.R0 | "r1" -> A.R1 | "r2" -> A.R2 | "r3" -> A.R3
  | "r4" -> A.R4 | "r5" -> A.R5 | "r6" -> A.R6 | "r7" -> A.R7
  | "r8" -> A.R8 | "r9" -> A.R9 | "r10" -> A.R10
  | _ -> raise (Parse_error ("bad register " ^ s))

let int_of (s: string) : Z.t =
  let s = String.trim s in
  if String.length s > 2 && String.sub s 0 2 = "0x"
  then Z.of_string s else Z.of_string s

let width_of (mn: string) : A.width * string =
  let n = String.length mn in
  if n >= 2 && String.sub mn (n-2) 2 = "64" then (A.W64, String.sub mn 0 (n-2))
  else if n >= 2 && String.sub mn (n-2) 2 = "32" then (A.W32, String.sub mn 0 (n-2))
  else raise (Parse_error ("no width suffix on " ^ mn))

let alu_of (base: string) : A.alu_op option =
  match base with
  | "add" -> Some A.ADD | "sub" -> Some A.SUB | "mul" -> Some A.MUL
  | "div" -> Some A.DIV | "sdiv" -> Some A.SDIV | "mod" -> Some A.MOD
  | "smod" -> Some A.SMOD | "and" -> Some A.AND | "or" -> Some A.OR
  | "xor" -> Some A.XOR | "lsh" -> Some A.LSH | "rsh" -> Some A.RSH
  | "arsh" -> Some A.ARSH | _ -> None

let i32 (v: Z.t) : Stdint.int32 = Stdint.Int32.of_string (Z.to_string v)

let operand_of (s: string) : A.operand =
  let s = String.trim s in
  if String.length s >= 1 && s.[0] = 'r' && (try let _ = int_of_string (String.sub s 1 (String.length s - 1)) in true with _ -> false)
  then A.OpReg (reg_of s)
  else A.OpImm (i32 (int_of s))

(* split "op dst, rest" -> (op, dst, rest) *)
let split_insn (body: string) : string * string * string =
  match String.index_opt body ' ' with
  | None -> (body, "", "")
  | Some sp ->
    let mn = String.sub body 0 sp in
    let args = String.trim (String.sub body (sp+1) (String.length body - sp - 1)) in
    (match String.index_opt args ',' with
     | None -> (mn, String.trim args, "")
     | Some c -> (mn, String.trim (String.sub args 0 c),
                  String.trim (String.sub args (c+1) (String.length args - c - 1))))

let atomkind_of (s: string) : F.atomkind =
  match s with
  | "bvule" -> F.KUle | "bvult" -> F.KUlt | "bvuge" -> F.KUge
  | "=" -> F.KEq | "distinct" -> F.KNe
  | _ -> raise (Parse_error ("unsupported claim cmp " ^ s))

(* parse "(cmp rREG CONST)" possibly with (_ bvN w) const syntax *)
let parse_claim_atom (s: string) : F.atomkind * A.reg * Z.t =
  let s = String.trim s in
  let s = if String.length s >= 2 && s.[0]='(' then String.sub s 1 (String.length s - 2) else s in
  (* now "cmp rREG CONST" ; CONST may be "(_ bvV w)" -> we scan tokens *)
  let toks = String.split_on_char ' ' s |> List.filter (fun t -> t <> "") in
  (match toks with
   | cmp :: rreg :: rest ->
     let k = atomkind_of cmp in
     let r = reg_of rreg in
     (* find the numeric value: either a bare int, or the "bvV" token *)
     let bound =
       let joined = String.concat " " rest in
       (* strip SMT-LIB (_ bvV w) -> V *)
       (match String.index_opt joined 'v' with
        | Some i when i+1 < String.length joined && joined.[i-1]='b' ->
          let j = ref (i+1) in
          while !j < String.length joined && joined.[!j] >= '0' && joined.[!j] <= '9' do incr j done;
          Z.of_string (String.sub joined (i+1) (!j - i - 1))
        | _ -> int_of (String.trim joined)) in
     (k, r, bound)
   | _ -> raise (Parse_error ("bad claim " ^ s)))

let parse (text: string) : A.insn list * claim list =
  let prog = ref [] and claims = ref [] and idx = ref 0 in
  let lines = String.split_on_char '\n' text in
  List.iter (fun raw ->
    let line = (match String.index_opt raw ';' with
                | Some i -> String.sub raw 0 i | None -> raw) |> String.trim in
    if line = "" then ()
    else if line.[0] = '.' then ()                         (* directive *)
    else if String.length line >= 7 && String.sub line 0 7 = "@assert" then begin
      let (k, r, b) = parse_claim_atom (String.trim (String.sub line 7 (String.length line - 7))) in
      claims := { after = !idx - 1; kind = k; reg = r; bound = b } :: !claims
    end
    else if line = "exit" then (prog := A.Exit :: !prog; incr idx)
    else begin
      let (mn, dst, src) = split_insn line in
      let insn =
        if mn = "neg64" then A.Neg (A.W64, reg_of dst)
        else if mn = "neg32" then A.Neg (A.W32, reg_of dst)
        else
          let (w, base) = width_of mn in
          if base = "mov" then A.Mov (w, reg_of dst, operand_of src)
          else (match alu_of base with
                | Some op -> A.Alu (w, op, reg_of dst, operand_of src)
                | None -> raise (Parse_error ("unknown mnemonic " ^ mn))) in
      prog := insn :: !prog; incr idx
    end) lines;
  (List.rev !prog, List.rev !claims)

(* ---------- binding computation (via verified defterm) ---------- *)
let binding_at (prog: A.insn list) (upto: int) (r: A.reg) : F.term option =
  let b = ref CC.b0 in
  List.iteri (fun i insn ->
    if i <= upto then
      match N.defterm !b insn, N.wdst insn with
      | FStar_Pervasives_Native.Some t, FStar_Pervasives_Native.Some dst ->
        b := N.upd !b dst t
      | _ -> ()) prog;
  (match !b r with
   | FStar_Pervasives_Native.Some t -> Some t
   | FStar_Pervasives_Native.None -> None)

(* ---------- the certifying prover (untrusted) ---------- *)
(* Emits Ebpf_Proof.rule steps into a buffer; returns the 0-based index of
   the step that concludes (bvule t (TC 64 bound)), and bound. *)
exception Cannot_prove of string

type pbuf = { mutable steps: P.rule list; mutable n: int }
let emit (buf: pbuf) (r: P.rule) : int =
  buf.steps <- r :: buf.steps; let i = buf.n in buf.n <- i + 1; i

(* A proof plan: the tightest upper bound this prover can establish for `t`,
   paired with an emitter that appends exactly the steps for that bound and
   returns the index of the step concluding (bvule t (TC 64 bound)).
   Computing bounds purely first lets us pick the tighter of AND's two sides
   (mask bound vs operand bound) and emit only the chosen path. *)
let rec plan (t: F.term) : Z.t * (pbuf -> int) =
  match t with
  | F.TC (_w, v) -> (v, fun buf -> emit buf (P.R_UleRefl t))
  | F.TOp2 (F.And, a, b) ->
    let (ba, ea) = plan a and (bb, eb) = plan b in
    if Z.leq ba bb
    then (ba, fun buf -> let ia = ea buf in
                         let il = emit buf (P.R_AndLeL t) in       (* (bvule t a) *)
                         emit buf (P.R_TransUle (z il, z ia)))     (* (bvule t (TC ba)) *)
    else (bb, fun buf -> let ib = eb buf in
                         let ir = emit buf (P.R_AndLeR t) in       (* (bvule t b) *)
                         emit buf (P.R_TransUle (z ir, z ib)))
  | F.TOp2 (F.Mul, a, b) ->
    let (ba, ea) = plan a and (bb, eb) = plan b in
    let prod = Z.mul ba bb in
    if Z.geq prod two64 then raise (Cannot_prove "mul bound overflows 64 bits");
    (prod, fun buf -> let ia = ea buf in let ib = eb buf in
                      emit buf (P.R_MonoMul (z ia, z ib, t)))
  | F.TOp2 (F.Add, a, b) ->
    let (ba, ea) = plan a and (bb, eb) = plan b in
    let sum = Z.add ba bb in
    if Z.geq sum two64 then raise (Cannot_prove "add bound overflows 64 bits");
    (sum, fun buf -> let ia = ea buf in let ib = eb buf in
                     emit buf (P.R_MonoAdd (z ia, z ib, t)))
  (* division: match the SPEC-5 ITE-wrapped defterm and use the fused rules.
     If the divisor is a literal constant d>=1, R_DivIteBound gives the tight
     bound(a)/d; otherwise R_DivIteLe gives bound(a). *)
  | F.TIte (F.Atom (F.KEq, s, F.TC (_, zero)), F.TC (_, _), F.TOp2 (F.Udiv, a, _s2))
    when Z.equal zero (z 0) ->
    let (ba, ea) = plan a in
    (match s with
     | F.TC (_, d) when Z.geq d (z 1) ->
       (Z.div ba d,
        fun buf -> let ia = ea buf in
                   let iq = emit buf (P.R_UgeConst (s, s)) in   (* (bvuge s d) *)
                   emit buf (P.R_DivIteBound (z ia, z iq, t)))
     | _ ->
       (ba, fun buf -> let ia = ea buf in emit buf (P.R_DivIteLe (z ia, t))))
  (* unsigned remainder: (urem a s) <= a, chained to a's constant bound *)
  | F.TOp2 (F.Urem, a, _s) ->
    let (ba, ea) = plan a in
    (ba, fun buf -> let ia = ea buf in
                    let im = emit buf (P.R_ModLe t) in       (* (bvule t a) *)
                    emit buf (P.R_TransUle (z im, z ia)))     (* (bvule t (TC ba)) *)
  (* universal fallback for any other GROUND term (or/xor/sub/shift/sdiv/...):
     evaluate it and bridge to a bound via EvalEq + EqUle. *)
  | _ ->
    (match F.evalT t with
     | FStar_Pervasives_Native.Some (Prims.Mkdtuple2 (_w, v)) ->
       (v, fun buf -> let ie = emit buf (P.R_EvalEq t) in emit buf (P.R_EqUle (z ie)))
     | FStar_Pervasives_Native.None -> raise (Cannot_prove "term does not evaluate (ill-formed)"))

let eval_bound (t: F.term) : Z.t option =
  match F.evalT t with
  | FStar_Pervasives_Native.Some (Prims.Mkdtuple2 (_w, v)) -> Some v
  | _ -> None

(* Prove goal atom (kind, term, bound); returns the rule list. Tries the tight
   structural proof first (small, generalizes to symbolic terms); if its bound
   exceeds the claim (AND min-bound, mod dividend-bound, mul overflow), falls
   back to an EXACT evaluation proof (EvalEq+EqUle) — complete for any ground
   term whose true value satisfies the claim. *)
let prove_claim (goal_kind: F.atomkind) (t: F.term) (k: Z.t) : P.rule list =
  let buf = { steps = []; n = 0 } in
  (match goal_kind with
   | F.KUle ->
     (* emit a proof of (bvule t k) given a proof of (bvule t b) at step `it`
        with b <= k (weakening via UleConst + TransUle). *)
     let use_bound (b: Z.t) (it: int) : unit =
       if Z.equal b k then ()
       else (let ic = emit buf (P.R_UleConst (tc b, tc k)) in
             let _ = emit buf (P.R_TransUle (z it, z ic)) in ()) in
     let structural_ok =
       try (let (b, em) = plan t in
            if Z.leq b k then (let it = em buf in use_bound b it; true) else false)
       with Cannot_prove _ -> false in
     if structural_ok then ()
     else begin
       buf.steps <- []; buf.n <- 0;                 (* nothing emitted yet; reset defensively *)
       match eval_bound t with
       | Some v when Z.leq v k ->
         let ie = emit buf (P.R_EvalEq t) in
         let iu = emit buf (P.R_EqUle (z ie)) in     (* (bvule t v) *)
         use_bound v iu
       | _ -> raise (Cannot_prove "claim does not hold (true value exceeds bound)")
     end
   | _ -> raise (Cannot_prove "only bvule claims in v0-core prover"));
  List.rev buf.steps

(* ---------- driver ---------- *)
let atom_of_claim (t: F.term) (c: claim) : F.atom = F.Atom (c.kind, t, tc c.bound)

(* Adversarial self-test: show the VERIFIED proof checker rejects forged and
   transplanted proofs. Every "expect false" below is Ebpf_Proof.check_proof
   returning false on a bad certificate — the anti-forge / anti-transplant
   guarantees made concrete. *)
let selftest () =
  let mul = F.TOp2 (F.Mul, tci 6, tci 7) in        (* B(r1) in mul.kir *)
  let add = F.TOp2 (F.Add, tci 100, tci 50) in     (* B(r1) in add.kir *)
  let honest = prove_claim F.KUle mul (z 42) in
  let g_ok    = F.Atom (F.KUle, mul, tci 42) in
  let g_false = F.Atom (F.KUle, mul, tci 41) in     (* 42 </= 41: a lie *)
  let g_trans = F.Atom (F.KUle, add, tci 42) in     (* different program *)
  let forged_side = [ P.R_UleConst (tci 42, tci 41) ] in  (* claims 42 <= 41 *)
  let pr name expect got =
    Printf.printf "  %-42s check_proof = %b  (expected %b) %s\n"
      name got expect (if got = expect then "OK" else "!! MISMATCH") in
  Printf.printf "self-test (all use the VERIFIED Ebpf_Proof.check_proof):\n";
  pr "honest proof vs its true goal"     true  (P.check_proof [] g_ok honest);
  pr "honest proof vs a FALSE goal (<=41)" false (P.check_proof [] g_false honest);
  pr "honest proof TRANSPLANTED to add"   false (P.check_proof [] g_trans honest);
  pr "forged rule (42<=41 side cond)"     false (P.check_proof [] g_ok forged_side)

(* ---------- measurement (M2.4) ---------- *)
(* Self-contained per-claim certificate byte count: a recursive term/atom
   encoding (tag + operands) with NO node sharing — an honest UPPER BOUND. The
   SPEC §8 shared-arena + delta format would be smaller. Reported alongside
   the sharing-free proof-step count (the clean metric, comparable to VEP's
   proof-line counts) and the verified-check time (comparable to BCF's ~48µs).*)
let rec tbytes (t: F.term) : int =
  match t with
  | F.TC (_, _) -> 10                                   (* tag+width+8B value *)
  | F.TOp2 (_, a, b) -> 2 + tbytes a + tbytes b
  | F.TOp1 (_, a) -> 2 + tbytes a
  | F.TConcat (a, b) -> 1 + tbytes a + tbytes b
  | F.TExtract (_, _, a) -> 3 + tbytes a
  | F.TZext (_, a) -> 3 + tbytes a
  | F.TSext (_, a) -> 3 + tbytes a
  | F.TIte (c, a, b) -> 1 + abytes c + tbytes a + tbytes b
and abytes (a: F.atom) : int = match a with F.Atom (_, x, y) -> 1 + tbytes x + tbytes y

let rule_terms (r: P.rule) : F.term list =
  match r with
  | P.R_EvalEq t | P.R_UleRefl t | P.R_EqRefl t | P.R_AndLeL t | P.R_AndLeR t
  | P.R_ShrLe t | P.R_ModLe t -> [t]
  | P.R_UleConst (a, b) | P.R_UltConst (a, b) | P.R_UgeConst (a, b) | P.R_NeConst (a, b) -> [a; b]
  | P.R_DivLe (_, t) | P.R_ShrBound (_, t) | P.R_DivIteLe (_, t) -> [t]
  | P.R_MonoAdd (_, _, t) | P.R_MonoMul (_, _, t) | P.R_DivIteBound (_, _, t) | P.R_ModBound (_, _, t) -> [t]
  | P.R_TransUle _ | P.R_NeFromUge _ | P.R_EqUle _ -> []

let rule_prems (r: P.rule) : int =
  match r with
  | P.R_DivLe _ | P.R_ShrBound _ | P.R_NeFromUge _ | P.R_EqUle _ | P.R_DivIteLe _ -> 1
  | P.R_TransUle _ | P.R_MonoAdd _ | P.R_MonoMul _ | P.R_DivIteBound _ | P.R_ModBound _ -> 2
  | _ -> 0

let step_bytes (r: P.rule) : int =
  3 + rule_prems r + List.fold_left (fun acc t -> acc + tbytes t) 0 (rule_terms r)

(* collect (goal, proof) for each certifiable claim of a program *)
let certify_claims (prog: A.program) (claims: claim list) : (F.atom * P.rule list) list =
  List.filter_map (fun c ->
    match binding_at prog c.after c.reg with
    | None -> None
    | Some t ->
      (try let goal = atom_of_claim t c in Some (goal, prove_claim c.kind t c.bound)
       with Cannot_prove _ -> None)) claims

let measure (file: string) : unit =
  let ic = open_in file in
  let text = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let (prog, claims) = parse text in
  let goals_proofs = certify_claims prog claims in
  let steps = List.fold_left (fun a (_, pf) -> a + List.length pf) 0 goals_proofs in
  let cbytes = List.fold_left (fun a (g, pf) ->
                 a + abytes g + List.fold_left (fun b r -> b + step_bytes r) 0 pf) 16 goals_proofs in
  (* time the VERIFIED checks: accepts + every claim's check_proof, N iters *)
  let iters = 20000 in
  let t0 = Unix.gettimeofday () in
  for _ = 1 to iters do
    ignore (CC.accepts prog);
    List.iter (fun (g, pf) -> ignore (P.check_proof [] g pf)) goals_proofs
  done;
  let us = (Unix.gettimeofday () -. t0) *. 1e6 /. float_of_int iters in
  let name = Filename.remove_extension (Filename.basename file) in
  Printf.printf "%s\t%d\t%d\t%d\t%d\t%.2f\n"
    name (List.length prog) (List.length goals_proofs) steps cbytes us

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "selftest" then (selftest (); exit 0);
  if Array.length Sys.argv > 2 && Sys.argv.(1) = "measure" then (measure Sys.argv.(2); exit 0);
  let file = if Array.length Sys.argv > 1 then Sys.argv.(1) else "/dev/stdin" in
  let ic = open_in file in
  let n = in_channel_length ic in
  let text = really_input_string ic n in
  close_in ic;
  let (prog, claims) = parse text in
  Printf.printf "parsed %d instructions, %d claim(s)\n" (List.length prog) (List.length claims);

  (* step 2: verified safety *)
  let safe = CC.accepts prog in
  Printf.printf "[verified] Ebpf_CertCheck.accepts = %b\n" safe;
  if not safe then (Printf.printf "REJECT: program is not accepted by the verified checker\n"; exit 1);

  (* step 3+4: certify each claim *)
  let total_proof_steps = ref 0 in
  List.iteri (fun ci c ->
    match binding_at prog c.after c.reg with
    | None -> Printf.printf "claim %d: register unbound at that point — cannot certify\n" ci
    | Some t ->
      let goal = atom_of_claim t c in
      (try
         let proof = prove_claim c.kind t c.bound in
         let ok = P.check_proof [] goal proof in    (* VERIFIED proof checker *)
         total_proof_steps := !total_proof_steps + List.length proof;
         Printf.printf "claim %d (%s %s %s): prover emitted %d step(s); [verified] check_proof = %b\n"
           ci (reg_name c.reg) (cmp_name c.kind) (Z.to_string c.bound) (List.length proof) ok;
         if not ok then Printf.printf "  !! verified checker REJECTED the synthesized proof\n"
       with Cannot_prove msg ->
         Printf.printf "claim %d: prover could not certify (%s)\n" ci msg)) claims;

  (* step 5: verified bytecode emission *)
  let hex = S.serialize_hex prog in
  Printf.printf "[verified] bytecode (%d bytes): %s\n" (String.length hex / 2) hex;
  Printf.printf "summary: %d claim(s), %d total proof step(s)\n"
    (List.length claims) !total_proof_steps
