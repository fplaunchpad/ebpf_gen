(* Ebpf.Annot — the simulation bridge between Keel arena terms and the M1
   ISA semantics (ir/SPEC.md §5 definition terms).

   A `bnds` maps each register to the arena term that denotes its value.
   `bagree b rf` says every bound register's term evaluates to the concrete
   64-bit value the register holds in `rf`. `defterm` builds the §5
   definition term for an instruction's destination; `defterm_sound` proves
   that rebinding the destination to that term preserves agreement with the
   M1-stepped register file — i.e. the checker's symbolic bindings track the
   real machine exactly.

   v0-core coverage: 64-bit MOV/NEG and the ALU ops
   ADD/SUB/MUL/AND/OR/XOR/DIV/SDIV/MOD/SMOD/LSH/RSH/ARSH (register and
   immediate forms). SDIV/SMOD use the sign-magnitude = truncated-division
   equivalence (`sdiv_equiv`/`srem_equiv` below) to match M1's `alu_sem`;
   their §5 shapes are the SMT-LIB `bvsdiv`/`bvsrem` (RFC 9669 makes them
   truncated toward zero, `SDIV INT64_MIN -1 = INT64_MIN`, `SMOD _ 0 = _`).
   MOVSX (sign-extend the low 8/16/32 bits) is supported via the §5
   sign_extend/extract terms and `defterm_sound_movsx`; (W32,SX32) has no §5
   row (movsx32 is ALU64-only) so it stays unsupported. Staged (definition
   terms defined in SPEC §5, bridge lemma deferred): all ALU32 (the zero-extend
   wrapper layer) and byte swaps. These return None from `defterm` here so the
   checker treats them as unsupported in v0-core rather than trusting an
   unproven shape. *)
module Ebpf.Annot

open FStar.Mul
open Ebpf.Int
open Ebpf.Ast
open Ebpf.Semantics
open Ebpf.Formula
module U64 = FStar.UInt64
module UInt = FStar.UInt

type bnds = reg -> option term

let upd (b: bnds) (r: reg) (t: term) : bnds = fun r' -> if r' = r then Some t else b r'

unfold let bagree_at (b: bnds) (rf: regfile) (r: reg) : prop =
  match b r, rf r with
  | Some t, Some x -> evalT t == Some (mkres 64 (U64.v x))
  | Some _, None -> False           (* bound in b ⟹ bound in rf *)
  | None, _ -> True

let bagree (b: bnds) (rf: regfile) : prop =
  bagree_at b rf R0 /\ bagree_at b rf R1 /\ bagree_at b rf R2 /\
  bagree_at b rf R3 /\ bagree_at b rf R4 /\ bagree_at b rf R5 /\
  bagree_at b rf R6 /\ bagree_at b rf R7 /\ bagree_at b rf R8 /\
  bagree_at b rf R9 /\ bagree_at b rf R10

let bagree_lookup (b: bnds) (rf: regfile) (r: reg)
  : Lemma (requires bagree b rf) (ensures bagree_at b rf r) =
  match r with
  | R0 -> () | R1 -> () | R2 -> () | R3 -> () | R4 -> () | R5 -> ()
  | R6 -> () | R7 -> () | R8 -> () | R9 -> () | R10 -> ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let bagree_at_update (b: bnds) (rf: regfile) (r: reg) (t: term) (v: U64.t) (rk: reg)
  : Lemma (requires bagree_at b rf rk /\ evalT t == Some (mkres 64 (U64.v v)))
          (ensures bagree_at (upd b r t) (updr rf r v) rk) =
  if rk = r then () else ()
#pop-options

let bagree_update (b: bnds) (rf: regfile) (r: reg) (t: term) (v: U64.t)
  : Lemma (requires bagree b rf /\ evalT t == Some (mkres 64 (U64.v v)))
          (ensures bagree (upd b r t) (updr rf r v)) =
  bagree_at_update b rf r t v R0; bagree_at_update b rf r t v R1;
  bagree_at_update b rf r t v R2; bagree_at_update b rf r t v R3;
  bagree_at_update b rf r t v R4; bagree_at_update b rf r t v R5;
  bagree_at_update b rf r t v R6; bagree_at_update b rf r t v R7;
  bagree_at_update b rf r t v R8; bagree_at_update b rf r t v R9;
  bagree_at_update b rf r t v R10

(* operand term (SPEC §3/§5), 64-bit forms only in v0-core *)
unfold let opterm (b: bnds) (o: operand) : option term =
  match o with
  | OpImm i -> Some (TC 64 (imm64 i))
  | OpReg r -> b r

(* the §5 definition term for the W64 core; None where staged/unsupported *)
let defterm (b: bnds) (i: insn) : option term =
  match i with
  | Mov W64 dst src -> opterm b src
  | Ebpf.Ast.Neg W64 dst -> (match b dst with Some a -> Some (TOp1 Neg a) | None -> None)
  | Alu W64 op dst src ->
    (match b dst, opterm b src with
     | Some a, Some s ->
       (match op with
        | ADD -> Some (TOp2 Add a s)
        | SUB -> Some (TOp2 Sub a s)
        | MUL -> Some (TOp2 Mul a s)
        | AND -> Some (TOp2 And a s)
        | OR  -> Some (TOp2 Or a s)
        | XOR -> Some (TOp2 Xor a s)
        | DIV -> Some (TIte (Atom KEq s (TC 64 0)) (TC 64 0) (TOp2 Udiv a s))
        | MOD -> Some (TOp2 Urem a s)
        | LSH -> Some (TOp2 Shl  a (TOp2 And s (TC 64 63)))
        | RSH -> Some (TOp2 Lshr a (TOp2 And s (TC 64 63)))
        | ARSH-> Some (TOp2 Ashr a (TOp2 And s (TC 64 63)))
        | SDIV-> Some (TIte (Atom KEq s (TC 64 0)) (TC 64 0) (TOp2 Sdiv a s))
        | SMOD-> Some (TOp2 Srem a s))
     | _, _ -> None)
  | MovSX w sz dst src ->
    (* §5: movsx{f}_64 = (sign_extend (64-f)) (extract (f-1) 0 S);
       movsx{f}_32 = (zero_extend 32) ((sign_extend (32-f)) (extract (f-1) 0 S)).
       (W32,SX32) has no §5 row (movsx32 is ALU64-only) -> unsupported. *)
    (match b src with
     | Some s ->
       let f = movsx_bits sz in
       (match w with
        | W64 -> Some (TSext (64 - f) (TExtract (f - 1) 0 s))
        | W32 -> if f < 32
                 then Some (TZext 32 (TSext (32 - f) (TExtract (f - 1) 0 s)))
                 else None)
     | None -> None)
  | _ -> None                              (* W32 ALU / Swap / Assert / Exit staged *)

(* the destination register an instruction writes, when defterm supports it *)
let wdst (i: insn) : option reg =
  match i with
  | Mov W64 dst _ | Ebpf.Ast.Neg W64 dst | Alu W64 _ dst _ -> Some dst
  | MovSX _ _ dst _ -> Some dst
  | _ -> None

(* ------------------------------------------------------------------ *)
(* the simulation bridge                                               *)
(* ------------------------------------------------------------------ *)

(* eBPF masks the shift amount; SPEC §5 makes it explicit with (bvand s 63).
   This connects that to M1's `s % 64`. *)
let mask63 (sv: int{fits 64 sv}) : Lemma (UInt.logand #64 sv 63 == sv % 64) =
  assert_norm (pow2 6 - 1 == 63);
  assert_norm (pow2 6 == 64);
  FStar.UInt.logand_mask #64 sv 6

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let opterm_sound (b: bnds) (rf: regfile) (src: operand)
  : Lemma (requires bagree b rf /\ Some? (opterm b src))
          (ensures (match opterm b src, opbits rf W64 src with
                    | Some t, Some v -> evalT t == Some (mkres 64 v)
                    | _, _ -> False)) =
  match src with
  | OpImm i -> ()
  | OpReg r ->
    bagree_lookup b rf r;
    (match b r, rf r with
     | Some t, Some x -> ()
     | Some _, None -> ()           (* bagree_at b rf r reduces to False *)
     | None, _ -> ())               (* contradicts Some? (opterm b src) *)
#pop-options

let res64v (w: width) (x: int{fits (bits w) x}) : Lemma (U64.v (res64 w x) == x) =
  FStar.Math.Lemmas.pow2_lt_compat 64 32

(* ---- SDIV/SMOD bridge: SMT-LIB bvsdiv/bvsrem = eBPF truncated division ----
   The §5 definition terms use SMT-LIB's sign-magnitude bvsdiv/bvsrem
   (Formula.eval_sdiv/eval_srem); M1's alu_sem uses truncated-toward-zero
   division on the signed interpretations (Ebpf.Int.trunc_div/trunc_mod).
   These are equal at every width. Proved once, consumed by defterm_sound. *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
(* two's-complement negation equals pow2 w - x on (0, pow2 w); self-inverse *)
let negp_pos (w: pos) (x: int{fits w x})
  : Lemma (requires x <> 0) (ensures negp w x == pow2 w - x) =
  FStar.Math.Lemmas.lemma_mod_plus (0 - x) 1 (pow2 w);
  FStar.Math.Lemmas.modulo_lemma (pow2 w - x) (pow2 w)

let negp_negp (w: pos) (x: int{fits w x}) : Lemma (negp w (negp w x) == x) =
  if x = 0 then () else (negp_pos w x; negp_pos w (negp w x))

(* a width-w pattern divided by a positive value stays in range (wrap = id) *)
let quot_wrap (w: pos) (x: int{fits w x}) (y: int{y >= 1})
  : Lemma (wrap w (x / y) == x / y) =
  FStar.Math.Lemmas.nat_over_pos_is_nat x y;
  FStar.Math.Lemmas.lemma_div_mod x y;
  FStar.Math.Lemmas.lemma_mod_lt x y;
  FStar.Math.Lemmas.modulo_lemma (x / y) (pow2 w)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let sdiv_equiv (w: pos) (a: int{fits w a}) (b: int{fits w b})
  : Lemma (requires b <> 0)
          (ensures eval_sdiv w a b == wrap w (trunc_div (sval w a) (sval w b))) =
  negp_pos w b;
  (if msb w a then negp_pos w a else ());
  if not (msb w a) && not (msb w b) then quot_wrap w a b
  else if msb w a && msb w b then quot_wrap w (negp w a) (negp w b)
  else ()                            (* diff sign: eval_sdiv = negp (q) = wrap(-q) *)

let srem_equiv (w: pos) (a: int{fits w a}) (b: int{fits w b})
  : Lemma (ensures eval_srem w a b ==
                   (if b = 0 then a
                    else wrap w (trunc_mod (sval w a) (sval w b)))) =
  (if msb w a then negp_pos w a else ());
  (if b <> 0 && msb w b then negp_pos w b else ());
  if b = 0 then (if msb w a then negp_negp w a else ())
  else begin
    let da = if msb w a then negp w a else a in
    let db = if msb w b then negp w b else b in
    FStar.Math.Lemmas.lemma_div_mod da db;
    FStar.Math.Lemmas.lemma_mod_lt da db;
    FStar.Math.Lemmas.modulo_lemma (da % db) (pow2 w)
  end
#pop-options

(* ---- extract / zero-narrow eval lemmas (MOVSX now, ALU32 next) ---------- *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
(* extracting the low f bits of a width-w term yields (low f) of its value *)
let eval_extract_low (t: term) (w: pos) (x: int{fits w x}) (f: pos{f <= w})
  : Lemma (requires evalT t == Some (mkres w x))
          (ensures evalT (TExtract (f - 1) 0 t) == Some (mkres f (low f x))) =
  assert_norm (pow2 0 == 1)

(* re-narrowing: taking the low f bits after the low n bits (f <= n) is low f *)
let low_low (x: int) (f: pos) (n: pos{f <= n})
  : Lemma (low f (low n x) == low f x) =
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 x f n
#pop-options

(* ---- MOVSX bridge (delegated; isolated VC) ------------------------------ *)
(* MOVSX reads src, takes the low f bits, sign-extends to the op width, and
   zero-extends to 64 (res64). The §5 term is (sign_extend)(extract) for W64
   and (zero_extend 32)(sign_extend)(extract) for W32; both evaluate to
   sext f (bits w) (regbits w sv), which is exactly alu-free step semantics. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let defterm_sound_movsx (b: bnds) (rf: regfile) (w: width) (sz: movsx_sz) (dst src: reg)
  : Lemma (requires bagree b rf /\ Some? (defterm b (MovSX w sz dst src)))
          (ensures (match wdst (MovSX w sz dst src), defterm b (MovSX w sz dst src),
                           step rf (MovSX w sz dst src) with
                    | Some d, Some t, Some rf' -> bagree (upd b d t) rf'
                    | _, _, _ -> False)) =
  bagree_lookup b rf src;
  (match b src, rf src with
   | Some s, Some sv ->
     let f = movsx_bits sz in
     eval_extract_low s 64 (U64.v sv) f;
     (match w with W32 -> low_low (U64.v sv) f 32 | W64 -> ());
     let rv = res64 w (sext f (bits w) (regbits w sv)) in
     res64v w (sext f (bits w) (regbits w sv));
     bagree_update b rf dst (Some?.v (defterm b (MovSX w sz dst src))) rv
   | _, _ -> ())
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 2"

let defterm_sound (b: bnds) (rf: regfile) (i: insn)
  : Lemma (requires bagree b rf /\ Some? (defterm b i))
          (ensures (match wdst i, defterm b i, step rf i with
                    | Some dst, Some t, Some rf' -> bagree (upd b dst t) rf'
                    | _, _, _ -> False)) =
  match i with
  | Mov W64 dst src ->
    opterm_sound b rf src;
    (match opterm b src, opbits rf W64 src with
     | Some t, Some v -> res64v W64 v; bagree_update b rf dst t (res64 W64 v)
     | _, _ -> ())
  | Ebpf.Ast.Neg W64 dst ->
    bagree_lookup b rf dst;
    (match b dst, rf dst with
     | Some a, Some dv ->
       res64v W64 (wrap 64 (0 - regbits W64 dv));
       bagree_update b rf dst (TOp1 Ebpf.Formula.Neg a)
         (res64 W64 (wrap 64 (0 - regbits W64 dv)))
     | _, _ -> ())
  | Alu W64 op dst src ->
    bagree_lookup b rf dst;
    opterm_sound b rf src;
    (match b dst, rf dst, opterm b src, opbits rf W64 src with
     | Some a, Some dv, Some s, Some v ->
       let rv = res64 W64 (alu_sem W64 op (regbits W64 dv) v) in
       res64v W64 (alu_sem W64 op (regbits W64 dv) v);
       (match op with
        | LSH | RSH | ARSH -> mask63 v
        | SDIV -> if v <> 0 then sdiv_equiv 64 (regbits W64 dv) v else ()
        | SMOD -> srem_equiv 64 (regbits W64 dv) v
        | _ -> ());
       bagree_update b rf dst (Some?.v (defterm b i)) rv
     | _, _, _, _ -> ())
  | MovSX w sz dst src -> defterm_sound_movsx b rf w sz dst src
  | _ -> ()

#pop-options
