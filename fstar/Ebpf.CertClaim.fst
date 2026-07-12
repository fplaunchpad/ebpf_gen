(* Ebpf.CertClaim — closes the M2.1 hole "claim-validity + strict obligations
   in the end-to-end theorem". It ties the verified proof system
   (Ebpf.Proof.check_proof) into the certificate-checking walk, so the
   soundness theorem now covers what the certificate actually asserts:

     awalk accepts (prog + @assert claims + strict obligations)
       ⟹  the program runs safely AND every asserted bound holds at its
           point AND (strict mode) no div-by-0 / oversized shift occurs.

   The heart is `claim_holds`: a proof that check_proof-validates a claim
   `r ≤ k` (whose goal is built from the checker's current binding of r)
   implies the CONCRETE value of r is ≤ k — because check_proof_sound makes
   the goal `valid` and the binding provably tracks the machine (bagree).
   Composes: Ebpf.Annot.defterm_sound + Ebpf.Proof.check_proof_sound. *)
module Ebpf.CertClaim

open FStar.Mul
open Ebpf.Ast
open Ebpf.Int
open Ebpf.Semantics
open Ebpf.Formula
open Ebpf.Annot
open Ebpf.CertCheck
module P = Ebpf.Proof
module U64 = FStar.UInt64

(* claim as an upper bound on a register, with a proof certificate *)
let tcU (k: U64.t) : term = TC 64 (U64.v k)

(* --- the key lemma: a validated claim holds in the real machine --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let claim_holds (b: bnds) (rf: regfile) (r: reg) (k: U64.t) (pf: list P.rule)
  : Lemma (requires bagree b rf /\ Some? (b r) /\
                    P.check_proof [] (Atom KUle (Some?.v (b r)) (tcU k)) pf)
          (ensures Some? (rf r) /\ U64.v (Some?.v (rf r)) <= U64.v k) =
  let t = Some?.v (b r) in
  P.check_proof_sound [] (Atom KUle t (tcU k)) pf;   (* ⟹ valid (KUle t (tcU k)) *)
  bagree_lookup b rf r                               (* ⟹ evalT t tracks rf r *)
#pop-options

(* --- strict-mode safety obligations (divisor ≠ 0, shift < width) --- *)
(* Same mechanism as claim_holds: a validated obligation proof implies the
   concrete runtime condition, hence the Defensive semantics does not get
   stuck (alu_defined holds). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let ne_holds (b: bnds) (rf: regfile) (r: reg) (pf: list P.rule)
  : Lemma (requires bagree b rf /\ Some? (b r) /\
                    P.check_proof [] (Atom KNe (Some?.v (b r)) (TC 64 0)) pf)
          (ensures Some? (rf r) /\ U64.v (Some?.v (rf r)) <> 0) =
  P.check_proof_sound [] (Atom KNe (Some?.v (b r)) (TC 64 0)) pf;
  bagree_lookup b rf r

let ult_holds (b: bnds) (rf: regfile) (r: reg) (c: nat) (pf: list P.rule)
  : Lemma (requires fits 64 c /\ bagree b rf /\ Some? (b r) /\
                    P.check_proof [] (Atom KUlt (Some?.v (b r)) (TC 64 c)) pf)
          (ensures Some? (rf r) /\ U64.v (Some?.v (rf r)) < c) =
  P.check_proof_sound [] (Atom KUlt (Some?.v (b r)) (TC 64 c)) pf;
  bagree_lookup b rf r
#pop-options

(* Bridge to the Defensive semantics' definedness predicate: a divisor proved
   nonzero / a shift amount proved < 64 makes `alu_defined` true, so
   `stepx Defensive` on that ALU op does not get stuck. (These are the
   content lemmas for strict-mode obligations; the full Defensive-mode walk
   theorem is the analogue of awalk_sound below, threading these in place of
   claim_holds — the same structure, using stepx Defensive.) *)
let ne_defends (n: pos) (op: alu_op) (s: int{fits n s})
  : Lemma (requires (DIV? op \/ SDIV? op \/ MOD? op \/ SMOD? op) /\ s <> 0)
          (ensures alu_defined n op s) = ()

let ult_defends (n: pos) (op: alu_op) (s: int{fits n s})
  : Lemma (requires (LSH? op \/ RSH? op \/ ARSH? op) /\ s < n)
          (ensures alu_defined n op s) = ()

(* --- annotated program: instructions interleaved with claims --- *)
noeq type ai =
  | IStep  : insn -> ai
  | IClaim : reg -> U64.t -> list P.rule -> ai

let aprog = list ai

(* semantic run of an annotated program: steps instructions, and at each
   IClaim gets STUCK unless the register is bound and within its bound. So
   `Some? (arun ...)` means safe-to-exit AND every claim held. *)
let rec arun (sm: semantics) (rf: regfile) (p: aprog) : Tot (option regfile) (decreases p) =
  match p with
  | [] -> None
  | IStep Exit :: _ -> (match rf R0 with Some _ -> Some rf | None -> None)
  | IStep i :: rest -> (match stepx sm rf i with Some rf' -> arun sm rf' rest | None -> None)
  | IClaim r k _ :: rest ->
    (match rf r with
     | Some v -> if U64.v v <= U64.v k then arun sm rf rest else None
     | None -> None)

(* the checker walk over an annotated program *)
let claim_ok (b: bnds) (r: reg) (k: U64.t) (pf: list P.rule) : bool =
  match b r with
  | Some t -> P.check_proof [] (Atom KUle t (tcU k)) pf
  | None -> false

let rec awalk (b: bnds) (p: aprog) : Tot bool (decreases p) =
  match p with
  | [] -> false
  | IStep Exit :: _ -> Some? (b R0)
  | IStep i :: rest ->
    (match wdst i, defterm b i with
     | Some dst, Some t -> awalk (upd b dst t) rest
     | _, _ -> false)
  | IClaim r k pf :: rest -> claim_ok b r k pf && awalk b rest

(* --- soundness: awalk accepts ⟹ arun (Total) safe + all claims hold --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let rec awalk_sound (b: bnds) (rf: regfile) (p: aprog)
  : Lemma (requires bagree b rf /\ awalk b p)
          (ensures Some? (arun Total rf p))
          (decreases p) =
  match p with
  | IStep Exit :: _ -> bagree_lookup b rf R0
  | IStep i :: rest ->
    (match wdst i, defterm b i with
     | Some dst, Some t ->
       defterm_sound b rf i;
       (match step rf i with
        | Some rf' -> awalk_sound (upd b dst t) rf' rest
        | None -> ())
     | _, _ -> ())
  | IClaim r k pf :: rest ->
    claim_holds b rf r k pf;         (* ⟹ Some? (rf r) /\ rf r <= k, so arun doesn't stick here *)
    awalk_sound b rf rest
#pop-options

let b0 : bnds = fun _ -> None
let bagree_b0 () : Lemma (bagree b0 rf0) = ()

(* End-to-end (kernel/Total): an accepted annotated certificate runs safely
   AND every asserted bound holds at its point. For ANY certificate bytes. *)
let claim_soundness (p: aprog)
  : Lemma (requires awalk b0 p) (ensures Some? (arun Total rf0 p)) =
  bagree_b0 ();
  awalk_sound b0 rf0 p

(* non-vacuity: awalk accepts a claim-free safe program, rejects no-R0 and
   unbound-operand ones. (Claim-bearing non-vacuity is shown concretely by the
   userspace certifier: 18 corpus programs certify — see ir/MEASUREMENTS.md.) *)
let _ = assert_norm (awalk b0 [IStep (Mov W64 R0 (OpImm 0l)); IStep Exit])
let _ = assert_norm (not (awalk b0 [IStep Exit]))
let _ = assert_norm (not (awalk b0 [IStep (Mov W64 R0 (OpReg R3)); IStep Exit]))

(* M2.1 hole A: the newly-bridged families walk non-vacuously (defterm Some) *)
let _ = assert_norm (awalk b0 [IStep (Mov W64 R0 (OpImm 5l));
                               IStep (Alu W32 ADD R0 (OpImm 3l)); IStep Exit])
let _ = assert_norm (awalk b0 [IStep (Mov W64 R0 (OpImm 9l));
                               IStep (Alu W64 SDIV R0 (OpImm 2l)); IStep Exit])
let _ = assert_norm (awalk b0 [IStep (Mov W64 R1 (OpImm 200l));
                               IStep (MovSX W64 SX8 R0 R1); IStep Exit])
let _ = assert_norm (awalk b0 [IStep (Mov W32 R0 (OpImm 7l)); IStep Exit])

(* ================================================================== *)
(* STRICT mode: run under Defensive semantics (div/0 and oversized     *)
(* shifts are stuck), with a safety obligation proved at each register  *)
(* div/shift and a structural check for immediate div/shift.            *)
(* ================================================================== *)

let is_reg_divshift (i: insn) : bool =
  match i with
  | Alu _ op _ (OpReg _) ->
    DIV? op || SDIV? op || MOD? op || SMOD? op || LSH? op || RSH? op || ARSH? op
  | _ -> false

let imm_val (w: width) (k: FStar.Int32.t) : (s:int{fits (bits w) s}) =
  match w with | W64 -> imm64 k | W32 -> imm32 k

(* structural definedness for an immediate div/shift (imm-0 divisor and
   imm shift >= width are rejected; = the alu_defined condition on the imm) *)
let imm_ok (i: insn) : bool =
  match i with
  | Alu w op _ (OpImm k) -> alu_defined (bits w) op (imm_val w k)
  | _ -> true

(* obligation atom for a register div/shift (over the src binding) *)
let obl_atom (b: bnds) (i: insn) : option atom =
  match i with
  | Alu W64 op _ (OpReg src) ->
    (match b src with
     | Some t ->
       if DIV? op || SDIV? op || MOD? op || SMOD? op then Some (Atom KNe t (TC 64 0))
       else if LSH? op || RSH? op || ARSH? op then Some (Atom KUlt t (TC 64 64))
       else None
     | None -> None)
  | _ -> None

(* when the ALU operand is defined, the Defensive step equals the Total step *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150"
let defensive_step (rf: regfile) (i: insn)
  : Lemma (requires Some? (step rf i) /\
                    (match i with
                     | Alu w op _ src ->
                       (match opbits rf w src with Some s -> alu_defined (bits w) op s | None -> True)
                     | _ -> True))
          (ensures stepx Defensive rf i == step rf i) = ()

(* SStep (non-reg-div/shift, imm_ok) ⟹ its ALU operand is defined *)
let sstep_defined (rf: regfile) (i: insn)
  : Lemma (requires (not (is_reg_divshift i)) /\ imm_ok i /\ Some? (step rf i))
          (ensures (match i with
                    | Alu w op _ src ->
                      (match opbits rf w src with Some s -> alu_defined (bits w) op s | None -> True)
                    | _ -> True)) =
  match i with
  | Alu w op dst (OpImm k) -> ()          (* opbits = imm_val; imm_ok = alu_defined *)
  | Alu w op dst (OpReg src) -> ()        (* not reg-div/shift ⟹ op is +,-,*,&,|,^ ⟹ defined *)
  | _ -> ()

(* SObl (reg div/shift with a validated obligation) ⟹ its operand is defined *)
let sobl_defined (b: bnds) (rf: regfile) (i: insn) (pf: list P.rule)
  : Lemma (requires bagree b rf /\ is_reg_divshift i /\ Some? (obl_atom b i) /\
                    P.check_proof [] (Some?.v (obl_atom b i)) pf /\ Some? (step rf i))
          (ensures (match i with
                    | Alu w op _ src ->
                      (match opbits rf w src with Some s -> alu_defined (bits w) op s | None -> True)
                    | _ -> True)) =
  match i with
  | Alu W64 op dst (OpReg src) ->
    if DIV? op || SDIV? op || MOD? op || SMOD? op
    then ne_holds b rf src pf
    else ult_holds b rf src 64 pf
  | _ -> ()
#pop-options

noeq type si = | SStep : insn -> si | SObl : insn -> list P.rule -> si
let sprog = list si

(* Defensive run; SStep/SObl both step under Defensive semantics *)
let rec srun (rf: regfile) (p: sprog) : Tot (option regfile) (decreases p) =
  match p with
  | [] -> None
  | SStep Exit :: _ -> (match rf R0 with Some _ -> Some rf | None -> None)
  | SStep i :: rest | SObl i _ :: rest ->
    (match stepx Defensive rf i with Some rf' -> srun rf' rest | None -> None)

let rec swalk (b: bnds) (p: sprog) : Tot bool (decreases p) =
  match p with
  | [] -> false
  | SStep Exit :: _ -> Some? (b R0)
  | SStep i :: rest ->
    (not (is_reg_divshift i)) && imm_ok i &&
    (match wdst i, defterm b i with
     | Some dst, Some t -> swalk (upd b dst t) rest
     | _, _ -> false)
  | SObl i pf :: rest ->
    is_reg_divshift i &&
    (match obl_atom b i with
     | Some ob -> P.check_proof [] ob pf &&
                  (match wdst i, defterm b i with
                   | Some dst, Some t -> swalk (upd b dst t) rest
                   | _, _ -> false)
     | None -> false)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let rec swalk_sound (b: bnds) (rf: regfile) (p: sprog)
  : Lemma (requires bagree b rf /\ swalk b p)
          (ensures Some? (srun rf p))
          (decreases p) =
  match p with
  | SStep Exit :: _ -> bagree_lookup b rf R0
  | SStep i :: rest ->
    (match wdst i, defterm b i with
     | Some dst, Some t ->
       defterm_sound b rf i;
       (match step rf i with
        | Some rf' -> sstep_defined rf i; defensive_step rf i; swalk_sound (upd b dst t) rf' rest
        | None -> ())
     | _, _ -> ())
  | SObl i pf :: rest ->
    (match obl_atom b i with
     | Some ob ->
       (match wdst i, defterm b i with
        | Some dst, Some t ->
          defterm_sound b rf i;
          (match step rf i with
           | Some rf' -> sobl_defined b rf i pf; defensive_step rf i; swalk_sound (upd b dst t) rf' rest
           | None -> ())
        | _, _ -> ())
     | None -> ())
#pop-options

(* End-to-end (strict/Defensive): an accepted strict certificate runs safely
   under the Defensive semantics — no div-by-0, no oversized shift, every
   obligation discharged — reaching Exit with R0 set, for ANY certificate. *)
let strict_soundness (p: sprog)
  : Lemma (requires swalk b0 p) (ensures Some? (srun rf0 p)) =
  bagree_b0 ();
  swalk_sound b0 rf0 p
