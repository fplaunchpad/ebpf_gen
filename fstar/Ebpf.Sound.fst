(* Ebpf.Sound — soundness of the checker against the machine semantics.

   Main theorem (`soundness`): if `check_prog m ts0 p` accepts, then
   running p from the empty register file is SAFE under the semantics
   matching the mode:
   - Kernel mode  -> Total semantics (ISA-defined div/0, masked shifts):
     no uninitialized reads, every Assert_ holds, R0 set at Exit.
   - Strict mode  -> Defensive semantics: additionally, no div/mod by
     zero and no shift amount >= width ever occurs.

   The proof is a step-indexed simulation between the abstract typing
   state (per-register unsigned intervals) and the concrete register
   file, using the per-op transfer soundness from Ebpf.Interval. *)
module Ebpf.Sound

open FStar.Mul
open Ebpf.Ast
open Ebpf.Int
open Ebpf.Semantics
open Ebpf.Interval
open Ebpf.Check
module U64 = FStar.UInt64

let sem_of (m: mode) : semantics =
  match m with | Strict -> Defensive | Kernel -> Total

(* --- agreement between abstract and concrete state ---------------------- *)

let agree_at (ts: tystate) (rf: regfile) (r: reg) : prop =
  Some? (ts r) ==> (Some? (rf r) /\ inb (Some?.v (ts r)) (U64.v (Some?.v (rf r))))

(* explicit finite conjunction: quantifier-free, Z3-robust *)
let agree (ts: tystate) (rf: regfile) : prop =
  agree_at ts rf R0 /\ agree_at ts rf R1 /\ agree_at ts rf R2 /\
  agree_at ts rf R3 /\ agree_at ts rf R4 /\ agree_at ts rf R5 /\
  agree_at ts rf R6 /\ agree_at ts rf R7 /\ agree_at ts rf R8 /\
  agree_at ts rf R9 /\ agree_at ts rf R10

let agree_lookup (ts: tystate) (rf: regfile) (r: reg)
  : Lemma (requires agree ts rf) (ensures agree_at ts rf r) =
  match r with
  | R0 -> () | R1 -> () | R2 -> () | R3 -> () | R4 -> () | R5 -> ()
  | R6 -> () | R7 -> () | R8 -> () | R9 -> () | R10 -> ()

let agree_update (ts: tystate) (rf: regfile) (r: reg) (i: iv 64) (v: U64.t)
  : Lemma (requires agree ts rf /\ inb i (U64.v v))
          (ensures agree (wr ts r i) (updr rf r v)) = ()

(* --- operand agreement --------------------------------------------------- *)

let aiv_sound (ts: tystate) (rf: regfile) (w: width) (o: operand)
  : Lemma (requires agree ts rf /\ Some? (aiv ts w o))
          (ensures Some? (opbits rf w o) /\
                   inb (Some?.v (aiv ts w o)) (Some?.v (opbits rf w o))) =
  match o with
  | OpImm _ -> ()
  | OpReg r ->
    agree_lookup ts rf r;
    let a = Some?.v (read ts r) in
    let x = Some?.v (rf r) in
    (match w with
     | W64 -> ()
     | W32 -> narrow32_sound a x)

(* --- per-instruction soundness lemmas for MovSX / Swap ------------------- *)

let tf_movsx_sound (n: pos) (f: pos{f <= n}) (a: iv n) (x: int{fits n x})
  : Lemma (requires inb a x)
          (ensures inb (tf_movsx n f a) (sext f n x)) =
  if a.ihi < pow2 (f - 1)
  then begin
    FStar.Math.Lemmas.pow2_lt_compat f (f - 1);
    FStar.Math.Lemmas.small_mod x (pow2 f);       (* low f x = x *)
    FStar.Math.Lemmas.pow2_le_compat n (f - 1);
    FStar.Math.Lemmas.small_mod x (pow2 n)        (* wrap n x = x *)
  end
  else ()

let tf_swap_sound (k: swap_kind) (sz: swap_sz) (a: iv 64) (x: int{fits 64 x})
  : Lemma (requires inb a x)
          (ensures inb (tf_swap k sz a) (swap_sem k sz x)) =
  FStar.Math.Lemmas.pow2_le_compat 64 (swap_bits sz);
  match k with
  | ToLE ->
    if a.ihi < pow2 (swap_bits sz)
    then FStar.Math.Lemmas.small_mod x (pow2 (swap_bits sz))
    else ()
  | ToBE -> ()
  | Bswap -> ()

(* --- main per-instruction simulation ------------------------------------- *)

#push-options "--z3rlimit 150 --fuel 1 --ifuel 2"

let check_insn_sound (m: mode) (ts: tystate) (rf: regfile) (i: insn{~(Exit? i)})
  : Lemma (requires agree ts rf /\ Some? (check m ts i))
          (ensures Some? (stepx (sem_of m) rf i) /\
                   agree (Some?.v (check m ts i)) (Some?.v (stepx (sem_of m) rf i))) =
  match i with
  | Alu w op dst src ->
    let a64 = Some?.v (read ts dst) in
    let b = Some?.v (aiv ts w src) in
    agree_lookup ts rf dst;
    let dv = Some?.v (rf dst) in
    aiv_sound ts rf w src;
    let s = Some?.v (opbits rf w src) in
    (match w with
     | W64 -> ()
     | W32 -> narrow32_sound a64 dv);
    tf_alu_sound (bits w) op (narrow w a64) b (regbits w dv) s;
    (* Strict mode: the accepted operand is defined under Defensive semantics *)
    assert (allowed m op w src b);
    (match op with
     | DIV | SDIV | MOD | SMOD -> ()
     | LSH | RSH | ARSH -> ()
     | _ -> ());
    agree_update ts rf dst
      (widen w (tf_alu (bits w) op (narrow w a64) b))
      (res64 w (alu_sem w op (regbits w dv) s))
  | Neg w dst ->
    agree_lookup ts rf dst;
    let dv = Some?.v (rf dst) in
    agree_update ts rf dst
      (widen w (havoc (bits w)))
      (res64 w (wrap (bits w) (0 - regbits w dv)))
  | Mov w dst src ->
    aiv_sound ts rf w src;
    let b = Some?.v (aiv ts w src) in
    let s = Some?.v (opbits rf w src) in
    agree_update ts rf dst (widen w b) (res64 w s)
  | MovSX w sz dst src ->
    agree_lookup ts rf src;
    let a64 = Some?.v (read ts src) in
    let sv_ = Some?.v (rf src) in
    (match w with
     | W64 -> ()
     | W32 -> narrow32_sound a64 sv_);
    let f = movsx_bits sz in
    tf_movsx_sound (bits w) f (narrow w a64) (regbits w sv_);
    agree_update ts rf dst
      (widen w (tf_movsx (bits w) f (narrow w a64)))
      (res64 w (sext f (bits w) (regbits w sv_)))
  | Swap k sz dst ->
    agree_lookup ts rf dst;
    let a = Some?.v (read ts dst) in
    let dv = Some?.v (rf dst) in
    tf_swap_sound k sz a (U64.v dv);
    FStar.Math.Lemmas.pow2_le_compat 64 (swap_bits sz);
    agree_update ts rf dst (tf_swap k sz a) (to_u64 (swap_sem k sz (U64.v dv)))
  | Assert_ r bound ->
    agree_lookup ts rf r

#pop-options

(* --- whole-program soundness --------------------------------------------- *)

let rec run_sound (m: mode) (ts: tystate) (rf: regfile) (p: program)
  : Lemma (requires agree ts rf /\ Some? (check_prog m ts p))
          (ensures Some? (runx (sem_of m) rf p))
          (decreases p) =
  match p with
  | [] -> ()
  | Exit :: _ -> agree_lookup ts rf R0
  | i :: rest ->
    check_insn_sound m ts rf i;
    run_sound m (Some?.v (check m ts i)) (Some?.v (stepx (sem_of m) rf i)) rest

let soundness (m: mode) (p: program)
  : Lemma (requires accepts m p)
          (ensures Some? (runx (sem_of m) rf0 p)) =
  run_sound m ts0 rf0 p
