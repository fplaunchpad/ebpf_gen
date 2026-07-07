(* Ebpf.Interval — unsigned interval abstract domain for width-n values,
   with per-operation transfer functions and their soundness lemmas
   against the machine semantics (Ebpf.Semantics.alu_semn).

   Precision policy (M1): precise transfer for ADD/SUB/MUL (overflow-checked),
   AND (min upper bound), DIV/MOD (divisor interval excluding 0),
   constant-amount shifts, RSH (never increases); width-bounded havoc for
   the signed ops (SDIV/SMOD/ARSH), OR/XOR, and dynamic-amount LSH.
   Precision upgrades are sound-by-construction extensions later.

   Note the transfer functions are mode-independent: verifier *acceptance*
   (strict vs kernel-faithful) is decided in Ebpf.Check; the abstraction
   here must simply be sound for every accepted case. *)
module Ebpf.Interval

open FStar.Mul
open Ebpf.Ast
open Ebpf.Int
open Ebpf.Semantics
module UInt = FStar.UInt
module U64 = FStar.UInt64

type iv (n: pos) = {
  ilo: nat;
  ihi: h:int{ilo <= h /\ h < pow2 n}
}

let inb (#n: pos) (i: iv n) (x: int) : bool =
  i.ilo <= x && x <= i.ihi

let mk (#n: pos) (l: nat) (h: int{l <= h /\ h < pow2 n}) : iv n = { ilo = l; ihi = h }

let havoc (n: pos) : iv n = mk 0 (pow2 n - 1)

let exact (#n: pos) (x: int{fits n x}) : iv n = mk x x

(* --- helper lemmas ------------------------------------------------------ *)

(* division is antitone in the divisor *)
let div_antitone (a: nat) (d1: pos) (d2: pos{d1 <= d2})
  : Lemma (a / d2 <= a / d1) =
  FStar.Math.Lemmas.lemma_div_mod a d2;
  FStar.Math.Lemmas.lemma_mult_le_right (a / d2) d1 d2;
  FStar.Math.Lemmas.lemma_div_le ((a / d2) * d1) a d1;
  FStar.Math.Lemmas.cancel_mul_div (a / d2) d1

(* division by >=1 never increases *)
let div_le_self (a: nat) (d: pos) : Lemma (a / d <= a) =
  div_antitone a 1 d

let mul_mono (a1: nat) (a2: nat{a1 <= a2}) (b1: nat) (b2: nat{b1 <= b2})
  : Lemma (a1 * b1 <= a2 * b2) =
  FStar.Math.Lemmas.lemma_mult_le_left a1 b1 b2;
  FStar.Math.Lemmas.lemma_mult_le_right b2 a1 a2

(* --- transfer function -------------------------------------------------- *)

let is_const (#n: pos) (i: iv n) : bool = i.ilo = i.ihi

let tf_alu (n: pos) (op: alu_op) (a: iv n) (b: iv n) : iv n =
  match op with
  | ADD ->
    if a.ihi + b.ihi < pow2 n then mk (a.ilo + b.ilo) (a.ihi + b.ihi)
    else if is_const a && is_const b then exact #n (wrap n (a.ilo + b.ilo))
    else havoc n
  | SUB ->
    if b.ihi <= a.ilo then mk (a.ilo - b.ihi) (a.ihi - b.ilo)
    else if is_const a && is_const b then exact #n (wrap n (a.ilo - b.ilo))
    else havoc n
  | MUL ->
    if a.ihi * b.ihi < pow2 n
    then (mul_mono a.ilo a.ihi b.ilo b.ihi; mk (a.ilo * b.ilo) (a.ihi * b.ihi))
    else if is_const a && is_const b then exact #n (wrap n (a.ilo * b.ilo))
    else havoc n
  | DIV ->
    if b.ilo > 0
    then (FStar.Math.Lemmas.lemma_div_le a.ilo a.ihi b.ihi;
          div_antitone a.ihi b.ilo b.ihi;
          div_le_self a.ihi b.ilo;
          mk (a.ilo / b.ihi) (a.ihi / b.ilo))
    else havoc n
  | MOD ->
    if b.ilo > 0 then mk 0 (b.ihi - 1)
    else havoc n
  | AND ->
    mk 0 (if a.ihi <= b.ihi then a.ihi else b.ihi)
  | RSH ->
    if is_const b && b.ilo < n
    then (FStar.Math.Lemmas.lemma_div_le a.ilo a.ihi (pow2 b.ilo);
          div_le_self a.ihi (pow2 b.ilo);
          mk (a.ilo / pow2 b.ilo) (a.ihi / pow2 b.ilo))
    else mk 0 a.ihi                       (* RSH never increases the value *)
  | LSH ->
    if is_const b && b.ilo < n && a.ihi * pow2 b.ilo < pow2 n
    then (mul_mono a.ilo a.ihi (pow2 b.ilo) (pow2 b.ilo);
          mk (a.ilo * pow2 b.ilo) (a.ihi * pow2 b.ilo))
    else havoc n
  | SDIV | SMOD | ARSH | OR | XOR -> havoc n

(* --- soundness ---------------------------------------------------------- *)

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"

let tf_alu_sound (n: pos) (op: alu_op) (a: iv n) (b: iv n)
                 (d: int{fits n d}) (s: int{fits n s})
  : Lemma (requires inb a d /\ inb b s)
          (ensures inb (tf_alu n op a b) (alu_semn n op d s)) =
  match op with
  | ADD ->
    if a.ihi + b.ihi < pow2 n
    then FStar.Math.Lemmas.small_mod (d + s) (pow2 n)
    else ()                (* const-const: d = a.ilo, s = b.ilo, exact wrap *)
  | SUB ->
    if b.ihi <= a.ilo
    then FStar.Math.Lemmas.small_mod (d - s) (pow2 n)
    else ()
  | MUL ->
    if a.ihi * b.ihi < pow2 n
    then begin
      mul_mono a.ilo a.ihi b.ilo b.ihi;
      mul_mono a.ilo d b.ilo s;         (* a.ilo * b.ilo <= d * s *)
      mul_mono d a.ihi s b.ihi;         (* d * s <= a.ihi * b.ihi *)
      FStar.Math.Lemmas.small_mod (d * s) (pow2 n)
    end
    else ()
  | DIV ->
    if b.ilo > 0
    then begin
      (* d/s <= a.ihi/b.ilo *)
      FStar.Math.Lemmas.lemma_div_le d a.ihi s;
      div_antitone a.ihi b.ilo s;
      (* a.ilo/b.ihi <= d/s *)
      FStar.Math.Lemmas.lemma_div_le a.ilo d b.ihi;
      div_antitone d s b.ihi;
      div_le_self d s;
      FStar.Math.Lemmas.small_mod (d / s) (pow2 n)
    end
    else ()
  | MOD ->
    if b.ilo > 0
    then begin
      FStar.Math.Lemmas.lemma_mod_lt d s;
      FStar.Math.Lemmas.small_mod (d % s) (pow2 n)
    end
    else ()
  | AND ->
    UInt.logand_le #n d s
  | RSH ->
    let j = s % n in
    div_le_self d (pow2 j);
    FStar.Math.Lemmas.small_mod (d / pow2 j) (pow2 n);
    if is_const b && b.ilo < n
    then begin
      (* s = b.ilo < n so the shift mask is the identity: j = s *)
      FStar.Math.Lemmas.small_mod s n;
      FStar.Math.Lemmas.lemma_div_le a.ilo d (pow2 j);
      FStar.Math.Lemmas.lemma_div_le d a.ihi (pow2 j)
    end
    else ()
  | LSH ->
    if is_const b && b.ilo < n && a.ihi * pow2 b.ilo < pow2 n
    then begin
      let j = s % n in
      FStar.Math.Lemmas.small_mod s n;    (* s = b.ilo < n *)
      mul_mono a.ilo d (pow2 j) (pow2 j);
      mul_mono d a.ihi (pow2 j) (pow2 j);
      mul_mono a.ilo a.ihi (pow2 j) (pow2 j);
      FStar.Math.Lemmas.small_mod (d * pow2 j) (pow2 n)
    end
    else ()
  | SDIV | SMOD | ARSH | OR | XOR -> ()

#pop-options

(* width narrowing/widening between the 64-bit register state and the
   operating width of an ALU32 instruction *)

let narrow32 (i: iv 64) : iv 32 =
  if i.ihi < pow2 32 then mk i.ilo i.ihi else havoc 32

let narrow32_sound (i: iv 64) (x: U64.t)
  : Lemma (requires inb i (U64.v x))
          (ensures inb (narrow32 i) (low 32 (U64.v x))) =
  if i.ihi < pow2 32
  then FStar.Math.Lemmas.small_mod (U64.v x) (pow2 32)
  else ()

let widen32 (i: iv 32) : iv 64 =
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  mk i.ilo i.ihi
