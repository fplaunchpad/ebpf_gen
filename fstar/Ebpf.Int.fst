(* Ebpf.Int — arithmetic helpers over mathematical integers with explicit
   wrapping, shared by the machine semantics and the checker soundness proofs.

   Register values are U64.t; all operation semantics are phrased as
   math-integer computations followed by a wrap to the target width.
   Euclidean div/mod (F* Prims semantics) + wrap gives the RFC 9669
   behaviors for free (e.g. SDIV INT64_MIN / -1 = INT64_MIN). *)
module Ebpf.Int

module U64 = FStar.UInt64
module I32 = FStar.Int32
open FStar.Mul

(* bit pattern of width n: an int in [0, 2^n) *)
let fits (n: pos) (x: int) : bool = 0 <= x && x < pow2 n

let wrap (n: pos) (x: int) : y:int{fits n y} =
  FStar.Math.Lemmas.lemma_mod_lt x (pow2 n);
  x % pow2 n

let to_u64 (x: int{fits 64 x}) : U64.t = U64.uint_to_t x

(* signed value of a width-n bit pattern (two's complement) *)
let sval (n: pos) (x: int{fits n x}) : int =
  if x >= pow2 (n - 1) then x - pow2 n else x

(* low n bits of a 64-bit pattern *)
let low (n: pos) (x: int) : y:int{fits n y} = wrap n x

(* sign-extend the low `f` bits of pattern x to a width-n pattern *)
let sext (f: pos) (n: pos{f <= n}) (x: int) : y:int{fits n y} =
  wrap n (sval f (low f x))

(* imm (i32) as a sign-extended 64-bit pattern (ALU64 immediate rule) *)
let imm64 (i: I32.t) : x:int{fits 64 x} = wrap 64 (I32.v i)

(* imm (i32) as a 32-bit pattern (ALU32 immediate rule) *)
let imm32 (i: I32.t) : x:int{fits 32 x} = wrap 32 (I32.v i)

(* truncated (toward-zero) division and remainder, per BPF SDIV/SMOD.
   b <> 0. Note trunc_mod a b = a - b * trunc_div a b. *)
let trunc_div (a: int) (b: int{b <> 0}) : int =
  if (a < 0) = (b < 0) then abs a / abs b else 0 - (abs a / abs b)

let trunc_mod (a: int) (b: int{b <> 0}) : int =
  a - b * trunc_div a b

(* byte swap of the low nb bytes; defensive wrap keeps the refinement
   trivial (the result provably fits 8*nb bits anyway) *)
let rec swap_bytes (nb: nat) (x: int) : int =
  if nb = 0 then 0
  else (x % 256) * pow2 (8 * (nb - 1)) + swap_bytes (nb - 1) (x / 256)

let bswap (nb: pos) (x: int) : y:int{fits (8 * nb) y} =
  wrap (8 * nb) (swap_bytes nb x)
