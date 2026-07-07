(* Ebpf.Check — the dual-mode verifier/checker for the arithmetic subset.

   `requires`-side transcription of the constraint sources:
   - universal (both modes, mirrors Linux + Veritas spec.dfy):
     * destination register is never R10          (spec.dfy: every ALU method)
     * no read of an uninitialized register       (SP5 / type_check_* predicates)
     * R10 is not readable as a scalar (M1: scalar-only register file)
     * immediate divisor 0 rejected                (spec.dfy Div*/Mod*_IMM requires)
     * immediate shift amount >= width rejected    (spec.dfy Bv*_IMM requires)
     * (W32, SX32) is not a valid instruction
     * R0 initialized at Exit                      (return-code.dfy)
     * Assert_ r k requires provable r <= k        (our pseudo-instruction)
   - Strict mode only (clean-slate spec):
     * register divisor provably nonzero           (interval excludes 0)
     * register shift amount provably < width
   - Kernel mode (kernel-faithful): register divisor / oversized shift
     accepted; the result is havoc — matching the Linux verifier, which
     never rejects them (runtime semantics are total) but marks the
     destination unknown.

   Mode changes acceptance only; the transfer functions (Ebpf.Interval)
   and the machine semantics are shared. *)
module Ebpf.Check

open FStar.Mul
open Ebpf.Ast
open Ebpf.Int
open Ebpf.Semantics
open Ebpf.Interval
module U64 = FStar.UInt64

type mode = | Strict | Kernel

type tystate = reg -> option (iv 64)

(* R10 is the (read-only) frame pointer — a pointer, not a scalar; in the
   scalar-only M1 fragment it is neither readable nor writable *)
let read (ts: tystate) (r: reg) : option (iv 64) =
  if r = R10 then None else ts r

let wr (ts: tystate) (r: reg) (i: iv 64) : tystate =
  fun r' -> if r' = r then Some i else ts r'

(* abstract operand value at width w *)
let aiv (ts: tystate) (w: width) (o: operand) : option (iv (bits w)) =
  match o with
  | OpImm i ->
    (match w with
     | W64 -> Some (exact #64 (imm64 i))
     | W32 -> Some (exact #32 (imm32 i)))
  | OpReg r ->
    (match read ts r with
     | None -> None
     | Some a ->
       (match w with
        | W64 -> Some a
        | W32 -> Some (narrow32 a)))

let narrow (w: width) (a: iv 64) : iv (bits w) =
  match w with
  | W64 -> a
  | W32 -> narrow32 a

let widen (w: width) (a: iv (bits w)) : iv 64 =
  match w with
  | W64 -> a
  | W32 -> widen32 a

(* mode-dependent acceptance of an ALU instruction's second operand *)
let allowed (m: mode) (op: alu_op) (w: width) (src: operand) (b: iv (bits w)) : bool =
  match op with
  | DIV | SDIV | MOD | SMOD ->
    (match src with
     | OpImm _ -> b.ilo > 0            (* exact interval: imm pattern <> 0 *)
     | OpReg _ -> (match m with
                  | Strict -> b.ilo > 0
                  | Kernel -> true))
  | LSH | RSH | ARSH ->
    (match src with
     | OpImm _ -> b.ihi < bits w       (* exact: also rejects negative imm *)
     | OpReg _ -> (match m with
                  | Strict -> b.ihi < bits w
                  | Kernel -> true))
  | _ -> true

let tf_movsx (n: pos) (f: pos{f <= n}) (a: iv n) : iv n =
  if a.ihi < pow2 (f - 1) then a else havoc n

let tf_swap (k: swap_kind) (sz: swap_sz) (a: iv 64) : iv 64 =
  FStar.Math.Lemmas.pow2_le_compat 64 (swap_bits sz);
  match k with
  | ToLE -> if a.ihi < pow2 (swap_bits sz) then a else mk 0 (pow2 (swap_bits sz) - 1)
  | ToBE | Bswap -> mk 0 (pow2 (swap_bits sz) - 1)

let check (m: mode) (ts: tystate) (i: insn) : option tystate =
  match i with
  | Exit ->
    (match read ts R0 with Some _ -> Some ts | None -> None)
  | Alu w op dst src ->
    if dst = R10 then None
    else
      (match read ts dst, aiv ts w src with
       | Some a64, Some b ->
         if allowed m op w src b
         then Some (wr ts dst (widen w (tf_alu (bits w) op (narrow w a64) b)))
         else None
       | _, _ -> None)
  | Neg w dst ->
    if dst = R10 then None
    else
      (match read ts dst with
       | Some _ -> Some (wr ts dst (widen w (havoc (bits w))))
       | None -> None)
  | Mov w dst src ->
    if dst = R10 then None
    else
      (match aiv ts w src with
       | Some b -> Some (wr ts dst (widen w b))
       | None -> None)
  | MovSX w sz dst src ->
    if dst = R10 || (W32? w && SX32? sz) then None
    else
      (match read ts src with
       | Some a64 -> Some (wr ts dst (widen w (tf_movsx (bits w) (movsx_bits sz) (narrow w a64))))
       | None -> None)
  | Swap k sz dst ->
    if dst = R10 then None
    else
      (match read ts dst with
       | Some a -> Some (wr ts dst (tf_swap k sz a))
       | None -> None)
  | Assert_ r bound ->
    (match read ts r with
     | Some a -> if a.ihi <= U64.v bound then Some ts else None
     | None -> None)

(* whole straight-line program: instructions then a single terminal Exit *)
let rec check_prog (m: mode) (ts: tystate) (p: program) : option tystate =
  match p with
  | [] -> None
  | [Exit] -> check m ts Exit
  | Exit :: _ -> None                    (* unreachable trailing code *)
  | i :: rest ->
    (match check m ts i with
     | Some ts' -> check_prog m ts' rest
     | None -> None)

(* initial abstract state: nothing initialized (M1: scalar-only) *)
let ts0 : tystate = fun _ -> None

let accepts (m: mode) (p: program) : bool = Some? (check_prog m ts0 p)
