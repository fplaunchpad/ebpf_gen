(* Ebpf.Semantics — executable machine semantics for the arithmetic subset.

   Ground truth: RFC 9669, cross-checked against Linux 6.8 and the Veritas
   Dafny spec's `ensures` clauses. Key rules encoded here:
   - ALU32 (W32) computes on the low 32 bits and ZERO-EXTENDS the result.
   - ALU64 immediates are sign-extended 32->64 (imm64); ALU32 immediates
     are used as 32-bit patterns (imm32).
   - DIV/MOD are unsigned; x/0 = 0, x%0 = x (width-adjusted, so W32 x%0
     zero-extends the truncated dst, per Veritas Mod32_REG).
   - SDIV/SMOD are truncated (toward-zero); math-then-wrap yields
     SDIV INT64_MIN / -1 = INT64_MIN, SMOD -> 0 (RFC 9669).
   - Shift amounts are masked to the operand width (s % n).
   - Byte swaps: little-endian host pinned (TO_LE = truncate).

   `run` returns Some final-regfile iff execution is SAFE: no read of an
   uninitialized register, every Assert_ holds, and R0 is initialized at
   Exit. Getting "stuck" (None) is the event the checker must rule out. *)
module Ebpf.Semantics

open FStar.Mul
open Ebpf.Ast
open Ebpf.Int
module U64 = FStar.UInt64
module UInt = FStar.UInt

type regfile = reg -> option U64.t

let bits (w: width) : pos = match w with | W32 -> 32 | W64 -> 64

(* a register's value viewed at width w *)
let regbits (w: width) (x: U64.t) : y:int{fits (bits w) y} =
  match w with
  | W64 -> U64.v x
  | W32 -> low 32 (U64.v x)

(* operand value at width w; None = uninitialized register read *)
let opbits (rf: regfile) (w: width) (o: operand) : option (y:int{fits (bits w) y}) =
  match o with
  | OpImm i ->
    (match w with
     | W64 -> Some (imm64 i)
     | W32 -> Some (imm32 i))
  | OpReg r ->
    (match rf r with
     | None -> None
     | Some x -> Some (regbits w x))

(* width-adjusted result written back to a 64-bit register:
   W32 results are zero-extended by construction (fits 32 ==> fits 64) *)
let res64 (w: width) (x: int{fits (bits w) x}) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  to_u64 x

let updr (rf: regfile) (r: reg) (v: U64.t) : regfile =
  fun r' -> if r' = r then Some v else rf r'

let alu_semn (n: pos) (op: alu_op)
             (d: int{fits n d}) (s: int{fits n s})
  : r:int{fits n r} =
  match op with
  | ADD  -> wrap n (d + s)
  | SUB  -> wrap n (d - s)
  | MUL  -> wrap n (d * s)
  | DIV  -> if s = 0 then 0 else wrap n (d / s)
  | SDIV -> if s = 0 then 0 else wrap n (trunc_div (sval n d) (sval n s))
  | MOD  -> if s = 0 then d else wrap n (d % s)
  | SMOD -> if s = 0 then d else wrap n (trunc_mod (sval n d) (sval n s))
  | AND  -> UInt.logand #n d s
  | OR   -> UInt.logor  #n d s
  | XOR  -> UInt.logxor #n d s
  | LSH  -> wrap n (d * pow2 (s % n))
  | RSH  -> wrap n (d / pow2 (s % n))
  | ARSH -> wrap n (sval n d / pow2 (s % n))

let alu_sem (w: width) (op: alu_op)
            (d: int{fits (bits w) d}) (s: int{fits (bits w) s})
  : r:int{fits (bits w) r} =
  alu_semn (bits w) op d s

let movsx_bits (sz: movsx_sz) : pos =
  match sz with | SX8 -> 8 | SX16 -> 16 | SX32 -> 32

let swap_bits (sz: swap_sz) : pos =
  match sz with | SW16 -> 16 | SW32 -> 32 | SW64 -> 64

let swap_sem (k: swap_kind) (sz: swap_sz) (d: int{fits 64 d})
  : r:int{fits (swap_bits sz) r} =
  match k with
  | ToLE  -> low (swap_bits sz) d               (* LE host: truncate *)
  | ToBE  -> bswap (swap_bits sz / 8) d
  | Bswap -> bswap (swap_bits sz / 8) d

(* Two observation levels:
   - Total: the ISA semantics — div/0 and oversized shift amounts are
     DEFINED (x/0=0, shifts masked); matches what hardware/interpreter does.
   - Defensive: div/mod by zero and shift amounts >= width are STUCK.
     Strict-mode checking proves these events never happen, which is
     exactly the extra guarantee over kernel-faithful mode. *)
type semantics = | Total | Defensive

let alu_defined (n: pos) (op: alu_op) (s: int{fits n s}) : bool =
  match op with
  | DIV | SDIV | MOD | SMOD -> s <> 0
  | LSH | RSH | ARSH -> s < n
  | _ -> true

(* single-instruction step; None = stuck (unsafe). Exit is handled by run. *)
let stepx (sm: semantics) (rf: regfile) (i: insn) : option regfile =
  match i with
  | Exit -> None
  | Alu w op dst src ->
    (match rf dst, opbits rf w src with
     | Some dv, Some s ->
       if Defensive? sm && not (alu_defined (bits w) op s) then None
       else Some (updr rf dst (res64 w (alu_sem w op (regbits w dv) s)))
     | _, _ -> None)
  | Neg w dst ->
    (match rf dst with
     | Some dv -> Some (updr rf dst (res64 w (wrap (bits w) (0 - regbits w dv))))
     | None -> None)
  | Mov w dst src ->
    (match opbits rf w src with
     | Some s -> Some (updr rf dst (res64 w s))
     | None -> None)
  | MovSX w sz dst src ->
    (match rf src with
     | Some sv_ ->
       let f = movsx_bits sz in
       if f <= bits w
       then Some (updr rf dst (res64 w (sext f (bits w) (regbits w sv_))))
       else None                        (* (W32, SX32) is not a valid insn *)
     | None -> None)
  | Swap k sz dst ->
    (match rf dst with
     | Some dv ->
       FStar.Math.Lemmas.pow2_le_compat 64 (swap_bits sz);
       Some (updr rf dst (to_u64 (swap_sem k sz (U64.v dv))))
     | None -> None)
  | Assert_ r bound ->
    (match rf r with
     | Some x -> if U64.v x <= U64.v bound then Some rf else None
     | None -> None)

(* Safe execution of a straight-line program: must reach Exit with R0 set. *)
let rec runx (sm: semantics) (rf: regfile) (p: program) : option regfile =
  match p with
  | [] -> None
  | Exit :: _ -> (match rf R0 with Some _ -> Some rf | None -> None)
  | i :: rest ->
    (match stepx sm rf i with
     | Some rf' -> runx sm rf' rest
     | None -> None)

let step (rf: regfile) (i: insn) : option regfile = stepx Total rf i
let run (rf: regfile) (p: program) : option regfile = runx Total rf p

(* initial machine state: nothing usable as a scalar is initialized
   (R1=ctx and R10=fp are pointers — out of scope until M2/M3) *)
let rf0 : regfile = fun _ -> None
