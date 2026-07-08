(* Ebpf.Emit — pretty-print a lowered program (Ebpf.Ast.program) as Keel `.kir`
   text (M2.3.3), the exact format `ir/certifier`'s parser reads.

   The DSL author's `Assert (Var v) bound` became an `Assert_` pseudo-insn in
   the lowered program; here it prints as `@assert (bvule rN (_ bvBOUND 64))`.
   The certifier then proves those claims (using the verified interval /
   division rules) and emits the certificate + bytecode. So "bound
   propagation" is the certifier's job; this module just places the author's
   claims at the right program points and renders the instruction stream.

   `emit_dsl` chains Ebpf.Lower.lower with the printer: DSL -> .kir text. *)
module Ebpf.Emit

open FStar.Mul
open Ebpf.Int
open Ebpf.Ast
module U64 = FStar.UInt64
module I32 = FStar.Int32
module L = Ebpf.Lower
module D = Ebpf.Dsl

(* --- decimal rendering (avoid relying on a library string_of_int) --- *)
let digit (d: nat{d < 10}) : string =
  match d with
  | 0 -> "0" | 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
  | 5 -> "5" | 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9"

let rec dec_of_nat (n: nat) : Tot string (decreases n) =
  if n < 10 then digit n else dec_of_nat (n / 10) ^ digit (n % 10)

let dec_of_int (i: int) : string =
  if i < 0 then "-" ^ dec_of_nat (- i) else dec_of_nat i

(* --- renderers --- *)
let reg_s (r: reg) : string =
  match r with
  | R0 -> "r0" | R1 -> "r1" | R2 -> "r2" | R3 -> "r3" | R4 -> "r4" | R5 -> "r5"
  | R6 -> "r6" | R7 -> "r7" | R8 -> "r8" | R9 -> "r9" | R10 -> "r10"

let width_s (w: width) : string = match w with | W32 -> "32" | W64 -> "64"

let alu_s (op: alu_op) : string =
  match op with
  | ADD -> "add" | SUB -> "sub" | MUL -> "mul" | DIV -> "div" | SDIV -> "sdiv"
  | MOD -> "mod" | SMOD -> "smod" | AND -> "and" | OR -> "or" | XOR -> "xor"
  | LSH -> "lsh" | RSH -> "rsh" | ARSH -> "arsh"

let operand_s (o: operand) : string =
  match o with
  | OpReg r -> reg_s r
  | OpImm i -> dec_of_int (I32.v i)

let insn_s (i: insn) : string =
  match i with
  | Mov w dst src -> "  mov" ^ width_s w ^ " " ^ reg_s dst ^ ", " ^ operand_s src
  | Alu w op dst src -> "  " ^ alu_s op ^ width_s w ^ " " ^ reg_s dst ^ ", " ^ operand_s src
  | Neg w dst -> "  neg" ^ width_s w ^ " " ^ reg_s dst
  | Assert_ r bound ->
    "  @assert (bvule " ^ reg_s r ^ " (_ bv" ^ dec_of_nat (U64.v bound) ^ " 64))"
  | Exit -> "  exit"
  | MovSX w sz dst src -> "  ; movsx (unsupported by emitter)"
  | Swap k sz dst -> "  ; bswap (unsupported by emitter)"

let rec body_s (p: program) : string =
  match p with
  | [] -> ""
  | i :: rest -> insn_s i ^ "\n" ^ body_s rest

let emit_kir (p: program) : string =
  ".keel 0\n.mode kernel\n.prog\n" ^ body_s p

let emit_dsl (p: D.prog) : option string =
  match L.lower p with
  | Some prog -> Some (emit_kir prog)
  | None -> None
