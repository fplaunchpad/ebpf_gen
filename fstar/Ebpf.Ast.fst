(* Ebpf.Ast — deep embedding of the eBPF arithmetic (ALU) instruction subset.

   Milestone 1 scope: straight-line programs, scalar-only register file.
   Semantics ground truth: RFC 9669 (BPF ISA), cross-checked against the
   Linux 6.8 verifier and the Veritas Dafny spec (ebpf-dafny-spec/spec.dfy).

   `Assert_` is our own pseudo-instruction (an upper-bound claim on a
   register); it is erased at serialization and exists so that
   arithmetic-only programs carry non-vacuous proof obligations. *)
module Ebpf.Ast

module U64 = FStar.UInt64
module I32 = FStar.Int32

type reg =
  | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10

(* BPF_ALU (32-bit, upper bits zeroed) vs BPF_ALU64 *)
type width = | W32 | W64

(* Binary ALU operations; SDIV/SMOD are DIV/MOD with offset=1 (ISA v4). *)
type alu_op =
  | ADD | SUB | MUL | DIV | SDIV | MOD | SMOD
  | AND | OR  | XOR | LSH | RSH  | ARSH

(* Second operand: register or 32-bit immediate.
   ALU64+imm: imm is sign-extended to 64 bits (RFC 9669). *)
type operand =
  | OpReg : reg -> operand
  | OpImm : I32.t -> operand

(* MOVSX source sizes: 8/16 for both widths, 32 only for ALU64. *)
type movsx_sz = | SX8 | SX16 | SX32

(* Byte-swap family (BPF_END + unconditional BSWAP from ISA v4).
   On a little-endian target: TO_LE = truncate, TO_BE = swap+truncate. *)
type swap_kind = | ToLE | ToBE | Bswap
type swap_sz = | SW16 | SW32 | SW64

type insn =
  | Alu     : w:width -> op:alu_op -> dst:reg -> src:operand -> insn
  | Neg     : w:width -> dst:reg -> insn
  | Mov     : w:width -> dst:reg -> src:operand -> insn
  | MovSX   : w:width -> sz:movsx_sz -> dst:reg -> src:reg -> insn
  | Swap    : k:swap_kind -> sz:swap_sz -> dst:reg -> insn
  | Assert_ : r:reg -> bound:U64.t -> insn   (* claim: r <= bound; erased *)
  | Exit    : insn

type program = list insn
