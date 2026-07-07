(* Ebpf.Serialize — instruction list -> real eBPF bytecode (RFC 9669 wire
   format, 8-byte instructions, little-endian). `Assert_` is erased.

   Encoding cross-checked against include/uapi/linux/bpf.h:
   opcode = op | source | class; classes ALU32=0x04, ALU64=0x07, JMP=0x05;
   SDIV/SMOD are DIV/MOD with offset=1; MOVSX is MOV with offset=8/16/32;
   byte swaps use the END op (TO_LE/TO_BE via the source bit in class ALU,
   unconditional BSWAP in class ALU64), width in imm. *)
module Ebpf.Serialize

open FStar.Mul
open FStar.List.Tot
open Ebpf.Ast
open Ebpf.Int
module I32 = FStar.Int32

let byte = b:nat{b < 256}

let reg_num (r: reg) : n:nat{n < 16} =
  match r with
  | R0 -> 0 | R1 -> 1 | R2 -> 2 | R3 -> 3 | R4 -> 4 | R5 -> 5
  | R6 -> 6 | R7 -> 7 | R8 -> 8 | R9 -> 9 | R10 -> 10

let cls (w: width) : n:nat{n <= 0x07} = match w with | W32 -> 0x04 | W64 -> 0x07

let op_bits (op: alu_op) : n:nat{n <= 0xc0} =
  match op with
  | ADD -> 0x00 | SUB -> 0x10 | MUL -> 0x20 | DIV -> 0x30 | SDIV -> 0x30
  | OR  -> 0x40 | AND -> 0x50 | LSH -> 0x60 | RSH -> 0x70
  | MOD -> 0x90 | SMOD -> 0x90 | XOR -> 0xa0 | ARSH -> 0xc0

let op_off (op: alu_op) : nat =
  match op with
  | SDIV | SMOD -> 1
  | _ -> 0

let src_bit (o: operand) : n:nat{n <= 0x08} =
  match o with | OpReg _ -> 0x08 | OpImm _ -> 0x00

(* k little-endian bytes of v *)
let rec le_bytes (k: nat) (v: nat) : l:list byte{length l = k} =
  if k = 0 then [] else (v % 256) :: le_bytes (k - 1) (v / 256)

(* one 8-byte instruction: opcode, dst|src<<4, off (le16), imm (le32) *)
let fields (opcode: nat{opcode < 256}) (dst: reg) (src: nat{src < 16})
           (off: nat) (imm: nat) : list byte =
  opcode :: (reg_num dst + 16 * src) :: (le_bytes 2 off @ le_bytes 4 imm)

let op_imm (o: operand) : nat =
  match o with
  | OpImm i -> imm32 i
  | OpReg _ -> 0

let op_src (o: operand) : n:nat{n < 16} =
  match o with
  | OpImm _ -> 0
  | OpReg r -> reg_num r

let swap_imm (sz: swap_sz) : nat =
  match sz with | SW16 -> 16 | SW32 -> 32 | SW64 -> 64

let movsx_off (sz: movsx_sz) : nat =
  match sz with | SX8 -> 8 | SX16 -> 16 | SX32 -> 32

let encode_insn (i: insn) : list byte =
  match i with
  | Alu w op dst src ->
    fields (op_bits op + src_bit src + cls w) dst (op_src src) (op_off op) (op_imm src)
  | Neg w dst ->
    fields (0x80 + cls w) dst 0 0 0
  | Mov w dst src ->
    fields (0xb0 + src_bit src + cls w) dst (op_src src) 0 (op_imm src)
  | MovSX w sz dst src ->
    fields (0xb0 + 0x08 + cls w) dst (reg_num src) (movsx_off sz) 0
  | Swap ToLE sz dst  -> fields (0xd0 + 0x04) dst 0 0 (swap_imm sz)         (* TO_LE,  ALU32 *)
  | Swap ToBE sz dst  -> fields (0xd0 + 0x08 + 0x04) dst 0 0 (swap_imm sz) (* TO_BE,  ALU32 *)
  | Swap Bswap sz dst -> fields (0xd0 + 0x07) dst 0 0 (swap_imm sz)        (* BSWAP,  ALU64 *)
  | Assert_ _ _ -> []                                                       (* erased *)
  | Exit -> fields 0x95 R0 0 0 0

let rec encode (p: program) : list byte =
  match p with
  | [] -> []
  | i :: rest -> encode_insn i @ encode rest

(* --- hex dump (usable before OCaml extraction is wired up) --------------- *)

let nib (n: nat{n < 16}) : string =
  match n with
  | 0 -> "0" | 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4" | 5 -> "5"
  | 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9" | 10 -> "a" | 11 -> "b"
  | 12 -> "c" | 13 -> "d" | 14 -> "e" | 15 -> "f"

let byte_hex (b: byte) : string = nib (b / 16) ^ nib (b % 16)

let rec hex_of (l: list byte) : string =
  match l with
  | [] -> ""
  | b :: t -> byte_hex b ^ hex_of t

let serialize_hex (p: program) : string = hex_of (encode p)

(* encoding sanity anchors (computed at typechecking time):
   mov64 r0, 0 = b7 00 ... ; exit = 95 00 ... *)
let _ = assert_norm
  (encode [Mov W64 R0 (OpImm 0l); Exit] =
   [0xb7; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
    0x95; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00])

(* add64 r1, r2 = 0f 21 *)
let _ = assert_norm
  (encode [Alu W64 ADD R1 (OpReg R2)] =
   [0x0f; 0x21; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00])
