(* Ebpf.Dump — emit the differential-test manifest at typechecking time.

   Until OCaml extraction is wired up (opam fstar.lib), we normalize each
   example inside a tactic and print:
     MANIFEST <name> <hex> <strict-verdict> <kernel-mode-verdict>
   harness/gen_manifest.py turns fstar's output into manifest.tsv for
   harness/diff.py. *)
module Ebpf.Dump

open Ebpf.Ast
open Ebpf.Check
open Ebpf.Build
open Ebpf.Serialize
open Ebpf.Semantics
module T = FStar.Tactics.V2
module U64 = FStar.UInt64

let steps = [primops; iota; zeta; delta]

(* ---- M2.1-hole-A opcodes: value-checkable programs -----------------------
   Each puts a semantically-meaningful result in R0 so BPF_PROG_TEST_RUN's
   retval (r0 truncated to u32) validates the *computed value* against
   Ebpf.Semantics — not just the accept/reject verdict.  The `r0lo` asserts
   are the F*-derived expectations (machine-checked = the semantics), which we
   then compare to the real kernel's retval on kernel7. *)
let ex_sdiv       : program = [Mov W64 R0 (OpImm (-7l)); Alu W64 SDIV R0 (OpImm 2l); Exit]
let ex_smod       : program = [Mov W64 R0 (OpImm (-7l)); Alu W64 SMOD R0 (OpImm 2l); Exit]
let ex_movsx_neg  : program = [Mov W64 R1 (OpImm 200l); MovSX W64 SX8 R0 R1; Exit]
let ex_bswap16    : program = [Mov W64 R0 (OpImm 0x1234l); Swap Bswap SW16 R0; Exit]
let ex_bswap32    : program = [Mov W64 R0 (OpImm 0x12345678l); Swap Bswap SW32 R0; Exit]
let ex_bswap64    : program = [Mov W64 R0 (OpImm 0x12345678l); Swap Bswap SW64 R0; Exit]

(* r0 (low 32) after running the program under the Total ISA semantics *)
let r0lo (p: program) : int =
  match run rf0 p with
  | Some rf -> (match rf R0 with Some x -> U64.v x % 0x100000000 | None -> -1)
  | None -> -2

(* expected retvals, machine-derived from Ebpf.Semantics (checked at Dump time) *)
let _ = assert_norm (r0lo ex_sdiv      == 4294967293)   (* -3  = (-7) sdiv 2, toward zero (floor=-4) *)
let _ = assert_norm (r0lo ex_smod      == 4294967295)   (* -1  = (-7) smod 2, dividend's sign *)
let _ = assert_norm (r0lo ex_movsx_neg == 4294967240)   (* -56 = s8 of 200 (0xC8) sign-extended *)
let _ = assert_norm (r0lo ex_bswap16   == 0x3412)        (* byte-reverse 0x1234 *)
let _ = assert_norm (r0lo ex_bswap32   == 0x78563412)    (* byte-reverse 0x12345678 *)
let _ = assert_norm (r0lo ex_bswap64   == 0)             (* low 32 of 0x7856341200000000 *)

let dump (name: string) (p: program) : T.Tac unit =
  let h = T.term_to_string (T.norm_term steps (quote (serialize_hex p))) in
  let s = T.term_to_string (T.norm_term steps (quote (accepts Strict p))) in
  let k = T.term_to_string (T.norm_term steps (quote (accepts Kernel p))) in
  T.print ("MANIFEST\t" ^ name ^ "\t" ^ h ^ "\t" ^ s ^ "\t" ^ k)

let _ = assert True by (
  dump "ex_shift" ex_shift;
  dump "ex_div" ex_div;
  dump "ex_alu32" ex_alu32;
  dump "ex_chain" ex_chain;
  dump "ex_movsx" ex_movsx;
  dump "ex_mul" ex_mul;
  dump "ex_div0_reg" ex_div0_reg;
  dump "ex_shift_reg" ex_shift_reg;
  dump "ex_uninit" [Mov W64 R0 (OpReg R3); Exit];
  dump "ex_no_r0" [Exit];
  dump "ex_r10_dst" [Alu W64 ADD R10 (OpImm 1l); Exit];
  dump "ex_imm_div0" [Mov W64 R1 (OpImm 1l); Alu W64 DIV R1 (OpImm 0l);
                      Mov W64 R0 (OpImm 0l); Exit];
  dump "ex_imm_shift64" [Mov W64 R1 (OpImm 1l); Alu W64 LSH R1 (OpImm 64l);
                         Mov W64 R0 (OpImm 0l); Exit];
  (* M2.1 hole A opcodes (SDIV/SMOD/MOVSX/bswap), value-checkable *)
  dump "ex_sdiv" ex_sdiv;
  dump "ex_smod" ex_smod;
  dump "ex_movsx_neg" ex_movsx_neg;
  dump "ex_bswap16" ex_bswap16;
  dump "ex_bswap32" ex_bswap32;
  dump "ex_bswap64" ex_bswap64;
  ())
