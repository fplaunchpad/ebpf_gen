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
module T = FStar.Tactics.V2

let steps = [primops; iota; zeta; delta]

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
  ())
