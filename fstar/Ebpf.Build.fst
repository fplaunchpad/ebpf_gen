(* Ebpf.Build — correct-by-construction program authoring.

   Two styles:
   1. Whole-program: write a `list insn` and discharge `accepts m p` by
      normalization (`assert_norm`) — everything is concrete, so the
      checker simply computes.
   2. Incremental pipeline: `finish (start m |>. i1 |>. i2 ...)` — each
      `|>.` carries the refinement that the checker accepts the next
      instruction in the current abstract state, so an ill-typed program
      is a TYPE ERROR at the offending instruction.

   Negative tests use [@@expect_failure]: the program text is the test. *)
module Ebpf.Build

open FStar.Mul
open Ebpf.Ast
open Ebpf.Int
open Ebpf.Semantics
open Ebpf.Interval
open Ebpf.Check
module U64 = FStar.UInt64
module I32 = FStar.Int32
open FStar.List.Tot

(* --- prefix checking (no terminal Exit yet) ------------------------------ *)

let rec check_list (m: mode) (ts: tystate) (l: list insn) : option tystate =
  match l with
  | [] -> Some ts
  | i :: rest ->
    (match check m ts i with
     | Some ts' -> check_list m ts' rest
     | None -> None)

let rec no_exit (l: list insn) : bool =
  match l with
  | [] -> true
  | Exit :: _ -> false
  | _ :: t -> no_exit t

let rec check_list_snoc (m: mode) (ts: tystate) (l: list insn) (i: insn)
  : Lemma (ensures check_list m ts (l @ [i]) ==
                   (match check_list m ts l with
                    | Some ts' -> check m ts' i
                    | None -> None))
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs ->
    (match check m ts x with
     | Some ts' -> check_list_snoc m ts' xs i
     | None -> ())

let rec no_exit_snoc (l: list insn) (i: insn{~(Exit? i)})
  : Lemma (requires no_exit l) (ensures no_exit (l @ [i])) =
  match l with
  | [] -> ()
  | _ :: xs -> no_exit_snoc xs i

let rec check_prog_snoc_exit (m: mode) (ts: tystate) (l: list insn{no_exit l})
  : Lemma (ensures check_prog m ts (l @ [Exit]) ==
                   (match check_list m ts l with
                    | Some ts' -> check m ts' Exit
                    | None -> None))
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs ->
    (match check m ts x with
     | Some ts' -> check_prog_snoc_exit m ts' xs
     | None -> ())

(* --- the builder ---------------------------------------------------------- *)

noeq type bld (m: mode) = {
  body: l:list insn{no_exit l};
  bts:  tystate;
  bok:  squash (check_list m ts0 body == Some bts)
}

let start (m: mode) : bld m = { body = []; bts = ts0; bok = () }

let emit (#m: mode) (b: bld m) (i: insn{~(Exit? i) /\ Some? (check m b.bts i)})
  : bld m =
  check_list_snoc m ts0 b.body i;
  no_exit_snoc b.body i;
  { body = b.body @ [i]; bts = Some?.v (check m b.bts i); bok = () }

(* pipeline operator: `finish (start m |>. insn |>. insn)` *)
let ( |>. ) (#m: mode) (b: bld m) (i: insn{~(Exit? i) /\ Some? (check m b.bts i)})
  : bld m = emit b i

let finish (#m: mode) (b: bld m{Some? (check m b.bts Exit)})
  : p:program{accepts m p} =
  check_prog_snoc_exit m ts0 b.body;
  b.body @ [Exit]

(* --- positive examples ---------------------------------------------------- *)

(* BCF examples/shift_constraint pattern, re-expressed:
   r1 = 255; r1 &= 0x0f; r1 >>= 1; claim r1 <= 7; r0 = r1; exit *)
let ex_shift : p:program{accepts Strict p} =
  finish (start Strict
  |>. Mov W64 R1 (OpImm 255l)
  |>. Alu W64 AND R1 (OpImm 15l)
  |>. Alu W64 RSH R1 (OpImm 1l)
  |>. Assert_ R1 7uL
  |>. Mov W64 R0 (OpReg R1))

(* register-divisor division, provably nonzero: strict-mode accepted *)
let ex_div : p:program{accepts Strict p} =
  finish (start Strict
  |>. Mov W64 R1 (OpImm 100l)
  |>. Mov W64 R2 (OpImm 3l)
  |>. Alu W64 DIV R1 (OpReg R2)
  |>. Assert_ R1 33uL
  |>. Mov W64 R0 (OpImm 0l))

(* ALU32 zero-extension: mov32 r1,-1 yields 0xffffffff, not -1 *)
let ex_alu32 : p:program{accepts Strict p} =
  finish (start Strict
  |>. Mov W32 R1 (OpImm (-1l))
  |>. Assert_ R1 0xffffffffuL
  |>. Alu W32 ADD R1 (OpImm 1l)      (* wraps to 0 in 32 bits *)
  |>. Assert_ R1 0uL
  |>. Mov W64 R0 (OpImm 0l))

(* interval reasoning through a chain: (x & 0xf0) + 15 <= 255, then /16 *)
let ex_chain : p:program{accepts Strict p} =
  finish (start Strict
  |>. Mov W64 R3 (OpImm 1000l)
  |>. Alu W64 AND R3 (OpImm 0xf0l)
  |>. Alu W64 ADD R3 (OpImm 15l)
  |>. Assert_ R3 255uL
  |>. Alu W64 DIV R3 (OpImm 16l)
  |>. Assert_ R3 15uL
  |>. Mov W64 R0 (OpReg R3))

(* MOVSX stays precise when the value provably fits the narrow width *)
let ex_movsx : p:program{accepts Strict p} =
  finish (start Strict
  |>. Mov W64 R1 (OpImm 127l)
  |>. MovSX W64 SX8 R2 R1
  |>. Assert_ R2 127uL
  |>. Mov W64 R0 (OpImm 0l))

(* MUL within range stays exact *)
let ex_mul : p:program{accepts Strict p} =
  finish (start Strict
  |>. Mov W64 R1 (OpImm 1000l)
  |>. Alu W64 MUL R1 (OpReg R1)
  |>. Assert_ R1 1000000uL
  |>. Mov W64 R0 (OpImm 0l))

(* --- mode-divergence witnesses (the differential-test payload) ----------- *)

(* register divisor that MAY be zero: kernel-faithful accepts (runtime
   x/0 = 0), strict rejects. Whole-program style with assert_norm. *)
let ex_div0_reg : program = [
  Mov W64 R1 (OpImm 10l);
  Mov W64 R2 (OpImm 0l);
  Alu W64 DIV R1 (OpReg R2);
  Mov W64 R0 (OpImm 0l);
  Exit
]
let _ = assert_norm (accepts Kernel ex_div0_reg)
let _ = assert_norm (not (accepts Strict ex_div0_reg))

(* register shift amount >= width: kernel accepts (masked), strict rejects *)
let ex_shift_reg : program = [
  Mov W64 R1 (OpImm 1l);
  Mov W64 R2 (OpImm 200l);
  Alu W64 LSH R1 (OpReg R2);
  Mov W64 R0 (OpImm 0l);
  Exit
]
let _ = assert_norm (accepts Kernel ex_shift_reg)
let _ = assert_norm (not (accepts Strict ex_shift_reg))

(* --- rejected-by-both sanity (universal constraints) --------------------- *)

let _ = assert_norm (not (accepts Kernel [Mov W64 R0 (OpReg R3); Exit]))        (* uninit read *)
let _ = assert_norm (not (accepts Kernel [Exit]))                               (* R0 unset *)
let _ = assert_norm (not (accepts Kernel [Alu W64 ADD R10 (OpImm 1l); Exit]))   (* dst = r10 *)
let _ = assert_norm (not (accepts Kernel
  [Mov W64 R1 (OpImm 1l); Alu W64 DIV R1 (OpImm 0l); Mov W64 R0 (OpImm 0l); Exit]))  (* imm/0 *)
let _ = assert_norm (not (accepts Kernel
  [Mov W64 R1 (OpImm 1l); Alu W64 LSH R1 (OpImm 64l); Mov W64 R0 (OpImm 0l); Exit])) (* imm shift 64 *)

(* --- construction-time type errors (negative tests) ---------------------- *)

(* dividing by a possibly-zero register is a TYPE ERROR in strict mode *)
[@@expect_failure]
let bad_div : program =
  finish (start Strict
  |>. Mov W64 R1 (OpImm 10l)
  |>. Mov W64 R2 (OpImm 0l)
  |>. Alu W64 DIV R1 (OpReg R2)
  |>. Mov W64 R0 (OpImm 0l))

(* claiming a bound the intervals cannot justify is a TYPE ERROR *)
[@@expect_failure]
let bad_assert : program =
  finish (start Strict
  |>. Mov W64 R1 (OpImm 255l)
  |>. Alu W64 RSH R1 (OpImm 1l)
  |>. Assert_ R1 3uL                 (* actual bound is 127 *)
  |>. Mov W64 R0 (OpImm 0l))

(* using an uninitialized register is a TYPE ERROR *)
[@@expect_failure]
let bad_uninit : program =
  finish (start Strict
  |>. Alu W64 ADD R1 (OpImm 1l))
