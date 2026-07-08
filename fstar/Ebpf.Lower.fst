(* Ebpf.Lower — lowering the high-level DSL (Ebpf.Dsl) to the M1 instruction
   list (Ebpf.Ast.program) with register allocation (M2.3.2). This is the
   "small compiler" back half for the ALU fragment.

   Allocation (straight-line, ALU-only):
   - variable `v` lives permanently in register R(v+1)  (R0 reserved for the
     return value; R10 the frame pointer is never used); so `v <= 8`.
   - expression temporaries use a scratch pool ABOVE all variable registers:
     scratch base = (max var id) + 2, growing downward into the expression.
   - two-address ALU: `Bin op a b` computes `a` into `dst`, `b` into a scratch
     register `t`, then `Alu op dst t` (dst = a OP b — correct operand order
     for non-commutative ops).
   - constants use `Mov W32` (which zero-extends), so any 32-bit constant
     loads directly; constants >= 2^32 need LD_IMM64 (absent) -> lowering
     fails cleanly (returns None), a documented register/constant cap.

   The lowering is TRUSTED but its functional correctness is validated by the
   M2.3.4 pipeline test (loaded program's result vs the Ebpf.Dsl evaluator).
   Soundness never depends on it: the verified checker validates the
   certificate against the emitted bytecode regardless. *)
module Ebpf.Lower

open FStar.Mul
open Ebpf.Int
open Ebpf.Dsl
module U64 = FStar.UInt64
module I32 = FStar.Int32
module A = Ebpf.Ast
open FStar.List.Tot

let maxn (a b: nat) : nat = if a >= b then a else b

(* allocation index -> register; R0..R9 only (R10 excluded) *)
let regn (n: nat) : option A.reg =
  match n with
  | 0 -> Some A.R0 | 1 -> Some A.R1 | 2 -> Some A.R2 | 3 -> Some A.R3
  | 4 -> Some A.R4 | 5 -> Some A.R5 | 6 -> Some A.R6 | 7 -> Some A.R7
  | 8 -> Some A.R8 | 9 -> Some A.R9 | _ -> None

let varreg (v: var) : option A.reg = regn (v + 1)

(* Load a constant via a 64-bit (sign-extending) mov. Correct for c < 2^31
   (imm64 (i32 c) = c). Constants >= 2^31 would need either the W32
   zero-extend trick (but ALU32 is staged in the verified checker) or
   LD_IMM64 (absent) -> lowering fails cleanly. Documented cap; the demo
   corpus stays well under 2^31. Staying W64-only keeps every emitted
   instruction inside the checker-supported (Ebpf.Annot.defterm) fragment. *)
let const_insn (dst: A.reg) (c: U64.t) : option (list A.insn) =
  let cv = U64.v c in
  if cv < pow2 31
  then Some [A.Mov A.W64 dst (A.OpImm (I32.int_to_t cv))]
  else None

(* compile expression e into register dst, using scratch registers from
   index `nlo` upward. *)
let rec compile_expr (dst: A.reg) (nlo: nat) (e: expr)
  : Tot (option (list A.insn)) (decreases e) =
  match e with
  | Const c -> const_insn dst c
  | Var v -> (match varreg v with Some r -> Some [A.Mov A.W64 dst (A.OpReg r)] | None -> None)
  | Un Neg a ->
    (match compile_expr dst nlo a with
     | Some ca -> Some (ca @ [A.Neg A.W64 dst])
     | None -> None)
  | Bin op a b ->
    (match regn nlo with
     | None -> None                            (* out of scratch registers *)
     | Some t ->
       (match compile_expr dst nlo a, compile_expr t (nlo + 1) b with
        | Some ca, Some cb -> Some (ca @ cb @ [A.Alu A.W64 (alu_of op) dst (A.OpReg t)])
        | _, _ -> None))

let rec compile_stmts (nlo0: nat) (p: prog) : Tot (option (list A.insn)) (decreases p) =
  match p with
  | [] -> None                                 (* no Ret *)
  | Ret e :: _ ->
    (match compile_expr A.R0 nlo0 e with Some ce -> Some (ce @ [A.Exit]) | None -> None)
  | Let v e :: rest ->
    (match varreg v with
     | None -> None
     | Some dv ->
       (match compile_expr dv nlo0 e, compile_stmts nlo0 rest with
        | Some ce, Some cr -> Some (ce @ cr)
        | _, _ -> None))
  | Assert (Var v) bound :: rest ->            (* asserts are on a bound variable *)
    (match varreg v, compile_stmts nlo0 rest with
     | Some rv, Some cr -> Some (A.Assert_ rv bound :: cr)
     | _, _ -> None)
  | Assert _ _ :: _ -> None                    (* non-Var asserts unsupported (desugar to Let+Assert) *)

let rec max_var_e (e: expr) : Tot nat (decreases e) =
  match e with
  | Const _ -> 0
  | Var v -> v
  | Un _ a -> max_var_e a
  | Bin _ a b -> maxn (max_var_e a) (max_var_e b)

let rec max_var (p: prog) : Tot nat (decreases p) =
  match p with
  | [] -> 0
  | Let v e :: r -> maxn v (maxn (max_var_e e) (max_var r))
  | Assert e _ :: r -> maxn (max_var_e e) (max_var r)
  | Ret e :: r -> maxn (max_var_e e) (max_var r)

let lower (p: prog) : option A.program = compile_stmts (max_var p + 2) p

(* --- sanity: the demo programs lower successfully (cheap: no semantics) --- *)
let _ = assert_norm (Some? (lower ex_mul))
let _ = assert_norm (Some? (lower ex_chain))
let _ = assert_norm (Some? (lower ex_div))
let _ = assert_norm (Some? (lower ex_nested))
