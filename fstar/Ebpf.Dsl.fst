(* Ebpf.Dsl — a small high-level expression dialect for ALU-only eBPF
   (M2.3.1). This is the *surface* an author writes, far above the TAL
   instruction pipeline: named variables, nested arithmetic expressions, and
   `assert` bound-claims.

   This module provides the AST and the REFERENCE EVALUATOR — the executable
   "intended meaning" of a program, defined to agree with the M1 machine
   semantics (`Ebpf.Semantics.alu_semn` at width 64) BY CONSTRUCTION. The
   evaluator is the oracle the M2.3.4 pipeline test compares the loaded
   program's result against; the M2.3.2 lowering is checked to preserve it.

   Scope: 64-bit ALU only, straight-line. Control flow and memory are later
   milestones; the DSL grows with them. *)
module Ebpf.Dsl

open FStar.Mul
open Ebpf.Int
module U64 = FStar.UInt64
module A = Ebpf.Ast
module S = Ebpf.Semantics

(* ------------------------------------------------------------------ *)
(* syntax                                                              *)
(* ------------------------------------------------------------------ *)

type var = nat                       (* SSA-ish variable id *)

type unop = | Neg
type binop =
  | Add | Sub | Mul | Div | Mod | And | Or | Xor | Lsh | Rsh | Arsh

type expr =
  | Const : U64.t -> expr
  | Var   : var -> expr
  | Un    : unop -> expr -> expr
  | Bin   : binop -> expr -> expr -> expr

type stmt =
  | Let    : var -> expr -> stmt     (* v := e *)
  | Assert : expr -> U64.t -> stmt   (* claim: (value of e) <= bound *)
  | Ret    : expr -> stmt            (* return e (into r0) *)

type prog = list stmt                (* should end in Ret *)

(* ------------------------------------------------------------------ *)
(* reference semantics (agrees with Ebpf.Semantics by construction)    *)
(* ------------------------------------------------------------------ *)

let alu_of (op: binop) : A.alu_op =
  match op with
  | Add -> A.ADD | Sub -> A.SUB | Mul -> A.MUL | Div -> A.DIV | Mod -> A.MOD
  | And -> A.AND | Or -> A.OR | Xor -> A.XOR
  | Lsh -> A.LSH | Rsh -> A.RSH | Arsh -> A.ARSH

let eval_bin (op: binop) (x y: U64.t) : U64.t =
  to_u64 (S.alu_semn 64 (alu_of op) (U64.v x) (U64.v y))

let eval_un (op: unop) (x: U64.t) : U64.t =
  match op with
  | Neg -> to_u64 (wrap 64 (0 - U64.v x))

type env = var -> option U64.t

let empty : env = fun _ -> None
let bind (e: env) (v: var) (x: U64.t) : env = fun v' -> if v' = v then Some x else e v'

let rec eval_expr (e: env) (ex: expr) : Tot (option U64.t) (decreases ex) =
  match ex with
  | Const c -> Some c
  | Var v -> e v
  | Un op a ->
    (match eval_expr e a with Some x -> Some (eval_un op x) | None -> None)
  | Bin op a b ->
    (match eval_expr e a, eval_expr e b with
     | Some x, Some y -> Some (eval_bin op x y)
     | _, _ -> None)

(* run a program: fold Lets into the env, ignore Asserts (claims, not
   computation), return the Ret expression's value. None if a variable is
   used before binding or there is no Ret. *)
let rec eval_prog (e: env) (p: prog) : Tot (option U64.t) (decreases p) =
  match p with
  | [] -> None
  | Let v ex :: rest ->
    (match eval_expr e ex with Some x -> eval_prog (bind e v x) rest | None -> None)
  | Assert _ _ :: rest -> eval_prog e rest
  | Ret ex :: _ -> eval_expr e ex

let run (p: prog) : option U64.t = eval_prog empty p

(* ------------------------------------------------------------------ *)
(* sample programs + evaluator tests (M2.3.1 acceptance)               *)
(* ------------------------------------------------------------------ *)

(* r = 6 * 7 = 42 *)
let ex_mul : prog =
  [ Let 0 (Const 6uL); Let 1 (Const 7uL); Let 2 (Bin Mul (Var 0) (Var 1));
    Assert (Var 2) 42uL; Ret (Var 2) ]
let _ = assert_norm (run ex_mul = Some 42uL)

(* r = (10 * 20) & 0xff = 200. NB: no `assert_norm` here — normalizing
   `UInt.logand #64` (bit-vector defined) hangs the F* normalizer, though it
   is a fast native op at runtime. The bitwise evaluator is exercised in the
   M2.3.4 pipeline test (extracted OCaml), not at compile time. *)
let ex_chain : prog =
  [ Let 0 (Const 10uL); Let 1 (Const 20uL);
    Let 2 (Bin And (Bin Mul (Var 0) (Var 1)) (Const 0xffuL));
    Assert (Var 2) 200uL; Ret (Var 2) ]

(* r = 100 / 4 = 25 *)
let ex_div : prog =
  [ Let 0 (Const 100uL); Let 1 (Const 4uL); Let 2 (Bin Div (Var 0) (Var 1));
    Assert (Var 2) 25uL; Ret (Var 2) ]
let _ = assert_norm (run ex_div = Some 25uL)

(* nested expression: (100 + 50) then /3 = 50 *)
let ex_nested : prog =
  [ Ret (Bin Div (Bin Add (Const 100uL) (Const 50uL)) (Const 3uL)) ]
let _ = assert_norm (run ex_nested = Some 50uL)

(* div-by-zero is defined (eBPF: x/0 = 0), matching the machine semantics *)
let ex_div0 : prog = [ Ret (Bin Div (Const 42uL) (Const 0uL)) ]
let _ = assert_norm (run ex_div0 = Some 0uL)

(* use-before-bind is None *)
let _ = assert_norm (run [ Ret (Var 5) ] = None)
