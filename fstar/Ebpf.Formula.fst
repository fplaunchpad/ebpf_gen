(* Ebpf.Formula — the Keel annotation/term language (ir/SPEC.md §4) and its
   SMT-LIB2 QF_BV evaluation semantics.

   The kernel checker uses a u32-indexed arena where syntactic equality is
   index equality; here in the reference model a term is an inductive value
   and syntactic equality is structural `=`. Evaluation is the totalized
   SMT-LIB semantics verbatim — in particular bvudiv/bvurem/bvsdiv/bvsrem
   have SMT-LIB's zero-divisor results (all-ones / dividend / sign-dependent),
   NOT eBPF's; eBPF behavior is recovered by the ITE-guarded and mask-guarded
   *definition terms* in Ebpf.Annot, exactly as SPEC §5 prescribes.

   v0: every term is ground (all leaves are constants — there is no register
   or variable node; the certifier resolves registers to their bindings).
   `eval` therefore never needs an environment. *)
module Ebpf.Formula

open FStar.Mul
open Ebpf.Int
module UInt = FStar.UInt

type bvop2 =
  | Add | Sub | Mul | Udiv | Sdiv | Urem | Srem
  | And | Or | Xor | Shl | Lshr | Ashr

type bvop1 = | Not | Neg

type atomkind = | KEq | KNe | KUle | KUlt | KUge

(* A term carries no width field; widths are computed (and checked) by eval.
   The arena encoding (SPEC §8) stores width explicitly, but the reference
   semantics derives it, so an ill-widthed term simply evaluates to None. *)
type term =
  | TC      : w:pos -> v:nat -> term
  | TOp2    : bvop2 -> term -> term -> term
  | TOp1    : bvop1 -> term -> term
  | TConcat : term -> term -> term
  | TExtract: hi:nat -> lo:nat -> term -> term
  | TZext   : n:nat -> term -> term
  | TSext   : n:pos -> term -> term
  | TIte    : atom -> term -> term -> term

and atom =
  | Atom : atomkind -> term -> term -> atom

(* A result: width + a pattern fitting that width. *)
type res = w:pos & (v:int{fits w v})

let mkres (w:pos) (v:int{fits w v}) : res = (| w, v |)

(* signed value of the low-`w` interpretation, reused from Ebpf.Int.sval *)
let sgn (w:pos) (v:int{fits w v}) : int = sval w v

(* SMT-LIB msb test *)
let msb (w:pos) (v:int{fits w v}) : bool = v >= pow2 (w - 1)

(* unsigned two's-complement negation as a w-bit pattern *)
let negp (w:pos) (v:int{fits w v}) : y:int{fits w y} = wrap w (0 - v)

(* --- non-recursive arithmetic kernels (no term recursion) --------------- *)

let eval_ashr (w: pos) (a: int{fits w a}) (b: int{fits w b}) : v:int{fits w v} =
  if b >= w then (if msb w a then pow2 w - 1 else 0)
  else wrap w (sgn w a / pow2 b)

(* SMT-LIB bvsdiv via sign-magnitude over bvudiv (b may be 0). *)
let eval_sdiv (w: pos) (a: int{fits w a}) (b: int{fits w b}) : v:int{fits w v} =
  let ma = msb w a in let mb = msb w b in
  let ud (x:int{fits w x}) (y:int{fits w y}) : v:int{fits w v} =
    if y = 0 then pow2 w - 1 else x / y in
  if not ma && not mb then ud a b
  else if ma && not mb then negp w (ud (negp w a) b)
  else if not ma && mb then negp w (ud a (negp w b))
  else ud (negp w a) (negp w b)

let eval_srem (w: pos) (a: int{fits w a}) (b: int{fits w b}) : v:int{fits w v} =
  let ma = msb w a in let mb = msb w b in
  let ur (x:int{fits w x}) (y:int{fits w y}) : v:int{fits w v} =
    if y = 0 then x else x % y in
  if not ma && not mb then ur a b
  else if ma && not mb then negp w (ur (negp w a) b)
  else if not ma && mb then ur a (negp w b)
  else negp w (ur (negp w a) (negp w b))

let eval_op2 (op: bvop2) (w: pos) (a: int{fits w a}) (b: int{fits w b})
  : option res =
  match op with
  | Add -> Some (mkres w (wrap w (a + b)))
  | Sub -> Some (mkres w (wrap w (a - b)))
  | Mul -> Some (mkres w (wrap w (a * b)))
  | And -> Some (mkres w (UInt.logand #w a b))
  | Or  -> Some (mkres w (UInt.logor #w a b))
  | Xor -> Some (mkres w (UInt.logxor #w a b))
  | Udiv -> Some (mkres w (if b = 0 then pow2 w - 1 else a / b))
  | Urem -> Some (mkres w (if b = 0 then a else a % b))
  | Shl  -> Some (mkres w (if b >= w then 0 else wrap w (a * pow2 b)))
  | Lshr -> Some (mkres w (if b >= w then 0 else a / pow2 b))
  | Ashr -> Some (mkres w (eval_ashr w a b))
  | Sdiv -> Some (mkres w (eval_sdiv w a b))
  | Srem -> Some (mkres w (eval_srem w a b))

(* --- the mutually-recursive term/atom evaluator ------------------------- *)

let rec evalT (t: term) : Tot (option res) (decreases t) =
  match t with
  | TC w v -> if fits w v then Some (mkres w v) else None
  | TOp1 op a ->
    (match evalT a with
     | None -> None
     | Some (| w, va |) ->
       (match op with
        | Not -> Some (mkres w (UInt.lognot #w va))
        | Neg -> Some (mkres w (wrap w (0 - va)))))
  | TOp2 op a b ->
    (match evalT a, evalT b with
     | Some (| wa, va |), Some (| wb, vb |) ->
       if wa <> wb then None else eval_op2 op wa va vb
     | _, _ -> None)
  | TConcat a b ->
    (match evalT a, evalT b with
     | Some (| wa, va |), Some (| wb, vb |) ->
       FStar.Math.Lemmas.pow2_plus wa wb;
       Some (mkres (wa + wb) (va * pow2 wb + vb))
     | _, _ -> None)
  | TExtract hi lo a ->
    (match evalT a with
     | Some (| wa, va |) ->
       if lo <= hi && hi < wa
       then (let w = hi - lo + 1 in
             Some (mkres w (wrap w (va / pow2 lo))))   (* wrap guarantees fits w *)
       else None
     | None -> None)
  | TZext n a ->
    (match evalT a with
     | Some (| wa, va |) ->
       FStar.Math.Lemmas.pow2_le_compat (wa + n) wa;
       Some (mkres (wa + n) va)
     | None -> None)
  | TSext n a ->
    (match evalT a with
     | Some (| wa, va |) -> Some (mkres (wa + n) (wrap (wa + n) (sgn wa va)))
     | None -> None)
  | TIte c a b ->
    (match evalA c, evalT a, evalT b with
     | Some g, Some (| wa, va |), Some (| wb, vb |) ->
       if wa = wb then Some (mkres wa (if g then va else vb)) else None
     | _, _, _ -> None)

and evalA (c: atom) : Tot (option bool) (decreases c) =
  match c with
  | Atom k a b ->
    (match evalT a, evalT b with
     | Some (| wa, va |), Some (| wb, vb |) ->
       if wa <> wb then None
       else Some (match k with
                  | KEq  -> va = vb
                  | KNe  -> va <> vb
                  | KUle -> va <= vb
                  | KUlt -> va < vb
                  | KUge -> va >= vb)
     | _, _ -> None)

(* An atom is *valid* when it is well-formed and evaluates to true. This is
   the semantics the proof rules are proved sound against, and the property
   the end-to-end theorem reports for each proven claim. *)
let valid (c: atom) : prop = evalA c == Some true

(* A conjunction (SPEC φ) is a list of atoms; all must be valid. *)
let rec valid_all (cs: list atom) : prop =
  match cs with
  | [] -> True
  | c :: rest -> valid c /\ valid_all rest
