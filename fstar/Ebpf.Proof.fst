(* Ebpf.Proof — the Keel proof system (ir/SPEC.md §7): a checkable proof
   language over QF_BV atoms, with each rule's soundness machine-checked
   against Ebpf.Formula.evalA.

   Reference model vs kernel encoding: SPEC represents conclusions as
   internal one-level shapes and terms as arena indices; here a conclusion
   is an `atom` and terms are inductive values (syntactic = structural).
   A proof is a list of steps; step i may cite steps < i as premises. The
   checker folds the list; the invariant is that every derived conclusion
   is `valid` (Ebpf.Formula.valid). The final conclusion must equal the
   goal atom.

   This module implements a verified CORE of the catalog — the rules the M1
   demo corpus needs plus the ones the adversarial review flagged as
   soundness-critical (DIV_LE, MONO_*, the _LO variants). Remaining catalog
   entries are staged; none are admitted. *)
module Ebpf.Proof

open FStar.Mul
open Ebpf.Int
open Ebpf.Formula
module UInt = FStar.UInt
module L = FStar.List.Tot

(* ------------------------------------------------------------------ *)
(* small arithmetic helpers (re-derived to keep deps to Formula only)  *)
(* ------------------------------------------------------------------ *)

let div_antitone (a: nat) (d1: pos) (d2: pos{d1 <= d2})
  : Lemma (a / d2 <= a / d1) =
  FStar.Math.Lemmas.lemma_div_mod a d2;
  FStar.Math.Lemmas.lemma_mult_le_right (a / d2) d1 d2;
  FStar.Math.Lemmas.lemma_div_le ((a / d2) * d1) a d1;
  FStar.Math.Lemmas.cancel_mul_div (a / d2) d1

let div_le_self (a: nat) (d: pos) : Lemma (a / d <= a) = div_antitone a 1 d

let mul_mono (a1: nat) (a2: nat{a1 <= a2}) (b1: nat) (b2: nat{b1 <= b2})
  : Lemma (a1 * b1 <= a2 * b2) =
  FStar.Math.Lemmas.lemma_mult_le_left a1 b1 b2;
  FStar.Math.Lemmas.lemma_mult_le_right b2 a1 a2

(* ------------------------------------------------------------------ *)
(* rule language                                                       *)
(* ------------------------------------------------------------------ *)

(* Premises are indices into the list of already-derived conclusions.
   Term/const params are inductive terms (the kernel stores arena indices).
   Every rule application is validated by `apply`, which also confirms the
   well-formedness (evalT-success) it needs — v0 arena nodes are ground and
   pre-validated, so this always succeeds for honest certificates and
   rejects malformed ones. *)
type rule =
  | R_EvalEq   : t:term -> rule
  | R_UleConst : c1:term -> c2:term -> rule
  | R_UltConst : c1:term -> c2:term -> rule
  | R_UgeConst : c1:term -> c2:term -> rule
  | R_NeConst  : c1:term -> c2:term -> rule
  | R_UleRefl  : t:term -> rule
  | R_EqRefl   : t:term -> rule
  | R_AndLeL   : t:term -> rule            (* t must be (And a b) *)
  | R_AndLeR   : t:term -> rule
  | R_ShrLe    : t:term -> rule            (* t must be (Lshr a s) *)
  | R_DivLe    : p:nat -> t:term -> rule   (* prem (Ne b 0); t = (Udiv a b) *)
  | R_ShrBound : p:nat -> t:term -> rule   (* prem (Ule a c); t = (Lshr a k) *)
  | R_MonoAdd  : p:nat -> q:nat -> t:term -> rule
  | R_MonoMul  : p:nat -> q:nat -> t:term -> rule
  | R_TransUle : p:nat -> q:nat -> rule
  | R_NeFromUge: p:nat -> rule

(* nth conclusion, total *)
let nth (cs: list atom) (i: nat) : option atom =
  if i < L.length cs then Some (L.index cs i) else None

(* ------------------------------------------------------------------ *)
(* the rule application function (SPEC §7 apply)                       *)
(* ------------------------------------------------------------------ *)

(* `apply cs r` computes the conclusion atom of rule r, given the list `cs`
   of already-derived conclusions (premises are indices into it). Returns
   None on any structural / side-condition / well-formedness failure. It
   evaluates the terms it needs; v0 arena nodes are ground so evaluation is
   total, and any ill-formed input is rejected here. *)
let mkc (w: pos) (v: int) : term = if fits w v then TC w v else TC w 0

let apply (cs: list atom) (r: rule) : option atom =
  match r with
  | R_EvalEq t ->
    (match evalT t with Some (| w, v |) -> Some (Atom KEq t (TC w v)) | None -> None)
  | R_UleConst (TC w1 v1) (TC w2 v2) ->
    if w1 = w2 && fits w1 v1 && fits w2 v2 && v1 <= v2
    then Some (Atom KUle (TC w1 v1) (TC w2 v2)) else None
  | R_UltConst (TC w1 v1) (TC w2 v2) ->
    if w1 = w2 && fits w1 v1 && fits w2 v2 && v1 < v2
    then Some (Atom KUlt (TC w1 v1) (TC w2 v2)) else None
  | R_UgeConst (TC w1 v1) (TC w2 v2) ->
    if w1 = w2 && fits w1 v1 && fits w2 v2 && v1 >= v2
    then Some (Atom KUge (TC w1 v1) (TC w2 v2)) else None
  | R_NeConst (TC w1 v1) (TC w2 v2) ->
    if w1 = w2 && fits w1 v1 && fits w2 v2 && v1 <> v2
    then Some (Atom KNe (TC w1 v1) (TC w2 v2)) else None
  | R_UleRefl t -> (match evalT t with Some _ -> Some (Atom KUle t t) | None -> None)
  | R_EqRefl t -> (match evalT t with Some _ -> Some (Atom KEq t t) | None -> None)
  | R_AndLeL (TOp2 And a b) ->
    (match evalT (TOp2 And a b) with Some _ -> Some (Atom KUle (TOp2 And a b) a) | None -> None)
  | R_AndLeR (TOp2 And a b) ->
    (match evalT (TOp2 And a b) with Some _ -> Some (Atom KUle (TOp2 And a b) b) | None -> None)
  | R_ShrLe (TOp2 Lshr a s) ->
    (match evalT (TOp2 Lshr a s) with Some _ -> Some (Atom KUle (TOp2 Lshr a s) a) | None -> None)
  | R_DivLe p (TOp2 Udiv a b) ->
    (match nth cs p, evalT (TOp2 Udiv a b) with
     | Some (Atom KNe b' (TC _ 0)), Some _ -> if b' = b then Some (Atom KUle (TOp2 Udiv a b) a) else None
     | _, _ -> None)
  | R_TransUle p q ->
    (match nth cs p, nth cs q with
     | Some (Atom KUle a b), Some (Atom KUle b' c) -> if b' = b then Some (Atom KUle a c) else None
     | _, _ -> None)
  | R_ShrBound p (TOp2 Lshr a (TC kw kv)) ->
    (match nth cs p, evalT (TOp2 Lshr a (TC kw kv)) with
     | Some (Atom KUle a' (TC cw cv)), Some (| w, _ |) ->
       if a' = a && cw = w && fits kw kv && kv < w && fits cw cv
       then Some (Atom KUle (TOp2 Lshr a (TC kw kv)) (TC w (cv / pow2 kv))) else None
     | _, _ -> None)
  | R_MonoMul p q (TOp2 Mul a b) ->
    (match nth cs p, nth cs q, evalT (TOp2 Mul a b) with
     | Some (Atom KUle a' (TC caw ca)), Some (Atom KUle b' (TC cbw cb)), Some (| w, _ |) ->
       if a' = a && b' = b && caw = w && cbw = w && fits w ca && fits w cb && ca * cb < pow2 w
       then Some (Atom KUle (TOp2 Mul a b) (TC w (ca * cb))) else None
     | _, _, _ -> None)
  | R_MonoAdd p q (TOp2 Add a b) ->
    (match nth cs p, nth cs q, evalT (TOp2 Add a b) with
     | Some (Atom KUle a' (TC caw ca)), Some (Atom KUle b' (TC cbw cb)), Some (| w, _ |) ->
       if a' = a && b' = b && caw = w && cbw = w && fits w ca && fits w cb && ca + cb < pow2 w
       then Some (Atom KUle (TOp2 Add a b) (TC w (ca + cb))) else None
     | _, _, _ -> None)
  | R_NeFromUge p ->
    (match nth cs p with
     | Some (Atom KUge a (TC cw cv)) -> if fits cw cv && cv >= 1 then Some (Atom KNe a (TC cw 0)) else None
     | _ -> None)
  | _ -> None

(* ------------------------------------------------------------------ *)
(* soundness of rule application                                       *)
(* ------------------------------------------------------------------ *)

let rec all_valid (cs: list atom) : prop =
  match cs with
  | [] -> True
  | c :: t -> valid c /\ all_valid t

let rec nth_valid (cs: list atom) (i: nat)
  : Lemma (requires all_valid cs)
          (ensures (match nth cs i with | Some c -> valid c | None -> True)) =
  match cs with
  | [] -> ()
  | x :: t -> if i = 0 then () else nth_valid t (i - 1)

let rec all_valid_snoc (cs: list atom) (c: atom)
  : Lemma (requires all_valid cs /\ valid c) (ensures all_valid (L.append cs [c])) =
  match cs with
  | [] -> ()
  | x :: t -> all_valid_snoc t c

#push-options "--z3rlimit 300 --fuel 2 --ifuel 2"

let apply_sound (cs: list atom) (r: rule)
  : Lemma (requires all_valid cs)
          (ensures (match apply cs r with | Some c -> valid c | None -> True)) =
  match r with
  | R_EvalEq _ -> ()
  | R_UleConst _ _ -> ()
  | R_UltConst _ _ -> ()
  | R_UgeConst _ _ -> ()
  | R_NeConst _ _ -> ()
  | R_UleRefl _ -> ()
  | R_EqRefl _ -> ()
  | R_DivLe p (TOp2 Udiv a b) ->
    nth_valid cs p;
    (match nth cs p, evalT (TOp2 Udiv a b) with
     | Some (Atom KNe b' (TC _ 0)), Some _ ->
       if b' = b then
         (match evalT a, evalT b with
          | Some (| _, va |), Some (| _, vb |) -> if vb <> 0 then div_le_self va vb else ()
          | _, _ -> ())
       else ()
     | _, _ -> ())
  | R_ShrLe (TOp2 Lshr a s) ->
    (match evalT a, evalT s with
     | Some (| _, va |), Some (| _, vs |) -> if vs > 0 then div_le_self va (pow2 vs) else ()
     | _, _ -> ())
  | R_AndLeL (TOp2 And a b) ->
    (match evalT a, evalT b with
     | Some (| wa, va |), Some (| wb, vb |) -> if wa = wb then UInt.logand_le #wa va vb else ()
     | _, _ -> ())
  | R_AndLeR (TOp2 And a b) ->
    (match evalT a, evalT b with
     | Some (| wa, va |), Some (| wb, vb |) -> if wa = wb then UInt.logand_le #wa va vb else ()
     | _, _ -> ())
  | R_ShrBound p (TOp2 Lshr a (TC kw kv)) ->
    nth_valid cs p;
    (match nth cs p, evalT (TOp2 Lshr a (TC kw kv)) with
     | Some (Atom KUle a' (TC cw cv)), Some (| w, _ |) ->
       if a' = a && cw = w && fits kw kv && kv < w && fits cw cv then
         (match evalT a with
          | Some (| wa, va |) ->
            FStar.Math.Lemmas.lemma_div_le va cv (pow2 kv);
            div_le_self cv (pow2 kv)
          | None -> ())
       else ()
     | _, _ -> ())
  | R_MonoMul p q (TOp2 Mul a b) ->
    nth_valid cs p; nth_valid cs q;
    (match nth cs p, nth cs q, evalT (TOp2 Mul a b) with
     | Some (Atom KUle a' (TC caw ca)), Some (Atom KUle b' (TC cbw cb)), Some (| w, _ |) ->
       if a' = a && b' = b && caw = w && cbw = w && fits w ca && fits w cb && ca * cb < pow2 w then
         (match evalT a, evalT b with
          | Some (| _, va |), Some (| _, vb |) ->
            mul_mono va ca vb cb; FStar.Math.Lemmas.small_mod (va * vb) (pow2 w)
          | _, _ -> ())
       else ()
     | _, _, _ -> ())
  | R_MonoAdd p q (TOp2 Add a b) ->
    nth_valid cs p; nth_valid cs q;
    (match nth cs p, nth cs q, evalT (TOp2 Add a b) with
     | Some (Atom KUle a' (TC caw ca)), Some (Atom KUle b' (TC cbw cb)), Some (| w, _ |) ->
       if a' = a && b' = b && caw = w && cbw = w && fits w ca && fits w cb && ca + cb < pow2 w then
         (match evalT a, evalT b with
          | Some (| _, va |), Some (| _, vb |) -> FStar.Math.Lemmas.small_mod (va + vb) (pow2 w)
          | _, _ -> ())
       else ()
     | _, _, _ -> ())
  | R_TransUle p q -> nth_valid cs p; nth_valid cs q
  | R_NeFromUge p -> nth_valid cs p
  | _ -> ()

#pop-options

(* ------------------------------------------------------------------ *)
(* proof driver + top-level soundness                                  *)
(* ------------------------------------------------------------------ *)

let rec run_proof (cs: list atom) (steps: list rule)
  : Tot (option (list atom)) (decreases steps) =
  match steps with
  | [] -> Some cs
  | r :: rest ->
    (match apply cs r with
     | Some c -> run_proof (L.append cs [c]) rest
     | None -> None)

let rec run_proof_sound (cs: list atom) (steps: list rule)
  : Lemma (requires all_valid cs)
          (ensures (match run_proof cs steps with | Some cs' -> all_valid cs' | None -> True))
          (decreases steps) =
  match steps with
  | [] -> ()
  | r :: rest ->
    apply_sound cs r;
    (match apply cs r with
     | Some c ->
       all_valid_snoc cs c;
       run_proof_sound (L.append cs [c]) rest;
       assert (run_proof cs steps == run_proof (L.append cs [c]) rest)
     | None -> assert (run_proof cs steps == None))

(* A proof establishes `goal` from the initial fact set `init` (the claims
   available at this point) if it runs and its last conclusion is `goal`. *)
let last_is (cs: list atom) (goal: atom) : bool =
  match cs with [] -> false | _ -> L.last cs = goal

let check_proof (init: list atom) (goal: atom) (steps: list rule) : bool =
  match run_proof init steps with
  | Some cs -> last_is cs goal
  | None -> false

let rec last_all_valid (cs: list atom)
  : Lemma (requires all_valid cs /\ Cons? cs) (ensures valid (L.last cs)) =
  match cs with
  | [x] -> ()
  | x :: t -> last_all_valid t

(* Top-level: a checked proof from valid initial facts yields a valid goal.
   This is the property Ebpf.CertCheck relies on for each discharged
   obligation/claim. *)
let check_proof_sound (init: list atom) (goal: atom) (steps: list rule)
  : Lemma (requires all_valid init /\ check_proof init goal steps)
          (ensures valid goal) =
  run_proof_sound init steps;
  (match run_proof init steps with
   | Some cs -> last_all_valid cs
   | None -> ())
