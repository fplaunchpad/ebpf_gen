(* Ebpf.Annot — the simulation bridge between Keel arena terms and the M1
   ISA semantics (ir/SPEC.md §5 definition terms).

   A `bnds` maps each register to the arena term that denotes its value.
   `bagree b rf` says every bound register's term evaluates to the concrete
   64-bit value the register holds in `rf`. `defterm` builds the §5
   definition term for an instruction's destination; `defterm_sound` proves
   that rebinding the destination to that term preserves agreement with the
   M1-stepped register file — i.e. the checker's symbolic bindings track the
   real machine exactly.

   v0-core coverage: 64-bit MOV/NEG and the ALU ops
   ADD/SUB/MUL/AND/OR/XOR/DIV/MOD/LSH/RSH/ARSH (register and immediate
   forms). Staged (definition terms defined in SPEC §5, bridge lemma
   deferred): SDIV/SMOD (needs the sign-magnitude = truncated-division
   equivalence), all ALU32 (needs the zero-extend wrapper layer), MOVSX and
   byte swaps. These return None from `defterm` here so the checker treats
   them as unsupported in v0-core rather than trusting an unproven shape. *)
module Ebpf.Annot

open FStar.Mul
open Ebpf.Int
open Ebpf.Ast
open Ebpf.Semantics
open Ebpf.Formula
module U64 = FStar.UInt64
module UInt = FStar.UInt

type bnds = reg -> option term

let upd (b: bnds) (r: reg) (t: term) : bnds = fun r' -> if r' = r then Some t else b r'

unfold let bagree_at (b: bnds) (rf: regfile) (r: reg) : prop =
  match b r, rf r with
  | Some t, Some x -> evalT t == Some (mkres 64 (U64.v x))
  | Some _, None -> False           (* bound in b ⟹ bound in rf *)
  | None, _ -> True

let bagree (b: bnds) (rf: regfile) : prop =
  bagree_at b rf R0 /\ bagree_at b rf R1 /\ bagree_at b rf R2 /\
  bagree_at b rf R3 /\ bagree_at b rf R4 /\ bagree_at b rf R5 /\
  bagree_at b rf R6 /\ bagree_at b rf R7 /\ bagree_at b rf R8 /\
  bagree_at b rf R9 /\ bagree_at b rf R10

let bagree_lookup (b: bnds) (rf: regfile) (r: reg)
  : Lemma (requires bagree b rf) (ensures bagree_at b rf r) =
  match r with
  | R0 -> () | R1 -> () | R2 -> () | R3 -> () | R4 -> () | R5 -> ()
  | R6 -> () | R7 -> () | R8 -> () | R9 -> () | R10 -> ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let bagree_at_update (b: bnds) (rf: regfile) (r: reg) (t: term) (v: U64.t) (rk: reg)
  : Lemma (requires bagree_at b rf rk /\ evalT t == Some (mkres 64 (U64.v v)))
          (ensures bagree_at (upd b r t) (updr rf r v) rk) =
  if rk = r then () else ()
#pop-options

let bagree_update (b: bnds) (rf: regfile) (r: reg) (t: term) (v: U64.t)
  : Lemma (requires bagree b rf /\ evalT t == Some (mkres 64 (U64.v v)))
          (ensures bagree (upd b r t) (updr rf r v)) =
  bagree_at_update b rf r t v R0; bagree_at_update b rf r t v R1;
  bagree_at_update b rf r t v R2; bagree_at_update b rf r t v R3;
  bagree_at_update b rf r t v R4; bagree_at_update b rf r t v R5;
  bagree_at_update b rf r t v R6; bagree_at_update b rf r t v R7;
  bagree_at_update b rf r t v R8; bagree_at_update b rf r t v R9;
  bagree_at_update b rf r t v R10

(* operand term (SPEC §3/§5), 64-bit forms only in v0-core *)
unfold let opterm (b: bnds) (o: operand) : option term =
  match o with
  | OpImm i -> Some (TC 64 (imm64 i))
  | OpReg r -> b r

(* the §5 definition term for the W64 core; None where staged/unsupported *)
let defterm (b: bnds) (i: insn) : option term =
  match i with
  | Mov W64 dst src -> opterm b src
  | Ebpf.Ast.Neg W64 dst -> (match b dst with Some a -> Some (TOp1 Neg a) | None -> None)
  | Alu W64 op dst src ->
    (match b dst, opterm b src with
     | Some a, Some s ->
       (match op with
        | ADD -> Some (TOp2 Add a s)
        | SUB -> Some (TOp2 Sub a s)
        | MUL -> Some (TOp2 Mul a s)
        | AND -> Some (TOp2 And a s)
        | OR  -> Some (TOp2 Or a s)
        | XOR -> Some (TOp2 Xor a s)
        | DIV -> Some (TIte (Atom KEq s (TC 64 0)) (TC 64 0) (TOp2 Udiv a s))
        | MOD -> Some (TOp2 Urem a s)
        | LSH -> Some (TOp2 Shl  a (TOp2 And s (TC 64 63)))
        | RSH -> Some (TOp2 Lshr a (TOp2 And s (TC 64 63)))
        | ARSH-> Some (TOp2 Ashr a (TOp2 And s (TC 64 63)))
        | _   -> None)                     (* SDIV/SMOD staged *)
     | _, _ -> None)
  | _ -> None                              (* W32 / MovSX / Swap / Assert / Exit staged *)

(* the destination register an instruction writes, when defterm supports it *)
let wdst (i: insn) : option reg =
  match i with
  | Mov W64 dst _ | Ebpf.Ast.Neg W64 dst | Alu W64 _ dst _ -> Some dst
  | _ -> None

(* ------------------------------------------------------------------ *)
(* the simulation bridge                                               *)
(* ------------------------------------------------------------------ *)

(* eBPF masks the shift amount; SPEC §5 makes it explicit with (bvand s 63).
   This connects that to M1's `s % 64`. *)
let mask63 (sv: int{fits 64 sv}) : Lemma (UInt.logand #64 sv 63 == sv % 64) =
  assert_norm (pow2 6 - 1 == 63);
  assert_norm (pow2 6 == 64);
  FStar.UInt.logand_mask #64 sv 6

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let opterm_sound (b: bnds) (rf: regfile) (src: operand)
  : Lemma (requires bagree b rf /\ Some? (opterm b src))
          (ensures (match opterm b src, opbits rf W64 src with
                    | Some t, Some v -> evalT t == Some (mkres 64 v)
                    | _, _ -> False)) =
  match src with
  | OpImm i -> ()
  | OpReg r ->
    bagree_lookup b rf r;
    (match b r, rf r with
     | Some t, Some x -> ()
     | Some _, None -> ()           (* bagree_at b rf r reduces to False *)
     | None, _ -> ())               (* contradicts Some? (opterm b src) *)
#pop-options

let res64v (x: int{fits 64 x}) : Lemma (U64.v (res64 W64 x) == x) = ()

#push-options "--z3rlimit 600 --fuel 4 --ifuel 2"

let defterm_sound (b: bnds) (rf: regfile) (i: insn)
  : Lemma (requires bagree b rf /\ Some? (defterm b i))
          (ensures (match wdst i, defterm b i, step rf i with
                    | Some dst, Some t, Some rf' -> bagree (upd b dst t) rf'
                    | _, _, _ -> False)) =
  match i with
  | Mov W64 dst src ->
    opterm_sound b rf src;
    (match opterm b src, opbits rf W64 src with
     | Some t, Some v -> res64v v; bagree_update b rf dst t (res64 W64 v)
     | _, _ -> ())
  | Ebpf.Ast.Neg W64 dst ->
    bagree_lookup b rf dst;
    (match b dst, rf dst with
     | Some a, Some dv ->
       res64v (wrap 64 (0 - regbits W64 dv));
       bagree_update b rf dst (TOp1 Ebpf.Formula.Neg a)
         (res64 W64 (wrap 64 (0 - regbits W64 dv)))
     | _, _ -> ())
  | Alu W64 op dst src ->
    bagree_lookup b rf dst;
    opterm_sound b rf src;
    (match b dst, rf dst, opterm b src, opbits rf W64 src with
     | Some a, Some dv, Some s, Some v ->
       let rv = res64 W64 (alu_sem W64 op (regbits W64 dv) v) in
       res64v (alu_sem W64 op (regbits W64 dv) v);
       (match op with
        | LSH | RSH | ARSH -> mask63 v
        | _ -> ());
       bagree_update b rf dst (Some?.v (defterm b i)) rv
     | _, _, _, _ -> ())
  | _ -> ()

#pop-options
