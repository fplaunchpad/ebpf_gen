(* Ebpf.CertCheck — the Keel checker over an annotated program, and the
   end-to-end soundness theorem (ir/SPEC.md §6, §10).

   The checker walks the instruction stream maintaining the symbolic
   register bindings (Ebpf.Annot). Each instruction must be a supported
   SPEC §5 definition-term shape (defterm = Some); the program must end in
   a single Exit with R0 bound. `defterm_sound` guarantees the bindings
   track the concrete machine, so an accepted program provably runs to Exit
   with R0 initialized under the ISA (Total) semantics — i.e. it is safe.

   This is the v0-core capstone. It establishes the *transplanting/forging*
   guarantees of the threat model concretely: the walk reconstructs each
   definition term from the loaded instruction (Annot.defterm), never from
   the certificate, so a certificate cannot make an unsafe program check.
   Strict-mode safety obligations (div≠0, shift<width discharged by
   Ebpf.Proof) and claim-validity reporting compose on top of this walk and
   are the next increment; the proof-rule soundness they rely on is already
   machine-checked in Ebpf.Proof. *)
module Ebpf.CertCheck

open Ebpf.Ast
open Ebpf.Semantics
open Ebpf.Formula
open Ebpf.Annot
module U64 = FStar.UInt64

(* The checker: fold over instructions, rebinding dst at each supported
   step; accept a program that ends in Exit with R0 bound. *)
let rec check_walk (b: bnds) (p: program) : Tot bool (decreases p) =
  match p with
  | [] -> false
  | [Exit] -> Some? (b R0)
  | Exit :: _ :: _ -> false          (* no code after Exit (SPEC C17) *)
  | i :: rest ->
    (match wdst i, defterm b i with
     | Some dst, Some t -> check_walk (upd b dst t) rest
     | _, _ -> false)                (* unsupported op / unbound operand *)

let b0 : bnds = fun _ -> None

let accepts (p: program) : bool = check_walk b0 p

(* b0 agrees with the empty register file (nothing bound). *)
let bagree_b0 () : Lemma (bagree b0 rf0) = ()

(* Core induction: from an agreeing state, an accepted suffix runs safely. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let rec walk_sound (b: bnds) (rf: regfile) (p: program)
  : Lemma (requires bagree b rf /\ check_walk b p)
          (ensures Some? (runx Total rf p))
          (decreases p) =
  match p with
  | [] -> ()
  | [Exit] -> bagree_lookup b rf R0  (* Some? (b R0) ⟹ Some? (rf R0) via bagree *)
  | i :: rest ->
    (match wdst i, defterm b i with
     | Some dst, Some t ->
       defterm_sound b rf i;
       (* defterm_sound gives: step rf i = Some rf' /\ bagree (upd b dst t) rf' *)
       (match step rf i with
        | Some rf' -> walk_sound (upd b dst t) rf' rest
        | None -> ())
     | _, _ -> ())
#pop-options

(* End-to-end (v0-core, kernel/Total semantics): an accepted program runs to
   Exit with R0 initialized — it is safe. The certificate cannot influence
   goal construction (every definition term is rebuilt from the loaded
   instruction by `defterm`), so this holds for ANY program the checker
   accepts. *)
let soundness (p: program)
  : Lemma (requires accepts p) (ensures Some? (runx Total rf0 p)) =
  bagree_b0 ();
  walk_sound b0 rf0 p

(* --- non-vacuity: concrete accept/reject over the W64 core -------------- *)

(* r1=100; r1+=1; r0=r1; exit  — accepts, and soundness applies *)
let demo1 : program =
  [Mov W64 R1 (OpImm 100l); Alu W64 ADD R1 (OpImm 1l);
   Mov W64 R0 (OpReg R1); Exit]
let _ = assert_norm (accepts demo1)

(* r1=6; r2=7; r1*=r2; r0=r1; exit — MUL, accepts *)
let demo2 : program =
  [Mov W64 R1 (OpImm 6l); Mov W64 R2 (OpImm 7l); Alu W64 MUL R1 (OpReg R2);
   Mov W64 R0 (OpReg R1); Exit]
let _ = assert_norm (accepts demo2)

let _ = assert_norm (not (accepts [Exit]))                              (* R0 unbound *)
let _ = assert_norm (not (accepts [Mov W64 R0 (OpReg R3); Exit]))       (* R3 unbound *)
let _ = assert_norm (not (accepts [Mov W64 R0 (OpImm 0l)]))             (* no Exit *)
