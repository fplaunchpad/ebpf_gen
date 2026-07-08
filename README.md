# Proof-Carrying eBPF

**A frontend-agnostic, refinement-typed intermediate representation for
correct-by-construction eBPF, with proof certificates checked by a small,
formally verified kernel checker.**

> Research prototype. Current scope: the arithmetic instruction fragment
> (`ARITHUNARY` / `ARITHBINREG` / `ARITHBINIMM`), straight-line programs.
> The metatheory that exists is machine-checked in F* with no admitted
> lemmas; everything not yet proved is documented as such.

---

## The problem

The Linux eBPF verifier is a large, evolving piece of in-kernel C that both
*decides* whether a program is safe and *is trusted* to be correct. It is a
recurring source of soundness and precision bugs (Agni, Buzzer,
CVE-2023-39191, …), it rejects many safe programs for lack of precision, and
its errors are opaque — a poor fit for the emerging world of LLM-generated
kernel extensions, where a tool needs to know *which* safety constraint it
failed to establish.

Two lines of prior work point at a way out. **Proof-carrying code** (Necula;
BCF, SOSP'25) moves the *reasoning* to a compiler that ships a proof, leaving
the kernel to only *check* it. **Verified compilation** (Vale/HACL*,
CompCert) shows a toolchain can be trusted because it is proved correct, not
because it is re-tested. But BCF keeps the entire verifier and augments it;
VEP (NSDI'25) replaces it but with an unverified checker and an unpublished,
C-specific IR.

## The idea

Move all the reasoning to compile time and make the kernel's job tiny and
trustworthy:

1. **A published, frontend-agnostic IR** ("Keel") with rich refinement-type
   annotations. Any SMT-backed proof language — F*, Dafny, Lean (+ lean-smt),
   Verus — can target it by writing a *printer*, not a deep integration.
2. **A certifier** compiles annotated IR to eBPF bytecode **plus a proof
   certificate**.
3. **A small, formally verified checker** — destined for the kernel —
   validates the certificate against the bytecode. No SMT solver, no
   abstract interpretation, no fixpoint: just expression-arena bookkeeping,
   syntactic equality, and a fixed table of proof rules.

The checker is the *reference model itself*, implemented and proved sound in
F*. That is the key difference from BCF (unverified C checker) and VEP
(unverified checker implementation): here, "the checker is correct" is a
theorem, not a test suite.

### Why this shape

- **TAL-style density → minimal kernel TCB.** Every instruction is
  annotated in the wire format, so the checker never runs an abstract
  domain or a solver; it validates certificate-supplied facts against the
  loaded bytecode. Frontends still author *sparsely* — the userspace
  certifier densifies.
- **Certificates can't be faked.** The checker reconstructs every proof
  *goal* from the loaded bytecode, never from the certificate; the
  certificate supplies only *derivations*. A certificate attached to a
  different program proves statements about terms the checker never builds
  → reject. This "anti-transplant" property is a machine-checked theorem
  (`Ebpf.CertCheck.soundness`), quantified over *arbitrary* certificate
  bytes. See [`ir/SPEC.md`](ir/SPEC.md) §10 for the full threat model.
- **QF_BV as the value logic, a type/region layer beside it for memory.**
  eBPF registers are 64-bit machine words; quantifier-free bitvector
  formulas model their arithmetic exactly. Memory (a later milestone) adds
  a structural pointer-region layer *next to* the value logic rather than
  growing the formula language — this is the scaling story for the full ISA.

## Status

| Milestone | What | State |
|-----------|------|-------|
| **M1** | Arithmetic constraints in F*: deep-embedded ISA, dual-mode checker, machine-checked soundness, bytecode serializer | **Done.** All modules verify; **zero-divergence** differential vs the real Linux verifier (kernels 6.8 and 7.0). |
| **M2.0** | The Keel IR specification (tool-neutral): text + binary format, formula grammar, checker algorithm, proof-rule catalog, threat model | **Done** (revised after adversarial review). [`ir/SPEC.md`](ir/SPEC.md) |
| **M2.1** | IR metatheory in F*: annotation semantics, a sound proof system, the term↔ISA simulation bridge, and the **end-to-end soundness theorem** | **Done** for the W64 arithmetic core; no admits. |
| **M2.2** | Userspace pipeline: `.kir` parser, certifying prover, `irc` certifier around the extracted verified checker | **Done.** DSL/hand programs certify + load on kernel 7.0; `irc selftest` shows forged/transplanted certificates rejected. |
| **M2.3** | High-level ALU expression **DSL** (`Ebpf.Dsl`) → verified lowering + register allocation → `.kir` → certificate + bytecode | **Done.** 14-program corpus: all certify (verified), load ACCEPT on kernel 7.0, and `BPF_PROG_TEST_RUN` result matches the DSL evaluator. [`ir/dsl/`](ir/dsl/) |
| **M2.4** | Certificate-size / proof-step / check-time measurements | **Done.** avg 3.1 proof steps, ~123 B certs, ~1–4 µs checks. [`ir/MEASUREMENTS.md`](ir/MEASUREMENTS.md) |

**Milestone 2 is complete**: published IR spec, verified metatheory (15 F*
modules, no admits), a working front-to-kernel pipeline, a high-level DSL
frontend, and measurements.

**Machine-checked:** the M1 checker is sound against the ISA model; the
annotation semantics is well-defined; every proof rule is individually sound;
symbolic bindings provably track the real machine; and *an accepted program
runs safely, for any certificate*. **Staged for later milestones (documented,
not assumed):** control flow (v1) and memory (v2); strict-mode
obligation/claim integration into the checker walk; the definition-term
bridge for SDIV/SMOD, ALU32, MOVSX, byte swaps; a binary certificate file
format; a verified lowering; and the Dafny frontend.

## Repository layout

```
ir/SPEC.md          The Keel IR specification (the design; tool-neutral)
fstar/              F* development (the metatheory)
  Ebpf.Ast          instruction syntax
  Ebpf.Int          bitvector arithmetic helpers          } trusted
  Ebpf.Semantics    the ISA model (what a program does)    } spec
  Ebpf.Interval     unsigned-interval abstract domain (+ soundness)
  Ebpf.Check        M1 dual-mode (strict/kernel) checker
  Ebpf.Sound        M1 soundness theorem
  Ebpf.Build        correct-by-construction authoring + tests
  Ebpf.Serialize    IR → eBPF bytecode
  Ebpf.Formula      QF_BV annotation language + SMT-LIB semantics (trusted)
  Ebpf.Proof        the proof system + per-rule soundness
  Ebpf.Annot        term ↔ ISA simulation bridge
  Ebpf.CertCheck    the checker + end-to-end soundness theorem
  WALKTHROUGH.md    per-function guide, framed for manual review
  CONSTRAINTS.md    the C1–C17 arithmetic-constraint transcription table
harness/            differential tester: loader.c + diff.py (vs real verifier)
TESTING.md          how to reproduce everything
plan.md             milestone plan + progress tracker
pubs/ repos/        reference papers and artifacts (BCF, VEP, Veritas, Vale, Silver)
```

## Quick start

Everything runs in a multipass VM with the toolchain
(F* 2026.03.24 + Z3 4.13.3). Verify the whole development:

```sh
multipass exec test-clone -- bash -c \
  'cd /home/ubuntu/ebpf_gen/fstar && eval $(opam env --switch=default) && make verify'
```

Differential-test the M1 checker against the real kernel 7.0 verifier:

```sh
multipass exec kernel7 -- bash -c \
  'cd /home/ubuntu/ebpf_gen/harness && make -s loader && sudo python3 diff.py manifest.tsv'
```

Full instructions, per-module commands, and non-vacuity checks are in
[`TESTING.md`](TESTING.md). To review the proofs by hand, start with
[`fstar/WALKTHROUGH.md`](fstar/WALKTHROUGH.md) §0 — it separates what must be
*believed* (the ISA model, the annotation semantics, the theorem statements)
from what F* has already *proved*.

## Relation to prior work

- **BCF** (SOSP'25) — PCC via proof-guided abstraction refinement. Keeps the
  full verifier and adds an (unverified, C) proof checker. We reuse its
  expression-arena / recomputed-conclusion wire discipline but *replace*
  kernel analysis and *verify* the checker.
- **VEP** (NSDI'25) — two-stage verified eBPF over annotated C. Closest in
  spirit; its IR is unpublished and C-specific, and its checker
  implementation is unverified. Our IR is published and frontend-agnostic.
- **Veritas / SpecCheck** (SOSP'25) — a Dafny specification of verifier
  acceptance; our single best source for the arithmetic constraints (see
  `fstar/CONSTRAINTS.md`) and the model our differential harness echoes.
- **Vale** and **Silver/Viper** — architectural inspiration for the IR
  (instructions-as-Hoare-triples, VC-gen as a total function; assert-as-
  primitive, per-obligation identity). Neither exports checkable proofs
  outside its proof assistant — the gap this project fills.

## Context

Research project at FPLaunchpad, IIT Madras.
See `plan.md` for the full gap analysis and design rationale.
