# PCC for eBPF — Gap Analysis + Milestone 1 (arithmetic constraints in F*)

## Progress (updated as milestones land)

**Current goal: ARITHUNARY + ARITHBINREG + ARITHBINIMM (Veritas Fig. 14a classes)**
mapped to the deep embedding as: `Neg`/`Swap`/`MovSX` (unary), `Alu w op dst (OpReg r)`
(bin-reg), `Alu w op dst (OpImm i)` (bin-imm), plus `Mov` both forms.

### Phase 0 — environment
- [x] VM resized to 4 vCPU / 8 GB / 20 GB (2026-07-07)
- [x] apt toolchain (clang, libbpf-dev, bpftool, opam, build tools)
- [x] F* 2026.03.24 via opam (source build; binary-tarball path abandoned — GitHub
      CDN too slow on this link) + Z3 4.13.3 (+ apt z3 4.8.12 fallback)
- [x] OCaml extraction wiring — closed during M2: extracted Ebpf.{Ast..Check,
      Serialize} compile against opam fstar.lib (dune, `-w -a` for projector
      warnings) and run natively (smoke: serializer + Kernel-mode accept ✓)
- [x] project mounted at /home/ubuntu/ebpf_gen in VM

### Phase 1 — F* modules (all verified)
- [x] `fstar/Ebpf.Ast.fst` — AST: all 13 ALU ops × {W32,W64} × {REG,IMM}, NEG,
      MOV, MOVSX, byte swaps, `Assert_` pseudo-insn, Exit
- [x] `fstar/Ebpf.Int.fst` — math-int semantics helpers (wrap/sext/trunc_div/bswap)
- [x] `fstar/Ebpf.Semantics.fst` — executable step/run semantics; Total (ISA) vs
      Defensive (div0/oversized-shift = stuck) observation levels
- [x] `fstar/Ebpf.Interval.fst` — unsigned interval domain + transfer functions
      + per-op soundness lemmas
- [x] `fstar/Ebpf.Check.fst` — dual-mode checker (Strict | Kernel)
- [x] `fstar/Ebpf.Sound.fst` — soundness theorem statement + proof
- [x] `fstar/Ebpf.Build.fst` — `|>.` pipeline constructors, 6 positive examples,
      2 mode-divergence witnesses, 5 universal-reject tests, 3 expect_failure negatives
- [x] `fstar/Ebpf.Serialize.fst` — bytecode encoder (Assert_ erased) + hex dump
- [x] **all modules verify under fstar.exe** (F* 2026.03.24 / Z3 4.13.3, 2026-07-07)
- [x] soundness theorem machine-checked (no admits); Strict mode proven safe under
      Defensive semantics (div/0 + oversized shifts = stuck), Kernel mode under Total
- [x] fix found during verification: ADD/SUB/MUL transfer functions now const-fold
      (exact wraparound for constant operands) — needed for ex_alu32's 32-bit wrap

### Phase 2 — differential validation
- [x] `harness/loader.c` (BPF_PROG_LOAD, verifier log capture) — built in VM
- [x] `harness/diff.py` comparison driver
- [x] manifest generation via tactic dump (`Ebpf.Dump.fst` + `gen_manifest.py`)
- [x] **run on VM kernel 6.8.0-134: 13 programs, ZERO divergences** between
      F* kernel-faithful mode and the real verifier; both divergence witnesses
      (ex_div0_reg, ex_shift_reg) behave exactly as designed

### Phase 3 — documentation
- [x] `fstar/CONSTRAINTS.md` — 17-constraint transcription table (C1–C17)
- [x] differential results section filled in (13-program table)
- [x] final pass after verification

## Context

Project: correct-by-construction eBPF via a specialised, refinement-typed eBPF IR.
Frontends (F*, Lean, Dafny, Verus) target the IR; a formally verified compiler emits
bytecode + a proof certificate; a small kernel checker replaces the stock verifier's
analysis. First milestone: transcribe the arithmetic (ALU) constraints from the
literature into F* and write correct-by-construction arithmetic-only programs.

Materials analysed (via parallel extraction agents; full reports in session transcript):
- **VEP (NSDI'25)** `pubs/nsdi25-wu-xiwei.pdf` — two-stage sep-logic PCC, annotated-C
  frontend. No per-ALU-opcode VC catalogue, no wraparound model (user asserts Z64,
  internal asserts unbounded Z), no tnum/Spectre discussion, IR spec unpublished
  (repo only) → confirms the frontend-agnostic-published-IR novelty claim.
- **Veritas/SpecCheck (SOSP'25)** `pubs/ebpf_smt_fuzz-paper.pdf` +
  `repos/veritas/ebpf-dafny-spec/spec.dfy` (3,311 lines) — **the single best
  transcription source**: every insn is a ghost method, `requires` = verifier
  acceptance, `ensures` = ISA semantics; complete per-opcode ALU catalogue (~76
  methods) with file:line map. `enable_org` flag = kernel-faithful vs cleaned-up rules.
- **BCF (SOSP'25)** `pubs/BCF.pdf` + `repos/BCF` — kernel proof checker (2,337 LOC),
  QF_BV expr + 50-rule proof format (conclusions recomputed, avg proof 541 B, ~48 µs
  check). Proofs stay small only because they cover on-demand single-path refinement;
  the 31 MB figure is Nelson et al.'s Lean PCC proving *all* instructions — the naive
  full-program-PCC regime. BCF checker can't bit-blast MUL/DIV/MOD and currently
  trusts POLY_NORM/unknown rewrites (prototype soundness holes).

Environment: multipass VM `test-clone` (Ubuntu 24.04, kernel 6.8, 2 vCPU / 2 GB, root
available). No F*/Z3/Dafny/cvc5 installed on host or VM yet.

## Gaps in the plan (the user's question — consolidated)

1. **"The constraints" is three different things.** Kernel-faithful acceptance
   (Veritas `enable_org=true`), cleaned-up consistent rules (Veritas "beacon" mode),
   and actual runtime-safety obligations (what a clean-slate replacement needs).
   E.g. kernel: reg-divisor div/0 is *accepted* (runtime x/0→0, x%0→dst) while imm 0
   is rejected; reg shifts ≥ width accepted-and-havoced while imm shifts rejected.
   A replacement verifier gets to *choose* its spec — must decide before transcribing.
2. **F*/Z3 proofs are not shippable certificates.** Correct-by-construction in F* ≠
   proof-carrying: the kernel can't re-run Z3. The certificate design (SMT proof à la
   BCF vs per-instruction-checkable typing witness à la TAL vs VEP-style
   symbolic-exec + entailment proofs) dictates *how* constraints should be encoded in
   F* (deep embedding + typing judgment vs shallow refinements). BCF's data says
   full-program SMT proofs blow up; per-point annotations checked locally
   (linear, no solver) is the size-safe regime. This fork must be taken now, not later.
3. **Arithmetic-only programs are nearly vacuous under the kernel-faithful spec.**
   Real obligations only appear via: init-before-use, R10-not-dst, imm-form
   div0/shift-range rejects (syntactic), R0-initialized-at-exit. The value-tracking
   machinery (the research meat) is only exercised if we adopt strict semantic
   preconditions (prove divisor≠0, shift<width for register forms) and/or a
   bounds-assertion sink. Milestone needs a non-vacuity decision.
4. **No named ground-truth semantics.** ALU32 zero-extension, MOVSX, imm
   sign-extension (div/mod imm sign-extends 32→64), div/0 semantics, shift masking —
   must be pinned to RFC 9669 + a pinned kernel version. The Dafny spec has known
   quirks not to copy (Add64_IMM missing type requires; twocom2Abs32Bit masks with
   0xEFFF_FFFF (typo); SDIV/SMOD by INT64_MIN falls into the div/0 branch).
5. **Verifier ≠ checker.** The stock verifier also rewrites programs (ctx access
   conversion, runtime div/0 patching, speculation barriers, helper inlining) and
   feeds the JIT. A replacement must keep those transforms somewhere. Out of scope
   for M1 but must be on the roadmap.
6. **Spectre scope undefined.** All three papers essentially punt (BCF disables
   refinement on speculative paths; Veritas has a bypass flag; VEP silent).
   Decision: target privileged (CAP_BPF) programs initially; document it.
7. **Value-domain choice.** Kernel: tnum + u64/s64/u32/s32 ranges. BCF: ranges only,
   recovers bit-info by replaying ALU ops. Veritas: exact bv64 or full havoc. F*
   refinements can be exact for straight-line code — more precise than the kernel —
   but every fact claimed must be checkable by the eventual kernel checker.
   Non-linear ops (MUL/DIV/MOD) are exactly where checkers get weak.
8. **No validation loop.** Nothing ties "our spec accepts" to reality. Need
   differential testing: serialize our IR programs to real bytecode, load on the VM
   kernel, compare verdicts (Veritas' fuzzer method, reusable later at scale).
9. **Toolchain gap.** No F* anywhere; VM (2 vCPU/2 GB) too small for F*+Z3 dev and
   far too small for kernel builds. Decide host-vs-VM split.
10. **Version pinning.** VM kernel is 6.8; BCF patches target ≥6.17-ish trees;
    verifier behavior drifts per release. Pin kernel + ISA doc revision in the spec.
11. **Positioning vs BCF.** BCF keeps the whole verifier and augments it; we remove
    kernel analysis entirely. Must answer "why not just BCF": their approach retains
    verifier complexity/cruft and per-load solver latency (avg 9 s analysis on
    refinement-heavy programs); ours moves all reasoning to compile time — but then
    must solve the certificate-size problem BCF sidesteps (→ gap 2).
12. **Frontend-agnosticism risk.** Transcribing constraints as idiomatic F*
    refinements can bake F*-isms into the IR. The IR spec (syntax, typing rules,
    certificate format) should be documented in a tool-neutral way from day one.

## Design decisions (confirmed with user)

1. **Spec basis: both, flag-selected** — a mode flag (mirroring Veritas' `enable_org`)
   selects *kernel-faithful* rules (accept reg-div/0 with ISA runtime semantics,
   accept+havoc reg shifts ≥ width) or *strict clean-slate* rules (prove divisor≠0,
   shift<width). Precisely documents where the two specs diverge — feeds the writeup.
2. **Encoding: deep embedding + smart constructors** — instruction AST + executable
   semantics + checker + soundness theorem; refinement-typed smart constructors give
   the shallow-feeling authoring surface. Programs are serializable instruction lists;
   the typing derivation is the future certificate (TAL-style, locally checkable).
3. **Non-vacuity: strict preconditions + assert-bounds sink** — an `Assert (r ≤ K)`
   pseudo-instruction (erased at serialization) exercises range reasoning through ALU
   chains; strict mode adds divisor≠0 / shift<width / init-before-use / R0-at-exit.
4. **Toolchain: everything in the VM** — grow `test-clone` (2→4 vCPU, 2→8 GB RAM,
   9.6→20 GB disk; multipass set only grows, VM must be stopped). Install F* binary
   release (bundled Z3) + opam/OCaml for extraction inside the VM. Host stays clean;
   kernel loading tests run in the same VM with root.

## Milestone 1 implementation plan

### Phase 0 — environment (VM)
- `multipass stop test-clone`; `multipass set local.test-clone.{cpus=4,memory=8G,disk=20G}`; restart.
- Install: F* binary release (fstar.exe + z3 bundled), opam + OCaml (for extraction),
  build tools, libbpf/bpftool + kernel headers (for the loader).
- Mount or clone the project into the VM (`multipass mount /home/r41k0u/ebpf_gen ...`).

### Phase 1 — F* development (new `fstar/` directory in repo)
1. **`Ebpf.Ast.fst`** — arithmetic subset AST: ALU64/ALU32 ×
   {ADD,SUB,MUL,DIV,SDIV,MOD,SMOD,AND,OR,XOR,LSH,RSH,ARSH,NEG,MOV,MOVSX,END} ×
   {REG,IMM} + `Assert` pseudo-insn + EXIT. Straight-line only (no jumps) in M1.
   Scalar-only register file (pointers are M2+).
2. **`Ebpf.Semantics.fst`** — executable step semantics over
   `regfile = reg → option u64` (None = uninit), transcribed from spec.dfy `ensures`
   clauses cross-checked against RFC 9669: ALU32 zero-extension, MOVSX sign-extension,
   div/mod imm sign-extension 32→64, x/0→0, x%0→dst, shift masking. Known Dafny-spec
   quirks NOT copied (Add64_IMM missing requires; twocom2Abs32Bit 0xEFFF_FFFF typo;
   SDIV/SMOD INT64_MIN-as-zero-divisor).
3. **`Ebpf.Check.fst`** — the constraint transcription: `check : mode -> tystate ->
   insn -> option tystate` from spec.dfy `requires` clauses (universal: dst≠R10,
   operands initialized; strict mode: semantic divisor≠0 / shift<width / assert
   bounds; kernel mode: syntactic imm rejects only, havoc semantics).
   **Soundness theorem**: `check` succeeds ⟹ `step` never gets stuck (and in strict
   mode: no div-by-zero, no out-of-range shift, asserts hold).
4. **`Ebpf.Build.fst`** — smart constructors: `prog ts` indexed by typing state,
   pipeline style (`start |> mov64i R1 255l |> ... |> exit`). 5–10 positive examples
   (incl. BCF's shift_constraint pattern re-expressed) + negative tests via
   `[@@expect_failure]`.
5. **`Ebpf.Serialize.fst`** — instruction list → eBPF bytecode bytes (Assert erased),
   extracted to OCaml. Encoding per the ISA: 8-byte insns, opcode = op|source|class.

### Phase 2 — differential validation (VM, root)
- Tiny C loader: reads serialized bytecode, bpf(2) BPF_PROG_LOAD (socket filter or
  kprobe prog type — simplest ctx), captures verifier verdict + log.
- Harness: for each example, compare {F* strict verdict, F* kernel-mode verdict,
  real kernel 6.8 verdict}; log divergences.

### Phase 3 — documentation
- **`CONSTRAINTS.md`** — transcription table: per-opcode constraint ↔ spec.dfy
  file:line ↔ kernel behavior ↔ our F* refinement, mode differences and divergences
  flagged. Seeds the IR spec document and the 2–3 page writeup for Kartikeya.

## Verification
- All F* modules verify (`fstar.exe`); `[@@expect_failure]` negative tests fail for
  the intended reason (wrong-precondition, not syntax).
- Soundness theorem machine-checked, not admitted.
- All positive examples serialize, load, and are ACCEPTED by the VM kernel verifier;
  at least one strict-mode-rejected / kernel-accepted program (reg-div by possibly-
  zero) and the mirror case documented in CONSTRAINTS.md.
- End-to-end demo: shift_constraint-style program built in F*, proof obligations
  discharged at construction, loaded successfully on the VM.

## Roadmap context (post-M1, for orientation only)
M2: conditional jumps → path-sensitive tystate + join/annotations (certificate shape
becomes real). M3: memory (stack/ctx/map ptrs) — where assert-sink generalizes to
access bounds. M4: certificate extraction + standalone checker (C, few hundred LOC,
compare against BCF checker rules). Throughout: IR spec doc kept tool-neutral.

---

# Milestone 2 — frontend-agnostic annotated IR + proof certificates

Scope: ARITHUNARY / ARITHBINREG / ARITHBINIMM. Full M2 plan in
`~/.claude/plans/` (session); this section tracks decisions + progress.

## Design decisions (confirmed 2026-07-07)
1. **Own minimal proof format** (not BCF reuse) — consequence: the proof checker is
   implemented AND verified in F* against the same formula semantics as the IR;
   the end-to-end theorem covers the checker itself.
2. **Annotations = SMT-LIB2 QF_BV subset** over r0..r10 (text); expr-arena binary
   form for the kernel. Scaling to full ISA via type/region layer BESIDE the value
   logic (M3), not by growing the formula language.
3. **Full scope**: spec + F* metatheory + working pipeline + two-frontend demo
   (F* + Python) + measurements.
4. **TAL-style density** (user: minimize in-kernel TCB): kernel checker has NO
   abstract domain — per insn either SP-exact (rebind dst, zero bytes) or weaken
   (claim + small proof). Frontends author sparse; the userspace certifier
   densifies. Delta-encoded annotations in a shared DAG arena.

## Threat model (summary)
- No transplanting: checker constructs every goal from the loaded bytecode itself;
  certificates supply derivations only. Wrong program → wrong goals → reject.
- No forging: proof steps carry rule+premises; conclusions recomputed; final
  conclusion must equal the goal. End-to-end theorem quantifies over ARBITRARY
  certificate bytes.
- No assumption smuggling: no `@assume` in wire format; entry annotation pinned by
  checker (all regs uninit).
- Load-time TCB: the small checker only (no solver, no F*). Residual: semantics
  model vs interpreter/JIT (differential testing), C rewrite vs verified reference
  (M4), DoS hygiene (size caps, backward-only refs, linear pass).

## Progress
- [ ] M2.-1 bookkeeping (this section) committed
- [~] M2.0 `ir/SPEC.md` v0 ("Keel", working name) — draft 2 committed after 5-lens
      adversarial review (28 findings triaged/fixed, incl. 3 unsound rules);
      round-2 verification workflow running
- [x] differential target re-pinned to kernel 7.0 (Ubuntu 26.04 VM `kernel7`);
      M1 corpus re-run: zero divergences on 7.0.0-27 (identical to 6.8)
- [~] M2.1 F* metatheory (verified, no admits; on kernel 7.0 VM w/ F* 2026.03.24):
      - [x] Ebpf.Formula — term/atom AST + totalized SMT-LIB QF_BV evaluation
      - [x] Ebpf.Proof — checkable rule language + machine-checked per-rule
            soundness for a verified core (incl. the 3 review-flagged rules);
            check_proof_sound
      - [x] Ebpf.Annot — simulation bridge: defterm_sound proves term
            evaluation tracks the ISA semantics (W64 core)
      - [x] Ebpf.CertCheck — end-to-end soundness theorem: accepts ⟹ program
            runs to Exit with R0 set (safe), for ANY certificate; non-vacuity
            demos check
      - [ ] strict-mode obligation integration + claim-validity reporting into
            the CertCheck walk (proof-rule soundness already done)
      - [ ] SDIV/SMOD, ALU32, MOVSX, byte-swap definition-term bridge lemmas
      - [x] OCaml extraction wiring (done earlier this milestone)
- [~] M2.2 pipeline (`ir/certifier/`, OCaml around extracted verified code):
      - [x] `.kir` parser (instructions + `@assert (cmp rN const)` claims)
      - [x] binding computation via extracted `Ebpf_Annot.defterm`
      - [x] certifying prover (`plan`): tightest-bound proof synthesis for
            MOV/AND/ADD/MUL/const via UleRefl/AndLeL-R/MonoAdd/MonoMul/Trans
      - [x] verified validation: `Ebpf_CertCheck.accepts` (safety) +
            `Ebpf_Proof.check_proof` (each claim's proof)
      - [x] bytecode via extracted `Ebpf_Serialize`; loads ACCEPT on kernel 7.0
      - [x] adversarial `selftest`: verified checker rejects false-goal,
            transplanted, and forged-rule certificates
      - [x] reproducible: `make extract` (fstar) → `make build`/`run`/`selftest`
      - [x] DIV/MOD claim proving: added verified DivIteLe/DivIteBound/ModLe/
            ModBound/EqUle rules to Ebpf.Proof; prover uses them + an
            EvalEq+EqUle fallback for any ground term (shift/or/xor/sub/sdiv);
            div.kir/mod.kir certify and load on kernel 7.0
      - [ ] binary certificate file format; full SMT-LIB parsing; non-ground
            (symbolic, v1) claim proving
- [ ] M2.3 two-frontend demo: Ebpf.Emit.fst + python binding → same certificates
- [ ] M2.4 measurements (bytes/insn, proof bytes, check time) + tamper-rejection
      tests + docs
