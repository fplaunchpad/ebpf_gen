# F* code walkthrough (for manual verification)

This documents every function in the F* development so you can review it by
hand. Read §0 first: it tells you **what you must check by eye** versus what
F* has already machine-checked for you.

## 0. How to read this / the trust model

F* + Z3 mechanically prove every `Lemma` and every refinement-type
obligation. So you do **not** need to re-check any proof body. What a proof
assistant *cannot* tell you is whether the **statements** are meaningful.
Manual review should therefore focus on exactly three things:

1. **The trusted specification.** These definitions are *assumed to model
   reality*; nothing proves them. If they are wrong, everything above them
   is vacuously "correct." They are:
   - `Ebpf.Semantics` — the model of what an eBPF program *does* (the ISA).
     Believe-or-check against RFC 9669 / the kernel. (We also validate it by
     differential testing against the real kernel verifier — see TESTING.md.)
   - `Ebpf.Formula.evalT` / `evalA` — the *meaning of an annotation formula*
     (SMT-LIB2 QF_BV semantics). If this diverges from real SMT-LIB, a
     "valid" annotation could mean something other than you think.
   - `Ebpf.Int` — the arithmetic helpers both rest on (small, checkable).
2. **The theorem statements** — `Ebpf.Sound.soundness`,
   `Ebpf.Proof.check_proof_sound`, `Ebpf.Annot.defterm_sound`,
   `Ebpf.CertCheck.soundness`. Check that each says what you want "safe" and
   "sound" to mean. A true-but-weak theorem is the classic trap.
3. **Non-vacuity.** Check the `assert_norm`/`expect_failure` tests actually
   exercise acceptance *and* rejection, so the checker isn't trivially
   accepting/rejecting everything.

Everything else (`Interval`, `Check`, `Proof.apply`, the bridge lemmas) is
*derived and proved*; you can trust it modulo (1)–(2).

Module dependency order (also the compile/verify order):
`Ast → Int → Semantics → Interval → Check → Sound → Build → Serialize`
(M1), then `Formula → Proof → Annot → CertCheck` (M2.1).

---

# Milestone 1 modules

## `Ebpf.Ast.fst` — the instruction syntax (TRUSTED shape)

A deep embedding of the arithmetic instruction subset. No functions, just
datatypes:
- `reg` — the 11 registers `R0..R10`.
- `width` — `W32` (32-bit ALU, zero-extends) or `W64`.
- `alu_op` — `ADD SUB MUL DIV SDIV MOD SMOD AND OR XOR LSH RSH ARSH`.
- `operand` — `OpReg reg` or `OpImm I32.t` (32-bit immediate).
- `movsx_sz` (`SX8/16/32`), `swap_kind` (`ToLE/ToBE/Bswap`), `swap_sz`.
- `insn` — `Alu | Neg | Mov | MovSX | Swap | Assert_ | Exit`. `Assert_ r
  bound` is our pseudo-instruction (a claimed upper bound on a register),
  erased at serialization.
- `program = list insn`.
Review: check the constructors cover the ops you intend and nothing is
mis-typed (e.g. `Neg` is unary, `Alu` carries a width).

## `Ebpf.Int.fst` — arithmetic helpers (TRUSTED, small)

Bit-vector arithmetic phrased as math-integer ops with an explicit wrap.
- `fits n x` — `x` is a valid `n`-bit pattern (`0 ≤ x < 2^n`).
- `wrap n x` — reduce `x` mod `2^n` (the return type proves it fits).
- `to_u64 x` — a fitting 64-bit pattern as a machine `U64.t`.
- `sval n x` — the *signed* (two's-complement) value of pattern `x`.
- `low n x` — low `n` bits (= `wrap n x`).
- `sext f n x` — sign-extend the low `f` bits to width `n`.
- `imm64 i` / `imm32 i` — a 32-bit immediate as a 64-bit (sign-extended) or
  32-bit pattern. **Check:** `imm64` sign-extends (ALU64 rule), `imm32`
  truncates (ALU32 rule) — this is a real ISA distinction.
- `trunc_div a b` / `trunc_mod a b` — toward-zero signed division/remainder
  (BPF SDIV/SMOD). **Check:** rounds toward zero, not floor.
- `swap_bytes` / `bswap` — byte reversal of the low `nb` bytes.

## `Ebpf.Semantics.fst` — the ISA model (**TRUSTED — the core spec**)

This is *the* definition of program behavior. Review it against RFC 9669.
- `regfile = reg -> option U64.t` — a machine state; `None` = uninitialized.
- `bits w` — 32 or 64.
- `regbits w x` — register `x` viewed at width `w` (W32 = low 32 bits).
- `opbits rf w o` — the operand's value at width `w`; `None` if it reads an
  uninitialized register. (Immediates always defined.)
- `res64 w x` — the width-`w` result written back into a 64-bit register
  (W32 results zero-extend, by `fits 32 ⇒ fits 64`).
- `updr rf r v` — functional register update.
- `alu_semn n op d s` — **the arithmetic truth table** at width `n`. Check
  each line: `DIV`/`MOD` are unsigned with `x/0=0`, `x%0=x`;
  `SDIV`/`SMOD` truncated with the same zero convention; `LSH/RSH/ARSH` mask
  the shift amount (`s % n`); `AND/OR/XOR` are the bitwise ops; `ARSH` uses
  the signed value. `alu_sem w = alu_semn (bits w)`.
- `movsx_bits`, `swap_bits`, `swap_sem` — MOVSX widths and byte-swap
  semantics (little-endian host: `ToLE` truncates, `ToBE`/`Bswap` reverse).
- `semantics = Total | Defensive` — **two observation levels.** `Total` =
  the ISA (div/0 and big shifts are defined). `Defensive` = div/0 and
  shift ≥ width are *stuck* (`None`). The difference *is* the extra
  guarantee strict mode buys.
- `alu_defined n op s` — the predicate that fails exactly on div/0 and
  oversized shift (used by `Defensive`).
- `stepx sm rf i` — **single-instruction execution**, returning `None` when
  *stuck* (uninit read, `Exit`, or a Defensive-undefined op). This is where
  "unsafe = stuck" is defined. `step = stepx Total`.
- `runx sm rf p` — run a straight-line program; `Some` iff it reaches `Exit`
  with `R0` initialized without getting stuck. `run = runx Total`.
- `rf0` — the empty initial state (nothing initialized).
**Manual-review focus:** `alu_semn`, `stepx`, `runx`, and the meaning of
`Some`/`None`. "`runx` returns `Some`" is our definition of **safe**; make
sure you accept it (reaches Exit, R0 set, no stuck step).

## `Ebpf.Interval.fst` — abstract domain (PROVED sound)

Unsigned intervals `iv n = {ilo; ihi}` and per-op transfer functions, each
proved to over-approximate `alu_semn`.
- `inb i x` — `x` is in `[ilo, ihi]`. `mk`, `havoc` (⊤ = `[0,2^n-1]`),
  `exact x` (`[x,x]`), `is_const`.
- `div_antitone`, `div_le_self`, `mul_mono` — arithmetic monotonicity
  lemmas reused throughout.
- `tf_alu n op a b` — the transfer function: precise for ADD/SUB/MUL when no
  overflow (with const-const folding), AND (min bound), DIV/MOD (divisor
  excludes 0), constant shifts, RSH; `havoc` for signed ops / OR / XOR /
  dynamic LSH.
- `tf_alu_sound` — **the key lemma:** if `d ∈ a` and `s ∈ b`, then
  `alu_semn n op d s ∈ tf_alu n op a b`. This is what makes interval
  tracking trustworthy.
- `narrow32`/`narrow32_sound`/`widen32` — move intervals between the 64-bit
  register state and a 32-bit operating width.

## `Ebpf.Check.fst` — the M1 dual-mode checker (PROVED sound in Sound.fst)

- `mode = Strict | Kernel`. `tystate = reg -> option (iv 64)` — abstract
  state (per-register interval; `None` = uninitialized).
- `read ts r` — reads `ts`, but returns `None` for `R10` (frame pointer is
  not a scalar in M1). `wr` — update.
- `aiv ts w o` — abstract operand value (narrows to 32 bits for W32).
- `narrow`/`widen` — width conversions.
- `allowed m op w src b` — **the mode-dependent acceptance rule.** For
  DIV/MOD: immediate 0 always rejected; register divisor rejected only in
  `Strict` (needs `b.ilo > 0`, i.e. interval excludes 0). For shifts:
  immediate ≥ width always rejected; register amount constrained only in
  `Strict`. **Check:** this is the strict-vs-kernel fork.
- `tf_movsx`, `tf_swap` — transfer functions for MOVSX / byte swap.
- `check m ts i` — one-instruction check → next `tystate` or `None` (reject).
  Encodes C1–C17 (see CONSTRAINTS.md): dst ≠ R10, operands initialized,
  imm-div0/imm-shift rejects, R0-at-Exit, no code after Exit, Assert bound.
- `check_prog`, `ts0`, `accepts m p`.

## `Ebpf.Sound.fst` — M1 soundness theorem (PROVED)

- `sem_of m` — `Strict ↦ Defensive`, `Kernel ↦ Total`.
- `agree_at`/`agree` — the simulation invariant: every register's interval
  contains its concrete value (finite 11-way conjunction for Z3 robustness).
- `agree_lookup`, `agree_update`, `aiv_sound`, `tf_movsx_sound`,
  `tf_swap_sound` — supporting lemmas.
- `check_insn_sound` — one-step simulation: if `check` accepts an
  instruction from an agreeing state, `stepx (sem_of m)` doesn't get stuck
  and the results still agree. **This is where strict-mode acceptance is
  connected to Defensive non-stuckness.**
- `run_sound`, and the top-level **`soundness m p`**: *if `accepts m p`
  then `runx (sem_of m) rf0 p` is `Some`* — an accepted program runs safely
  under its mode's semantics. **Manual-review focus:** this theorem
  statement.

## `Ebpf.Build.fst` — correct-by-construction authoring (M1) + tests

- `check_list`/`no_exit`/`check_list_snoc`/`no_exit_snoc`/`check_prog_snoc_exit`
  — list plumbing lemmas so a program can be built incrementally.
- `bld m` — a builder carrying a validated instruction prefix + its
  `tystate` + a proof the prefix checks. `start`, `emit`, `( |>. )`
  (pipeline op), `finish` (append `Exit`, yielding `p{accepts m p}`).
  **Point:** writing a program with `|>.` *is* proving it — an ill-typed
  step is a type error.
- Positive examples (`ex_shift`, `ex_div`, `ex_alu32`, `ex_chain`,
  `ex_movsx`, `ex_mul`) each have type `p:program{accepts Strict p}`.
- Mode-divergence witnesses (`ex_div0_reg`, `ex_shift_reg`) with
  `assert_norm (accepts Kernel ..)` and `assert_norm (not (accepts Strict ..))`.
- Universal-reject `assert_norm`s (uninit read, no R0, dst=R10, imm div0,
  imm shift 64).
- `[@@expect_failure]` negatives (`bad_div`, `bad_assert`, `bad_uninit`) —
  programs that must *fail to typecheck*. **Non-vacuity evidence.**

## `Ebpf.Serialize.fst` — bytecode emitter (PROVED well-formed)

- `reg_num`, `cls` (ALU32=0x04/ALU64=0x07), `op_bits` (opcode per op),
  `op_off` (SDIV/SMOD carry offset 1), `src_bit`, `le_bytes`, `fields`
  (one 8-byte instruction), `op_imm`, `op_src`, `swap_imm`, `movsx_off`.
- `encode_insn`/`encode` — instruction(s) → bytes (`Assert_` → `[]`, erased).
- `nib`/`byte_hex`/`hex_of`/`serialize_hex` — hex dump.
- Two `assert_norm` encoding anchors (`mov64 r0,0; exit` and `add64 r1,r2`)
  pin the wire format. **Check these against `bpf.h` if you want.**

---

# Milestone 2.1 modules (the IR metatheory)

## `Ebpf.Formula.fst` — annotation language + meaning (**TRUSTED: `evalT`/`evalA`**)

The QF_BV term/atom language and its SMT-LIB evaluation. **`evalT`/`evalA`
are the definition of what an annotation *means*; review them against
SMT-LIB2.**
- `bvop2` / `bvop1` / `atomkind` — operators and comparison kinds.
- `term` — the expression AST: `TC w v` (constant), `TOp2/TOp1`, `TConcat`,
  `TExtract hi lo`, `TZext n`, `TSext n`, `TIte`. `atom = Atom kind t t`.
- `res = (w:pos & v:int{fits w v})`; `mkres`.
- `sgn`, `msb`, `negp` — signed value, MSB test, two's-complement negate.
- `eval_ashr`, `eval_sdiv`, `eval_srem` — **the SMT-LIB total semantics of
  the signed/arith-shift ops**, including zero-divisor cases (`bvsdiv x 0`
  = all-ones or 1 by sign; `bvsrem x 0 = x`). **Check:** these implement
  SMT-LIB's `bvsdiv`/`bvsrem` via sign-magnitude over `bvudiv`/`bvurem`. The
  eBPF divergence (e.g. eBPF `sdiv x 0 = 0`) is NOT here — it lives in the
  ITE-guarded *definition terms* (Annot), so the evaluator stays pure
  SMT-LIB.
- `eval_op2 op w a b` — the binary-op evaluator: `Udiv`-by-0 = all-ones,
  `Urem`-by-0 = dividend, `Shl/Lshr` saturate to 0 when the amount ≥ width
  (SMT-LIB, *not* masked — masking is expressed in the term).
- `evalT t` — evaluate a term to `Some (width, value)` or `None`
  (ill-formed, e.g. width mismatch). Recursive; total.
- `evalA c` — evaluate an atom to `Some bool` or `None`.
- `valid c` — `evalA c == Some true`. **The meaning of "this annotation
  holds."** `valid_all` — a conjunction of atoms.
**Manual-review focus:** `eval_op2`, `evalT`, `evalA`, and that `valid`
means "well-formed and true."

## `Ebpf.Proof.fst` — the proof system (PROVED sound, rule by rule)

A checkable proof language; each rule's soundness is a machine-checked
lemma against `Formula.valid`.
- `div_antitone`, `div_le_self`, `mul_mono` — local arithmetic lemmas.
- `rule` — the proof-rule AST. Leaves (0-premise): `R_EvalEq` (constant
  folding), `R_UleConst/R_UltConst/R_UgeConst/R_NeConst` (decide a
  constant comparison), `R_UleRefl`, `R_EqRefl`. Structural:
  `R_AndLeL/R` (`a&b ≤ a`, `≤ b`), `R_ShrLe` (`a>>s ≤ a`), `R_DivLe`
  (`a/b ≤ a`, **requires a proof that `b≠0`**), `R_ShrBound`, `R_MonoAdd`,
  `R_MonoMul` (bounds, **with no-overflow side conditions**), `R_TransUle`,
  `R_NeFromUge`. Premises are indices into earlier conclusions.
- `nth` — safe list lookup.
- `apply cs r` — **compute a rule's conclusion atom** from the prior
  conclusions `cs`, or `None` on any structural/side-condition/
  well-formedness failure. This is the checker's per-step work; note it
  *evaluates* terms where needed (so ill-formed inputs are rejected).
- `all_valid cs` — every conclusion in `cs` is `valid`. `nth_valid`,
  `all_valid_snoc` — bookkeeping.
- `apply_sound cs r` — **the core soundness lemma:** if all prior
  conclusions are valid, then whatever `apply` returns is valid. The
  interesting cases (`R_DivLe`, `R_ShrBound`, `R_MonoMul/Add`, ...) are the
  three review-flagged rules plus the bounds rules, each discharged via the
  arithmetic lemmas. **This is the heart of "proofs can't lie."**
- `run_proof cs steps` — fold `apply` over a step list, appending
  conclusions. `run_proof_sound` — preserves `all_valid`.
- `check_proof init goal steps` — the proof checks iff it runs and its last
  conclusion equals `goal`. `last_all_valid`.
- **`check_proof_sound init goal steps`:** *if the initial facts are valid
  and the proof checks, then `goal` is valid.* **Manual-review focus:** this
  statement (it's what CertCheck will rely on for obligations/claims).

## `Ebpf.Annot.fst` — the simulation bridge (PROVED, W64 core)

Connects arena terms to the ISA semantics.
- `bnds = reg -> option term` — symbolic bindings (each register's value as
  a term). `upd`.
- `bagree_at`/`bagree` (unfolded, finite conjunction) — **the bridge
  invariant:** every bound register's term evaluates to the register's
  concrete 64-bit value (and "bound in `b` ⇒ bound in `rf`").
- `bagree_lookup`, `bagree_at_update`, `bagree_update` — invariant plumbing.
- `opterm b o` — the term for an operand (immediate → `TC 64 (imm64 i)`;
  register → its binding). `opterm_sound` — it evaluates to the concrete
  operand value.
- `defterm b i` — **the SPEC §5 definition term** for the instruction's
  destination (e.g. `div64` → `ite (s=0) 0 (bvudiv a s)`; shifts → masked;
  `neg64` → `bvneg`). Returns `None` for the *staged* ops (SDIV/SMOD, all
  ALU32, MOVSX, byte-swaps) so the checker treats them as unsupported rather
  than trusting an unproven shape.
- `wdst i` — the destination register when `defterm` supports `i`.
- `mask63` — `logand s 63 = s % 64`, connecting SPEC's explicit shift mask
  to the semantics' `s % 64`.
- `res64v` — `U64.v (res64 W64 x) = x`.
- **`defterm_sound b rf i`:** if `bagree b rf` and `defterm` supports `i`,
  then the machine step succeeds and rebinding `dst` to its definition term
  *preserves* `bagree` against the stepped register file. **This is the
  proof that symbolic bindings track the real machine.**

## `Ebpf.CertCheck.fst` — the checker + end-to-end theorem (PROVED)

- `check_walk b p` — **the checker:** walk instructions, requiring each to
  be a supported `defterm` shape and rebinding `dst`; accept iff the program
  ends in a single `Exit` with `R0` bound. (`b0` = empty bindings,
  `accepts p = check_walk b0 p`.)
- `bagree_b0` — the empty bindings agree with `rf0`.
- `walk_sound b rf p` — induction: from an agreeing state, an accepted
  suffix runs safely (composing `defterm_sound`).
- **`soundness p`:** *if `accepts p`, then `runx Total rf0 p` is `Some`* —
  **an accepted program provably runs to Exit with R0 initialized, i.e. it
  is safe, for ANY certificate.** Because `check_walk` rebuilds every
  definition term from the loaded instruction (never from certificate
  data), this is the machine-checked form of the anti-transplant guarantee.
- `demo1`, `demo2` + reject `assert_norm`s — **non-vacuity:** concrete
  programs the checker accepts, and unbound-register / no-R0 / no-Exit
  programs it rejects.
**Manual-review focus:** the `soundness` statement and the reject tests.

---

## What is deliberately *not yet* proved (staged, documented)

- Strict-mode safety **obligations** (div≠0, shift<width discharged by
  `Ebpf.Proof`) and **claim reporting** are not yet folded into
  `check_walk`; the current `soundness` is for `Total` (kernel) semantics.
  The proof-rule soundness they need is already done in `Ebpf.Proof`.
- `defterm` covers the **W64 core** only. SDIV/SMOD (needs the
  sign-magnitude = truncated-division equivalence), all **ALU32** (the
  zero-extend wrapper), **MOVSX** and **byte swaps** return `None` from
  `defterm` — the checker rejects them rather than trusting them.
- No step here is `admit`ted. "Staged" means *absent*, not *assumed*.
