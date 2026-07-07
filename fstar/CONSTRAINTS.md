# Arithmetic (ALU) constraint transcription — eBPF → F*

Milestone 1 of the PCC-for-eBPF project: the constraints the eBPF ecosystem
imposes on arithmetic instructions, transcribed into a deep-embedded F*
checker (`Ebpf.Check.fst`) with a machine-checked soundness theorem
(`Ebpf.Sound.fst`) against an executable semantics (`Ebpf.Semantics.fst`).

**Pinned ground truth**: RFC 9669 (BPF ISA), Linux kernel 6.8 verifier
behavior, Veritas Dafny spec (`repos/veritas/ebpf-dafny-spec/spec.dfy`,
SOSP'25 artifact). Scope: straight-line programs, scalar-only register
file (pointers, jumps, memory are M2/M3).

## Modes

`Ebpf.Check.mode` mirrors the Veritas `enable_org` flag idea:

- **Kernel** (kernel-faithful): accept exactly what the Linux verifier
  accepts on this fragment. Register divisors that may be zero and
  register shift amounts ≥ width are *accepted* (the ISA defines the
  runtime behavior; the verifier havocs the result).
- **Strict** (clean-slate): additionally *prove* divisor ≠ 0 and shift
  amount < width. Formally: Strict-checked programs are safe under the
  **Defensive** semantics (`Ebpf.Semantics.semantics`), where div/0 and
  oversized shifts are stuck states — see `Ebpf.Sound.soundness`.

## Per-constraint transcription table

| # | Constraint | Source (spec.dfy unless noted) | Kernel 6.8 behavior | F* transcription | Mode |
|---|------------|-------------------------------|---------------------|------------------|------|
| C1 | dst register is never R10 | every ALU method: `requires dst.regNo != R10` | reject ("frame pointer is read only") | `check`: `if dst = R10 then None` | both |
| C2 | no read of uninitialized register | `type_check_single_src_operand` (:174), SP5 | reject ("!read_ok") | `tystate = reg → option (iv 64)`; `None` operand rejects | both |
| C3 | R10 not readable as scalar | scalar-only M1 restriction (kernel allows `mov r,r10` as ptr) | accept as pointer | `read` returns None for R10 — M1 scalarization, revisit M3 | both |
| C4 | immediate divisor 0 rejected | `Div*/Mod*_IMM`: `requires srcImm != 0` | reject ("div by zero") | `allowed`: `OpImm → b.ilo > 0` (exact interval ⇔ pattern ≠ 0) | both |
| C5 | register divisor may be 0: runtime x/0=0, x%0=x | `Div64_REG` (:975) ensures; RFC 9669 | accept, dst havoc | Kernel mode: accept + `tf_alu` havoc; semantics: `DIV → if s=0 then 0`, `MOD → if s=0 then d` | Kernel |
| C6 | register divisor provably ≠ 0 | clean-slate (our spec) | n/a (kernel never requires) | Strict mode: `allowed` requires `b.ilo > 0`; then `tf_alu` is *precise*: `[lo_a/hi_b, hi_a/lo_b]` | Strict |
| C7 | immediate shift ≥ width rejected | `Bv*_IMM`: `requires srcImm < 32/64` | reject ("invalid shift") | `allowed`: `OpImm → b.ihi < bits w` (also rejects negative imm via pattern) | both |
| C8 | register shift amount: kernel masks (s % width) | RFC 9669; kernel havocs result | accept, dst havoc | Kernel mode: accept; semantics masks `s % n` | Kernel |
| C9 | register shift provably < width | spec.dfy `requires src.regVal < 64` (stricter than kernel!) | n/a | Strict mode: `b.ihi < bits w` | Strict |
| C10 | ALU32 zero-extends result to 64 bits | spec.dfy header (:13); RFC 9669 | value tracking via u32 bounds | `res64 W32` = fits-32 value stored in u64; `narrow32`/`widen32` on intervals | both |
| C11 | ALU64 immediate sign-extended 32→64 | `signExtend32To64` in Div/Mod_IMM; RFC 9669 general rule | ditto | `imm64 i = wrap 64 (I32.v i)` (Euclidean mod = sign extension) applied to ALL ALU64 imms | both |
| C12 | SDIV/SMOD: truncated division; INT64_MIN/-1 = INT64_MIN, smod → 0 | RFC 9669; kernel runtime patching | accept | `trunc_div`/`trunc_mod` + wrap (gives INT_MIN case for free); do NOT copy spec.dfy's `twocom2Abs` INT_MIN-as-zero-divisor quirk | both |
| C13 | MOVSX sign extension (8/16/32) | `Mov*SX*` (:305,:795); reg source only | accept | `MovSX` insn, `sext`; (W32,SX32) rejected as invalid encoding | both |
| C14 | byte swap TO_LE/TO_BE/BSWAP truncate to width | RFC 9669; LE host pinned | accept | `Swap` insn; `tf_swap` bounds to `2^width - 1` | both |
| C15 | R0 initialized at Exit | `return-code.dfy` | reject ("R0 !read_ok") | `check Exit`: `read ts R0` must be `Some` | both |
| C16 | `Assert_ r k`: claimed bound must be provable | our pseudo-instruction (erased at serialization) | n/a (not in bytecode) | `check`: `a.ihi <= k`; semantics: stuck if violated (so soundness covers it) | both |
| C17 | no unreachable code after Exit | kernel: unreachable insn reject | reject ("unreachable insn") | `check_prog`: `Exit :: _ :: _ → None` | both |

## Value-tracking domain

Kernel: tnum + u64/s64/u32/s32 ranges (5 domains). Veritas: exact bv64 or
full havoc. **Ours (M1): unsigned 64-bit intervals** (`Ebpf.Interval.iv`),
with per-op transfer functions proved sound against the semantics
(`tf_alu_sound`). Precise for: ADD/SUB/MUL (overflow-checked), AND (min
bound), DIV/MOD (divisor excludes 0), constant shifts, RSH (never grows),
MOVSX (value fits narrow width), TO_LE (value fits). Havoc (width-bounded)
for: OR/XOR, signed ops (SDIV/SMOD/ARSH), NEG, dynamic LSH, byte swaps.
Signed intervals and tnum-style bit tracking are sound extensions slotted
for M2 (needed for JSLT-style branch refinement anyway).

## Deliberate divergences from the artifacts

- spec.dfy `Add64_IMM` (:879) lacks the uninit-dst check — bug in the
  artifact, not copied (C2 applies uniformly here).
- spec.dfy `twocom2Abs32Bit` masks with `0xEFFF_FFFF` (typo) and makes
  SDIV/SMOD by INT64_MIN hit the zero-divisor branch — not copied (C12).
- spec.dfy requires *register* shift amounts < width unconditionally —
  stricter than the kernel; we put that in Strict mode only (C9).
- Kernel's tnum precision on AND/OR chains exceeds our M1 intervals in
  some cases (kernel-mode acceptance is not affected on this fragment,
  since acceptance never depends on precision for arithmetic-only
  programs — it will for memory access in M3).

## Kernel-faithfulness caveats (to validate in Phase 2)

1. Socket-filter programs on 6.8: R0 must be readable at exit — matches C15.
2. Kernel rejects `BPF_END` with invalid imm (not 16/32/64) — our AST
   makes this unrepresentable.
3. MOVSX (ISA v4) needs kernel ≥ 6.6 — OK on 6.8. SDIV/SMOD likewise.
4. Unprivileged (Spectre) constraints are OUT OF SCOPE — we compare
   against the verifier as root (CAP_BPF/CAP_SYS_ADMIN), matching the
   papers' punt on speculative safety.

## Differential results (Phase 2 — run 2026-07-07, kernel 6.8.0-134, root)

13 programs, generated by `Ebpf.Dump` → `harness/gen_manifest.py`, loaded
via `harness/loader.c` (BPF_PROG_LOAD, socket filter), compared by
`harness/diff.py`. **Zero divergences between F* kernel-faithful mode and
the real verifier.**

| program | F* Strict | F* Kernel | kernel 6.8 | exercises |
|---|---|---|---|---|
| ex_shift | accept | accept | accept | C7, C16; AND-min + RSH-const intervals |
| ex_div | accept | accept | accept | C6 (precise reg-div), C16 |
| ex_alu32 | accept | accept | accept | C10, C11; const-folded 32-bit wrap |
| ex_chain | accept | accept | accept | C6, C16; AND→ADD→DIV chain |
| ex_movsx | accept | accept | accept | C13 (precise when value fits) |
| ex_mul | accept | accept | accept | MUL overflow-checked interval |
| ex_div0_reg | **reject** | accept | accept | C5 vs C6 (the strict/kernel fork) |
| ex_shift_reg | **reject** | accept | accept | C8 vs C9 (the strict/kernel fork) |
| ex_uninit | reject | reject | reject | C2 |
| ex_no_r0 | reject | reject | reject | C15 |
| ex_r10_dst | reject | reject | reject | C1 |
| ex_imm_div0 | reject | reject | reject | C4 |
| ex_imm_shift64 | reject | reject | reject | C7 |

Verification status: all 8 modules + Dump verify under F* 2026.03.24 /
Z3 4.13.3; the soundness theorem (`Ebpf.Sound.soundness`) is
machine-checked with no admits.
