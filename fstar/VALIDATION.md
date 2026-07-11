# Validating our arithmetic domain + abstract operations against Agni / CGO

Cross-check of our F* eBPF model against the Rutgers verifier-verification
work: **Agni** (CAV 2023, `pubs/agni-cav2023.pdf` + `repos/agni`) and the
**tnum** paper (CGO 2022, `pubs/cgo-2022.pdf`). **NB — the local
`pubs/cgo-2022.pdf` is corrupt/truncated** (102 400 B of ~587 KB, no `%%EOF`,
only page 1 recoverable); the tnum facts in §6 are quoted from the authoritative
extended version **arXiv:2105.05398v3** (page-1 abstract byte-matches the local
file; identical technical content, adds appendices). Re-download the CGO
camera-ready if a local full copy is wanted. Agni verifies the *Linux
kernel's* abstract operators against concrete eBPF semantics for kernels
4.14–5.19; its artifact has per-version SMT encodings + a Python model of the
abstract domain (`lib_reg_bounds_tracking.py`) and the soundness checks.

Our pieces under review: `Ebpf.Semantics.alu_semn` (concrete ISA truth),
`Ebpf.Interval` (unsigned-interval abstract domain + `tf_alu` + the
machine-checked `tf_alu_sound`).

## Verdict

- **Abstract domain — correct.** Our unsigned interval is *exactly* the
  kernel's `u64` domain, with the identical concretization.
- **Soundness-claim form — correct, and the stronger one.** Our
  `tf_alu_sound` is Agni's canonical Eq. 1; we don't need Agni's weakening.
- **Concrete semantics of the range-tracked ops — match** Agni's concrete
  model (ADD/SUB/MUL/AND/OR/XOR/RSH/ARSH/LSH, ALU32 zero-extension), with one
  documented shift-masking difference where *we* match real hardware.
- **SDIV/SMOD/MOVSX/byteswap (Hole A) — Agni is not a reference** (out of its
  scope); validate against RFC 9669. Div/mod are not range-tracked by the
  kernel (havoc), so Agni doesn't check them either.

## 1. Abstract domain: ours = the kernel's `u64` domain

Agni's five domains are tnum (`value`,`mask`) + intervals over
{u64, s64, u32, s32} (10 integers in `bpf_reg_state`). Our domain is a single
unsigned 64-bit interval — i.e. **precisely the kernel's `u64` component**.
The concretization matches to the letter. Agni (paper):
`γ_u64([x,y]) = {z | x ≤_u64 z ≤_u64 y}`; Agni artifact
(`lib_reg_bounds_tracking.py`):
```python
def get_contains64_predicate_only_unsigned(self):
    return And(ULE(self.umin_value, self.conc64), ULE(self.conc64, self.umax_value))
```
which is exactly our `Ebpf.Interval.inb i x = i.ilo <= x && x <= i.ihi`.

**Consequence:** our domain is a sound *coarsening* of the kernel's — we keep
`u64` and drop tnum/s64/u32/s32. Sound, less precise. For arithmetic bounds
(ADD/SUB/MUL/DIV) the `u64` interval is the naturally precise domain; for
bitwise ops (AND/OR/XOR) tnum is more precise (see §5).

## 2. Soundness-claim form: ours is Agni's Eq. 1 (the strong, modular form)

Agni's core soundness property (binary): an abstract op `g` is sound iff
`∀ a₁ a₂. f(γ(a₁), γ(a₂)) ⊑ γ(g(a₁,a₂))` — "for all abstract inputs, the
concrete result lands in the concretization of the abstract output." Our
`tf_alu_sound` is exactly this: `inb a d ∧ inb b s ⟹ inb (tf_alu n op a b)
(alu_semn n op d s)`, ∀ intervals.

Crucially, Agni had to **weaken** this to `sro`-preconditioned / reachable
inputs (their Eq. 4) *only because the kernel fuses abstraction with a
cross-domain reduction (`reg_bounds_sync`) and is non-modular* — under the
clean Eq. 1 the kernel operators are reported unsound (latent violations).
Our per-op transfer functions are **modular** (each is independent, no
cross-domain reduction), so we prove the universal Eq. 1 directly and do
**not** need the reachability/`sro` machinery. Our soundness statement is the
stronger one, and it is machine-checked.

## 3. Concrete semantics of range-tracked ops — cross-check

From `lib_reg_bounds_tracking.py` (`set_concrete_operation`), Agni's concrete
model vs ours (`Ebpf.Semantics.alu_semn`):

| op | Agni concrete | ours (`alu_semn`) | match |
|----|---------------|-------------------|-------|
| ADD/SUB/MUL | `dst ± dst`, `*` (wrapping bv) | `wrap n (d ± s)`, `wrap n (d*s)` | ✅ |
| AND/OR/XOR | bv `& \| ^` | `UInt.logand/logor/logxor` | ✅ |
| RSH | `LShR(dst, src)` (logical) | `wrap n (d / pow2 (s mod n))` | ✅ (see shift note) |
| ARSH | `dst >> src` (arithmetic) | `wrap n (sval n d / pow2 (s mod n))` | ✅ (see shift note) |
| LSH | `dst << src` | `wrap n (d * pow2 (s mod n))` | ✅ (see shift note) |
| **ALU32 (any)** | `conc32 = Extract(31,0,...)`, op on 32 bits, **`conc64 = ZeroExt(32, conc32)`** | `regbits W32 = low 32`, op at width 32, **`res64 W32` zero-extends** | ✅ |

**ALU32 zero-extension is confirmed identical** — the historically bug-prone
part (CVE-2021-3490 etc.) — good, since Hole A's ALU32 bridge depends on it.

**Shift-masking difference (the one divergence, and we are the faithful one):**
Agni's concrete shift is the *raw* SMT-LIB/Z3 shift (`dst << src`,
`LShR(dst,src)`), which **saturates to 0 when `src ≥ width`**. Our `alu_semn`
**masks** the amount (`s mod n`, i.e. `s & (n-1)`), so e.g. `d << 64` gives
`d`, not `0`. Real hardware (x86 `shl`, ARM `lsl`) and the kernel interpreter
mask the count, and RFC 9669 takes the shift amount modulo the width — so
**our masked semantics is the ISA-/hardware-faithful one**; Agni's raw form is
a modeling simplification that is harmless for its purpose (the verifier only
tracks precise bounds for constant, in-range shift amounts and havocs the
rest, where masked ≡ raw). Our M2.3.4 corpus shifts (`3<<4`, `200>>2`) are
in-range, so they agree with both; the difference only shows for
`amount ≥ width`, where ours matches the real kernel.

## 4. Ops Agni does NOT cover → Hole A must lean on RFC 9669

Agni encodes 16 ALU ops but **excludes**: `MUL` from full verification
(64-bit bv-mul times out — verified only at 8-bit), and **`DIV, MOD` are not
range-tracked** by the kernel (it havocs the result), so their *concrete
semantics are irrelevant to Agni's checks*. `SDIV, SMOD, MOVSX, BSWAP/BPF_END`
are **entirely out of scope** (cpuv4, kernel ≥ 6.6, past Agni's 4.14–5.19
range). The paper writes out only `add64` concretely; everything else defers
to the eBPF ISA doc.

**Implication for Hole A** (`defterm`/`defterm_sound` for
SDIV/SMOD/ALU32/MOVSX/byteswap): Agni validates our **ALU32** concrete
semantics (§3, confirmed) but is **not** a reference for **SDIV/SMOD/MOVSX/
byteswap** — those must be validated against **RFC 9669** (already our pinned
ISA in `CONSTRAINTS.md`). In particular Hole A still needs, from RFC 9669:
- SDIV/SMOD are **truncated (toward-zero)** signed division, and
  `SDIV(INT_MIN, -1) = INT_MIN`, `SMOD(x, -1) = 0` (no trap). Our `alu_semn`
  uses `trunc_div`/`trunc_mod` on the signed interpretations with `x/0 = 0`,
  `x%0 = x` — consistent with RFC 9669; the F* bridge additionally needs the
  lemma `eval_sdiv (SMT-LIB sign-magnitude) = wrap (trunc_div sval sval)`.
- MOVSX sign-extends the low 8/16/32 bits; byteswap reverses bytes. Standard,
  but no external cross-check beyond the ISA.

## 5. Bug-class avoidance + precision (informative)

Agni's 27 bugs concentrate in **bitwise ops (esp. ALU32 AND/OR/XOR bounds:
CVE-2021-3490) and shifts (RSH truncation: CVE-2018-18445) and sign
handling** — precisely the places the kernel attempts *precise* range/tnum
tracking and gets it subtly wrong. Our `tf_alu` is deliberately
**conservative** there: it havocs OR/XOR and the signed ops (SDIV/SMOD/ARSH),
uses the simple `min` bound for AND, and havocs dynamic LSH. So we **avoid the
entire precision-bug class** by not attempting the tracking that produced
those CVEs — at the cost of precision, not soundness (and `tf_alu_sound`
proves the soundness).

**Precision (future):** for bitwise ops the kernel's **tnum** (known-bits)
domain is strictly more precise than our interval. Adopting tnum is a precision
upgrade orthogonal to the soundness validated here — §6 is the full reference.

## 6. Tnum domain (CGO 2022) — reference for a future bitwise-precision upgrade

The CGO 2022 paper ("Sound, Precise, and Fast Abstract Interpretation with
Tristate Numbers", Vishwanathan et al., Rutgers) is **not** a validation of our
*current* domain — we use unsigned intervals, not tnums. It is the precise
reference for a *future* tnum domain, which would buy bitwise (AND/OR/XOR) and
alignment precision that intervals structurally cannot express. Facts below are
verbatim from arXiv:2105.05398v3 (§/Eq numbers are the arXiv/CGO main-text
numbering).

**Representation + concretization (CONFIRMS the invariant we had recorded).**
A tnum is a pair `(P.v, P.m)` (value, mask); mask bit `1` = unknown trit `µ`,
`0` = known (Eq 3). Well-formedness is **`wellformed(P) ≜ P.v & P.m = 0`**
(Eq 10/17) — an ill-formed tnum is `⊥`/`∅` (Eq 4). Concretization is
**`γ(P) ≜ { c | c & ~P.m = P.v }`** (Eq 7), membership `member(x,P) ≜ x & ~P.m
= P.v` (Eq 9). Abstraction `α(C) ≜ (α&(C), α&(C) ⊕ α|(C))` (Eq 5) is bitwise
exact and forms a **Galois connection** with γ. So the two facts we had noted
are confirmed verbatim, including the `~P.m` negation in γ.

**Soundness / optimality obligation — mirrors ours.** An abstract op `opT` is
*sound* iff (Eq 11/18): `wellformed(P) ∧ wellformed(Q) ∧ member(x,P) ∧
member(y,Q) ∧ z = opC(x,y) ∧ R = opT(P,Q) ⟹ member(z,R)` — the same
"concrete result lands in the abstract output's concretization" shape as our
`tf_alu_sound` (and Agni Eq. 1). *Optimal* (maximally precise) is the stronger
`R = α(f(γ(P), γ(Q)))` (the smallest sound abstraction).

**What is proved optimal vs merely sound:**

| tnum op | result | scope |
|---------|--------|-------|
| `tnum_add` | **sound AND optimal** (Thm 6) | unbounded n, hand proof |
| `tnum_sub` | **sound AND optimal** (Lem 27) | unbounded n, hand proof |
| `our_mul` (their new mul) | **sound only — explicitly NOT optimal** (Thm 10) | unbounded n, hand proof |
| `&`, `\|`, shifts | sound (SMT to 64-bit); optimal per prior work [3,41] | no theorem here |
| `kern_mul` (kernel's old mul) | soundness proved **only to 8-bit** | times out >24 h at n=16 |

**The tnum_mul finding (the paper's headline).** The kernel's original
`kern_mul` could **not** be proved sound beyond 8 bits (non-linear + unrolled
loops make Z3 time out past n=16) — the paper does *not* claim it unsound, only
unverifiable at scale. Their replacement **`our_mul`** uses value-mask
decomposition (two accumulators, one final `tnum_add`), is **provably sound for
unbounded n**, is **more precise** (fewer additions: n+1 vs 2n; strictly more
precise on ~80% of the 8-trit cases where results differ, same result on
99.92% of all pairs), and **~33% faster** (≈262 vs ≈393 cycles on 40M random
64-bit pairs). **It is now merged into the Linux kernel.** Bounded verification
also surfaced that tnum add is non-associative, add/sub are not inverses, and
tnum mul is non-commutative — so operand order/count affects a multi-operand
tnum result's precision.

**Coverage gap to know before adopting tnum:** the paper gives explicit
algorithms only for add/sub/mul (Listings 1–6); **`tnum_and/or/xor` and the
shifts are only named** (verified sound by SMT, cited as already-optimal from
Regehr–Duongsaa [42] and LLVM known-bits [3,41]). So a tnum domain would take
those operators from the kernel / prior work, not from this paper. No
`tnum_intersect` appears.

**tnum vs interval — complementary, neither subsumes the other.** The paper
does **not** compare tnum to intervals or describe the kernel's tnum↔bounds
reconciliation (`reg_bounds_sync`) — do not cite it for those. What follows
from the definitions: tnum (non-relational, per-bit) is exact for bitwise
AND/OR/XOR and alignment/low-bit facts an interval cannot hold; intervals
capture ordered magnitude bounds and comparisons (ADD/SUB/MUL range
propagation) that tnum represents poorly (tnum add can blow up to all-`µ`).
Tnum outputs are frequently **incomparable** under the tnum order, so the
kernel keeps *both* and cross-refines — which is exactly why our single-`u64`
domain is a sound coarsening and a tnum layer would be an additive precision
gain, not a replacement.

**Verification method (the reference method — NOT Coq):** bounded automated
verification in **Z3, theory of fixed-size bitvectors**, VCs specialized per
bitwidth, loops unrolled + SSA; add/sub/bitwise verified sound at 64-bit "in a
few seconds", mul only to n=8. Unbounded soundness/optimality (add/sub/our_mul)
comes from **hand proofs** (carry/borrow lemmas, value-mask-decomposition
lemmas), not machine-checked. **Implication for us:** an F*-proved tnum domain
would give *unbounded, machine-checked* soundness/optimality directly —
strictly stronger than their bounded SMT (bitwise) and 8-bit mul result — using
the very obligation shape (`member`/`wellformed`) above.

## Bottom line

Our arithmetic **domain** and the **form** of our abstract-operation
soundness are validated as correct against Agni (indeed stronger, because our
domain is modular). Our **concrete semantics for the range-tracked ops** match
Agni's model, with shift-masking resolved in our favor (we match hardware).
The staged Hole A ops (SDIV/SMOD/MOVSX/byteswap) are outside Agni's scope and
remain anchored to RFC 9669 — no correctness surprise, but no external
cross-check either; the SDIV/SMOD F* bridge's difficulty (sign-magnitude =
truncated-division) is a proof-engineering matter, not a semantics gap.
