# Spec drift as the verifier evolves — the cpuv4 replay (MS5)

**What this measures.** The pilot claims that when the ISA evolves, maintaining
*one* spec source regenerates all artifacts coherently, and that the residual
manual work is small and measurable. This document replays a **real historical
ISA change** — cpuv4 (Linux 6.6, "ISA v4": signed division/modulo via `off=1`,
sign-extending `MOVSX`, unconditional `BSWAP`) — as a KeelSpec patch, and
measures every side of it: what the maintainer writes, what the pipeline
regenerates, what stays hand-written, and how long the loop takes.

Everything below is reproducible from `spec/experiments/pre-cpuv4/`; the
commands are in §8.

---

## 0. The boundary, stated up front

> **This experiment measures "the spec lags the AST", not "the spec lags the
> kernel".**

`specgen`'s K1 conformance check validates the `.kspec` against a reference
table of `Ebpf.Ast` constructors and enum cases that is **compiled into the
generator** (`spec/specgen/lib/astref.ml`). A maintainer adopting cpuv4 must
hand-edit that table — 4 new lines and 4 modified lines (§5, category (d)) —
*before* K1 or K9 can say anything at all. The detector fires because the AST
moved ahead of the spec; nothing in this pipeline reads a kernel header, an
RFC, or a `bpf.h`.

The mitigation, which is real but partial: `make -C spec test` runs
`specgen astcheck fstar/Ebpf.Ast.fst`, which re-extracts the constructor and
case names straight from the F* source and diffs them against the table
directionally. A stale table is therefore a **loud test failure**, not a silent
wrong answer — the hand edit cannot be skipped unnoticed, only performed. (See
`spec/DESIGN.md` §7, which already flags `astref.ml` as the one place
`specgen`'s own knowledge is load-bearing.)

*Future work, noted and not built:* K1's compiled-in table could be **derived**
from the `astcheck` extraction rather than duplicated by hand, which would take
the hand edit out of the loop entirely and make the detector fire on an
`Ebpf.Ast` edit alone.

---

## 1. Experiment design

The replay runs **backwards then forwards**: reconstruct the spec as it would
have read before cpuv4, show the drift detector firing against the *current*
`Ebpf.Ast`, then apply the change and confirm the artifacts regenerate
byte-identically to what is committed.

`spec/experiments/pre-cpuv4/` holds four fixtures, every one of them an
**expected-fail** artifact:

| file | state | `specgen check` says |
|---|---|---|
| `ebpf_alu.kspec` | stage 0 — the reconstructed pre-cpuv4 spec, `version 0` | `[K1]` `alu_op` disagrees with `Ebpf.Ast` |
| `stage1-enums.kspec` | + the three argument domains updated from `Ebpf.Ast` | `[K9]` family `alu` not exhaustive |
| `stage2-alu-rows.kspec` | + the `SDIV`/`SMOD` rows and the per-row `off` column | `[K9]` no family specifies `MovSX` |
| `stage3-movsx.kspec` | + the whole `movsx` family | `[K9]` family `swap` not exhaustive |

Applying the last diagnostic — the `Bswap` row — yields the live
`spec/ebpf_alu.kspec`.

**Why stages.** `specgen check` reports the first error and stops, so a single
pre-cpuv4 file yields a single diagnostic. Staging is also what exercises K9 at
all: K1 (enum conformance) runs before families are elaborated, so K9's
instance-level output only becomes reachable once the enums are complete. The
sequence is exactly the loop a maintainer runs — *update the argument domains
from the AST, then let the checker enumerate the rows you still owe it.*

**Stage 0's four removals**, relative to the live spec:

1. `alu_op` cases `SDIV`, `SMOD`;
2. the `alu` family's per-row `off` **column** — pre-cpuv4 every ALU op has
   `off = 0`, so `off` is a family constant (`enc ... off = 0`);
3. the whole `movsx` family and the `movsx_sz` enum;
4. `swap_kind` case `Bswap` and the `swap` table's `Bswap` row. `ToLE`/`ToBE`
   are classic `BPF_END` and stay — only the unconditional `BSWAP` (class
   `BPF_ALU64`, source bit 0) is cpuv4.

**What stage 0 is not.** It is a reconstruction, not a historical checkout.
This project's spec was authored after cpuv4 existed; there is no pre-cpuv4
`.kspec` in the history to check out. Two consequences are disclosed rather
than smoothed over:

- the `cite RFC 9669` lines are kept **unchanged** in stage 0, which is
  anachronistic (RFC 9669 postdates cpuv4). Holding the citation *style* fixed
  means the measured patch contains cpuv4 content only, not a re-citation pass.
  The `isa` string is the one citation that does move, because moving it is
  genuine cpuv4 content.
- the reconstruction is a **judgement call with a measurable cost**; §3 reports
  the patch under both plausible choices.

---

## 2. The detector, verbatim

Run against the **current** `fstar/Ebpf.Ast.fst`. This is the output the
experiment exists to produce.

```
experiments/pre-cpuv4/ebpf_alu.kspec:54:6: error: [K1] enum `alu_op` disagrees with Ebpf.Ast type `alu_op`:
       in spec, not in AST: (none)
       in AST, not in spec: SDIV, SMOD
   54 | enum alu_op    { ADD ; SUB ; MUL ; DIV ; MOD ; AND ; OR ; XOR ; LSH ; RSH ; ARSH }
             ^

experiments/pre-cpuv4/stage1-enums.kspec:42:8: error: [K9] family `alu` does not cover Ebpf.Ast constructor `Alu` exhaustively:
       in AST, not in spec: Alu(W32,SDIV,reg), Alu(W32,SDIV,imm), Alu(W32,SMOD,reg), Alu(W32,SMOD,imm), Alu(W64,SDIV,reg), Alu(W64,SDIV,imm), Alu(W64,SMOD,reg), Alu(W64,SMOD,imm)
       in spec, not in AST: (none)
   42 | family alu {
               ^

experiments/pre-cpuv4/stage2-alu-rows.kspec:16:1: error: [K9] no family specifies Ebpf.Ast constructor `MovSX`:
       in AST, not in spec: MovSX
   16 | spec ebpf_alu {
        ^

experiments/pre-cpuv4/stage3-movsx.kspec:125:8: error: [K9] family `swap` does not cover Ebpf.Ast constructor `Swap` exhaustively:
       in AST, not in spec: Swap(Bswap,SW16), Swap(Bswap,SW32), Swap(Bswap,SW64)
       in spec, not in AST: (none)
  125 | family swap {
               ^
```

Three properties of this output are the point:

- **Directional.** Every diagnostic reports both `in AST, not in spec` and
  `in spec, not in AST`, so a spec that is *ahead* of the model is as visible
  as one that is behind. K1 and K9 were built this way for this experiment
  (`DESIGN.md` §4).
- **Itemized at instance granularity.** K9 does not say "`alu` is incomplete";
  it names the eight missing `(width, op, operand-form)` points. A forgotten
  `(W32, imm)` form is a listed hole, not an invisible omission.
- **A worklist that terminates.** Each diagnostic is actionable in isolation,
  and acting on the last one produces a spec that passes all nine checks. The
  ISA change is not "a diff to review" but "a queue to drain".

**Pinned as a regression test.** `spec/tests/run.sh` gained a drift section
asserting that each fixture is *rejected*, with a `[K1]`/`[K9]` tag, a
`file:line:col` position, and the exact directional lines — pinned per file via
`# EXPECT:` / `# EXPECT-ALSO:` headers, the same convention as `tests/neg/`.
The fixtures are asserted **as failing**, so they cannot block the green path.
`make -C spec test` is 25 assertions, up from 21.

---

## 3. What the maintainer writes — the spec patch

`diff -u` from stage 0 (banner stripped) to the live `spec/ebpf_alu.kspec`:
**+49 / −25 lines**, 119 → 143.

| bucket | added | what it is |
|---|---|---|
| **genuinely new spec content** | **16** | `movsx_sz` enum (1), `SDIV` row (1), `SMOD` row (1), the `movsx` family block (12), the `Bswap` row (1) |
| **structurally forced** | **5** | `alu_op` and `swap_kind` case lists; the `alu` family's `enc`, `cols`, `cite` |
| spec-header bookkeeping | 3 | `version`, `isa`, the `host` trailing comment |
| pure realignment | 11 | the 11 pre-existing ALU rows re-piped to carry the new `off` column |
| comments / blank | 14 | family header comments, instance counts, the doc-comment artifact list |
| **total** | **49** | (removed side: 19 content + 6 comment = 25) |

> **Headline: 21 lines of real authoring** (16 new + 5 structurally forced).

**Both reconstructions, since the choice is mine.** Stage 0 gives the `alu`
family a family-constant `enc ... off = 0`, because that is what a pre-cpuv4
maintainer would write when every row's `off` is 0. That choice *costs the
patch more*: cpuv4 forces `off` out of `enc` and into a per-row column, which
re-pipes all 11 existing rows. Had stage 0 instead carried an all-zero `off`
column, the `enc`/`cols` lines would be unchanged context and the 11 rows would
not move:

| reconstruction | raw diff | authoring lines |
|---|---|---|
| family-constant `off` (**chosen**, stage 0 as committed) | +49 / −25 | **21** |
| all-zero `off` column (alternative) | +36 / −12 | **19** |

Both are reported so a reader can pick. The chosen one is the more expensive of
the two; the 11 realignment lines are a separable bucket in the table above, so
neither inflation nor deflation is hidden.

---

## 4. What the pipeline regenerates

Regenerating from the patched (= live) spec reproduces the committed F*
**byte for byte** — `specgen emit` followed by `make -C spec promote` leaves
`fstar/Ebpf.Semantics.fst` and `fstar/Ebpf.Serialize.fst` with unchanged MD5s.
That is the fidelity property, and it is asserted on every `make -C spec test`
run.

cpuv4-attributable generated lines, all inside `BEGIN/END GENERATED` regions:

| file | region | what | new | mod |
|---|---|---|---|---|
| `Ebpf.Semantics.fst` | `semantics-alu` | `alu_semn` arms `SDIV` (:68), `SMOD` (:70) | 2 | — |
| `Ebpf.Semantics.fst` | `semantics-tables` | `movsx_bits` (:89–93) | 6 | — |
| `Ebpf.Semantics.fst` | `semantics-tables` | `swap_sem` arm `Bswap` (:106) | 1 | — |
| `Ebpf.Semantics.fst` | `semantics-tables` | `movsx_semn` (:114–116) | 4 | — |
| `Ebpf.Semantics.fst` | `semantics-defined` | `alu_defined` (:134) gains `SDIV`/`SMOD` | — | 1 |
| `Ebpf.Serialize.fst` | `serialize-opcode` | `op_bits` (:43, :44) gain `SDIV`/`SMOD` | — | 2 |
| `Ebpf.Serialize.fst` | `serialize-opcode` | `op_off` (:52–55) — **the whole function is new** | 5 | — |
| `Ebpf.Serialize.fst` | `serialize-fields` | `movsx_off` (:82–86) | 6 | — |
| | | **total** | **24** | **3** |

(Counts include the blank line each definition carries; line numbers are into
the files as committed.)

`op_off` deserves a note, because it is where the "one source" claim is
load-bearing in a way a reader can check: with a **family-constant** `off`, the
emitter generates no per-op offset function at all (`emit_fstar.ml`,
`enc_key_table` returns `None` unless every row supplies a literal `off`) —
which is exactly why the `neg` and `mov` families have no such function today.
cpuv4 turning `off` into a per-row column is therefore what brings `op_off`
into existence, *and* what forces the matching hand edit in `encode_insn`
(§5(d)). The semantics arm, the opcode table, the offset table and the encoder
call site all move together or the build breaks.

**Prose is not counted.** `specgen prose` lives on the unmerged branch
`ms3-prose-backend`, not on `main`. The prose backend consumes `s_instances` +
`f_cites` and would render the 8 new instances plus the `movsx` family section
without authoring; the amplification figure here therefore **understates** the
merged pipeline. Measured on merge.

**Limitation on this table.** The pre-cpuv4 spec *cannot be emitted* — K1/K9
reject it against the current `astref` table (§0) — so these 27 lines are
attributed by inspection of the committed regions, with line references given
above so each is checkable, rather than by diffing two emissions.

---

## 5. The residue — what stays hand-written

The denominator is the M2.1 "hole A" work: the four commits that bridged this
instruction fragment into `Ebpf.Annot`'s certificate-checker term language by
hand (`9042f97` SDIV/SMOD, `808b64e` MOVSX, `5738464` ALU32, `abeeaa2` byte
swaps). Two of those four are **not** cpuv4 work — ALU32 and `TO_LE`/`TO_BE`
are classic — so the accounting is per line, not per commit.

### (a) what the pipeline would have generated — 27 lines

The §4 table: 24 new + 3 modified lines of `Ebpf.Semantics.fst` and
`Ebpf.Serialize.fst` that were hand-written in four notations before KeelSpec
and are now projections of the `.kspec`.

Inside hole A itself this category is **2 lines**, and they are the interesting
two: `808b64e` tightened `movsx_bits` to `n:pos{n <= 32}` and `abeeaa2`
tightened `swap_bits` to `{16 \/ 32 \/ 64}`, both by hand, both to make a proof
go through. Both of those lines now live **inside a generated region** — the
pipeline took them over, refinement type and all.

### (b1) manual forever under the current design — 85 lines

Proof relating **two independent formalizations**: the generated value
semantics (`alu_semn`, `movsx_semn`, …) and the certificate checker's SMT-LIB
term language (`Ebpf.Formula`). This is the kernel-TCB bridge — it is what
makes a certificate mean something — and no spec DSL was ever going to generate
it.

| item | lines | where |
|---|---|---|
| SDIV/SMOD bridge lemmas — `negp_pos`, `negp_negp`, `quot_wrap`, `sdiv_equiv`, `srem_equiv` | 50 | `Ebpf.Annot.fst` 215–264 |
| MOVSX — `eval_extract_low` + `low_low` (12), `defterm_sound_movsx` (23) | 35 | `Ebpf.Annot.fst` 266–277, 296–318 |
| BSWAP | **0** | — |
| **total** | **85** | |

Two caveats belong on the same line as those numbers:

- `eval_extract_low` / `low_low` (12 of the 35) are **shared** — MOVSX needed
  them first, ALU32 and the byte swaps later reused them. MOVSX is 35 lines
  with them and 23 without.
- **BSWAP costs zero, and that is contingent on `host little-endian`.** In both
  `defterm` (`Ebpf.Annot.fst` 171–173) and `defterm_sound_swap` the `Bswap`
  cases are covered by the `| _, SW..` wildcard shared with `ToBE`, because on
  an LE host "convert to big-endian" and "unconditionally reverse" are the same
  function. On a big-endian host they diverge and BSWAP would cost its own
  term arm and its own proof. The spec's `host little-endian` pin is what makes
  the zero true, which is precisely why the pin is in the spec.

### (b2) abstract-domain soundness (certifier-side) — 23 lines

`Ebpf.Sound.fst` relates a **third** artifact: the userspace interval-inference
engine (`Ebpf.Check`'s transfer functions) to the semantics. This is the
certifier keeping its own inference sound; it is tooling-side, not kernel-trust
side, which is why it is a separate row.

| item | lines | where |
|---|---|---|
| `tf_movsx_sound` | 11 | `Ebpf.Sound.fst` 67–77 |
| step-soundness `MovSX` arm | 12 | `Ebpf.Sound.fst` 131–142 |

In deployment accounting: a cpuv4-like change costs the **kernel-checker** story
85 manual lines (b1); the other 23 are the certifier's own inference.

### (c) generatable by a later (MS6 / P4-style) extension — 29 lines

Structural, derivable from the spec's `sem`/`ctor`, and today hand-written:

| item | lines | where |
|---|---|---|
| SDIV/SMOD `defterm` term arms | 4 | `Ebpf.Annot.fst` 115–116, 142, 144 |
| SDIV/SMOD dispatcher arms | 4 | `Ebpf.Annot.fst` 479–480, 374–375 |
| MOVSX `defterm` term arm | 13 | `Ebpf.Annot.fst` 149–161 |
| MOVSX `wdst` + dispatcher | 2 | `Ebpf.Annot.fst` 181, 487 |
| `CertClaim` non-vacuity `assert_norm`s (SDIV, MOVSX, BSWAP) | 6 | `Ebpf.CertClaim.fst` |
| **total** | **29** | |

*Sensitivity:* the 6 dispatcher/`wdst` lines are a judgement call — they are
one-line delegations, but a reader who counts them as proof rather than
plumbing moves the split to **91 / 23** instead of 85 / 29. Saying so is what
makes the 85 credible.

### (d) hand-frame edits outside the generated regions — 37 lines

cpuv4-forced, and the pipeline does not touch any of it:

| file | sites | new | mod |
|---|---|---|---|
| `spec/specgen/lib/astref.ml` | `alu_op` / `movsx_sz` / `swap_kind` case lists, `MovSX` ctor | 4 | 4 |
| `fstar/Ebpf.Ast.fst` | `SDIV`/`SMOD`, `movsx_sz`, `MovSX`, `Bswap` | 2 | 3 |
| `fstar/Ebpf.Semantics.fst` | `stepx` `MovSX` arm (:158–165); module doc comment | 8 | 2 |
| `fstar/Ebpf.Serialize.fst` | `encode_insn` `MovSX` arm, `Bswap` arm, `Alu` arm `0` → `op_off op` (:99); module doc comment | 3 | 2 |
| `fstar/Ebpf.Check.fst` | `tf_movsx` (:86–87), `check` `MovSX` arm (:120–125), `tf_swap` `\| ToBE \| Bswap` | 8 | 1 |
| **total** | | **25** | **12** |

The `astref.ml` row is §0's boundary, in numbers.

### Totals

| | lines |
|---|---|
| spec authoring (the reviewed surface) | **21** |
| generated F* (a) | **27** |
| manual, kernel-TCB proof (b1) | **85** |
| manual, certifier-side proof (b2) | **23** |
| manual, generatable later (c) | **29** |
| manual, hand frame (d) | **37** |
| **manual total** | **174** |

The pipeline did not make 174 into 21. It moved 27 lines out of the manual
column *and made the four artifacts provably coherent*, which is the part that
was previously untested. What remains is dominated by proof relating
independent formalizations — irreducible by construction.

---

## 6. Wall time

Measured on the `test-clone` VM (4 cores), idle and strictly serial;
`pgrep -f "fstar|z3"` clean before and after.

| phase | time |
|---|---|
| `specgen check` (parse, elaborate, K1–K9 over 72 instances) | **0.084 s** |
| `specgen emit` + `make -C spec promote` | **0.089 s** |
| cold `make verify` (16 F* modules, empty `.cache`) | **8 m 09 s** |
| **regenerate-verify cycle** | **8 m 10 s** |

> The pipeline's own cost is **0.17 s of an 8 m 10 s cycle — 0.03 %**.
> Regeneration is free; **re-verification dominates, and re-verification is
> exactly the part you want to pay**, because it is the faithfulness check
> (`DESIGN.md` §7: the generator is untrusted precisely because F* re-checks
> everything it emits).

(Reference cold verify on this VM is 7 m 53 s; +3 % is idle-machine noise.)

---

## 7. Honest boundaries

1. **The detector needs a hand edit first.** §0. The experiment shows the spec
   lagging the AST, not the kernel.
2. **Stage 0 is a reconstruction**, not a historical checkout, and the
   reconstruction choice moves the patch count by 2 authoring lines / 13 raw
   lines. Both variants are reported (§3).
3. **Bridge lemmas are manual, permanently**, under this design (§5 b1). The
   85-line figure is for one ISA revision that touched three families.
4. **BSWAP's zero cost is LE-host-contingent** (§5 b1).
5. **Prose is not measured** — the backend is on an unmerged branch, so the
   amplification figure understates the merged pipeline (§4).
6. **The generated-line attribution is by inspection**, not by diffing two
   emissions, because the pre-cpuv4 spec cannot be emitted (§4). Line
   references are given so every line is checkable.
7. **The stage files are not textually one line from the live spec.** Stages
   1–3 carry a worklist banner instead of the file's doc comment and keep
   `version 0`; the measured patch is stage 0 → live, not stage 3 → live.

---

## 8. Reproducing

```sh
# the four detector diagnostics, in order
make -C spec build
for f in spec/experiments/pre-cpuv4/ebpf_alu.kspec \
         spec/experiments/pre-cpuv4/stage1-enums.kspec \
         spec/experiments/pre-cpuv4/stage2-alu-rows.kspec \
         spec/experiments/pre-cpuv4/stage3-movsx.kspec; do
  spec/specgen/_build/default/bin/specgen.exe check "$f"
done

# the spec patch and its size
sed -n '30,$p' spec/experiments/pre-cpuv4/ebpf_alu.kspec > /tmp/pre.kspec
diff -u /tmp/pre.kspec spec/ebpf_alu.kspec

# fidelity: regenerating from the patched spec reproduces the committed F*
make -C spec emit && diff -u fstar/Ebpf.Semantics.fst spec/out/Ebpf.Semantics.fst
                     diff -u fstar/Ebpf.Serialize.fst spec/out/Ebpf.Serialize.fst

# everything, including the drift regression assertions (25 assertions)
make -C spec test
```

The OCaml and F* toolchains live in the `test-clone` VM; see `spec/DESIGN.md`
§4 for the `multipass` invocations.

---

## 9. What §5.5 can claim

A maintainer — or a model — drafts a spec patch of **21 authored lines**. The
pipeline projects it into **27 lines of F*** across five generated regions in
two files, in **0.17 seconds**, and the projection is verified byte-identical
to what is committed. The trusted review surface is the 21-line spec diff plus
the regenerated diff, both small and both in one notation; before KeelSpec the
same change was four hand edits in four notations with nothing forcing them to
agree.

Omissions are not silent. K1 and K9 report **directionally and at instance
granularity**, turning an ISA revision into a worklist that terminates exactly
when the spec is complete — four diagnostics, in this replay, each naming the
instructions still owed.

What the pipeline does **not** remove is 108 lines of proof (85 kernel-TCB
bridge + 23 certifier-side) relating the generated semantics to two other
formalizations. That is the honest shape of the result: **the table-maintenance
cost is eliminated outright; the proof cost is not, and no spec DSL was ever
going to eliminate it.** A further 29 lines are structural plumbing that a
term-generating backend could plausibly take over (MS6), and 37 are hand frame,
8 of which are the `astref.ml` table that §0 is about.
