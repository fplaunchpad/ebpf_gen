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

The directory holds one further artifact, `llm-draft.kspec`, which belongs to
the §9 drafting experiment rather than to the replay: it is a blinded model
draft of this same patch, committed exactly as written.

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
- **Itemized, at the finest granularity available.** K9 has two modes, both
  visible above. When a family exists but is incomplete it reports at
  **instance** granularity — it does not say "`alu` is incomplete", it names
  the eight missing `(width, op, operand-form)` points, so a forgotten
  `(W32, imm)` form is a listed hole rather than an invisible omission. When
  *no* family claims a constructor at all there are no instances to name, so
  it reports at **constructor** granularity (`in AST, not in spec: MovSX`) —
  which is stage 2's diagnostic.
- **A worklist that terminates.** Each diagnostic is actionable in isolation,
  and acting on the last one produces a spec that passes all nine checks. The
  ISA change is not "a diff to review" but "a queue to drain".

**Pinned as a regression test.** `spec/tests/run.sh` gained a drift section
asserting that each fixture is *rejected*, with a `[K1]`/`[K9]` tag, a
`file:line:col` position, and the exact directional lines — pinned per file via
`# EXPECT:` / `# EXPECT-ALSO:` headers, the same convention as `tests/neg/`.
The fixtures are asserted **as failing**, so they cannot block the green path.
`make -C spec test` is 26 assertions, up from 21.

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

**The version stamp makes regeneration auditable.** Every generated region
opens with `(* spec ebpf_alu v<N>, host little-endian *)`, which is why stage 0
carries `version 0`. Emitting a copy of the live spec with `version 1` changed
to `version 2` — a **one-line** spec edit — rewrites that stamp in **all five**
generated regions across both files and changes nothing else. So the generated
text always names the spec revision it came from, and a region left behind by a
partial promote is visible by inspection.

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
8. **The §9 drafting experiment is blinded by prompt construction, not by
   sandboxing**, and it measures DSL translation of a supplied change, not ISA
   derivation. Its pass is weak evidence by construction; §9 says why, and
   lists the behavioural evidence that the answer was not read.

---

## 8. Reproducing

```sh
make -C spec build
cd spec                      # the quoted diagnostics use spec-relative paths

# the four detector diagnostics, in order
for f in experiments/pre-cpuv4/ebpf_alu.kspec \
         experiments/pre-cpuv4/stage1-enums.kspec \
         experiments/pre-cpuv4/stage2-alu-rows.kspec \
         experiments/pre-cpuv4/stage3-movsx.kspec; do
  ./specgen/_build/default/bin/specgen.exe check "$f"
done

# the spec patch and its size (the banner is delimited by a marker line, so
# this does not depend on the banner's length)
sed '1,/^# --- everything below this line/d' \
    experiments/pre-cpuv4/ebpf_alu.kspec | sed '/./,$!d' > /tmp/pre.kspec
wc -l /tmp/pre.kspec        # 119
diff -u /tmp/pre.kspec ebpf_alu.kspec

# fidelity: regenerating from the patched spec reproduces the committed F*
make -C spec emit
diff -u ../fstar/Ebpf.Semantics.fst out/Ebpf.Semantics.fst
diff -u ../fstar/Ebpf.Serialize.fst out/Ebpf.Serialize.fst

# everything, including the drift regression assertions (26 assertions)
make -C spec test

# the section 9 drafting experiment: the draft as written is rejected by K1,
# and after the two one-line fixes the diagnostics name it passes 9/9
./specgen/_build/default/bin/specgen.exe check experiments/pre-cpuv4/llm-draft.kspec
cp experiments/pre-cpuv4/llm-draft.kspec /tmp/g.kspec
sed -i 's/^enum alu_op.*/enum alu_op    { ADD ; SUB ; MUL ; DIV ; SDIV ; MOD ; SMOD ; AND ; OR ; XOR ; LSH ; RSH ; ARSH }/' /tmp/g.kspec
./specgen/_build/default/bin/specgen.exe check /tmp/g.kspec        # now K5
sed -i 's/if sval n s = 0 then 0 else/if s = 0 then 0 else/; s/if sval n s = 0 then d else/if s = 0 then d else/' /tmp/g.kspec
./specgen/_build/default/bin/specgen.exe check /tmp/g.kspec        # 9/9
```

The OCaml and F* toolchains live in the `test-clone` VM; see `spec/DESIGN.md`
§4 for the `multipass` invocations.

---

## 9. Stretch — can a model draft the spec patch?

### Protocol, and the exact limits of the blinding

A fresh agent, with no access to this conversation, received **only**:

1. a condensation of the KeelSpec grammar (`DESIGN.md` §2.4–2.6: the header
   keyword table, the table rules, the complete combinator table, and the
   checker rules it had to satisfy);
2. the full text of the **pre-cpuv4** spec — stage 0 with its banner stripped,
   because that banner names the four removals and would have handed over the
   answer;
3. a paraphrase, from memory and marked as such, of RFC 9669's descriptions of
   the cpuv4 instructions.

It was instructed to read no repository file and to answer from the prompt
alone. It reported making exactly one tool call — a `Write` of its answer —
and its draft is committed verbatim at
`spec/experiments/pre-cpuv4/llm-draft.kspec`.

**Blinding was by prompt construction and instruction, not by sandboxing:**
`spec/ebpf_alu.kspec` was present on the same filesystem. The evidence that it
was not read is behavioural, and it is what a reader should weigh:

- the `exclude` reason string — free text, not derivable from anything supplied
  — is worded entirely differently;
- the draft **appends** `SDIV`/`SMOD` to the end of `alu_op`; the real file
  interleaves them after `DIV`/`MOD`;
- the draft's MOVSX `sem` reads `src@64`; the real file reads `src@n`;
- the draft contains a divisor-guard error the real file does not have.

Two strings do coincide (`13 ops x {W32,W64} x {reg,imm} = 52 instances` and
`sext f n s`), and both are derivable from what was supplied: the pre-cpuv4
file said `11 ops ... = 44 instances`, and 11 + 2 = 13, 13 × 2 × 2 = 52; the
combinator table gives `sext F N e` and the grammar example names the width
variables `n` and `f`.

**What this measures, stated precisely.** The prompt handed over the enum case
*names*, the `MovSX` constructor signature, "truncates toward zero" sitting
next to a `trunc_div` combinator in the table, the exact BSWAP encoding, and
the substance of the `(W32, SX32)` exclusion. So this measures **DSL
translation of a well-specified change**, not ISA derivation from primary
sources. Grade it asymmetrically: a pass is **weak** evidence, because most of
the content was supplied; a failure would have been **strong** evidence, because
it would mean the change could not be translated even when handed to it.

### Result

| state | `specgen check` |
|---|---|
| as drafted | **rejected** — `[K1] enum` `alu_op` `lists the right cases in the wrong order` |
| after fix 1 (one line) | **rejected** — `[K5]` `` `trunc_div` needs a non-zero divisor, but `sval n (s)` may be zero here `` |
| after fix 2 (one line) | **accepted** — 9/9 checks, 72 instances, `alu 52, neg 2, mov 4, movsx 5 (+1 excluded), swap 9` — identical counts to the real spec |

### The two errors, and which check caught each — this is the finding

1. **Enum case order** → **K1**, which printed both lists side by side. The
   draft's stated reasoning was *"the true F* order is unknowable from the
   prompt; appending is the minimal-diff convention for extending a datatype."*
   Sound reasoning, wrong answer, caught unambiguously with the fix displayed.
2. **Divisor guard** → **K5**, with a caret on the offending subterm. The draft
   wrote `if sval n s = 0 then 0 else wrap n (trunc_div (sval n d) (sval n s))`,
   reasoning that guarding on the *exact divisor expression* matched the
   checker's stated rule most literally. It does not: K5's tracker records
   non-zeroness for a **variable**, and separately accepts `sval n <nonzero
   var>` as non-zero — so `if s = 0`, the real spec's form, is what passes.

Neither error is one a reviewer would reliably catch by reading a 143-line
table. Both were caught mechanically in 0.084 s, each with a diagnostic that
named the fix.

### The generated artifact

Emitting from the corrected draft and diffing against the committed F*:

- **every semantic arm is identical** — `alu_semn`'s SDIV/SMOD bodies,
  `movsx_off`, `op_off`, `swap_sem`'s `Bswap` arm, `alu_defined`'s guard set,
  `op_bits`' groupings;
- **ordering differs**: `alu_semn` and `alu_defined` list SDIV/SMOD last
  (match-arm order follows table row order, and the draft appended its rows),
  and `movsx_bits` is emitted after `swap_bits` (definition order follows enum
  declaration order). Cosmetic — a `match` over disjoint constructors;
- **one real divergence**: `movsx_semn (s: int{fits 64 s})` where the committed
  file has `(s: int{fits n s})`, caused by the draft reading `src@64` instead
  of `src@n`. It is semantically equivalent — `sext f n s` inspects only the
  low `f` bits — but it is a **weaker refinement type** than the hand-written
  model carries. The fidelity test flags it as a diff; a human decides. That is
  the pipeline behaving correctly: a defensible-but-different modelling choice
  surfaces as a reviewable difference rather than as silence.
- **re-verification: 10 of 16 modules pass, and the 11th did not finish.** The
  draft's generated files were dropped into a scratch copy of `fstar/` and
  `make verify` run cold. `Ebpf.Semantics` and `Ebpf.Serialize` — the two
  generated files themselves — verify, and so does everything downstream of
  them up to and including `Ebpf.Interval`, `Ebpf.Check` and **`Ebpf.Sound`**
  (the abstract-domain soundness layer of §5 (b2)). `Ebpf.Annot` — the
  certificate-checker bridge that holds the 85 manual lines of §5 (b1) — was
  still running after **23 minutes** against a 4–5 minute baseline, and was
  stopped there rather than left to run.

  Not diagnosed to root cause; two candidates, **both cosmetic in ISA terms**:
  (i) `alu_semn` is a plain (non-`unfold`) `let` referenced *by name* from
  `Ebpf.Annot`'s `--z3rlimit 600` case analyses, so permuting its match arms
  changes the SMT encoding that every one of those proofs sees; (ii) the
  weaker `movsx_semn` refinement adds a `fits 32 x ==> fits 64 x` obligation
  at each use site.

  **This is the most useful thing the stretch produced.** Two specifications
  can pass all nine meta-checks, generate arm-for-arm semantically identical
  F*, and still differ enough to destabilise a downstream SMT proof. It is why
  the fidelity gate is **byte identity** rather than semantic equivalence, and
  why `DESIGN.md` §5 makes `unfold let` vs plain `let` a binding rule rather
  than a style choice — the experiment walked straight into the hazard that
  rule exists to prevent. It also says something about the residue: category
  (b1) is not merely 85 lines of labour, it is 85 lines that are *brittle* to
  changes which are invisible at the spec level.

### What this licenses saying

With the ISA content supplied, a model produced a spec patch that was **two
checker-directed one-line fixes** away from a specification passing all nine
meta-checks and generating semantically correct F* — which then verified
through ten of sixteen modules before stalling the SMT-heaviest one. The
meta-checks, not a human reader, did the reviewing; and where the meta-checks
stopped being sufficient, the re-verification gate caught what was left. That
is the same claim the rest of this document makes, arrived at from the other
direction: **the review surface is small and mechanical, and the parts that are
not mechanical are exactly the parts this pilot does not claim to have
automated.**

---

## 10. What §5.5 can claim

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
