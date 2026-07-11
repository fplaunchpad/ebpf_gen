# Internal reference stats (M2.4)

Recorded for our own reference as the pipeline evolves — **not** a comparison
to BCF or VEP. Those systems handle far more (real programs, memory, control
flow); we are at a toy straight-line-ALU stage, so a head-to-head would be
meaningless. These numbers exist to track our own size/latency as we grow.

Measured on the 18-program DSL corpus (`ir/examples/corpus/`) via
`irc measure <file.kir>` (extracted verified checker, OCaml, VM `test-clone`).
Each program is a straight-line 64-bit ALU program with one upper-bound
(`bvule`) claim; the last four are deeply-nested "comprehensive" expressions.

| program | insns | proof steps | cert bytes† | check µs‡ | e2e µs§ |
|---------|------:|------------:|------------:|----------:|--------:|
| add        |  7 |  3 | 102 |   2.1 |  18.6 |
| sub        |  7 |  2 |  78 |   1.0 |  13.5 |
| mul        |  7 |  3 | 102 |   1.6 |  17.4 |
| div        |  7 |  3 | 176 |   1.5 |  13.3 |
| mod        |  7 |  2 |  78 |   1.3 |  18.1 |
| and        |  7 |  3 |  92 | 141.5 | 152.9 |
| or         |  7 |  2 |  78 | 140.5 | 291.7 |
| xor        |  7 |  2 |  78 | 139.8 | 290.7 |
| lsh        |  7 |  2 | 102 | 144.7 | 288.8 |
| rsh        |  7 |  2 | 102 | 145.4 | 291.9 |
| chain      |  9 |  5 | 156 | 142.5 | 158.6 |
| poly       |  9 |  7 | 316 |   3.0 |  17.1 |
| mask_add   |  7 |  5 | 156 | 283.7 | 292.6 |
| big        |  5 |  3 | 102 |   2.7 |  14.9 |
| nest_arith | 17 | 14 | 648 |   6.4 |  33.9 |
| nest_chain | 15 | 13 | 542 |   5.6 |  29.5 |
| nest_mask  | 15 |  2 | 262 | 146.3 | 313.0 |
| nest_bits  |  9 |  4 | 168 | 700.9 | 1047  |

Arithmetic-only aggregate (the rows without bitwise ops — the "clean" cost):
avg 6.4 proof steps, ~240 B cert, **~2 µs check**, **~20 µs end-to-end**.

## Column meanings and honest caveats

**proof steps** — rule applications per obligation. Small by construction
(SP-exact steps carry no proof; weakenings are a few domain-aware rules).
Arithmetic nesting scales it linearly (`nest_arith`/`nest_chain` at 13–14);
the bitwise ones collapse to a 2–4-step evaluation proof.

**† cert bytes — UPPER BOUND.** Self-contained recursive term/atom encoding
with **no node sharing**; the SPEC §8 shared-arena + delta format would be
smaller (terms repeated across steps are stored once). Ceiling, not optimum.

**‡ check µs — arithmetic vs bitwise split is an EXTRACTION ARTIFACT.**
Arithmetic proofs check in ~1–6 µs; bitwise ones (`and/or/xor/lsh/rsh` and any
expression containing them) in ~140–700 µs. The gap is entirely F* `ulib`'s
`UInt.logand`/`logor`/`logxor`/shift, which extract to a bit-vector *list*
implementation (O(64) allocation per call) in OCaml. In the kernel-destined C
checker these are single native instructions, so every row would be a few µs.
The arithmetic figures reflect the checker's true algorithmic cost.

**§ e2e µs — end-to-end** = parse `.kir` → verified `accepts` → synthesize
proofs → verified `check_proof` → serialize bytecode (i.e. from the emitted IR
to "verified + bytecode ready"). Arithmetic programs complete in ~13–34 µs.
The DSL → `.kir` step (extracted `Ebpf.Lower` + `Ebpf.Emit`) adds only a few µs
on top and is not re-run in this loop.

## Reproduce

```sh
# on test-clone (build VM)
cd ir/certifier && make build && ./_build/default/bin/bpfc.exe
for k in ../examples/corpus/*.kir; do ./_build/default/bin/irc.exe measure "$k"; done
# columns: name insns claims steps cert-bytes check-µs e2e-µs
```
