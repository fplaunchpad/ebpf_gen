# Certificate-size and check-time measurements (M2.4)

Measured on the 14-program DSL corpus (`ir/examples/corpus/`), via
`irc measure <file.kir>` (extracted verified checker, OCaml, on VM
`test-clone`). Each program is a straight-line 64-bit ALU program with one
upper-bound (`bvule`) claim.

| program | insns | proof steps | cert bytes† | check µs‡ |
|---------|------:|------------:|------------:|----------:|
| add      | 7 | 3 | 102 | 2.0 |
| sub      | 7 | 2 |  78 | 1.6 |
| mul      | 7 | 3 | 102 | 1.3 |
| div      | 7 | 3 | 176 | 1.3 |
| mod      | 7 | 2 |  78 | 1.4 |
| and      | 7 | 3 |  92 | 140 |
| or       | 7 | 2 |  78 | 140 |
| xor      | 7 | 2 |  78 | 144 |
| lsh      | 7 | 2 | 102 | 141 |
| rsh      | 7 | 2 | 102 | 144 |
| chain    | 9 | 5 | 156 | 145 |
| poly     | 9 | 7 | 316 | 3.3 |
| mask_add | 7 | 5 | 156 | 284 |
| big      | 5 | 3 | 102 | 3.7 |
| **avg**  | — | **3.1** | **123** | — |
| **max**  | — | **7**   | **316** | 284 |

## What the numbers mean, honestly

**Proof steps (the clean metric).** 2–7 rule applications per obligation
(avg 3.1). This is the count comparable to VEP's proof-line counts, and to
BCF's step counts. It is small by construction: SP-exact instructions carry
no proof, and each weakening is a handful of domain-aware rules.

**† Certificate bytes — an UPPER BOUND.** This is a self-contained, recursive
term/atom encoding with **no node sharing**. The SPEC §8 format (a shared
expression-arena with u32 indices + delta-encoded annotations) would be
smaller, since terms repeated across steps (e.g. the `bvmul` node referenced
by several steps) are stored once. So 78–316 B is a conservative ceiling, not
the optimized size.

**‡ Check time — arithmetic vs bitwise split is an EXTRACTION ARTIFACT.**
The pure-arithmetic proofs check in **~1–4 µs**; the bitwise ones
(`and/or/xor/lsh/rsh` and the chains that contain them) in ~140–284 µs. The
difference is entirely F*'s `ulib` `UInt.logand`/`logor`/`logxor`/shift, which
extract to a **bit-vector list implementation** (O(64) allocation per call) in
OCaml. In the kernel-destined C checker these are single native instructions,
so all rows would be ~1 µs. The ~1–4 µs arithmetic figures reflect the
checker's true algorithmic cost; the bitwise figures do not.

## Context (order-of-magnitude, NOT apples-to-apples)

These are tiny straight-line ALU programs, not the real-world eBPF of the
BCF/VEP evaluations, so this is an indication for our current scope, not a
head-to-head benchmark:

- **BCF (SOSP'25)**: certificates avg **541 B** (range 136 B – 46 KB), check
  avg **~48 µs**. Ours: ~123 B upper-bound, ~1–4 µs (native-equivalent).
- **VEP (NSDI'25)**: **5,800 – 65,000 proof lines** for 63–618-LOC programs.
  Ours: **2–7 proof steps** per obligation.

The design intent these numbers support: TAL-style density with per-step
proofs kept tiny (SP-exact steps free, weakenings = a few domain-aware rules),
so per-obligation certificate cost stays sub-KB and check cost stays
microseconds. A like-for-like comparison on their benchmark programs awaits
scaling the IR to control flow and memory (later milestones).

## Reproduce

```sh
# on test-clone (build VM)
cd ir/certifier && make build && ./_build/default/bin/bpfc.exe
for k in ../examples/corpus/*.kir; do ./_build/default/bin/irc.exe measure "$k"; done
# columns: name  insns  claims  steps  cert-bytes  check-µs
```
