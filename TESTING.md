# How to test / reproduce what exists so far

Everything runs inside the multipass VMs. Two VMs are used:
- **`test-clone`** (Ubuntu 24.04, kernel 6.8) — has the F* toolchain
  (F* 2026.03.24 + Z3 4.13.3 via opam) and the OCaml/dune extraction stack.
  Used for all F* verification and extraction.
- **`kernel7`** (Ubuntu 26.04, kernel 7.0.0-27) — the differential-testing
  target (the "real verifier" we compare against). Root available.

The repo is mounted at `/home/ubuntu/ebpf_gen` in both. Edit on the host
(`/home/r41k0u/ebpf_gen`), run in the VM. Before any `fstar.exe` command:
```
multipass exec test-clone -- bash -c 'eval $(opam env --switch=default) && <cmd>'
```
(F* needs `z3-4.13.3` on PATH; the opam env + `/usr/local/bin/z3-4.13.3`
provide it. `opam env` is what makes `fstar.exe` resolve.)

---

## 1. Verify the F* development (the proofs)

This is the primary test: if it verifies, every theorem and refinement in
WALKTHROUGH.md holds. From a clean tree it takes a few minutes.

```
multipass exec test-clone -- bash -c \
  'cd /home/ubuntu/ebpf_gen/fstar && eval $(opam env --switch=default) && make verify'
```

Expect, for each of the 16 modules, `Verified module: Ebpf.X` and
`All verification conditions discharged successfully`, ending on
`Ebpf.Emit`. Module order:
`Ast Int Semantics Interval Check Sound Build Serialize Formula Proof Annot
CertCheck CertClaim Dsl Lower Emit`.

**A single module** (faster while reviewing one file):
```
multipass exec test-clone -- bash -c \
  'cd /home/ubuntu/ebpf_gen/fstar && eval $(opam env --switch=default) && \
   fstar.exe --cache_checked_modules --cache_dir .cache --odir out Ebpf.Proof.fst'
```

### How to convince yourself it's not vacuously passing

- **No admits/assumes.** Grep should return nothing:
  ```
  multipass exec test-clone -- bash -c \
    "grep -nE 'admit|assume|sorry' /home/ubuntu/ebpf_gen/fstar/*.fst"
  ```
- **Negative tests really fail to typecheck.** `Ebpf.Build.fst` has three
  `[@@expect_failure]` blocks (`bad_div`, `bad_assert`, `bad_uninit`). If
  you *delete* the `[@@expect_failure]` attribute on any of them and
  re-verify, F* must now report an error there — proving the checker
  actually rejects those programs (and that `expect_failure` isn't hiding a
  typo). Put it back afterwards.
- **Break a theorem on purpose.** e.g. in `Ebpf.Proof.fst`, change
  `R_DivLe`'s premise handling so it no longer requires `b ≠ 0`, and
  re-verify: `apply_sound` must fail. Or weaken a `MONO_*` no-overflow side
  condition. This confirms the soundness lemmas are load-bearing. `git
  checkout` to restore.
- **`assert_norm` acceptance/rejection.** `Ebpf.CertCheck.fst` (`demo1`,
  `demo2` accept; `[Exit]`, unbound-reg, no-Exit reject) and
  `Ebpf.Build.fst` (mode-divergence witnesses) are checked *at verification
  time* — they're already exercised by step 1. Flip an expected result to
  see it fail.

---

## 2. Differential test against the real kernel verifier

This checks that our M1 semantics/checker matches what the actual Linux
verifier accepts — the validation of the *trusted* `Ebpf.Semantics` model.

Regenerate the manifest from F* (only needed if you changed the programs;
the committed `harness/manifest.tsv` already has 13 entries):
```
multipass exec test-clone -- bash -c \
  'cd /home/ubuntu/ebpf_gen/fstar && eval $(opam env --switch=default) && \
   rm -f .cache/Ebpf.Dump.fst.checked && \
   fstar.exe --cache_checked_modules --cache_dir .cache --odir out Ebpf.Dump.fst \
   | python3 ../harness/gen_manifest.py > ../harness/manifest.tsv'
```
(`Ebpf.Dump` prints each demo program's serialized bytecode + its F* Strict
and Kernel verdicts; the `rm` forces the tactic to re-run since it's cached.)

Run the comparison on kernel 7.0:
```
multipass exec kernel7 -- bash -c \
  'cd /home/ubuntu/ebpf_gen/harness && make -s loader && sudo python3 diff.py manifest.tsv'
```
Expect a table of `F*strict | F*kernel | kernel` verdicts and the line
**`no divergences: F* kernel-faithful mode matches the real verifier`**.
`loader.c` does `BPF_PROG_LOAD` (socket-filter type) and reports ACCEPT or
`REJECT errno=..`; `diff.py` flags any row where our kernel-mode verdict
differs from the real one. The two mode-divergence witnesses (`ex_div0_reg`,
`ex_shift_reg`) are *designed* to show F*-Strict reject vs kernel accept —
that is not a divergence (different columns), it's the point.

`diff.py` compares only the accept/reject **verdict**. To also check that the
kernel **computes** what `Ebpf.Semantics` predicts (the SDIV/SMOD/MOVSX/byteswap
programs put their result in R0), run the value differential — it uses
`BPF_PROG_TEST_RUN` (`loader -r`) and compares each retval to the F*-derived
expectation (asserted in `Ebpf.Dump` as `r0lo exX == ..`):
```
multipass exec kernel7 -- bash -c \
  'cd /home/ubuntu/ebpf_gen/harness && make -s loader && sudo python3 valcheck.py manifest.tsv'
```
Expect every row `OK` and `all values match: real kernel computes what
Ebpf.Semantics predicts`.

You can also load any single program by hand to see the verifier log:
```
multipass exec kernel7 -- bash -c \
  'cd /home/ubuntu/ebpf_gen/harness && sudo ./loader <hex-from-manifest> -v'
```

---

## 3. Run the extracted checker natively (OCaml)

The F* modules extract to OCaml and run outside the proof assistant — this
is the seed of the future userspace certifier (M2.2).
```
multipass exec test-clone -- bash -c \
  'cd /home/ubuntu/ebpf_gen/fstar && eval $(opam env --switch=default) && \
   fstar.exe --cache_checked_modules --cache_dir .cache --odir out \
     --codegen OCaml --extract "Ebpf" Ebpf.CertCheck.fst && ls out/*.ml'
```
A prior run confirmed the extracted `Ebpf_Serialize`/`Ebpf_Check` compile
under dune (`-w -a` to silence F*'s projector warnings) and run — e.g.
serializing `mov64 r0,0; exit` yields `b700...9500...` and the Kernel-mode
checker returns `accept`. (Full dune wiring lands in M2.2.)

---

## 4. What each layer proves — quick map

| Test | Establishes |
|------|-------------|
| `make verify` (M1: Ast..Serialize) | M1 checker is sound vs the ISA model; C1–C17 encoded |
| `make verify` (M2: Formula..CertCheck) | annotation semantics well-defined; proof rules sound; terms track the machine; **accepted program ⇒ safe, for any certificate** |
| `diff.py` on kernel7 | the *trusted* semantics model matches the real 7.0 verifier on the corpus |
| `expect_failure` / break-a-proof | the results are non-vacuous |

See `fstar/WALKTHROUGH.md` §0 for what is *trusted* (must be reviewed by
eye) versus *proved* (machine-checked).
