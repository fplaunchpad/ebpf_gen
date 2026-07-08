# Keel DSL — writing ALU eBPF in F* and running the whole pipeline

This is a small **high-level dialect** for writing arithmetic (ALU-only)
eBPF programs, far above the raw instruction/TAL level. You write ordinary
arithmetic expressions with the properties you want to hold; the toolchain
proves those properties against the eBPF safety constraints, emits a proof
certificate + bytecode, and the kernel-destined **verified checker**
validates the certificate. This doc shows how to author programs and run
them through the entire pipeline — the "mini-fuzzing" harness for M2.3.

Scope (v0): straight-line, 64-bit ALU only, constants `< 2^31`, upper-bound
(`bvule`) claims. Control flow, memory, and symbolic inputs come in later
milestones. Everything here is a *proof of concept* of the frontend →
certificate → verified-checker path, not the final surface language.

## The pipeline

```
 DSL program (Ebpf.Dsl)                          you write this
   │  Ebpf.Lower.lower        (verified-extracted) lower to instructions + regalloc
   │  Ebpf.Emit.emit_dsl      (verified-extracted) print Keel .kir text
   ▼
 .kir text
   │  irc  ── Ebpf_CertCheck.accepts   [VERIFIED] straight-line safety
   │      ── prover (untrusted)         synthesize a proof for each @assert
   │      ── Ebpf_Proof.check_proof     [VERIFIED] validate the proof
   │      ── Ebpf_Serialize.serialize   [VERIFIED] emit eBPF bytecode
   ▼
 bytecode ── loader ── BPF_PROG_LOAD    real kernel 7.0 accepts
                    ── BPF_PROG_TEST_RUN retval == Ebpf.Dsl.run (the oracle)
```

Only the steps marked **VERIFIED** are trusted; they call F*-extracted code
whose soundness is machine-checked (see `fstar/WALKTHROUGH.md`). The lowering
and the prover are untrusted — a bug there can only make certification *fail*
or produce a *rejected* certificate, never make an unsafe program accepted
(the checker validates the certificate against the emitted bytecode).

## Writing a program

Programs are `Ebpf.Dsl.prog` values — a list of statements ending in `Ret`:

```
type expr = Const u64 | Var id | Un unop expr | Bin binop expr expr
type stmt = Let id expr | Assert expr bound | Ret expr
```

Binary ops: `Add Sub Mul Div Mod And Or Xor Lsh Rsh Arsh`; unary: `Neg`.
`Let v e` binds variable `v` to `e`; `Assert (Var v) K` claims `v ≤ K` (the
refinement the certifier proves); `Ret e` returns `e` (into r0).

A worked example — `(6 * 7) ≤ 42`, returned:

```ocaml
[ letv 0 (c 6); letv 1 (c 7);
  letv 2 (bin D.Mul (var 0) (var 1));
  assrt 2 42;                 (* claim: r(var2) <= 42 *)
  D.Ret (var 2) ]
```

The certifier proves `6*7 ≤ 42` with the verified `MONO_MUL` rule (3 steps).
Claims about div/mod/shift/and/... are proved either by their dedicated
verified rules or by an exact-evaluation fallback — you never write a proof
by hand, and for this ALU fragment you never give the SMT solver a hint.

## Add your own program and test it

1. Add an entry to the `corpus` list in `ir/certifier/bin/bpfc.ml` (copy one
   of the existing shapes; helpers `letv`, `var`, `assrt`, `bin`, `c`).
2. Regenerate + build + certify (on the build VM, `test-clone`):
   ```sh
   cd fstar && make extract              # if you touched any .fst
   cd ../ir/certifier && make build
   ./_build/default/bin/bpfc.exe         # writes ../examples/corpus/*.kir + manifest.tsv
   ./_build/default/bin/irc.exe ../examples/corpus/<name>.kir   # certify one
   ```
   `irc` prints `[verified] accepts = true` and, per claim,
   `[verified] check_proof = true`, plus the bytecode.
3. Run it on the real kernel (on `kernel7`):
   ```sh
   cd harness && gcc -O2 -o loader loader.c
   cd ../ir/dsl && sudo python3 run_corpus.py ../examples/corpus/manifest.tsv ../../harness/loader
   ```
   This loads each program and `BPF_PROG_TEST_RUN`s it, checking the returned
   value equals the DSL evaluator's prediction (`Ebpf.Dsl.run`, truncated to
   the u32 retval). Expected output ends with
   `N/N loaded and computed the predicted result`.

## Current corpus (all certify, load, and compute correctly)

`bpfc` ships 14 programs exercising every ALU op: `mul add sub and or xor div
mod lsh rsh` plus nested/chained ones (`chain poly mask_add big`). The
manifest (`ir/examples/corpus/manifest.tsv`) records each program's bytecode
and expected result.

## Limits (documented, not hidden)

- 64-bit ALU only; ALU32/MOVSX/byte-swap are staged in the verified checker,
  so the lowering stays W64 (constants load via sign-extending `mov64`, hence
  `< 2^31`).
- Claims are upper bounds (`bvule`). Equalities / lower bounds / signed
  bounds are future rule additions.
- The prover is complete for *ground* programs (all values from constants).
  Symbolic inputs need only the structural rules (already present) but arise
  with control flow (next milestone).
- `Assert` is on a variable (`Assert (Var v) K`); bind a subexpression to a
  variable first if you want to assert about it.
