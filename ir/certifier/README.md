# `irc` — the Keel certifier (M2.2 prototype)

A userspace pipeline that turns an annotated `.kir` program into eBPF
bytecode plus a checked proof certificate. It is built *around the
F*-extracted verified code*: the parser and prover are untrusted, but every
safety-relevant decision is made by extracted verified functions.

```
.kir ──parse──▶ program + @assert claims        (untrusted: bin/irc.ml parser)
        │
        ├─▶ Ebpf_CertCheck.accepts               (VERIFIED: straight-line safety)
        │
        ├─▶ Ebpf_Annot.defterm  (build each register's binding term)
        │   └─▶ certifying prover ──▶ proof       (untrusted: bin/irc.ml `plan`)
        │        └─▶ Ebpf_Proof.check_proof        (VERIFIED: validates the proof)
        │
        └─▶ Ebpf_Serialize.serialize_hex           (VERIFIED: real bytecode)
```

The three `Ebpf_*` calls are extracted from the machine-checked F* modules
(`fstar/Ebpf.{CertCheck,Proof,Annot,Serialize}.fst`). A bug in the parser or
prover can only cause a *rejection* or a wrong-but-checked artifact — it
cannot make the verified checker bless an unsafe program or a false claim.

## Build & run

Needs the F* OCaml extraction first (produces `../../fstar/out/Ebpf_*.ml`):

```sh
cd ../../fstar && make extract          # extract verified modules to OCaml
cd ../ir/certifier && make build        # copy them in + dune build
make run F=../examples/mul.kir          # certify a program
make selftest                           # adversarial checks (see below)
```

## What the demos show

`../examples/*.kir` (all accepted by the verified checker; all emitted
bytecode loads on the real kernel 7.0):

| file | program | claim | proof |
|------|---------|-------|-------|
| `mul.kir` | `r1=6; r2=7; r1*=r2` | `r1 ≤ 42` | MonoMul (3 steps) |
| `add.kir` | `r1=100; r2=50; r1+=r2` | `r1 ≤ 150` | MonoAdd (3 steps) |
| `chain.kir` | `r1=10*20; r1&=0xff` | `r1 ≤ 200` | MonoMul→AndLeL→Trans (5 steps) |
| `div.kir` | `r1=100; r2=4; r1/=r2` | `r1 ≤ 25` | UleRefl→UgeConst→DivIteBound (3 steps) |
| `mod.kir` | `r1=1000; r2=7; r1%=r2` | `r1 ≤ 1000` | UleRefl→ModLe→Trans (3 steps) |

`make selftest` exercises the **anti-forge / anti-transplant** guarantees —
each line runs the *verified* `check_proof` on a bad certificate and shows it
returns `false`:
- an honest proof checked against a **false goal** (`≤41` for a value of 42);
- an honest proof **transplanted** onto a different program's binding;
- a **forged rule** with an unsatisfiable side condition (`42 ≤ 41`).

## Scope (v0-core prover)

The prover discharges **upper-bound claims** (`bvule`) over registers.
Structural (small, symbolic-ready) proofs for `AND / ADD / MUL / constants`
via `UleRefl, AndLeL/R, MonoAdd, MonoMul, TransUle`; **division** via the
fused `DivIteLe`/`DivIteBound` rules that match the ITE-wrapped definition
term directly (tight bound `dividend/divisor` when the divisor is a known
constant); **remainder** via `ModLe`. Anything else that is *ground* — shift,
`or`, `xor`, `sub`, `sdiv`, `neg` — is discharged by the universal
`EvalEq → EqUle → weaken` fallback (evaluate the term, bridge the equality to
a bound). All rules are machine-checked sound in `fstar/Ebpf.Proof.fst`; the
prover never fabricates a proof — a claim it cannot establish is reported.

The remaining genuinely-unsupported case is a claim about a **non-ground**
(symbolic) term, which cannot arise until v1 adds branches / inputs; for
those the structural and fused rules already apply, but the `EvalEq` fallback
does not.

Not yet done (M2.2 refinements): a binary certificate file format (currently
the proof is validated in-process and the bytecode is printed as hex);
claim kinds beyond `bvule`; full SMT-LIB formula parsing (the parser handles
the `(cmp rN const)` claim shape the demos use).
