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

`make selftest` exercises the **anti-forge / anti-transplant** guarantees —
each line runs the *verified* `check_proof` on a bad certificate and shows it
returns `false`:
- an honest proof checked against a **false goal** (`≤41` for a value of 42);
- an honest proof **transplanted** onto a different program's binding;
- a **forged rule** with an unsatisfiable side condition (`42 ≤ 41`).

## Scope (v0-core prover)

The prover discharges **upper-bound claims** (`bvule`) over registers whose
value is built from `MOV / AND / OR-via-operands / ADD / SUB-free / MUL /
constants`, using the verified rules `UleRefl, AndLeL/R, MonoAdd, MonoMul,
UleConst, TransUle`. It does **not** yet prove claims about `DIV` (the
definition term is ITE-wrapped — needs the `ITE_F` + substitution rules) or
`SHIFT` (the amount is masked — needs an immediate-shift definition-term row
or a masked-shift bound rule). Those rules are staged in M2.1; the prover
reports such claims as "unsupported term shape", it never fabricates a proof.

Not yet done (M2.2 refinements): a binary certificate file format (currently
the proof is validated in-process and the bytecode is printed as hex);
richer claim kinds; full SMT-LIB formula parsing (the parser handles the
`(cmp rN const)` claim shape the demos use).
