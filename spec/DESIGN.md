# KeelSpec — a mechanized specification language for the eBPF ISA fragment

**Status:** MS0/MS1 design note. `spec/ebpf_alu.kspec` is the spec source;
`spec/specgen/` is the (untrusted) parser + checker. Backends are later
milestones; this note fixes the *contracts* they consume.

---

## 0. The problem this solves

The project currently maintains the same instruction-level facts in four
places, by hand:

| fact | lives in |
|---|---|
| what an instruction computes | `fstar/Ebpf.Semantics.fst` (`alu_semn`, `swap_sem`, …) |
| when it is *defined* (strict mode) | `fstar/Ebpf.Semantics.fst` (`alu_defined`) |
| how it encodes | `fstar/Ebpf.Serialize.fst` (`cls`, `op_bits`, `op_off`, `movsx_off`, `swap_imm`) |
| what it means in English | `fstar/CONSTRAINTS.md`, `README.md`, `ir/SPEC.md` |

Nothing forces the four to agree. Adding an instruction means four edits in
four notations, and a mismatch (SDIV encoded with `off=0`; a prose table that
still says shifts trap) is silent. KeelSpec makes one source (`.kspec`) the
authority for all four and derives the rest.

The generator is deliberately **untrusted** (§7): its F* output is re-verified
by F* and differentially validated against the real kernel, so a wrong
generator produces code that fails `make verify` or `harness/diff.py` — never
a silent unsoundness.

## 1. Scope — what the spec says, and what stays hand-written

KeelSpec MS1 specifies, per instruction form:

1. the **encoding** — the opcode fields `(cls, opc, sbit, off, imm)` and which
   register/immediate operand fields the form uses;
2. the **value semantics** — a pure function of the already-read operand
   values, at a symbolic width, over a fixed combinator set (`Ebpf.Int` +
   `FStar.UInt`);
3. the **definedness** condition — the strict-mode precondition
   (`Ebpf.Semantics.alu_defined`);
4. the **validity** condition — which points of the form's axis product are
   real instructions at all (MOVSX `(W32, SX32)`).

It deliberately does **not** specify (these stay hand-written in
`Ebpf.Semantics.fst`, and are the *frame* the generated functions plug into):

- the register file and `option`-typed initialization tracking (`regfile`,
  `updr`);
- operand *reading*: `regbits` (register at width w) and `opbits`
  (`imm64`/`imm32` sign-extension rules). The spec names a read as
  `d = dst@n` / `s = src@n`, i.e. *which* role at *which* width, but the
  reading functions themselves are hand-written and trusted;
- the write-back rule `res64`. Note this is not a gap: a result of declared
  type `bits n` stored into a 64-bit register **is** the ALU32
  zero-extension rule (C10) — there is nothing left to state;
- `stepx` / `runx` dispatch, the `Total`/`Defensive` observation levels, and
  the pseudo/terminal instructions `Assert_` and `Exit` (not ISA
  instructions; `specgen` knows they must *not* be covered);
- everything about control flow and memory (v1/v2 — §9).

## 2. Source language

### 2.1 Lexical

ASCII only. `#` starts a comment that runs to end of line. Blocks are
`keyword name { … }` with `}` alone on a line. Inside a family, a line whose
first token is a family keyword is a **header line**; any other line
containing `|` is a **table row**. Blank lines are ignored. Every token
carries a `file:line:col` position; every diagnostic quotes one.

Integer literals are decimal or `0x…`. Identifiers are
`[A-Za-z_][A-Za-z0-9_]*`. Strings are `"…"` (no escapes needed so far).

### 2.2 Top level

```
spec  <name> { version <int> ; isa <string> ; host little-endian|big-endian }
enum  <name> { <case> [: attr…] ; … }
family <name> { <header lines> <table> }
```

`host` is load-bearing and recorded in the IL: the LE-host pin is what makes
`ToLE` a truncation rather than a byte reversal.

### 2.3 Enums

An `enum` is a finite argument domain of an `Ebpf.Ast` constructor. Each case
may carry attributes:

| attribute | meaning | consumed by |
|---|---|---|
| `bits=<n>` | the numeric width this case denotes | width vars; generates `movsx_bits` / `swap_bits` |
| `enc=<b>` | the byte this case contributes to the opcode | encoding fields (`cls = w`, `sbit = src`) |

The case *names* and their order must match `Ebpf.Ast` exactly (checked, §4
K1). `operand { reg ; imm }` is the `OpReg`/`OpImm` choice of the
`Ebpf.Ast.operand` type.

### 2.4 Family header keywords

A family binds exactly one `Ebpf.Ast` constructor.

| keyword | form | meaning |
|---|---|---|
| `ctor` | `Alu(w, op, dst:reg, src:operand)` | the AST constructor and its argument order; args are either declared axes or operand **roles** (`dst:reg`, `src:reg`, `src:operand`) |
| `key` | `op : alu_op` | the enum whose cases name the table rows; becomes the match scrutinee of the generated function. At most one; may be omitted (then the family has exactly one row, named by a free identifier) |
| `axis` | `w : width, src : operand` | further form axes; instances = key × product of axes |
| `width` | `n = bits w, f = bits sz` | bind a semantic width variable to the `bits` attribute of an axis (spelled exactly as F*'s `bits w` / `movsx_bits sz`) |
| `sem` | `(n; d = dst@n, s = src@n) : bits n` | the semantics signature: width params `;` value params (each with the role it reads and the width it reads at) `:` result type |
| `defined` | `(n; s)` | the definedness signature — a *subset* of `sem`'s params (this is what makes "`defined` references only operands [in its declared scope]" a scope check). Optional; default = width params only |
| `valid` | `f < n` | an intensional predicate over width vars saying which axis points are real instructions. Optional; default `true` |
| `exclude` | `w = W32, sz = SX32 "reason"` | an extensional exclusion, with a mandatory reason. Must agree exactly with `valid` (§4 K6) |
| `enc` | `cls = w, opc = 0x80, sbit = 0x00, off = 0` | encoding fields constant over the family (or derived from an axis / width var) |
| `cite` | free text | provenance for the prose backend. Repeatable |
| `cols` | `name \| opc \| off \| defined \| sem` | the table's column layout |

Within a header line, `,` separates items; one `exclude` line declares one
excluded instance.

An axis named the same as a `:operand` ctor role is the same object seen two
ways: as a role it says *what is read*, as an axis it says *reg or imm*, and
`enc sbit = src` reads the axis case's `enc` attribute. Every family in this
fragment writes exactly the `dst` register; the IL derives `writes = dst`
from the ctor's `dst:reg` argument (multi-write and no-write forms are a v1
extension point).

### 2.5 The table

Pipe-separated cells, `name` plus any of the encoding fields plus `defined`
and `sem`. Each encoding field must be given exactly once — either in `enc`
(family-constant) or as a column (per-row); both, or neither, is an error
(§4 K7). `-` in a cell means "none": in `defined` it elaborates to `true`,
matching `alu_defined`'s `| _ -> true`.

Encoding field values are: an integer literal, an axis reference (→ the
case's `enc` attribute), a width-var reference (→ its numeric value), or `*`
(operand-carried, the default for `imm`).

The five encoding fields reconstruct `Ebpf.Serialize` exactly —
`opcode = cls + opc + sbit`, plus `off` and `imm`:

| form | cls | opc | sbit | off | imm | `Ebpf.Serialize` line |
|---|---|---|---|---|---|---|
| `Alu w op dst src` | `w` | per-row | `src` | per-row | `*` | `op_bits op + src_bit src + cls w`, `op_off op` |
| `Neg w dst` | `w` | `0x80` | `0x00` | 0 | `*` | `0x80 + cls w` |
| `Mov w dst src` | `w` | `0xb0` | `src` | 0 | `*` | `0xb0 + src_bit src + cls w` |
| `MovSX w sz dst src` | `w` | `0xb0` | `0x08` | `f` | `*` | `0xb0 + 0x08 + cls w`, `movsx_off sz` |
| `Swap ToLE/ToBE/Bswap sz dst` | per-row | `0xd0` | per-row | 0 | `m` | `0xd0 + 0x04` / `0xd0 + 0x08 + 0x04` / `0xd0 + 0x07`, `swap_imm sz` |

### 2.6 The semantics expression language

The whole point of the expression language is that it is a **thin AST over
exactly the `Ebpf.Int` + `FStar.UInt` combinator set**, so MS2's codegen is a
1:1 pretty-print. There are no derived forms, no user-defined functions, no
let-bindings, and no combinators that do not already exist.

```
sem   ::= expr
expr  ::= INT
        | var                                  -- value var (d, s) or width var (n, f, m)
        | expr ('+'|'-'|'*'|'/'|'%') expr
        | comb warg* expr*                     -- combinator application
        | 'if' cond 'then' expr 'else' expr
        | '(' expr ')'
warg  ::= wexp                                 -- width argument (see below)
wexp  ::= INT | widthvar | wexp ('*'|'/'|'+'|'-') INT | '(' wexp ')'
cond  ::= expr ('='|'<>'|'<'|'<='|'>'|'>=') expr
        | cond '&&' cond | cond '||' cond | 'not' cond | 'true' | '(' cond ')'
```

Precedence: application binds tightest, then `* / %`, then `+ -`, then
comparisons, then `not`, `&&`, `||`; `if … then … else …` is lowest and
extends as far right as possible. `-` is binary only — F* writes `0 - d`, and
so does KeelSpec.

Combinators, with the F* they print to and their types
(`Int` = mathematical integer, `Bits W` = `x:int{fits W x}`;
`Bits W <: Int`):

| KeelSpec | F* | type | side condition |
|---|---|---|---|
| `wrap W e` | `Ebpf.Int.wrap W e` | `Int → Bits W` | — |
| `low W e` | `Ebpf.Int.low W e` | `Int → Bits W` | — |
| `sval W e` | `Ebpf.Int.sval W e` | `Bits W → Int` | — |
| `sext F N e` | `Ebpf.Int.sext F N e` | `Int → Bits N` | `F ≤ N` |
| `bswap NB e` | `Ebpf.Int.bswap NB e` | `Int → Bits (8·NB)` | `NB ≥ 1` |
| `pow2 e` | `Prims.pow2 e` | `Int → Int` | `e ≥ 0` |
| `trunc_div a b` | `Ebpf.Int.trunc_div a b` | `Int → Int → Int` | `b ≠ 0` |
| `trunc_mod a b` | `Ebpf.Int.trunc_mod a b` | `Int → Int → Int` | `b ≠ 0` |
| `logand W a b` | `FStar.UInt.logand #W a b` | `Bits W → Bits W → Bits W` | — |
| `logor W a b` | `FStar.UInt.logor #W a b` | ditto | — |
| `logxor W a b` | `FStar.UInt.logxor #W a b` | ditto | — |
| `a + b` `a - b` `a * b` `a / b` `a % b` | Prims | `Int → Int → Int` | `/`,`%`: `b ≠ 0` |
| `INT` | literal | `Int`, and `Bits W` when `0 ≤ k < 2^W` | — |

`FStar.UInt.logand` takes its width implicitly; KeelSpec makes it explicit
(`logand n d s`) so that every width in a `sem` cell is visible in the
source. That is the only notational difference from the F* text.

**Widths are finite.** Every width variable is bound to the `bits` attribute
of an axis over a declared enum, so it ranges over a finite, known set. The
checker therefore type-checks each *instance* with concrete widths, which is
complete — no symbolic width arithmetic, no solver. (Symbolic width-generic
emission, e.g. `alu_semn (n: pos)`, is then a proof obligation F* discharges;
see §5.)

## 3. The IL

Elaboration turns the source into this typed intermediate form. Everything a
backend needs is here; nothing else is. (OCaml, `spec/specgen/lib/il.ml`.)

```ocaml
type pos    = { file : string; line : int; col : int }
type wexp   = WLit of int | WVar of string | WBin of aop * wexp * wexp
type ty     = TInt | TBits of wexp
type comb   = Wrap | Low | Sval | Sext | Bswap | Pow2 | TruncDiv | TruncMod
            | Logand | Logor | Logxor
type expr   = ELit of int * pos
            | EVar of string * pos          (* value var *)
            | EWidth of wexp * pos          (* width var used as a value *)
            | EArith of aop * expr * expr * pos
            | EComb of comb * wexp list * expr list * pos
            | EIf of cond * expr * expr * pos
type cond   = CTrue | CCmp of cmp * expr * expr * pos
            | CAnd | COr | CNot                       (* … of cond *)

type role   = RDst | RSrcReg | RSrcOperand
type read   = { r_var : string; r_role : role; r_width : wexp }
type field  = FLit of int | FAny             (* `*` = operand-carried *)
type enc    = { cls : field; opc : field; sbit : field; off : field; imm : field }
(* how a field is SPELLED before instantiation (MS3 wants this, not just
   the resolved bytes) *)
type fieldsrc = FSLit of int | FSAny | FSAxis of string | FSWidth of string

type oblig  = ONonZero of expr * pos         (* a divisor is non-zero *)
            | ONonNeg  of expr * pos         (* a pow2 argument *)
            | OLe of wexp * wexp * pos       (* sext: source ≤ target width *)
            | ODivides of int * wexp * pos   (* bswap: 8 | result width *)

type argval = AEnum of string * string       (* enum name, case name *)
            | ARole of role
type ctorarg = CAAxis of string | CARole of role

type instance = {                             (* one real machine instruction *)
  i_id      : string;                         (* "alu/ADD/W32/reg" *)
  i_family  : string;
  i_ctor    : string;                         (* "Alu" *)
  i_args    : (string * argval) list;         (* ctor argument order *)
  i_enc     : enc;                            (* concrete except FAny *)
  i_opcode  : int;                            (* cls + opc + sbit, or -1 *)
  i_widths  : (string * int) list;            (* n=32 … concrete for this instance *)
  i_reads   : read list;
  i_result  : ty;
  i_sem     : expr;                           (* SYMBOLIC in width vars *)
  i_defined : cond;
  i_obligs  : oblig list;
  i_cites   : string list;
  i_pos     : pos;
}

type entry = {                                (* one table row = one key case *)
  e_name : string; e_key : string option;
  e_sem : expr; e_defined : cond;
  e_enc_row : (string * fieldsrc) list; e_pos : pos }

type semsig = { sg_widths : string list; sg_vals : read list; sg_result : ty }

type family = {
  f_name : string; f_ctor : string; f_ctor_args : ctorarg list;
  f_key : (string * string) option;           (* var, enum *)
  f_axes : (string * string) list;            (* non-key axes *)
  f_widths : (string * string) list;          (* width var  ←  axis *)
  f_sem : semsig;
  f_def_widths : string list; f_def_vals : string list;
  f_valid : cond;
  f_excludes : ((string * string) list * string) list;   (* binds, reason *)
  f_enc_family : (string * fieldsrc) list;
  f_cols : string list; f_entries : entry list; f_cites : string list;
  f_pos : pos }

type enum_case = { c_name : string; c_bits : int option; c_enc : int option }
type enum = { en_name : string; en_cases : enum_case list; en_pos : pos }

type spec = { s_name : string; s_version : int; s_isa : string;
              s_host : endianness;
              s_enums : enum list; s_families : family list;
              s_instances : instance list }   (* the flattened product *)
```

Two views, both needed:

- **`s_families`** — the *structured* view: a family + its key enum + one
  `sem`/`defined` per key case, symbolic in the width variables. This is what
  the F* backend prints (`alu_semn` is one `match` over the key enum).
- **`s_instances`** — the *flattened* view: 72 records, one per real machine
  instruction, with concrete widths and a fully resolved encoding. This is
  what the encoding backend, the prose backend, the overlap check, and the
  exhaustiveness check consume.

## 4. Elaboration and meta-checks

`specgen check spec/ebpf_alu.kspec` runs, in order, and reports the first
error with `file:line:col` (or a summary if all pass):

| id | check | rejects |
|---|---|---|
| **K1** AST conformance | every declared enum's case list (and order), and every `ctor`'s name/arity/argument kinds, match `specgen`'s built-in `Ebpf.Ast` reference table; `Assert_`/`Exit` are known-pseudo and must not be claimed. `specgen astcheck fstar/Ebpf.Ast.fst` re-extracts the real constructor names and diffs them against that table, so the table itself cannot drift silently | drift from `Ebpf.Ast`, in either direction |
| **K2** scope | every variable in `sem` is a declared width var or a `sem` value param; every variable in `defined` is in the `defined` signature (⊆ `sem`'s); `valid` mentions width vars only | dangling operand reference; `defined` reading `d` |
| **K3** combinator well-formedness | every applied name is in the combinator table with the right width-arg/value-arg arity | unknown combinator; wrong arity |
| **K4** well-widthedness | bidirectional type check of every instance's `sem` against its declared result type, with concrete widths | `logand 32 d s` on 64-bit operands; a literal that does not fit; branches of different width |
| **K5** side conditions | each instance's obligations are discharged syntactically where possible (`sext F ≤ N`, `pow2` arg non-negative, divisor non-zero under the enclosing path condition) and **recorded in the IL** for the F* backend either way | `sem` for DIV without the `s = 0` guard |
| **K6** validity ≡ exclusions | the instances failing `valid` are *exactly* the declared `exclude` set | a `valid` predicate and an `exclude` list that disagree |
| **K7** completeness | every family gives each of `cls/opc/sbit/off/imm` exactly once (family-level or column, never both, `imm` defaulting to `*`), plus `defined` and `sem` for every row; every row has every declared column | missing field; duplicated field |
| **K8** encoding disjointness | no two instances have *compatible* encoding keys `(cls, opc, sbit, off, imm)`, where `*` is compatible with anything | SDIV encoded with `off = 0` (would alias DIV); two forms sharing an opcode |
| **K9** exhaustiveness | for every constructor in the AST table, the covered instances ∪ the excluded points = the full product of its argument enums | a missing `ARSH` row; a forgotten `(W32, imm)` form |

K8 is deliberately stronger than "no duplicate `(class, op, off)` triple":
`*` (operand-carried `imm`) is treated as matching *any* literal, so an
overlap is reported whenever two forms *could* decode to the same bytes.

K9's product includes the `OpReg`/`OpImm` choice of an `operand` argument, so
a forgotten `(W32, imm)` form is a hole, not an invisible omission. Declared
exclusions count as covered — an exclusion is a load-bearing spec *claim*
("this form does not exist"), which is why one costs a `valid` predicate that
agrees with it (K6), a mandatory reason string, and (from MS4) a kernel
negative test.

Every diagnostic prints `file:line:col`, the offending source line, and a
caret. K1 and K9 report **directionally and itemized** —

```
[K9] family `alu` does not cover Ebpf.Ast constructor `Alu` exhaustively:
       in AST, not in spec: Alu(W32,ARSH,reg), Alu(W32,ARSH,imm), …
       in spec, not in AST: (none)
```

— because the MS5 drift experiment (replaying a pre-cpuv4 spec against the
current AST) makes K1/K9 fire *by design*: their output is that experiment's
measurement surface, not just a failure.

K9 prints the constructor list it validated against, e.g.

```
AST conformance: Ebpf.Ast constructors [Alu; Neg; Mov; MovSX; Swap]
  (pseudo/terminal, not spec'd: Assert_, Exit)
```

`specgen check` also prints the instance count per family and the total, so a
diff in the summary line is a visible change in ISA coverage.

### Running it

The OCaml toolchain lives in the `test-clone` VM:

```sh
multipass exec test-clone -- mkdir -p /home/ubuntu/wt-ms01/fstar
multipass transfer -r spec test-clone:/home/ubuntu/wt-ms01/
multipass transfer fstar/Ebpf.Ast.fst test-clone:/home/ubuntu/wt-ms01/fstar/
multipass exec test-clone -- bash -c \
  'eval $(opam env --switch=default) && make -C /home/ubuntu/wt-ms01/spec test'
```

`make -C spec test` = the positive check + the encoding anchors against
`Ebpf.Serialize`'s own `assert_norm` values + the AST drift check + the six
negative fixtures in `spec/tests/neg/` (each of which must be rejected with
its expected diagnostic *and* a position).

## 5. Backend contracts (later milestones — MS2/MS3/MS4)

### F* semantics backend (MS2) — consumes `s_families` + `s_enums`

Generates, for each family, one width-generic total function plus (for
families with a `defined` signature) one definedness predicate:

```
<family>_semn  : (width params) → (key enum) → (value params) → result
<family>_defined : (width params) → (key enum) → (defined params) → bool
```

which for `alu` is exactly today's `alu_semn : (n:pos) → alu_op → (d:{fits n})
→ (s:{fits n}) → {fits n}` and `alu_defined`, and for `swap` exactly
`swap_sem`. Enum `bits` attributes generate the width tables (`movsx_bits`,
`swap_bits`, `bits`).

**`unfold let` vs plain `let` — a binding rule, not a style choice.**

| family | today in `Ebpf.Semantics` | MS2 emits |
|---|---|---|
| `alu` | `alu_semn`, `alu_defined` — *named*, and referenced **by name** from `Ebpf.Interval`, `Ebpf.Sound`, `Ebpf.Annot` | plain `let` |
| `movsx`/`swap` width tables | `movsx_bits`, `swap_bits`, `swap_sem` — named, referenced by name | plain `let` |
| `neg`, `mov`, `movsx` value semantics | **inline in `stepx`'s match arms** — no named function exists | `unfold let` (`neg_semn`, `mov_semn`, `movsx_semn`) |

The rule: *inline today ⇒ `unfold let`; named today ⇒ plain `let`.* F*
unfolds `unfold let` at elaboration, so every downstream proof term (e.g.
`Ebpf.Annot.defterm_sound`'s Neg case, which literally mentions
`wrap 64 (0 - regbits W64 dv)`) stays textually identical and the
re-verification gate cannot be disturbed by the refactor. The converse
matters too: making `alu_semn` `unfold` would inline a 13-branch match into
every VC that mentions it and blow up `tf_alu_sound`. `stepx` then gets a
three-line hand edit to call the generated functions — the documented glue.

The contract MS2 relies on:

1. `i_sem` / `e_sem` are symbolic in the width vars and mention **no** axis
   other than the key — guaranteed by K2's scoping. This is what makes a
   width-generic F* function well-formed.
2. Every node maps to exactly one F* term (§2.6 table); no elaboration
   choices are left to the backend.
3. A width param may be emitted **abstractly** (`n: pos`, as `alu_semn`) or
   **via its axis** (`sz: swap_sz` + `swap_bits sz`, as `swap_sem`). The IL
   records `f_widths : width var ← axis`, so both are derivable. Abstract
   emission is only valid when the sem type-checks for *every* `n`; the
   `bswap (m / 8)` in `swap` does not (it needs `8 | m`), which is exactly
   why `swap_sem` is written over `sz` in the hand-written model. `i_obligs`
   tells the backend which obligations F* will be asked to discharge.
4. Re-verification is the acceptance test: generated `.fst` must pass
   `make verify` unchanged, and the differential harness must stay at zero
   divergences.

### Encoding backend (MS3) — consumes `s_instances`

Generates `cls`, `op_bits`, `op_off`, `movsx_off`, `swap_imm` and the
`encode_insn` cases of `Ebpf.Serialize`, using `opcode = cls + opc + sbit`
and the operand roles for the register/immediate fields. K8 is the property
that makes the generated encoder injective on the fragment; MS3 should emit
the round-trip (`decode ∘ encode = id`) test corpus from the same instance
list.

### Prose backend (MS4) — consumes `s_instances` + `f_cites`

Renders English by structural recursion over `expr`/`cond` (one template per
node kind — `wrap n (d + s)` → "adds the source to the destination and
truncates to *n* bits"), plus the encoding table and the `cite` provenance.
Prose is never authored, so it cannot drift. The contract is that the `expr`
AST has a fixed, small node set with fixed arities (§2.6), and that every
instance carries its own cites.

## 6. Positioning

**vs. Sail.** Sail is the reference point for ISA specification languages
(ARM, RISC-V) and is far more expressive than KeelSpec: a full imperative
language with dependent types, from which C/OCaml emulators, Isabelle/HOL and
Coq models are generated. Two reasons it is not what we want here. (i) There
is no F* backend, and the consumer of our spec is not a fresh model but an
*existing* F* development whose soundness proofs must keep verifying against
the generated code — the generated text has to look like what a human would
have written in `Ebpf.Semantics.fst`, using our combinators, not a translated
Sail monad. (ii) Weight: our whole fragment is 72 first-order instructions
with no state beyond the register file; a Sail model would be a large
dependency and a second semantics to trust, where KeelSpec is a 5-family
table whose generator is untrusted by construction (§7). If the fragment
grows to the point where control flow, memory and a full emulator are wanted,
Sail becomes the right answer and this table is a small thing to port.

**vs. Wasm-SpecTec.** SpecTec is the closest methodological relative — one
mechanized source, many artifacts (prose for the standard, Coq/Isabelle
backends, an interpreter) — and it was **officially adopted for the Wasm 3.0
specification in March 2025**, so the "spec-as-source" idea is settled; we
are not claiming it. The differences are in setting and in what the backends must
satisfy: SpecTec's DSL is built around Wasm's relational, declarative
semantics (typing and reduction rules, contexts, an expression-nested
grammar), which is machinery an ISA fragment does not need — our semantics is
first-order and per-instruction, one pure function of the operand values, and
our table shape reflects that. And SpecTec's generated Coq/Isabelle
definitions are the *starting point* of new metatheory, whereas ours must
land in an existing 15-module F* development and **re-verify existing
proofs** (`Ebpf.Sound`, `Ebpf.Annot`, `Ebpf.CertCheck`) plus survive
kernel differential validation. That "generated code must satisfy a
downstream verified consumer" loop, in the F*/ISA setting, is the
contribution; the language design is intentionally the least novel part.

## 7. Trust story

**What leaves the TCB.** Today, the hand-maintained *consistency* of
semantics, encoding and prose is trusted: nothing checks that `op_off SDIV =
1` agrees with `alu_semn`'s SDIV case, or that CONSTRAINTS.md's C12 row
describes the function that is actually there. After MS2–MS4 those three
artifacts are projections of one source, and the four-way edit becomes one
edit.

**What remains trusted.** The `.kspec` file itself — it is the specification;
someone must read 72 rows against RFC 9669. That is the point: 72 dense,
uniform, machine-checked rows are a better review artifact than four
notations in four files. The hand-written frame in `Ebpf.Semantics.fst`
(§1) also remains trusted.

**What is explicitly *not* trusted: `specgen`.** The generator is an ordinary
OCaml program with no proof. It does not need one, because everything it
emits is re-checked downstream by something that already is trusted:

- generated F* is re-verified by F* itself (`make verify`), and the existing
  soundness proofs (`Ebpf.Sound`, `Ebpf.Annot`, `Ebpf.CertCheck`) are stated
  against those very functions — a generator bug that changes semantics
  breaks a proof;
- generated encodings are differentially validated against the real kernel
  verifier (`harness/diff.py`) and against `BPF_PROG_TEST_RUN` return values
  (`harness/valcheck.py`);
- the meta-checks (§4) catch spec-authoring mistakes early, but nothing
  depends on them being complete.

The residual risk is a generator bug that is *semantics-preserving and
proof-preserving but wrong about the ISA* — i.e. it agrees with the `.kspec`
and F* accepts it, but the `.kspec` is wrong. That is spec risk, not
generator risk, and it is what the differential harness exists for. The one
place `specgen`'s own knowledge is load-bearing is K1's built-in `Ebpf.Ast`
reference table (`spec/specgen/lib/astref.ml`): if `Ebpf.Ast` gains a
constructor, that table must be updated by hand or K1/K9 would validate
against a stale AST. That hazard is *caught, not merely documented*:
`specgen astcheck fstar/Ebpf.Ast.fst` re-extracts the constructor and case
names straight from the F* source (a scan for `type …` declarations and the
identifiers following each `|` — deliberately not an F* parser) and diffs
them against the table, directionally; `make -C spec test` runs it. A stale
table is therefore a loud test failure rather than a silent wrong answer.

## 8. Deviations from the approved sketch

| # | sketch | here | why |
|---|---|---|---|
| 1 | whitespace-aligned columns | `\|`-separated columns | `defined` and `sem` cells contain spaces; pipes make the column boundary unambiguous, give exact column positions in diagnostics, and read like the RFC tables |
| 2 | `s = 0 ? 0 : …` ternary | `if s = 0 then 0 else …` | letter-identical to `alu_semn`, so a cell is copy-pasteable into F*; one syntax instead of two |
| 3 | `≠` | `<>` | ASCII, and F*'s own spelling. `!=`/`==` are *not* accepted — one canonical spelling per operator |
| 4 | `—` for "always defined" | `-` | ASCII |
| 5 | `enc class=…` | fields `cls`/`opc`/`sbit`/`off`/`imm` | `class`/`op` would collide with the axis variable names `op`/`src`; the five fields reconstruct `Serialize`'s `+` exactly |
| 6 | class-level defaults only | header keywords + per-row columns, each field given exactly once (K7) | byte swaps need per-row `cls`/`sbit` (kind selects the class), MOVSX needs an axis-derived `off` |
| 7 | one line per instruction | one line per *entry*; instances are the axis product | `alu_semn` matches on the op only — a row per (op, width, operand form) would triple the table and lose the fact that the semantics is width-generic |
| 8 | — | `valid` + `exclude` + K6 | see the MOVSX note below |
| 9 | — | explicit width argument on `logand`/`logor`/`logxor` | F* passes it implicitly; making it explicit keeps every width visible in the source and keeps the AST uniform |

**MOVSX `(W32, SX32)` — a real discrepancy found while writing this.**
`Ebpf.Check.fst:121` rejects it extensionally (`W32? w && SX32? sz`),
`Ebpf.Annot.fst:158` excludes it (`f < 32`), but `Ebpf.Semantics.fst:129`
guards with `f <= bits w` — and since `movsx_bits : n:pos{n <= 32}` and
`bits w ∈ {32, 64}`, that guard is a **tautology**: its `else None` branch is
dead code for *every* `(w, sz)`, not merely wrong for `(W32, SX32)`. The
model therefore steps that non-instruction as the identity, despite the
comment on the next line saying it is invalid.

`valid f < n` is the intensional predicate that yields exactly the five real
forms, and it is what the spec states; K6 forces the `exclude` line to agree
with it. Adopting it means MS2 emits `if f < bits w`, which **changes one
reachable behavior of the trusted `Ebpf.Semantics.stepx`** — so it is
sign-off, not silence. The safety argument, to be recorded in the MS2 commit:

- all five real forms satisfy `f < bits w` (8, 16, 32 < 64; 8, 16 < 32), so
  every reachable call is unaffected;
- `Ebpf.Check.fst:121` already rejects `(W32, SX32)`, so `check_insn_sound`'s
  obligation is vacuous there;
- `Ebpf.Annot.defterm` already returns `None` for it;
- `tf_movsx` / `tf_movsx_sound` keep their `f <= n` refinement (satisfied by
  every reachable call — no edit);
- nothing in `Ebpf.Build` / `Ebpf.Dump` / `Ebpf.CertClaim` uses `SX32`.

`make verify` is the arbiter: if it stays green, the change is proved
harmless. MS4 adds a kernel negative test (`BPF_ALU|BPF_MOV|BPF_X` with
`off=32` must be rejected by the real verifier) so the claim in the
`exclude` reason is evidence-backed rather than asserted. `CONSTRAINTS.md`
C13 records the issue.

## 9. Deferred (and where it plugs in)

- **Control flow** (jumps, `JMP` class, the branch/fallthrough successor
  relation) — the next milestone. Extension points: a family whose `sem`
  writes the program counter rather than `dst`, and a `writes` line to make
  the write target explicit instead of derived.
- **Memory** (`LD`/`ST` classes) — needs multi-effect forms (a memory read as
  a `sem` param, a memory write as a result) and the region/type layer beside
  the value logic; the `reads`/result machinery generalizes, the combinator
  set does not change.
- **Multi-instruction forms** (`LDDW`'s 16-byte encoding) — the encoding
  record is per-8-byte-slot today.
- **Per-row `cite` column** — family-level `cite` is enough for five
  families; adding a column is a non-breaking extension.
