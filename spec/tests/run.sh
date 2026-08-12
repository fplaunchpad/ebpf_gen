#!/bin/sh
# KeelSpec MS1 test suite.  Run with `make -C spec test` (on the VM: the
# OCaml toolchain lives there).  Checks, in order:
#   1. the spec passes all meta-checks
#   2. the generated opcodes match Ebpf.Serialize's own anchors
#   3. specgen's built-in Ebpf.Ast table has not drifted from Ebpf.Ast.fst
#   4. the GENERATED regions of the committed F* files are exactly what the
#      spec produces today (MS2 fidelity / promote is idempotent)
#   5. every negative fixture is REJECTED, with its expected diagnostic and
#      a file:line:col position
set -u

cd "$(dirname "$0")/.." || exit 1          # spec/
SPECGEN=./specgen/_build/default/bin/specgen.exe
FSTARDIR=${FSTARDIR:-../fstar}
EBPF_AST=${EBPF_AST:-$FSTARDIR/Ebpf.Ast.fst}

pass=0
fail=0
ok()   { pass=$((pass + 1)); printf '  ok    %s\n' "$1"; }
bad()  { fail=$((fail + 1)); printf '  FAIL  %s\n' "$1"; }

if [ ! -x "$SPECGEN" ]; then
  echo "specgen not built: run 'make -C spec build' first" >&2
  exit 1
fi

echo "== positive: ebpf_alu.kspec =="
if out=$("$SPECGEN" check ebpf_alu.kspec 2>&1); then
  echo "$out" | sed 's/^/  /'
  ok "specgen check ebpf_alu.kspec"
else
  echo "$out" | sed 's/^/  /'
  bad "specgen check ebpf_alu.kspec"
fi

echo "== encoding anchors (vs Ebpf.Serialize) =="
list=$("$SPECGEN" list ebpf_alu.kspec 2>/dev/null)
anchor() {         # id  expected-opcode  what
  got=$(echo "$list" | grep -A1 "^$1 " | grep -o 'opcode=0x[0-9a-f]*' | head -1)
  if [ "$got" = "opcode=$2" ]; then ok "$1 = $2 ($3)"
  else bad "$1: expected opcode=$2, got ${got:-none} ($3)"; fi
}
anchor alu/ADD/W64/reg     0x0f "Serialize assert_norm: add64 r1,r2 = 0f"
anchor mov/MOV/W64/imm     0xb7 "Serialize assert_norm: mov64 r0,0 = b7"
anchor alu/SDIV/W64/reg    0x3f "sdiv64 = div64 opcode with off=1"
anchor movsx/MOVSX/W64/SX8 0xbf "0xb0 + 0x08 + cls W64"
anchor swap/ToLE/SW16      0xd4 "Serialize encode_insn Swap ToLE: 0xd0 + 0x04"
anchor swap/ToBE/SW64      0xdc "Serialize encode_insn Swap ToBE: 0xd0 + 0x08 + 0x04"
anchor swap/Bswap/SW32     0xd7 "Serialize encode_insn Swap Bswap: 0xd0 + 0x07"

echo "== IL: family-level encoding spellings (what MS3 reads) =="
spell() {          # family  expected-spelling
  if echo "$list" | grep -A2 "^family $1 " | grep -qF "enc family: $2"; then
    ok "$1 enc family: $2"
  else bad "$1 enc family: expected '$2'"; fi
}
spell alu   "cls = axis w, sbit = axis src"
spell movsx "cls = axis w, opc = 0xb0, sbit = 0x08, off = width f"
spell swap  "off = 0x00, imm = width m"

echo "== AST drift (specgen/lib/astref.ml vs Ebpf.Ast.fst) =="
if [ -f "$EBPF_AST" ]; then
  if out=$("$SPECGEN" astcheck "$EBPF_AST" 2>&1); then ok "astcheck $EBPF_AST"
  else echo "$out" | sed 's/^/  /'; bad "astcheck $EBPF_AST"; fi
else
  bad "astcheck: $EBPF_AST not found (set EBPF_AST=<path to Ebpf.Ast.fst>)"
fi

echo "== generated F* fidelity (spec -> $FSTARDIR) =="
# `specgen emit` copies the hand-written frame through verbatim and rewrites
# only the BEGIN/END GENERATED regions, so a difference here means exactly
# one thing: the committed F* no longer matches the spec.  Run
# `make -C spec promote` to fix it.
tmp=$(mktemp -d)
if out=$("$SPECGEN" emit ebpf_alu.kspec "$FSTARDIR" "$tmp" 2>&1); then
  ok "specgen emit ebpf_alu.kspec"
  for f in Ebpf.Semantics.fst Ebpf.Serialize.fst; do
    if diff -u "$FSTARDIR/$f" "$tmp/$f" > "$tmp/$f.diff" 2>&1; then
      ok "$f is up to date with the spec"
    else
      bad "$f has DRIFTED from ebpf_alu.kspec (run 'make -C spec promote')"
      sed 's/^/        /' "$tmp/$f.diff" | head -40
    fi
  done
else
  echo "$out" | sed 's/^/  /'
  bad "specgen emit ebpf_alu.kspec"
fi
rm -rf "$tmp"
echo "== prose backend (out/isa-alu.md) =="
prose_new=$(mktemp)
if "$SPECGEN" prose ebpf_alu.kspec > "$prose_new" 2>/dev/null; then
  ok "specgen prose ebpf_alu.kspec"
else
  bad "specgen prose ebpf_alu.kspec failed"
fi

# the committed artifact must be what the current generator produces
if [ ! -f out/isa-alu.md ]; then
  bad "out/isa-alu.md is missing (run 'make -C spec prose')"
elif diff -q out/isa-alu.md "$prose_new" >/dev/null 2>&1; then
  ok "out/isa-alu.md is up to date with the spec + generator"
else
  bad "out/isa-alu.md is STALE — regenerate with 'make -C spec prose'"
  diff -u out/isa-alu.md "$prose_new" | head -20 | sed 's/^/        /'
fi

# COVERAGE: one prose section per IL instance, and one row per IL entry.
# Ids come from `specgen list` / the family view, so a new instruction that
# the prose backend forgets is a test failure, not a silent omission.
ids=$(echo "$list" | grep -oE '^[a-z]+/[A-Za-z0-9_]+(/[A-Za-z0-9_]+)+' | sort -u)
nid=$(echo "$ids" | grep -c .)
miss=""
# the id lists must number exactly what `specgen check` reported, so that a
# broken extraction cannot make the coverage checks below pass vacuously
want=$("$SPECGEN" check ebpf_alu.kspec 2>/dev/null |
       sed -n 's/^OK: .* - \([0-9]*\) entries, \([0-9]*\) instances.*/\1 \2/p')
want_e=${want% *}
want_i=${want#* }
if [ "$nid" = "$want_i" ]; then ok "instance id list is complete ($nid ids)"
else bad "instance id extraction: got $nid ids, specgen check reports $want_i instances"; fi
for id in $ids; do
  # must be a `#### ` SECTION heading, not merely a row of the §3 encoding
  # table (which also names every id, and would satisfy a bare grep)
  grep -q "^#### .*\`$id\`\$" "$prose_new" || miss="$miss $id"
done
if [ -z "$miss" ]; then ok "prose covers all $nid instances (one section each)"
else bad "prose is missing sections for:$miss"; fi

ents=$(echo "$list" | awk '/^family /{f=$2} /^  entry /{print f "/" $2}')
nent=$(echo "$ents" | grep -c .)
missE=""
if [ "$nent" = "$want_e" ]; then ok "entry id list is complete ($nent ids)"
else bad "entry id extraction: got $nent ids, specgen check reports $want_e entries"; fi
for e in $ents; do
  # must be a row of a family's width-generic entry table: `family/ENTRY` in
  # the first cell (instance headings carry `family/ENTRY/...`, so the
  # trailing backtick keeps them from matching)
  grep -q "^| \`$e\` |" "$prose_new" || missE="$missE $e"
done
if [ -z "$missE" ]; then ok "prose covers all $nent table entries (width-generic row each)"
else bad "prose is missing entry rows for:$missE"; fi

# section count == instance count: no duplicate and no extra sections
nsec=$(grep -c '^#### ' "$prose_new")
if [ "$nsec" = "$nid" ]; then ok "exactly $nsec instruction sections for $nid instances"
else bad "prose has $nsec instruction sections but the IL has $nid instances"; fi

# mnemonic anchors: the assembly stems are the ONE naming the IL does not
# carry (emit_prose.ml), so pin them against ir/SPEC.md section 3
mnem() {           # instance-id  expected-mnemonic-line
  if grep -qF "#### \`$2\` — \`$1\`" "$prose_new"; then ok "$1 = \`$2\` (stem+width per ir/SPEC.md sec. 3)"
  else bad "$1: expected mnemonic \`$2\`; got: $(grep -F "\`$1\`" "$prose_new" | head -1)"; fi
}
mnem alu/SDIV/W32/imm       "sdiv32 dst, imm"
mnem movsx/MOVSX/W64/SX32   "movsx32_64 dst, src"
mnem swap/ToLE/SW16         "le16 dst"
mnem swap/ToBE/SW64         "be64 dst"
mnem swap/Bswap/SW32        "bswap32 dst"
mnem neg/NEG/W32            "neg32 dst"

# content anchors: the derived statements the RFC/CONSTRAINTS cross-check
# (spec/PROSE-CHECK.md) hangs on.  Each is rendered from the AST, so a
# semantics change in the .kspec must show up here.
say() {            # description  literal-text
  if grep -qF "$2" "$prose_new"; then ok "$1"
  else bad "$1: not found in the generated prose: $2"; fi
}
say "C5  div-by-zero result stated" \
  'dst = (src != 0) ? ((dst / src) mod 2^64) : 0'
say "C8  shift amount masked to the width" \
  '2 raised to the power (the unsigned remainder of the source register value divided by 64)'
say "C10 ALU32 result zero-extended into the 64-bit register" \
  'writing a 32-bit value into the 64-bit destination register clears bits 32..63 (zero extension)'
say "C12 SDIV is truncated toward zero, then wrapped" \
  'truncated toward zero), reduced modulo 2^64 (two'\''s-complement wrap-around)'
say "C13 (W32, SX32) is excluded, with its reason" \
  'the kernel rejects BPF_ALU|BPF_MOV|BPF_X with off=32'
say "C14 TO_LE on a little-endian host is a truncation" \
  'stated for a **little-endian** host'
say "C14 byte-swap sections state the byte reversal" \
  'the low 4 bytes of the destination value in reverse order'
say "C4/C7 immediates are rejected in BOTH modes (stated in 1.5)" \
  'a zero *immediate* divisor and an out-of-range *immediate* shift'
# a regression guard, not an anchor: the per-instruction definedness text once
# claimed blanket kernel-mode acceptance, which C4/C7 deny for immediate forms
nosay() {          # description  text-that-must-NOT-appear
  if grep -qF "$2" "$prose_new"; then bad "$1: forbidden text is back: $2"
  else ok "$1"; fi
}
nosay "no blanket kernel-mode acceptance claim per instruction" \
  'kernel mode accepts the instruction without one'
rm -f "$prose_new"

echo "== negative fixtures =="
for f in tests/neg/*.kspec; do
  want=$(grep -m1 '^# EXPECT: ' "$f" | sed 's/^# EXPECT: //')
  out=$("$SPECGEN" check "$f" 2>&1)
  rc=$?
  name=$(basename "$f")
  if [ $rc -eq 0 ]; then
    bad "$name was ACCEPTED (expected rejection)"
  elif ! echo "$out" | grep -qF "$want"; then
    bad "$name rejected with the wrong diagnostic"
    printf '        want: %s\n        got : %s\n' "$want" "$(echo "$out" | head -1)"
  elif ! echo "$out" | grep -qE "^$f:[0-9]+:[0-9]+: error:"; then
    bad "$name rejected without a file:line:col position"
    printf '        got : %s\n' "$(echo "$out" | head -1)"
  else
    ok "$name rejected: $(echo "$out" | head -1)"
  fi
done

echo
printf '%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ] || exit 1
