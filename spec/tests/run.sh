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
