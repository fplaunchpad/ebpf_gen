#!/usr/bin/env python3
"""Extract MANIFEST records from `fstar.exe Ebpf.Dump.fst` output into
manifest.tsv for diff.py.

The tactic printer appends `<: Prims.string` / `<: Prims.bool` ascriptions
and may wrap long records across lines, so parse the whole stream:
records are delimited by the MANIFEST marker; fields are the name token,
a quoted hex string, and two true/false tokens.

usage: fstar.exe ... Ebpf.Dump.fst | python3 gen_manifest.py > manifest.tsv
"""
import re
import sys

blob = sys.stdin.read()
count = 0
for chunk in blob.split("MANIFEST")[1:]:
    # stop at the next TAC>> marker or end; strip ascriptions and noise
    chunk = chunk.split("TAC>>")[0]
    chunk = chunk.replace("<:", " ").replace("Prims.string", " ").replace("Prims.bool", " ")
    m = re.search(r'^\s*(\S+)\s+"([0-9a-fA-F]*)"\s+(true|false)\s+(true|false)', chunk, re.S)
    if not m:
        print(f"skipping malformed record: {chunk[:80]!r}", file=sys.stderr)
        continue
    name, hexstr, strict, kmode = m.groups()
    v = lambda s: "accept" if s == "true" else "reject"
    print(f"{name}\t{hexstr}\t{v(strict)}\t{v(kmode)}")
    count += 1
print(f"{count} records", file=sys.stderr)
