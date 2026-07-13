#!/usr/bin/env python3
"""Value differential: run each named program with BPF_PROG_TEST_RUN and check
the kernel's retval (r0 truncated to u32) equals the value Ebpf.Semantics
predicts.  Complements diff.py (which checks accept/reject verdicts only).

The expected retvals below are machine-derived from Ebpf.Semantics — each is
asserted in Ebpf.Dump (`r0lo exX == ...`), so this compares the REAL kernel's
computed value against our (F*-checked) model, for the M2.1-hole-A opcodes
(SDIV/SMOD/MOVSX/byteswap) whose semantics were previously trusted-not-tested.

usage: sudo python3 valcheck.py [manifest.tsv]
"""
import subprocess
import sys

# name -> expected r0 (low 32), machine-checked by Ebpf.Dump assert_norms
EXPECTED = {
    "ex_sdiv":      4294967293,   # (-7) sdiv 2 = -3 (toward zero; floor = -4)
    "ex_smod":      4294967295,   # (-7) smod 2 = -1 (follows dividend sign)
    "ex_movsx_neg": 4294967240,   # s8 of 200 (0xC8) = -56, sign-extended
    "ex_bswap16":   0x3412,       # byte-reverse 0x1234
    "ex_bswap32":   0x78563412,   # byte-reverse 0x12345678
    "ex_bswap64":   0,            # low 32 of 0x7856341200000000
}


def retval(hexstr: str):
    r = subprocess.run(["./loader", hexstr, "-r"], capture_output=True, text=True)
    for ln in r.stdout.splitlines():
        if ln.startswith("RETVAL="):
            tail = ln.split("=", 1)[1]
            return int(tail) if tail.isdigit() else None
    return None


def main(manifest: str) -> int:
    hexes = {}
    with open(manifest) as f:
        for line in f:
            parts = line.strip().split("\t")
            if len(parts) >= 2 and parts[0] in EXPECTED:
                hexes[parts[0]] = parts[1]

    print(f"{'program':<14} {'kernel RETVAL':<14} {'F* expected':<14} note")
    bad = 0
    for name, exp in EXPECTED.items():
        if name not in hexes:
            print(f"{name:<14} {'(absent)':<14} {str(exp):<14} MISSING")
            bad += 1
            continue
        rv = retval(hexes[name])
        ok = rv == exp
        bad += not ok
        note = "OK" if ok else "MISMATCH"
        print(f"{name:<14} {str(rv):<14} {str(exp):<14} {note}")

    if bad:
        print(f"\n{bad} mismatch(es): kernel value diverges from Ebpf.Semantics")
    else:
        print("\nall values match: real kernel computes what Ebpf.Semantics predicts")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "manifest.tsv"))
