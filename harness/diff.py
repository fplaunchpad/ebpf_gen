#!/usr/bin/env python3
"""Differential harness: compare the F* checker verdicts (Strict/Kernel
modes) against the real kernel verifier for each example program.

Input: a manifest file where each line is
    name <TAB> hex <TAB> strict_verdict <TAB> kernel_mode_verdict
verdicts are "accept"/"reject" as decided by the F* checker
(produced by Ebpf.Dump / extraction).

Runs ./loader on each hex, prints a comparison table, flags divergences
between the F* kernel-faithful mode and the real kernel.
"""
import subprocess
import sys

LOADER = "./loader"


def kernel_verdict(hexstr: str) -> tuple[str, str]:
    r = subprocess.run([LOADER, hexstr], capture_output=True, text=True)
    out = r.stdout.strip()
    return ("accept" if out == "ACCEPT" else "reject"), out


def main(manifest: str) -> int:
    rows, divergences = [], []
    with open(manifest) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            name, hexstr, strict, kmode = line.split("\t")
            kern, detail = kernel_verdict(hexstr)
            ok = kern == kmode
            rows.append((name, strict, kmode, kern, "" if ok else "DIVERGE"))
            if not ok:
                divergences.append((name, kmode, kern, detail))

    w = max(len(r[0]) for r in rows) + 2
    print(f"{'program':<{w}} {'F*strict':<9} {'F*kernel':<9} {'kernel':<8} note")
    for r in rows:
        print(f"{r[0]:<{w}} {r[1]:<9} {r[2]:<9} {r[3]:<8} {r[4]}")

    if divergences:
        print(f"\n{len(divergences)} divergence(s) between F* kernel-mode and the real verifier:")
        for name, kmode, kern, detail in divergences:
            print(f"  {name}: F*={kmode} kernel={kern} ({detail})")
    else:
        print("\nno divergences: F* kernel-faithful mode matches the real verifier")
    return 1 if divergences else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "manifest.tsv"))
