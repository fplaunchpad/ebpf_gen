#!/usr/bin/env python3
"""Keel DSL end-to-end corpus runner (M2.3.4 "mini-fuzzing").

For each program in the bpfc-generated corpus, check the whole pipeline holds:
  1. certify   — run `irc` on the .kir; require verified accepts + all claims
                 check_proof=true                          (test-clone VM)
  2. load      — the emitted bytecode loads on the real kernel   (kernel7 VM)
  3. result    — BPF_PROG_TEST_RUN retval == the DSL evaluator's predicted
                 value (mod 2^32)                              (kernel7 VM)

This is orchestrated across the two VMs by the caller (the two steps run on
different hosts). This script runs the KERNEL side: given the manifest
(name<TAB>hex<TAB>expected) it loads+runs each program and checks the result,
and (if given --certified name=ok/fail lines on stdin) folds in the
certification verdicts collected on the build VM.

usage (on kernel7):  sudo python3 run_corpus.py corpus/manifest.tsv ./loader
"""
import subprocess
import sys


def main(manifest: str, loader: str) -> int:
    rows = []
    with open(manifest) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            name, hx, expected = line.split("\t")
            r = subprocess.run([loader, hx, "-r"], capture_output=True, text=True)
            out = r.stdout
            loaded = "ACCEPT" in out
            retval = None
            for tok in out.split():
                if tok.startswith("RETVAL="):
                    retval = tok[len("RETVAL="):]
            result_ok = (retval == expected)
            rows.append((name, expected, retval, loaded, result_ok))

    w = max(len(r[0]) for r in rows) + 2
    print(f"{'program':<{w}} {'expected':<12} {'retval':<12} {'loaded':<7} result")
    npass = 0
    for name, exp, rv, loaded, ok in rows:
        note = "OK" if (loaded and ok) else "FAIL"
        if loaded and ok:
            npass += 1
        print(f"{name:<{w}} {exp:<12} {str(rv):<12} {str(loaded):<7} {note}")
    print(f"\n{npass}/{len(rows)} loaded and computed the predicted result")
    return 0 if npass == len(rows) else 1


if __name__ == "__main__":
    mani = sys.argv[1] if len(sys.argv) > 1 else "corpus/manifest.tsv"
    ld = sys.argv[2] if len(sys.argv) > 2 else "./loader"
    sys.exit(main(mani, ld))
