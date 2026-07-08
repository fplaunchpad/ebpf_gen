# Keel certifier (M2.2). Depends on the F* OCaml extraction (../../fstar/out).
FSTAR_OUT := ../../fstar/out

# Copy the extracted verified modules in, then build the OCaml pipeline.
setup:
	@test -f $(FSTAR_OUT)/Ebpf_CertCheck.ml || \
	  (echo "run 'make extract' in ../../fstar first" && exit 1)
	cp $(FSTAR_OUT)/Ebpf_*.ml bin/

build: setup
	dune build

# irc <file.kir>  — certify a program; 'selftest' — adversarial checks
run: build
	./_build/default/bin/irc.exe $(F)

selftest: build
	./_build/default/bin/irc.exe selftest

clean:
	rm -rf _build bin/Ebpf_*.ml

.PHONY: setup build run selftest clean
