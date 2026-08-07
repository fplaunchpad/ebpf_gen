# KeelSpec (MS0/MS1).  The OCaml toolchain lives in the `test-clone` VM:
#   multipass transfer -r spec test-clone:/home/ubuntu/wt-ms01/
#   multipass exec test-clone -- bash -c \
#     'eval $$(opam env --switch=default) && make -C /home/ubuntu/wt-ms01/spec test'

SPECGEN := ./specgen/_build/default/bin/specgen.exe
SPEC    := ebpf_alu.kspec
EBPF_AST ?= ../fstar/Ebpf.Ast.fst

build:
	cd specgen && dune build

# parse + elaborate + meta-checks K1-K9, with a summary
check: build
	$(SPECGEN) check $(SPEC)

# the flattened instance table (what MS3/MS4 consume)
list: build
	$(SPECGEN) list $(SPEC)

# specgen's built-in Ebpf.Ast table vs the real Ebpf.Ast.fst
astcheck: build
	$(SPECGEN) astcheck $(EBPF_AST)

# positive check + encoding anchors + AST drift + negative fixtures
test: build
	EBPF_AST=$(EBPF_AST) ./tests/run.sh

clean:
	cd specgen && dune clean

.PHONY: build check list astcheck test clean
