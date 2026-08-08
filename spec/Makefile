# KeelSpec (MS0/MS1).  The OCaml toolchain lives in the `test-clone` VM:
#   multipass transfer -r spec test-clone:/home/ubuntu/wt-ms01/
#   multipass exec test-clone -- bash -c \
#     'eval $$(opam env --switch=default) && make -C /home/ubuntu/wt-ms01/spec test'

SPECGEN := ./specgen/_build/default/bin/specgen.exe
SPEC    := ebpf_alu.kspec
FSTARDIR ?= ../fstar
EBPF_AST ?= $(FSTARDIR)/Ebpf.Ast.fst
OUT     := out
GENFILES := Ebpf.Semantics.fst Ebpf.Serialize.fst

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

# regenerate the GENERATED regions of the F* files into $(OUT)/.  The
# hand-written frame is copied through verbatim from $(FSTARDIR), so `emit`
# is idempotent and `diff` is the drift check (see `test`).
emit: build
	@mkdir -p $(OUT)
	$(SPECGEN) emit $(SPEC) $(FSTARDIR) $(OUT)

# copy the regenerated files over the committed ones
promote: emit
	@for f in $(GENFILES); do \
	  cp $(OUT)/$$f $(FSTARDIR)/$$f && echo "promoted $(FSTARDIR)/$$f"; \
	done

# positive check + encoding anchors + AST drift + generated-F* fidelity
# + negative fixtures
test: build
	EBPF_AST=$(EBPF_AST) FSTARDIR=$(FSTARDIR) ./tests/run.sh

clean:
	cd specgen && dune clean
	rm -rf $(OUT)

.PHONY: build check list astcheck emit promote test clean
