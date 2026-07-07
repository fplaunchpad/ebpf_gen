# F* verification for the PCC-eBPF arithmetic milestone.
# Module order: Ast <- Int <- Semantics <- Interval <- Check <- Sound <- Build <- Serialize
FSTAR ?= fstar.exe
CACHE := .cache
FSTAR_FLAGS := --cache_checked_modules --cache_dir $(CACHE) --already_cached 'Prims FStar' --odir out

MODULES := Ebpf.Ast Ebpf.Int Ebpf.Semantics Ebpf.Interval Ebpf.Check Ebpf.Sound Ebpf.Build Ebpf.Serialize

verify: $(addsuffix .checked,$(MODULES))

%.checked: %.fst | $(CACHE)
	$(FSTAR) $(FSTAR_FLAGS) $<

$(CACHE):
	mkdir -p $(CACHE)

# OCaml extraction of the serializer + examples (needs opam fstar.lib)
extract: | $(CACHE)
	$(FSTAR) $(FSTAR_FLAGS) --codegen OCaml --extract 'Ebpf' Ebpf.Serialize.fst

clean:
	rm -rf $(CACHE) out

.PHONY: verify extract clean
