# F* verification for the PCC-eBPF arithmetic milestone.
# Module order: Ast <- Int <- Semantics <- Interval <- Check <- Sound <- Build <- Serialize
FSTAR ?= fstar.exe
CACHE := .cache
FSTAR_FLAGS := --cache_checked_modules --cache_dir $(CACHE) --already_cached 'Prims FStar' --odir out

MODULES := Ebpf.Ast Ebpf.Int Ebpf.Semantics Ebpf.Interval Ebpf.Check Ebpf.Sound Ebpf.Build Ebpf.Serialize \
           Ebpf.Formula Ebpf.Proof Ebpf.Annot Ebpf.CertCheck Ebpf.Dsl Ebpf.Lower Ebpf.Emit

verify: $(addsuffix .checked,$(MODULES))

# manifest for the differential harness (tactic-print bridge)
manifest: verify
	$(FSTAR) $(FSTAR_FLAGS) Ebpf.Dump.fst | python3 ../harness/gen_manifest.py > ../harness/manifest.tsv
	cat ../harness/manifest.tsv

%.checked: %.fst | $(CACHE)
	$(FSTAR) $(FSTAR_FLAGS) $<

$(CACHE):
	mkdir -p $(CACHE)

# OCaml extraction of all pipeline modules (needs opam fstar.lib).
# Produces out/Ebpf_*.ml consumed by ir/certifier.
extract: | $(CACHE)
	$(FSTAR) $(FSTAR_FLAGS) --codegen OCaml \
	  --extract 'Ebpf.Ast Ebpf.Int Ebpf.Semantics Ebpf.Interval Ebpf.Check Ebpf.Formula Ebpf.Proof Ebpf.Annot Ebpf.CertCheck Ebpf.Serialize Ebpf.Dsl Ebpf.Lower Ebpf.Emit' \
	  Ebpf.CertCheck.fst Ebpf.Serialize.fst Ebpf.Proof.fst Ebpf.Emit.fst

clean:
	rm -rf $(CACHE) out

.PHONY: verify extract clean
