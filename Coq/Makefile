# Coq Makefile for umst-formal
#
# Two-stage build strategy (best practice):
#   1. `make generate` — run coq_makefile to produce CoqMakefile, which
#      correctly computes inter-file dependencies (needed when Gate.v imports
#      lemmas and Extraction.v depends on Gate.vo).
#   2. `make` / `make all` — invoke CoqMakefile to compile in dependency order.
#
# Quick start:
#   make          # generate + compile
#   make extract  # generate + compile + extract to OCaml
#   make html     # generate Coqdoc HTML
#   make clean    # remove all build artifacts
#
# Tested with Coq 8.20.x.

COQC         := coqc
COQ_MAKEFILE := coq_makefile
SOURCES      := Gate.v Constitutional.v LandauerEinsteinBridge.v InfoTheory.v MeasurementCost.v Extraction.v
COQMAKEFILE  := CoqMakefile

.PHONY: all generate extract html clean check

# Default: generate then build.
all: generate
	$(MAKE) -f $(COQMAKEFILE) all

# Produce CoqMakefile from the source list.
generate: $(COQMAKEFILE)

$(COQMAKEFILE): $(SOURCES)
	@echo "── Generating CoqMakefile ──"
	$(COQ_MAKEFILE) -f _CoqProject -o $(COQMAKEFILE) 2>/dev/null \
	  || $(COQ_MAKEFILE) $(SOURCES) -o $(COQMAKEFILE)

# Extraction: `make all` already compiles `Extraction.v` under `CoqMakefile`, which
# applies `_CoqProject` (`-Q . UMSTFormal`). A bare `$(COQC) Extraction.v` here
# would omit those flags and fail with “Cannot find … UMSTFormal.Gate”.
extract: all
	@echo "── OCaml extraction (artifacts from CoqMakefile build of Extraction.v) ──"
	@test -f gate_extracted.ml && test -f gate_extracted.mli || \
	  (echo "missing gate_extracted.ml/.mli after build" >&2; exit 1)
	@echo "── OCaml files: gate_extracted.ml, gate_extracted.mli ──"

# Fallback: direct coqc invocation (no dep tracking; use for quick checks).
check:
	@echo "── Direct coqc check (no dependency tracking) ──"
	@for f in $(SOURCES); do \
		echo "  ⊢ $$f"; \
		$(COQC) $$f || exit 1; \
	done
	@echo "── Coq proofs compiled ──"

html:
	@echo "── Generating Coqdoc HTML ──"
	mkdir -p html
	coqdoc --html --utf8 --toc -d html $(SOURCES)

clean:
	$(MAKE) -f $(COQMAKEFILE) clean 2>/dev/null || true
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
	rm -f *.vo *.vos *.vok *.glob .*.aux *~
	rm -rf html ocaml .coq-native
