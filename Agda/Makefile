AGDA       := agda
# --library : uses umst-formal.agda-lib for the stdlib path.
# Note: we intentionally do NOT pass --safe here: Gate.agda and Helmholtz.agda
# contain physical-model postulates (ψ-antitone / fc-monotone at the state level,
# matching the Coq/Lean “axiom as interface” split). For a safe-only slice, add a
# separate target that type-checks only postulate-free modules.
# Agda 2.8 may emit spurious LibUnknownField on this repo’s .agda-lib when
# resolving `depend:`; silence if it appears (fields are valid for bundled libs).
AGDA_FLAGS := --library=umst-formal -W noLibUnknownField

SOURCES := Gate.agda Helmholtz.agda Naturality.agda DIB-Kleisli.agda Activation.agda LandauerEinsteinTrace.agda InfoTheory.agda MeasurementCost.agda

.PHONY: all check html clean

all: check html

check:
	@echo "── Type-checking Agda proofs ──"
	@for f in $(SOURCES); do \
		echo "  ⊢ $$f"; \
		$(AGDA) $(AGDA_FLAGS) $$f || exit 1; \
	done
	@echo "── All proofs verified ──"

html:
	@echo "── Generating HTML documentation ──"
	@for f in $(SOURCES); do \
		$(AGDA) $(AGDA_FLAGS) --html --html-dir=html $$f; \
	done

clean:
	rm -f *.agdai
	rm -rf html

# Dump the full dependency graph (useful for debugging import errors).
deps:
	@for f in $(SOURCES); do \
		echo "=== $$f ==="; \
		$(AGDA) --dependency-graph=/dev/stdout $$f 2>/dev/null || true; \
	done
