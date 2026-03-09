AGDA       := agda
# --safe   : forbids postulates not declared safe and disables all unsafe pragmas.
# --library : uses umst-formal.agda-lib for the stdlib path.
AGDA_FLAGS := --safe --library=umst-formal

SOURCES := Gate.agda Naturality.agda DIB-Kleisli.agda Activation.agda

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
		$(AGDA) --safe --html --html-dir=html $$f; \
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
