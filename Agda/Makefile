AGDA       := agda
AGDA_FLAGS := --safe

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
		$(AGDA) --html --html-dir=html $$f; \
	done

clean:
	rm -f *.agdai
	rm -rf html
