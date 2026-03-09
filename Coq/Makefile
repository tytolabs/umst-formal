COQC := coqc

SOURCES := Gate.v Extraction.v

.PHONY: all clean extraction

all: Gate.vo Extraction.vo
	@echo "── Coq proofs compiled ──"

Gate.vo: Gate.v
	@echo "  ⊢ Gate.v"
	$(COQC) Gate.v

Extraction.vo: Extraction.v Gate.vo
	@echo "  ⊢ Extraction.v (depends on Gate.vo)"
	$(COQC) Extraction.v

extraction: all
	@echo "── OCaml extracted to ocaml/ ──"

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
