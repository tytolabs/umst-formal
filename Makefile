# UMST-Formal — minimal orchestration (Wave 6.5.2)
.PHONY: lean-build lean-stats lean-print-axioms visuals haskell-test

lean-build:
	cd Lean && lake build

lean-stats:
	python3 scripts/lean_declaration_stats.py

lean-print-axioms:
	bash scripts/check_print_axioms.sh

visuals:
	python3 scripts/generate_visuals.py

haskell-test:
	cd Haskell && cabal test
