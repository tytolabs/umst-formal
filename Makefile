# UMST-Formal — minimal orchestration (Wave 6.5.2)
.PHONY: lean-build lean-stats visuals haskell-test

lean-build:
	cd Lean && lake build

lean-stats:
	python3 scripts/lean_declaration_stats.py

visuals:
	python3 scripts/generate_visuals.py

haskell-test:
	cd Haskell && cabal test
