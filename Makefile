# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
# UMST-Formal — minimal orchestration (Wave 6.5.2)
.PHONY: lean-build lean-stats lean-print-axioms visuals haskell-test coq-check agda-check formal-check

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

coq-check:
	$(MAKE) -C Coq clean
	$(MAKE) -C Coq all

agda-check:
	$(MAKE) -C Agda clean
	$(MAKE) -C Agda check

formal-check: coq-check agda-check
