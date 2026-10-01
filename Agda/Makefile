# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
AGDA       := agda
# --library : uses umst-formal.agda-lib for the stdlib path.
# Safe mode is set per module with `{-# OPTIONS --safe #-}`; the tree holds no `postulate`
# (the physical laws are module parameters, W-04 / P0-5). The flag is not passed globally
# because not every module carries the pragma yet; `agda --safe Gate.agda` type-checks.
# Agda 2.8 may emit spurious LibUnknownField on this repo’s .agda-lib when
# resolving `depend:`; silence if it appears (fields are valid for bundled libs).
AGDA_FLAGS := --library=umst-formal -W noLibUnknownField

# Every tracked module (a hand-picked list let 67 of 76 files go unchecked).
SOURCES := $(shell git ls-files '*.agda' | sort -u)

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
