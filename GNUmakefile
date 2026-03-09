# GNUmakefile — Root-level orchestration for umst-formal
#
# Builds all four layers in the correct dependency order:
#   Rust (ffi-bridge) → Agda → Coq → Haskell
#
# Quick-start:
#   make         → verify all layers (skips Rust if not needed)
#   make all     → build + verify everything
#   make rust    → compile ffi-bridge to libumst_ffi
#   make agda    → type-check all Agda proofs
#   make coq     → compile all Coq proofs + extract to OCaml
#   make haskell → build Haskell library + run QuickCheck tests
#   make clean   → remove all build artifacts
#   make status  → show proof completeness summary
#
# Prerequisites:
#   Rust / Cargo  — https://rustup.rs
#   Agda ≥ 2.6.4  — https://agda.readthedocs.io
#   Coq 8.20      — https://coq.inria.fr
#   GHC ≥ 9.6     — https://www.haskell.org/ghc
#   cabal ≥ 3.10  — https://cabal.readthedocs.io
#
# For a fully reproducible environment: nix-shell

.PHONY: all rust agda coq haskell clean status help

CARGO      := cargo
AGDA       := agda
COQC       := coqc
CABAL      := cabal
MAKE       := $(MAKE)

# ── Default: verify formal layers (no Rust required for pure proofs) ──────────

all: agda coq haskell

# ── Rust: compile ffi-bridge to a release shared/static library ───────────────

rust:
	@echo "══ Building Rust FFI bridge ══"
	cd ffi-bridge && $(CARGO) build --release
	@echo "   libumst_ffi compiled → ffi-bridge/target/release/"

rust-test:
	@echo "══ Running Rust integration tests ══"
	cd ffi-bridge && $(CARGO) test --release
	@echo "   Rust tests passed"

# ── Agda: type-check all proofs ───────────────────────────────────────────────

agda:
	@echo "══ Type-checking Agda proofs ══"
	$(MAKE) -C Agda check
	@echo "   Agda: all proofs verified"

agda-html:
	@echo "══ Generating Agda HTML docs ══"
	$(MAKE) -C Agda html

# ── Coq: compile proofs + extract to OCaml ────────────────────────────────────

coq:
	@echo "══ Compiling Coq proofs ══"
	$(MAKE) -C Coq all
	@echo "   Coq: all proofs compiled"

coq-extract:
	@echo "══ Extracting Coq → OCaml ══"
	$(MAKE) -C Coq extract
	@echo "   OCaml files written to Coq/ocaml/"

# ── Haskell: build + test (pure, no FFI) ─────────────────────────────────────

haskell:
	@echo "══ Building Haskell library + running QuickCheck tests ══"
	cd Haskell && $(CABAL) update --quiet && \
	  $(CABAL) build lib:umst-formal && \
	  $(CABAL) test umst-properties --test-show-details=streaming
	@echo "   Haskell: all properties passed"

haskell-ffi: rust
	@echo "══ Building Haskell library with FFI (requires libumst_ffi) ══"
	cd Haskell && $(CABAL) build lib:umst-formal -f with-ffi
	@echo "   Haskell+FFI: library built"

# ── Full stack: Rust → Agda → Coq → Haskell (with FFI) ──────────────────────

full: rust agda coq haskell-ffi rust-test
	@echo ""
	@echo "══════════════════════════════════════════════"
	@echo "  umst-formal: full verification stack PASSED"
	@echo "══════════════════════════════════════════════"

# ── Status: proof completeness summary ────────────────────────────────────────

status:
	@echo ""
	@echo "┌─────────────────────────────────────────────────────┐"
	@echo "│            umst-formal  ·  Proof Status             │"
	@echo "├─────────────────────────────────────────────────────┤"
	@echo "│ Agda                                                │"
	@printf "│   Holes (!!):       %4d (target: 0)               │\n" \
	  $$(grep -r '{!!}' Agda/ --include='*.agda' | wc -l)
	@printf "│   Postulates:       %4d (physical axioms)          │\n" \
	  $$(grep -r '^postulate' Agda/ --include='*.agda' | wc -l)
	@echo "│ Coq                                                 │"
	@printf "│   Admitted:         %4d (target: 0)               │\n" \
	  $$(grep -r 'Admitted\.' Coq/ --include='*.v' | wc -l)
	@echo "│ Haskell                                             │"
	@printf "│   Test modules:     %4d                            │\n" \
	  $$(ls Haskell/test/*.hs 2>/dev/null | wc -l)
	@echo "│ Rust                                                │"
	@printf "│   Integration tests:%4d                            │\n" \
	  $$(grep -c '^#\[test\]' ffi-bridge/tests/integration.rs 2>/dev/null || echo 0)
	@echo "└─────────────────────────────────────────────────────┘"
	@echo ""

# ── Clean ─────────────────────────────────────────────────────────────────────

clean:
	$(MAKE) -C Agda clean
	$(MAKE) -C Coq clean
	cd Haskell && $(CABAL) clean 2>/dev/null || true
	cd ffi-bridge && $(CARGO) clean 2>/dev/null || true
	@echo "Clean complete."

# ── Help ─────────────────────────────────────────────────────────────────────

help:
	@echo "umst-formal build targets:"
	@echo "  make         → verify Agda + Coq + Haskell (pure)"
	@echo "  make full    → full stack including Rust FFI"
	@echo "  make rust    → compile ffi-bridge only"
	@echo "  make agda    → type-check Agda proofs"
	@echo "  make coq     → compile Coq proofs"
	@echo "  make haskell → run Haskell QuickCheck tests"
	@echo "  make status  → proof completeness summary"
	@echo "  make clean   → remove all build artifacts"
