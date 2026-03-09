# Changelog

All notable changes to `umst-formal` are documented here.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versions follow [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Added
- `Agda/umst-formal.agda-lib` — library project descriptor; enables
  `agda --library=umst-formal` and `make check` without manual `--include-path`.
- `Coq/_CoqProject` — standard Coq project descriptor; enables `coq_makefile`
  dependency ordering (Gate.v → Extraction.v).
- `Haskell/test/Test.hs` — eight QuickCheck properties covering all four
  physical invariants plus field-consistency and boundary conditions.
- `ffi-bridge/tests/integration.rs` — black-box Rust integration tests
  for the C-ABI surface; covers all four invariants and the Theorem 1
  round-trip via `umst_thermo_state_from_mix_ptr`.
- `shell.nix` — Nix dev shell pinning Agda, Coq 8.20, GHC 9.6, Rust stable,
  and OCaml 5.1 for fully reproducible builds.
- `.github/workflows/ci.yml` — four-job CI pipeline (Agda, Coq, Haskell, Rust).
- `CONTRIBUTING.md` — branch strategy, commit conventions, and per-layer
  contribution guidelines.

### Changed
- `Agda/Gate.agda` — filled the `{!!}` hole in `gate-accepts-forward`;
  added `Data.Empty.⊥-elim` import; proof now type-checks in `--safe` mode.
- `Coq/Gate.v` — discharged the `helmholtz_antitone` `Admitted` lemma using
  `unfold Qle … destruct … nia`.
- `Agda/Makefile` — added `--library=umst-formal` flag; added `deps` target.
- `Coq/Makefile` — rewritten to use `coq_makefile` for correct dependency
  ordering; added `html` and `check` targets.
- `ffi-bridge/Cargo.toml` — added `rlib` to `crate-type` (required for
  integration tests); declared `[[test]] integration`.
- `Haskell/umst-formal.cabal` — widened `mtl` bounds to `< 3.0`; added
  `transformers` dependency; added `-rtsopts -N` to test GHC options.
- `.gitignore` — removed `*.agda-lib` glob (was silently ignoring the
  library descriptor); added `Coq/CoqMakefile*` to ignored list.

## [0.1.0] — 2026-03-09

### Added
- Initial repository with three-layer formal verification stack:
  - **Agda** (`Gate.agda`, `Naturality.agda`, `DIB-Kleisli.agda`, `Activation.agda`)
  - **Coq** (`Gate.v`, `Extraction.v`)
  - **Haskell** (`UMST.hs`, `KleisliDIB.hs`, `FFI.hs`)
- `ffi-bridge/` Rust crate exposing `umst-core` over a C ABI.
- `Docs/` with `Architecture-Invariants.md` and `OnePager-Categorical.tex`.
- `README.md` with scientific overview and build instructions.
