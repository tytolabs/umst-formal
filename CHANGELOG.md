# Changelog

All notable changes to `umst-formal` are documented here.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versions follow [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Added
- **`cabal test landauer-einstein-sanity`** — exact `Rational` regression vs Lean
  tight 300 K mass bracket numerators (`Haskell/test/LandauerEinsteinSanity.hs`);
  engineering check only (CI: `haskell-pure` job).
- **`Lean/LandauerEinsteinBridge.lean`** — SI-exact Boltzmann constant and \(c\),
  `Real.log 2`, Landauer–Einstein mass equivalent, linearity, **coarse and tight**
  numeric brackets at 300 K (`log_two_near_10`; see `PROOF-STATUS.md`).
- **`Coq/LandauerEinsteinBridge.v`** — algebraic fragment (parameters + positivity).
- **`Agda/LandauerEinsteinTrace.agda`** — empty `--safe` traceability module (proofs
  in Lean/Coq).
- **`Docs/FORMAL-PHYSICS-ROADMAP.md`** — optional extension phases; scoped to this
  formal artifact only.
- **`Docs/FORMAL-PHYSICS-DERIVATION-PLAN.md`** — mathematical statement shapes,
  required extensions (\(\Delta L\)), axiom bundles, and logical status vs core **L₀**
  (Landauer law, gravity, Jacobson, Bekenstein, Friedmann).
- **Lean 4 layer** — parity stack plus extensions: `Gate`, `Helmholtz`,
  `Constitutional`, `Naturality`, `Activation`, `DIBKleisli`,
  `LandauerEinsteinBridge`, `GraphProperties`, `Powers`, `Convergence`,
  `GaloisGate`, `EnrichedAdmissibility`, `LandauerLaw`, `InfoTheory`
  (**140** `theorem` + **21** `lemma` line-start counts in those roots per
  `PROOF-STATUS.md` / `scripts/lean_decl_stats.py`; sorry-free with one physical
  axiom `physicalSecondLaw` in `LandauerLaw.lean`).
  Graded `AdmissibleN` / `admissibleN_compose` replaces the refuted
  `admissibleTrans` axiom.  Includes `lean-toolchain` (v4.14.0) and `lakefile.lean`.
- `Coq/Constitutional.v` — Subject Reduction Lemma and Kleisli
  Admissibility Theorem.  Full mechanisation, zero `Admitted`.
- `Haskell/SDFGate.hs` — SDF / FRep interpretation of the thermodynamic
  gate.  CSG intersection, Helmholtz SDF, R-function combinators.
- `Haskell/test/Test.hs` — thirteen QuickCheck properties covering all
  four gate invariants, SDF/FRep properties, and constructor consistency.
- `Agda/Helmholtz.agda` — concrete Helmholtz free-energy model; antitone
  property, linearity, gradient theorem (SDF / Eikonal).
- `Agda/Gate.agda §7` — CSG decomposition (`admissible-to-csg`,
  `csg-to-admissible`).
- `Coq/Gate.v §8b` — `helmholtz_gradient` and `helmholtz_additive` lemmas
  (proved by `ring`).
- `Docs/FP-Primer.md` — 52-concept FP / Category Theory / SDF glossary
  anchored to the codebase.
- `PROOF-STATUS.md` — per-theorem cross-layer verification index.
- `Agda/umst-formal.agda-lib` — library project descriptor.
- `Coq/_CoqProject` — standard Coq project descriptor.
- `ffi-bridge/tests/integration.rs` — black-box Rust integration tests.
- `shell.nix` — Nix dev shell pinning Agda, Coq 8.20, GHC 9.6, Rust
  stable, Lean 4 (via elan), and OCaml.
- `.github/workflows/ci.yml` — six-job CI pipeline (Agda, Coq, Lean 4,
  Haskell, Rust, docs).
- `CONTRIBUTING.md` — branch strategy, commit conventions, and per-layer
  contribution guidelines (Agda, Coq, Lean 4, Haskell, Rust).

### Changed
- `Agda/Gate.agda` — filled the `{!!}` hole in `gate-accepts-forward`;
  added CSG decomposition (§7); proof type-checks in `--safe` mode.
- `Coq/Gate.v` — discharged `helmholtz_antitone` via `nia`; added
  `helmholtz_gradient` and `helmholtz_additive` (§8b).
- `Coq/Constitutional.v` — closed both `Admitted` lemmas
  (`gate_check_refl`, `kleisli_fold_well_typed`) via `admissible_refl`.
- `Agda/Makefile` — added `--library=umst-formal` flag; added `deps` target.
- `Coq/Makefile` — rewritten to use `coq_makefile`; includes
  `Constitutional.v` in SOURCES.
- `ffi-bridge/Cargo.toml` — added `rlib` to `crate-type`.
- `Haskell/umst-formal.cabal` — exposes `SDFGate`; configures
  `umst-properties` test suite.
- `.gitignore` — removed `*.agda-lib` glob; added `Coq/CoqMakefile*`.

## [0.1.0] — 2026-03-09

### Added
- Initial repository with three-layer formal verification stack:
  - **Agda** (`Gate.agda`, `Naturality.agda`, `DIB-Kleisli.agda`, `Activation.agda`)
  - **Coq** (`Gate.v`, `Extraction.v`)
  - **Haskell** (`UMST.hs`, `KleisliDIB.hs`, `FFI.hs`)
- `ffi-bridge/` Rust crate exposing `umst-core` over a C ABI.
- `Docs/` with `Architecture-Invariants.md` and `OnePager-Categorical.tex`.
- `README.md` with scientific overview and build instructions.
