# Changelog

All notable changes to `umst-formal` are documented here.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versions follow [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Fixed (2026-04-22)

- **Formal CI (`agda` / `coq` / `lean` jobs)** — register **`Agda/umst-formal.agda-lib`** and resolve **`standard-library.agda-lib`** via `dpkg -L agda-stdlib` / `find /usr /opt`; run **`coq`** via `docker run --user root` + **`chown`** back to the runner UID (bind-mount write perms); **`leanprover/lean-action@v1`** with `lake build UMST` (no `--wfail` on CI to avoid Mathlib replay flaking on upstream linter noise).
- **Lean sources** — `Powers.lean`: `div_le_div_iff₀`, `pow_le_pow_left₀` (Mathlib deprecations); `LandauerExtension.lean`: underscore binders for unused hypotheses (warning-clean under `lake build`).
- **Docs CI (`markdownlint`)** — relax `MD060` (compact GitHub-style tables), widen default `MD013` line budget for narrative docs, add `README.md` `markdownlint-disable-file` for hero-only rules (`MD001`/`MD026`), fix `CHANGELOG.md` / `Coq/README.md` spacing and fenced-code languages, `CONTRIBUTING.md` fenced language; restore green **`docs`** job.
- **README** — add single [**CI**](https://github.com/tytolabs/umst-formal/actions/workflows/ci.yml) workflow badge (pass/fail visible on GitHub like sibling double-slit repo).

### Documentation / CI (2026-04-22)

- **Lean declaration drift closure** — `scripts/expected_lean_declaration_snapshot.json` bumped to **45** lake roots, **221**/**17**/**238** (`theorem`/`lemma`/total, roots-only and all-`Lean/*` glob match). `README.md`, `FORMAL_FOUNDATIONS.md`, `Docs/DOCUMENTATION-COVERAGE-PLAN.md` hero + audit rows aligned with `python3 scripts/lean_declaration_stats.py`.
- **Haskell QuickCheck inventory** — `Haskell/README.md` now states **62** `quickCheck` calls in `test/Test.hs` `main` (not the obsolete “33 props in Test.hs” line count); matches `PROOF-STATUS.md` narrative for `cabal test umst-properties`.

### Added (Wave 6.5.2 — 2026-04-04)

- **`Lean/Economic/`** — 17 named modules + `EconomicDomain.lean`: classical Shannon/Landauer + gate burden story; **0** tactic `sorry`; **no** new physics axioms (still only `physicalSecondLaw` project-wide).
- **`SAFETY-LIMITS.md`**, **`Docs/FALSIFIABILITY_DASHBOARD.md`** — scope and honesty rails for Economic-layer names.
- **`visuals/`**, **`scripts/generate_visuals.py`**, **`requirements-visuals.txt`**, **`Makefile`** targets (`lean-build`, `lean-stats`, `visuals`, `haskell-test`).
- **Haskell** — QuickCheck mirrors for burden/stochastic drift and Economic lemmas (**33** properties total in `Haskell/test/Test.hs`).
- **`scripts/lean_declaration_stats.py`** — dotted Lake roots (`Economic.Foo`); exclude **`.lake`** from “all Lean” / axiom scans (avoids Mathlib noise).

### Added (CI + doc rigor — 2026-04-05)

- **CI** — `scripts/check_lean_axioms.py`; `lean_declaration_stats.py --verify-snapshot` + `scripts/expected_lean_declaration_snapshot.json`; `scripts/check_lean_sorry.sh` (Lean job). **Docs** job: Node 20, `scripts/check-markdown-links.sh` + `scripts/markdown-link-check.json`.
- **`Docs/DOCUMENTATION-COVERAGE-PLAN.md`** — maintainer checklist (not linked from `README` by design).
- **`lean_declaration_stats.py --theorem-names`** — JSON export of line-start `theorem` / `lemma` names per lake root.

### Fixed

- **Lean build** — `Constitutional.lean` module doc (graded Kleisli; legacy `admissibleTrans` refuted); `DIBKleisli.dib_semantic_step_admissible` structure proof; Economic / `MeasurementCost` / `InfoTheory` scoping (`ProbDist`, `JointDist`, `mutualInformation`); tactic imports (`Linarith`, `Ring`); `HorizonAwareGrounding` convex-combination proof without `gcongr`.
- **Documentation / counts** — Lean roots **39**, **176** `theorem` + **13** `lemma` (roots-only); `README.md` / `PROOF-STATUS.md` / `FORMAL_FOUNDATIONS.md` aligned with `python3 scripts/lean_declaration_stats.py`. (Older bullets below may cite superseded numbers.)
- **`PROOF-STATUS.md`** — Lean layer row previously listed **20** roots; corrected to **24** (historical note: was once “12 modules”).

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
  (**154** `theorem` + **13** `lemma` line-start counts in those roots per
  `PROOF-STATUS.md` / `scripts/lean_declaration_stats.py`; sorry-free with one physical
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
