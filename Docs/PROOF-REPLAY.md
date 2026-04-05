# Proof replay — install, closure, and evidence notes

This document is the **independent replay checklist** for `umst-formal`: what must be true to re-check the machine-checked layers, what the repository does **not** mechanize (see `PROOF-STATUS.md`), and known gaps between **documentation claims** and **default CI/local commands**.

## Scope vs external narratives

The mechanized core (gate invariants, naturality, constitutional / Kleisli structure,
SDF-related lemmas, Landauer–Einstein mass-equivalent fragment) is **this repository’s**
formal artifact. Anything not listed in `PROOF-STATUS.md` is **not certified here**,
regardless of discussions elsewhere in the MaOS / UMST ecosystem.

**Landauer–Einstein fragment:** `Lean/LandauerEinsteinBridge.lean` (SI + coarse/tight
300 K brackets), `Coq/LandauerEinsteinBridge.v` (algebraic fragment), Agda
`LandauerEinsteinTrace.agda` (empty traceability module). Optional extensions are scoped in `Docs/FORMAL-PHYSICS-ROADMAP.md`; exact derivation
prerequisites and the sense in which advanced claims are **not in L₀** are in
`Docs/FORMAL-PHYSICS-DERIVATION-PLAN.md`.

## End-to-end replay stages (conceptual pipeline)

| Stage | Command (from repo root) | Independent of |
|-------|--------------------------|----------------|
| 1. Rust FFI bridge | `cd ffi-bridge && cargo build --release` | Proof assistants |
| 2. Rust C-ABI tests | `cd ffi-bridge && cargo test --release -p umst-ffi-bridge` | Agda / Coq / Lean |
| 3. Agda | `cd Agda && make check` | Coq / Lean / Haskell |
| 4. Coq | `cd Coq && make` (or `make check`) | Agda / Lean / Haskell |
| 5. Lean 4 | `cd Lean && lake build UMST` | Agda / Coq / Haskell |
| 6. Haskell (pure QC) | `cd Haskell && cabal build lib:umst-formal -f -with-ffi && cabal test umst-properties -f -with-ffi` | Rust (matches CI) |
| 6b. Haskell Landauer sanity | `cd Haskell && cabal test landauer-einstein-sanity` | Lean tight bracket (engineering check) |
| 7. Haskell ↔ Rust FFI | Build bridge, then `cd Haskell && cabal test umst-ffi-correspondence -f with-ffi` | Optional test suite (see below) |
| 8. Lean declaration stats | `make lean-stats` (repo root) or `python3 scripts/lean_declaration_stats.py` | Regenerates counts; CI compares to `scripts/expected_lean_declaration_snapshot.json` |
| 8b. Axiom invariant | `python3 scripts/check_lean_axioms.py` | Exactly `LandauerLaw.physicalSecondLaw` |
| 8c. Snapshot drift | `python3 scripts/lean_declaration_stats.py --verify-snapshot scripts/expected_lean_declaration_snapshot.json` | Same gate as CI Lean job |
| 8d. Markdown links | `bash scripts/check-markdown-links.sh` | Curated corpus; same as CI docs job |
| 9. Visual fixtures | `make visuals` (repo root) | Runs `scripts/generate_visuals.py` (optional figures; see root `Makefile`) |

Stages 3–5 are **logically independent** proof layers; stage 6 is **computational** consistency of the Haskell reference model; stages 1–2 and 7 relate to the **Rust** implementation path. Stages 8–9 are **documentation / artifact** checks, not proof obligations.

## Repository / CI structural blockers

1. **`umst-prototype-2a` path dependency**  
   `ffi-bridge/Cargo.toml` points at `../../umst-prototype-2a/prototype/src/rust/core`. For a full Rust build, clone that repo **next to** `umst-formal` (sibling directories). GitHub Actions uses `UMST_PROTO_REPO` to clone it (see `.github/workflows/ci.yml`).

2. **Haskell CI vs “Haskell ↔ Rust” wording**  
   CI job `haskell-pure` intentionally builds with **FFI disabled** (`-f -with-ffi`). Default `cabal test` therefore runs **QuickCheck on the pure Haskell gate only**; it does **not** execute `FFI.runCorrespondenceTests`. To replay Rust correspondence, build the bridge and run the **`umst-ffi-correspondence`** test suite with `-f with-ffi` (see `Haskell/umst-formal.cabal`).

3. **Coq / Rocq version on macOS (Homebrew)**  
   Homebrew now installs **Rocq 9** (successor branding). The `.v` files are compatible with Rocq 9 and Coq 8.18+. If using an older Coq, pin via **opam**, **Nix** (`shell.nix`), or **Docker**.

4. **Lean / Mathlib**  
   First `lake build` downloads **mathlib4** for the commit pinned in `Lean/lakefile.lean` (`v4.14.0`). Requires network and sufficient disk; use `elan` and the `Lean/lean-toolchain` file.

5. **Agda standard library**  
   `Agda/umst-formal.agda-lib` depends on `standard-library`. Ensure your Agda installation exposes the stdlib (packaging differs: Debian `agda-stdlib`, Homebrew caveats, or Nix `agdaPackages.standard-library`).

## Evidence log template (fill when replaying)

Use this table for independent audits; **do not** mark PASS without running the command on your machine.

| Stage | Command | Result (PASS/FAIL) | Tool versions |
|-------|---------|--------------------|---------------|
| Rust build | `cd ffi-bridge && cargo build --release` | | `rustc --version` |
| Rust tests | `cargo test --release -p umst-ffi-bridge` | | |
| Agda | `cd Agda && make check` | | `agda --version` |
| Coq | `cd Coq && make` | | `coqc --version` |
| Lean | `cd Lean && lake build UMST` | | `lean --version` |
| Haskell pure | `cd Haskell && cabal test umst-properties -f -with-ffi` | | `ghc --version` |
| Haskell Landauer sanity | `cd Haskell && cabal test landauer-einstein-sanity` | | `ghc --version` |
| Haskell FFI | `cd Haskell && cabal test umst-ffi-correspondence -f with-ffi` | | (after `cargo build --release` in `ffi-bridge/`) |
| Lean stats | `make lean-stats` (repo root) | | `python3 --version` |
| Lean axiom gate | `python3 scripts/check_lean_axioms.py` | | |
| Lean count snapshot | `python3 scripts/lean_declaration_stats.py --verify-snapshot scripts/expected_lean_declaration_snapshot.json` | | |
| Markdown links | `bash scripts/check-markdown-links.sh` | | `node` / `npx` |
| Visuals | `make visuals` (repo root) | | `python3 --version` |

## Quick probe (no builds)

```bash
cd /path/to/umst-formal
chmod +x scripts/check-formal-environment.sh   # once
./scripts/check-formal-environment.sh
./scripts/check-formal-environment.sh --strict   # fails if anything missing
```

## macOS (Homebrew) — minimal unblock sequence

Exact commands are **environment-specific**; this sequence is a common path when Nix is not used.

1. **Rust** (if needed): `brew install rustup-init && rustup-init -y`  
   Confirm: `cargo --version`

2. **Sibling kernel**: ensure `../umst-prototype-2a/prototype/src/rust/core` exists relative to `umst-formal`.

3. **Agda**: `brew install agda`  
   Follow `brew info agda` caveats for the standard library paths.

4. **Coq 8.20-style replay**: prefer **opam** + `coq.8.20.x` or **Nix** `shell.nix`, not an unpinned Homebrew `coqc`, unless you have verified compatibility with `Coq/*.v`.

5. **Lean**: `brew install elan-init` then:
   ```bash
   cd Lean
   elan default leanprover/lean4:v4.14.0   # if not picked up automatically
   lake build UMST
   ```

6. **Haskell**: `brew install cabal-install ghc@9.10` (or another 9.6+ per `umst-formal.cabal`) and ensure `ghc`/`cabal` are on `PATH`.

7. **Full commands** (after tools work):
   ```bash
   cd umst-formal/ffi-bridge && cargo build --release && cargo test --release -p umst-ffi-bridge
   cd ../Agda && make check
   cd ../Coq && make
   cd ../Lean && lake build UMST
   cd ../Haskell && cabal update && cabal test umst-properties -f -with-ffi
   cd ../Haskell && cabal test umst-ffi-correspondence -f with-ffi
   ```

## Nix (optional)

If `nix-shell` is available:

```bash
cd umst-formal
nix-shell --run './scripts/check-formal-environment.sh'
```

Then run the same stage commands inside the shell. Pin `nixpkgs` for stronger reproducibility (comments in `shell.nix`).

## Known computational gap (evidence, not a proof fix)

As of the audit that added this file, **`cargo test --release -p umst-ffi-bridge`** can fail one integration case (`test_inv1_mass_conservation_accepted`) against the current sibling `umst-core`, while other integration tests pass. Treat **green Rust tests** as a separate empirical check from **Agda/Coq/Lean** proof checkers; resolve any failure in `umst-prototype-2a` / test expectations before claiming full computational closure.
