# Haskell Layer — Categorical Bridge & Property Tests

Categorical semantics bridge connecting the formal Agda/Coq specifications to the Rust kernel via FFI, with property-based testing for correspondence validation.

## Prerequisites

- GHC 9.6+
- cabal 3.10+
- Rust toolchain (for building `ffi-bridge`)

## Build

```bash
# 1. Build the FFI bridge first
cd ../ffi-bridge && cargo build --release && cd ../Haskell

# 2. Build the Haskell library
cabal build

# 3. Run property tests
cabal test
```

## Modules

| Module | Purpose |
|--------|---------|
| `UMST.hs` | Tensor types and pure reference implementation of the thermodynamic gate |
| `KleisliDIB.hs` | Discovery-Invention-Build loop as a Kleisli monad over `StateT UMST IO` |
| `SDFGate.hs` | SDF / FRep view of the gate (CSG intersection, Helmholtz SDF, R-functions) |
| `FFI.hs` | Foreign function interface binding to `libumst_ffi` (Rust via C ABI) |

## Property-Based Correspondence

- **`cabal test umst-properties`** (default / CI): QuickCheck over the **pure** Haskell gate in `UMST.hs` and SDF lemmas in `SDFGate.hs`. It does **not** link `libumst_ffi` or call Rust.
- **`cabal test umst-ffi-correspondence -f with-ffi`**: after `cargo build --release` in `../ffi-bridge/` (or wherever your `libumst_ffi.so` is produced — override with `UMST_FFI_LIB`), runs `FFI.runCorrespondenceTests` — fixed scenarios comparing the pure gate to the Rust C-ABI gate. **Preferred gate (N-hygiene-ffi):** from the workspace root, `bash scripts/run-ffi-tests.sh` — builds the test target, copies `libumst_ffi.so` next to the Cabal test binary so the linker uses `rpath=$ORIGIN` only, then executes the binary with `env -u LD_LIBRARY_PATH`. Plain `cabal test …` without the copy step may fail to load the `.so` after the rpath simplification. **GHC ≥ 9.8 / base ≥ 4.18** is required; on older distro GHC (e.g. 9.4 + base 4.17) Cabal will not resolve `umst-formal` — use **`bash scripts/ffi-docker/run.sh`** (Dockerfile under `scripts/ffi-docker/`) for a reproducible 360-seed run. For exhaustive random testing, wrap `FFI.prop_gateCorrespondence` in QuickCheck as sketched in `FFI.hs`.

Rust-side black-box tests live in `../ffi-bridge/tests/integration.rs` (`cargo test -p umst-ffi-bridge`).

## QuickCheck inventory

- **`Haskell/test/Test.hs`** `main` runs **62** `quickCheck` obligations (gate, SDF, InfoTheory, Landauer, monoidal state, MeasurementCost, burden/stochastic drift, Economic-layer mirrors, **CreditGreedy**, **Dignity**, **η_cog**, **ρ-MI**, **median warmup**, **order-statistics band** — props live in `Test.hs` and imported `test/*.hs` modules). Count matches `rg -c quickCheck test/Test.hs` and [`../PROOF-STATUS.md`](../PROOF-STATUS.md) § Haskell / cross-layer tables.
- **`landauer-einstein-sanity`** (`cabal test landauer-einstein-sanity`): Rational regression check against the Lean `LandauerEinsteinBridge` tight bracket (engineering consistency, not a proof checker).
