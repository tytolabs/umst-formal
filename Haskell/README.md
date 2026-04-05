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
- **`cabal test umst-ffi-correspondence -f with-ffi`**: after `cargo build --release` in `../ffi-bridge/`, runs `FFI.runCorrespondenceTests` — fixed scenarios comparing the pure gate to the Rust C-ABI gate. For exhaustive random testing, wrap `FFI.prop_gateCorrespondence` in QuickCheck as sketched in `FFI.hs`.

Rust-side black-box tests live in `../ffi-bridge/tests/integration.rs` (`cargo test -p umst-ffi-bridge`).

## QuickCheck inventory

- **`Haskell/test/Test.hs`** defines **33** `prop_*` properties (gate, SDF, InfoTheory, Landauer, monoidal state, burden/stochastic drift, Economic-layer mirrors). Count and grouping match [`../PROOF-STATUS.md`](../PROOF-STATUS.md) § Haskell / cross-layer tables.
- **`landauer-einstein-sanity`** (`cabal test landauer-einstein-sanity`): Rational regression check against the Lean `LandauerEinsteinBridge` tight bracket (engineering consistency, not a proof checker).
