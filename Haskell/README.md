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
| `FFI.hs` | Foreign function interface binding to `libumst_ffi` (Rust via C ABI) |

## Property-Based Correspondence

The test suite (`test/Test.hs`) validates that the formal model matches the Rust kernel:

1. **Gate correspondence** — QuickCheck generates random `ThermodynamicState` pairs, runs both the pure Haskell gate and the Rust gate via FFI, and asserts identical accept/reject decisions.
2. **Invariant preservation** — Properties verify that each of the four invariants (mass conservation, Clausius-Duhem, hydration irreversibility, strength monotonicity) is individually respected by the Rust implementation.
3. **Kleisli composition** — Tests that sequential DIB phases compose correctly and preserve admissibility across the full loop.
