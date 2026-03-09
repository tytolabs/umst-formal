# UMST-Formal

**Formal verification and categorical semantics for the Unified Material-State Tensor thermodynamic gate kernel.**

## Background

The UMST thermodynamic gate is a decision procedure: given a proposed material state
transition (old → new), it accepts or rejects the transition based on four physical
constraints — mass conservation, Clausius-Duhem dissipation, hydration irreversibility,
and strength monotonicity. The Rust kernel (`umst-prototype-2a`) implements that gate.

This repository proves, across three independent formal layers (Agda, Coq, Haskell),
that the implementation is sound with respect to those constraints. The proofs are
machine-checked; the correspondence to the Rust code is validated by property-based
testing.

The constraints themselves are empirically grounded — each one was identified through
field observation of specific material failure modes before it was formalised.
[Docs/Architecture-Invariants.md](Docs/Architecture-Invariants.md) documents that
derivation in detail.

## What This Repository Proves

Four invariants, verified across three formal layers (Agda, Coq, Haskell):

| # | Invariant | Physical meaning | Formal statement |
|---|-----------|-----------------|------------------|
| 1 | Mass conservation | Density cannot jump discontinuously | `|rho_new - rho_old| < delta` |
| 2 | Clausius-Duhem dissipation | Free energy must not increase (2nd law) | `D_int = -rho * psi_dot >= 0` |
| 3 | Hydration irreversibility | Cement hydration cannot reverse | `alpha_new >= alpha_old` |
| 4 | Strength monotonicity | Undamaged concrete cannot lose strength | `fc_new >= fc_old` |

## Architecture

```
umst-formal/
├── Agda/                   Dependent types + categorical proofs
│   ├── Gate.agda           Core admissible state, Theorem 1
│   ├── Naturality.agda     Natural transformation for the gate
│   ├── DIB-Kleisli.agda    Discovery-Invention-Build as Kleisli monad
│   └── Activation.agda     Material activations as dependent types
├── Coq/                    Verified extraction to OCaml
│   ├── Gate.v              Theorem proving over rationals
│   └── Extraction.v        OCaml code generation
├── Haskell/                Kleisli monad + Rust FFI bridge
│   ├── UMST.hs             Tensor types + pure reference gate
│   ├── KleisliDIB.hs       Categorical DIB monad
│   └── FFI.hs              Foreign function interface to Rust
├── ffi-bridge/             Thin C-ABI wrapper over umst-core
│   ├── src/lib.rs          extern "C" exports
│   └── include/umst_ffi.h  C header
├── Docs/                   Extended documentation
│   ├── Architecture-Invariants.md
│   ├── OnePager-Categorical.tex
│   └── Video-Demo-Placeholder.md
├── Cargo.toml              Workspace linking to Rust kernel
└── README.md               This file
```

### Layer Relationships

```
┌─────────────────────────────────────────────────────────────────┐
│  Agda (specification)                                           │
│  ────────────────────                                           │
│  Admissible : State → State → Set                               │
│  Gate : (s₁ s₂ : State) → Dec (Admissible s₁ s₂)              │
│  Naturality : gate ∘ F(f) ≡ F(f) ∘ gate                       │
│  ActivatedUMST : MaterialClass → Type                          │
└──────────────┬──────────────────────────────────────────────────┘
               │ specifies
┌──────────────▼──────────────────────────────────────────────────┐
│  Coq (extraction)                                               │
│  ────────────────                                               │
│  Same theorems proved with QArith                               │
│  Extraction to OCaml reference implementation                   │
└──────────────┬──────────────────────────────────────────────────┘
               │ validates against
┌──────────────▼──────────────────────────────────────────────────┐
│  Haskell (bridge)                                               │
│  ────────────────                                               │
│  Pure reference gate + property tests                           │
│  FFI calls to Rust kernel                                       │
│  DIB loop as Kleisli monad over StateT UMST IO                  │
└──────────────┬──────────────────────────────────────────────────┘
               │ calls via C ABI
┌──────────────▼──────────────────────────────────────────────────┐
│  ffi-bridge (Rust, new code)                                    │
│  ───────────────────────────                                    │
│  extern "C" wrappers around umst-core functions                 │
│  Produces libumst_ffi.dylib / .so                               │
└──────────────┬──────────────────────────────────────────────────┘
               │ path dependency (no modifications)
┌──────────────▼──────────────────────────────────────────────────┐
│  umst-prototype-2a/prototype/src/rust/core  (UNTOUCHED)         │
│  ──────────────────────────────────────────                     │
│  ThermodynamicFilter, PhysicsKernel, MixTensor, MaterialType    │
└─────────────────────────────────────────────────────────────────┘
```

### Categorical Structure

The mathematical backbone is a diagram in **Cat** (the category of small categories):

- **Objects**: `MaterialClass`, `ThermodynamicState`, `Bool`
- **Functors**: `F : MaterialClass → ThermodynamicState` (state construction),
  `G : ThermodynamicState² → Bool` (the gate)
- **Natural transformation**: `η : G ∘ (F × F) ⇒ G` (gate is material-agnostic)
- **Monoidal structure**: mass conservation as a monoidal constraint on
  the tensor product of state spaces
- **Kleisli category**: the DIB loop lives in `Kl(StateT UMST IO)`,
  composing discovery, invention, and build phases

See `Docs/OnePager-Categorical.tex` for the full commuting diagram.

## Building

### Prerequisites

| Tool | Version | Purpose |
|------|---------|---------|
| Rust | 1.75+ | FFI bridge compilation |
| Agda | 2.6.4+ | Dependent-type proofs |
| agda-stdlib | 2.0+ | Standard library |
| Coq | 8.18+ | Theorem proving + extraction |
| GHC | 9.6+ | Haskell bridge + property tests |
| cabal | 3.10+ | Haskell build system |

### Step-by-step

```bash
# 1. Build the Rust FFI bridge
cd ffi-bridge && cargo build --release && cd ..

# 2. Type-check Agda proofs (type-checking IS the proof)
cd Agda && make check && cd ..

# 3. Compile Coq proofs and extract OCaml
cd Coq && make && cd ..

# 4. Build Haskell bridge and run property tests
cd Haskell && cabal build && cabal test && cd ..
```

## Extending

To add a new material class (e.g., geopolymer):

1. **Agda**: Add constructor to `MaterialClass` in `Activation.agda`,
   define its engine set via `ActivatedUMST`
2. **Coq**: Mirror the Agda addition in `Gate.v`
3. **Haskell**: Add variant to `MaterialType` in `UMST.hs`,
   implement activation in `KleisliDIB.hs`
4. **FFI**: No changes needed (gate is material-agnostic by naturality)

## Correspondence to Rust Kernel

This repository does **not** modify the Rust kernel. The formal proofs establish
properties of an abstract mathematical model. Correspondence is validated by:

- Property-based tests (Haskell QuickCheck) that generate random states,
  run both the pure Haskell gate and the Rust gate via FFI, and assert
  identical accept/reject decisions
- The Coq-extracted OCaml serves as an independent reference implementation

## License

MIT. See [LICENSE](LICENSE).

## Citation

If you use this work, please cite both the formal verification layer and the
underlying Rust kernel:

```
Shyamsundar, S., Shenbagamoorthy, S. P. (2026).
UMST-Formal: Categorical Verification of Physics-Gated Material State Transitions.
```
