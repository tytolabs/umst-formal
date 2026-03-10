# UMST-Formal

**Formal verification and categorical semantics for the Unified Material-State Tensor (UMST).**

## Background

The Unified Material-State Tensor (UMST) is a mathematical framework for reasoning
about material state transitions in physical systems.  Its core components are:

- **Thermodynamic gate** — a decision procedure that accepts or rejects a proposed
  state transition based on four physical constraints (mass conservation,
  Clausius-Duhem dissipation, hydration irreversibility, strength monotonicity).
- **Naturality** — a categorical proof that the gate is material-agnostic: it
  applies uniformly across material classes (OPC, RAC, geopolymer, lime, earth, ...).
- **Constitutional sequences** — Kleisli-monadic composition of N gate-checked
  transitions, with Subject Reduction guaranteeing safety at every step.
- **Geometric interpretation** — the admissible region as an SDF / FRep implicit
  surface (CSG intersection of four half-spaces), with Helmholtz free energy
  providing the gradient field.
- **DIB cycle** — the Discovery-Invention-Build loop modelled as a state monad
  with verified associativity.

The Rust kernel (`umst-prototype-2a`) implements the gate.  This repository proves,
across four independent formal layers (Agda, Coq, Lean 4, Haskell QuickCheck), that
the UMST framework is internally consistent and the implementation is sound.
The proofs are machine-checked; the correspondence to the Rust code is validated
by property-based testing.

The constraints are empirically grounded — each was identified through field
observation of specific material failure modes before it was formalised.
[Docs/Architecture-Invariants.md](Docs/Architecture-Invariants.md) documents that
derivation.

## What This Repository Proves

Four invariants, verified across four formal layers (Agda, Coq, Lean 4, Haskell QuickCheck):

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
│   ├── Gate.agda           Core admissible state, Theorem 1; CSG decomposition
│   ├── Naturality.agda     Natural transformation for the gate
│   ├── DIB-Kleisli.agda    Discovery-Invention-Build as Kleisli monad
│   ├── Activation.agda     Material activations as dependent types
│   └── Helmholtz.agda      Helmholtz free-energy model; gradient / Eikonal theorem
├── Coq/                    Verified extraction to OCaml
│   ├── Gate.v              Theorem proving over rationals; Helmholtz gradient (§8b)
│   ├── Constitutional.v    Subject Reduction Lemma; Kleisli Admissibility Theorem
│   └── Extraction.v        OCaml code generation
├── Lean/                   Lean 4 layer (full parity, 59 theorems, zero sorry)
│   ├── Gate.lean           Core admissibility + gate soundness/completeness
│   ├── Helmholtz.lean      Concrete Helmholtz model + SDF / Eikonal
│   ├── Constitutional.lean Kleisli Admissibility + Subject Reduction
│   ├── Naturality.lean     Natural transformation + material-agnosticism
│   ├── Activation.lean     Engine activation profiles (sheaf section)
│   ├── DIBKleisli.lean     DIB monad + 3 monad laws + Kleisli assoc
│   ├── lakefile.lean       Lake build configuration
│   └── lean-toolchain      Lean 4 version pin (v4.14.0)
├── Haskell/                Kleisli monad + Rust FFI bridge
│   ├── UMST.hs             Tensor types + pure reference gate
│   ├── KleisliDIB.hs       Categorical DIB monad
│   ├── SDFGate.hs          SDF / FRep interpretation of the gate
│   ├── FFI.hs              Foreign function interface to Rust
│   └── test/Test.hs        QuickCheck property tests (gate + SDF)
├── ffi-bridge/             Thin C-ABI wrapper over umst-core
│   ├── src/lib.rs          extern "C" exports
│   └── include/umst_ffi.h  C header
├── Docs/                   Extended documentation
│   ├── Architecture-Invariants.md
│   ├── FP-Primer.md        52-concept FP / Category Theory / SDF glossary
│   ├── OnePager-Categorical.tex
│   └── Video-Demo-Placeholder.md
├── PROOF-STATUS.md         Per-theorem cross-layer verification index
├── Cargo.toml              Workspace linking to Rust kernel
├── shell.nix               Reproducible build environment (Nix)
└── README.md               This file
```

## What Is Verified

| Claim | Mechanized in |
|-------|--------------|
| Four gate invariants (mass, Clausius-Duhem, hydration, strength) | `Agda/Gate.agda`, `Coq/Gate.v`, `Lean/Gate.lean`, `Haskell/UMST.hs` |
| Gate is material-agnostic (naturality) | `Agda/Naturality.agda`, `Lean/Naturality.lean`, `Lean/Activation.lean` |
| Subject Reduction; Kleisli Admissibility (N-step safety) | `Coq/Constitutional.v`, `Lean/Constitutional.lean` |
| SDF / FRep interpretation; CSG decomposition; Eikonal | `Agda/Gate.agda §7`, `Agda/Helmholtz.agda §6`, `Lean/Helmholtz.lean`, `Haskell/SDFGate.hs` |
| Full Lean 4 mechanization | `Lean/` (6 modules, 59 theorems, zero sorry) |

Four independent proof layers (Agda, Coq, Lean 4, Haskell QuickCheck) verify the same invariants. See `PROOF-STATUS.md` for the complete per-theorem index across all layers.

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
│  umst-prototype-2a/prototype/src/rust/core                      │
│  ──────────────────────────────────────────                     │
│  PhysicsKernel, MixTensor, KleisliArrow<A,B>, gate_server      │
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
| Lean 4 | 4.14.0 | Independent proof layer (Mathlib4) |
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

# 4. Build Lean 4 proofs
cd Lean && lake build UMST && cd ..

# 5. Build Haskell bridge and run property tests
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

The formal proofs establish properties of an abstract mathematical model.
The Rust kernel now includes `KleisliArrow<A,B>` (`tensors/kleisli.rs`)
implementing the admissibility monad with bind, join, and composition —
the runtime backing for the categorical proofs here. Correspondence is validated by:

- Property-based tests (Haskell QuickCheck) that generate random states,
  run both the pure Haskell gate and the Rust gate via FFI, and assert
  identical accept/reject decisions
- The Coq-extracted OCaml serves as an independent reference implementation
- The Rust `KleisliArrow` tests verify monad left/right identity and
  short-circuit behavior, mirroring the formal monad law proofs

## License

MIT. See [LICENSE](LICENSE).

## Citation

If you use this work, please cite both the formal verification layer and the
underlying Rust kernel:

```
Shyamsundar, S., Shenbagamoorthy, S. P. (2026).
UMST-Formal: Categorical Verification of Physics-Gated Material State Transitions.
```
