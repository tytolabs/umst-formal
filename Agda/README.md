# Agda Layer — Dependent-Type Proofs

Dependent-type proofs of the four thermodynamic gate invariants and the categorical structure underlying the UMST kernel.

## Prerequisites

- Agda **2.6.4+** with **agda-stdlib 2.0+** (packaging varies; Homebrew may ship **2.8** with a bundled stdlib — see `PROOF-STATUS.md` proof-layers table)

## Build

```bash
make check    # type-checking IS the proof
make html     # browsable HTML documentation
make clean    # remove build artefacts
```

## Modules

| Module | Purpose |
|--------|---------|
| `Gate.agda` | Core admissible-state predicate, gate decision procedure, and Theorem 1 (forward hydration is admissible) |
| `Naturality.agda` | Proof that the gate commutes with material-class functors (natural transformation) |
| `DIB-Kleisli.agda` | Discovery-Invention-Build loop as a Kleisli category over the state monad |
| `Activation.agda` | Material activations as dependent types indexed by `MaterialClass` |

## Mathematical Overview

The Agda layer establishes three category-theoretic results:

1. **Naturality** — The gate `G : ThermodynamicState² → Bool` is a natural transformation: `G ∘ (F × F) ≡ G` for any material-class functor `F`.  This proves the gate is material-agnostic.

2. **Kleisli structure** — The DIB methodology forms a Kleisli category `Kl(StateT UMST IO)` where discovery, invention, and build are composable morphisms preserving the admissibility predicate.

3. **Monoidal conservation** — Mass conservation is encoded as a monoidal constraint on the tensor product of state spaces, ensuring `|ρ_new − ρ_old| < δ` is preserved under composition of transitions.
