# Architecture Invariants

This document describes the empirical basis for the four gate invariants and their
derivation from field observation. Each invariant was identified inductively — observed
to hold consistently across multiple material systems before being formalised as a
constraint. The formal proofs in this repository verify that the Rust implementation
is consistent with those constraints.

## 1. Field Origins

The table below maps observed material behaviour to the corresponding formal invariant.
Materials tested include variable earth, lime mortar, masonry, and recycled-aggregate
concrete (RAC).

| Observation | Material System | Invariant | Formal Statement |
|-------------|----------------|-----------|-----------------|
| Workability window closes abruptly; paste cannot be reworked once hydration crosses a threshold | OPC / blended cement | Hydration irreversibility | `α_new ≥ α_old` |
| Carbonation front advances at super-linear rates; strength gain never reverses in undamaged specimens | Lime mortar, RAC | Strength monotonicity | `fc_new ≥ fc_old` |
| Batch density remains stable within a band across curing; gross jumps indicate measurement error or material substitution | All systems | Mass conservation | `\|ρ_new − ρ_old\| < δ` |
| Exothermic heat release during hydration; free energy decreases monotonically | Cement paste | Clausius-Duhem dissipation | `D_int = −ρ · ψ̇ ≥ 0` |
| Interfacial crystal interlock is binary — it forms irreversibly or it does not; partial interlock is mechanically unstable | Masonry, earth-lime | Gate decidability | `gate : State² → Dec Admissible` |
| Path-dependent rheology: identical mix proportions yield different workability depending on mixing history | Earth, RAC | State-dependence of transitions | Kleisli composition in `StateT UMST IO` |

## 2. Derivation Methodology

Each constraint was identified inductively from observed failure modes that existing
linear and semi-empirical models failed to predict: abrupt workability closure at
hydration thresholds, super-linear carbonation front advance, density anomalies
caused by aggregate substitution, and irreversible exothermic free-energy release.
In each case the constraint was observed to hold consistently across chemically
dissimilar material systems before being encoded as a gate condition.

The Discovery-Invention-Build (DIB) cycle describes this trajectory formally: field
observation identifies the constraint; formalisation encodes it as a gate predicate;
implementation tests it against new batches. The formal verification layer closes
that loop by proving mathematical consistency.

The DIB cycle is itself modelled as a Kleisli category in `Agda/DIB-Kleisli.agda`,
making the derivation methodology a first-class object within the formal system.

## 3. Correspondence Table

Type correspondence across the five layers (four formal + one implementation):

| Concept | Rust (`umst-core`) | Agda | Coq | Lean 4 | Haskell |
|---------|-------------------|------|-----|--------|---------|
| Material state | `ThermodynamicState` | `ThermodynamicState` (record) | `thermo_state` (Record) | `ThermodynamicState` (structure) | `ThermodynamicState` (data) |
| Gate decision | `ThermodynamicFilter::check_transition` | `gate : State → State → Dec Admissible` | `gate_check : state → state → bool` | `gateCheck : State → State → Bool` | `gateCheck :: State -> State -> Double -> AdmissibilityResult` |
| Admissibility proof | `accepted: bool` (runtime) | `Admissible` (dependent record) | `admissible` (Prop) | `Admissible` (structure) | `accepted` field of `AdmissibilityResult` |
| Mass conservation | `density_check()` | `mass-conserved` field | `mass_conserved` hypothesis | `massConserved` field | `massConserved` field |
| Clausius-Duhem | `dissipation_check()` | `dissipation-nonneg` field | `dissipation_nonneg` hypothesis | `dissipNonneg` field | `energyPositive` field |
| Hydration irreversibility | `hydration_check()` | `hydration-monotone` field | `hydration_monotone` hypothesis | `hydrationMono` field | `hydrationOk` field |
| Strength monotonicity | `strength_check()` | `strength-monotone` field | `strength_monotone` hypothesis | `strengthMono` field | `strengthOk` field |
| Material class | `MaterialType` enum | `MaterialClass` data | `material_class` Inductive | `MaterialClass` inductive | `MaterialType` ADT |
| DIB loop | `Engine::step()` | Kleisli morphism in `Kl(StateT)` | — | `DIBMonad` Kleisli in `DIBKleisli.lean` | `dib :: Kleisli (StateT UMST IO)` |
| FFI surface | `extern "C"` in `lib.rs` | — | — | — | `foreign import ccall` in `FFI.hs` |
