# Architecture Invariants — Empirical Grounding

## 1. Empirical Sources

Field observations from seven years of practice at Studio Tyto (variable earth, lime, masonry, recycled-aggregate concrete) mapped to formal invariants:

| Observation | Material System | Invariant | Formal Statement |
|-------------|----------------|-----------|-----------------|
| Workability window closes abruptly; paste cannot be reworked once hydration crosses a threshold | OPC / blended cement | Hydration irreversibility | `α_new ≥ α_old` |
| Carbonation front advances at super-linear rates; strength gain never reverses in undamaged specimens | Lime mortar, RAC | Strength monotonicity | `fc_new ≥ fc_old` |
| Batch density remains stable within a band across curing; gross jumps indicate measurement error or material substitution | All systems | Mass conservation | `\|ρ_new − ρ_old\| < δ` |
| Exothermic heat release during hydration; free energy decreases monotonically | Cement paste | Clausius-Duhem dissipation | `D_int = −ρ · ψ̇ ≥ 0` |
| Interfacial crystal interlock either forms or never does; partial interlock is mechanically unstable | Masonry, earth-lime | Gate decidability | `gate : State² → Dec Admissible` |
| Path-dependent rheology: identical mix proportions yield different workability depending on mixing history | Earth, RAC | State-dependence of transitions | Kleisli composition in `StateT UMST IO` |

## 2. From Tacit Knowledge to Formal Model

The invariants were not designed top-down from continuum mechanics textbooks.  They emerged bottom-up from repeated encounters with failure modes that existing material models could not predict.  The workability window that closes without warning in a recycled-aggregate mix, the carbonation front that invalidates a linear service-life model — these phenomena forced the identification of a minimal set of constraints that any physically valid state transition must satisfy.

The Discovery-Invention-Build (DIB) methodology provided the epistemological frame: field observations (Discovery) yielded candidate invariants; encoding them as a thermodynamic gate (Invention) produced a testable computational model; deploying the gate inside a Rust kernel (Build) allowed iterative validation against new batches and sites.  The formal verification layer (this repository) closes the loop by proving that the gate is mathematically consistent and categorically well-founded.

This trajectory — tacit empirical knowledge → computational invariant → formal proof — is itself modelled as a Kleisli category in the Agda layer (`DIB-Kleisli.agda`), making the methodology a first-class mathematical object within the system it validates.

## 3. Correspondence Table

Type correspondence across the four layers:

| Concept | Rust (`umst-core`) | Agda | Coq | Haskell |
|---------|-------------------|------|-----|---------|
| Material state | `ThermodynamicState` | `ThermodynamicState` (record) | `thermo_state` (Record) | `ThermodynamicState` (data) |
| Gate decision | `ThermodynamicFilter::check_transition` | `gate : State → State → Dec Admissible` | `gate_check : state → state → bool` | `gate :: State -> State -> Bool` |
| Admissibility proof | `accepted: bool` (runtime) | `Admissible` (dependent record) | `admissible` (Prop) | `Admissible` (phantom) |
| Mass conservation | `density_check()` | `mass-conserved` field | `mass_conserved` hypothesis | `massConserved` property |
| Clausius-Duhem | `dissipation_check()` | `dissipation-nonneg` field | `dissipation_nonneg` hypothesis | `dissipationNonneg` property |
| Hydration irreversibility | `hydration_check()` | `hydration-monotone` field | `hydration_monotone` hypothesis | `hydrationMonotone` property |
| Strength monotonicity | `strength_check()` | `strength-monotone` field | `strength_monotone` hypothesis | `strengthMonotone` property |
| Material class | `MaterialType` enum | `MaterialClass` data | `material_class` Inductive | `MaterialType` ADT |
| DIB loop | `Engine::step()` | Kleisli morphism in `Kl(StateT)` | — | `dib :: Kleisli (StateT UMST IO)` |
| FFI surface | `extern "C"` in `lib.rs` | — | — | `foreign import ccall` in `FFI.hs` |
