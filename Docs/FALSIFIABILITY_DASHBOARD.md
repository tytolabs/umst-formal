<!--
SPDX-License-Identifier: MIT
-->

# Falsifiability dashboard — `umst-formal`

What can be refuted here, what is assumed once, what is a named shell, and what lives outside the proof artifact. Tables: [`PROOF-STATUS.md`](../PROOF-STATUS.md). Axiom audit: [`FORMAL_FOUNDATIONS.md`](../FORMAL_FOUNDATIONS.md). Loaded Economic names: [`SAFETY-LIMITS.md`](../SAFETY-LIMITS.md).

---

## Core L₀ (default `lake` roots, excluding `Economic/*`)

| Claim class | Status | Where checked |
|-------------|--------|---------------|
| Gate admissibility (`Admissible`, `AdmissibleN`) | Machine-checked | `Gate.lean`, `Constitutional.lean` |
| Kleisli composition / graded mass budget | Machine-checked | `Constitutional.lean`; `Gate.admissibleN_compose` |
| Material-agnostic gate, naturality square | Machine-checked | `Naturality.lean` — `gateMaterialAgnostic`, `naturalitySquare` |
| Helmholtz / activation / fibered engines | Machine-checked | `Helmholtz.lean`, `Activation.lean`, `FiberedActivation.lean` |
| DIB artifact semantics ↔ `gateCheck` | Machine-checked | `DIBKleisli.lean` (opaque `DIBState`, `discover` / `invent` / `build`) |
| Landauer / erasure layer | **Axiom** `physicalSecondLaw` + derived lemmas | `LandauerLaw.lean`, `LandauerExtension.lean`, `MeasurementCost.lean` |
| Finite Shannon / mutual information (product case) | Machine-checked | `InfoTheory.lean` |
| Graph, convergence, Galois gate, enriched admissibility | Machine-checked | `GraphProperties.lean`, `Convergence.lean`, `GaloisGate.lean`, `EnrichedAdmissibility.lean` |
| Monoidal state, accuracy–safety separation | Machine-checked | `MonoidalState.lean`, `SeparationBound.lean` |
| Landauer–Einstein SI brackets | Machine-checked | `LandauerEinsteinBridge.lean` |

---

## Economic meso-layer (`Lean/Economic/`)

Classical lemmas over the gate carrier and Shannon/Landauer bookkeeping; **no** new physics `axiom`. See `SAFETY-LIMITS.md` for loaded names (“hallucination”, “lie”, etc.).

| Module | Status | Notes |
|--------|--------|-------|
| `EconomicDomain` | Definitions only | Carrier definitions; 0 theorems |
| `EconomicTemperature` | Machine-checked | Shannon–Landauer economic temperature |
| `BurdenRecursionIsAdmissible` | Machine-checked | Burden step vs `Admissible` |
| `StochasticBurdenExpectation` | Machine-checked | Two-point mean, geometric decay, scale lemmas |
| `KleisliAdmissibilityComposition` | Machine-checked | Economic Kleisli typing / fold |
| `NPVIsSpecialCaseOfThermodynamicBurden` | Machine-checked | Burden iterate without entropy |
| `SelfReferentialEconomicTensor` | Machine-checked | One-step and iterate strict decrease |
| `DynamicEpsilonCalibration` | **Functional shell** | User-supplied `f : ℝ → ℝ`; no live data |
| `ThermodynamicUncertaintyCertificate` | Machine-checked | Certificate under stated hypotheses |
| `PhysicsConstrainedAI` | Machine-checked | Proposal well-typed vs gate |
| `EpistemicSensingModule` | Machine-checked | Product joint → mutual information zero |
| `HorizonAwareGrounding` | Machine-checked | Local/global convex blend in interval |
| `CollectiveCoherenceCost` | Machine-checked | Collective penalty nonneg |
| `CreativeExplorationTolerance` | Machine-checked | Admission vs admitted + tolerance |
| `CreativityBudget` | Machine-checked | Budget algebra |
| `NuanceIsolator` | Machine-checked | Cost-split identities |
| `HallucinationDetector` | **Surrogate predicate** | `InfoThreshold` parameter — Shannon alarm, not an NN |
| `LowEntropyLieDetector` | **Surrogate predicate** | Declared entropy vs adoption MI — not a deployment detector |

---

## Haskell / Agda / Coq / Rust

| Layer | Falsifiability role |
|-------|---------------------|
| **Haskell** `prop_*` | Computational consistency vs pure reference model; **33** properties in `Haskell/test/Test.hs` (`cabal test umst-properties`). `landauer-einstein-sanity`: Rational check vs Lean bracket. See `PROOF-STATUS.md` § Haskell. |
| **Agda / Coq** | Parallel postulate/lemma stories; Agda default `make check` may omit `--safe` — see `PROOF-STATUS.md`. |
| **ffi-bridge** | Empirical C-ABI alignment; not a proof obligation. See `Docs/PROOF-REPLAY.md`. |

---

## Out of this artifact

| Claim class | Status |
|-------------|--------|
| External empirical datasets | **Not** mechanized here |
| Deployment safety of ML systems or market participants | **Not** guaranteed |
| Full quantum double-slit package | Separate artifact `umst-formal-double-slit` (indexed in `PROOF-STATUS.md`) |

---

## Rule

If a statement is not in the `UMST` Lean roots inventory (`PROOF-STATUS.md` § Lean 4 Layer Summary, grounded in `Lean/lakefile.lean`), treat it as **documentation or analogy** until promoted.
