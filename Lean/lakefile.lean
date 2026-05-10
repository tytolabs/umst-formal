import Lake
open Lake DSL

package «umst-formal» where
  -- Package name is provided by the quoted identifier above.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-
  **Lean `roots` (51 modules)** — default `lake build` closure for `UMST`.  Includes the gate/Kleisli
  core, Landauer stack, extensions (monoidal state, separation bound, …), and **`Lean/Economic/`**
  (Wave 6.5.2 meso-layer).  Single project `axiom`: `LandauerLaw.physicalSecondLaw`.

  Examples (single-module builds):
    lake build UMST.Gate
    lake build UMST.Economic.EconomicTemperature
  Full inventory + theorem counts: `PROOF-STATUS.md` § Lean 4 Layer Summary; regenerate via
  `python3 scripts/lean_declaration_stats.py`.
-/
/-
  **Default `roots`** = core formal layer checked by `lake build` (constitutional gate,
  Landauer, DIB, convergence, …).  **Not listed here:** scratch / debug modules such as
  `_check_ext.lean` (local `#print` / `#check` only).  Add a module to `roots` when it
  should participate in CI; optional experiments stay out of the default closure.
-/
lean_lib «UMST» where
  roots := #[`Gate, `Helmholtz, `Constitutional, `Naturality, `Activation, `DIBKleisli, `FormalFoundations,
    `LandauerEinsteinBridge, `GraphProperties, `Powers, `Convergence,
    `GaloisGate, `EnrichedAdmissibility,     `LandauerLaw, `InfoTheory,
    `EndConditions, `MeasurementCost, `LandauerExtension, `FiberedActivation, `MonoidalState,
    `SeparationBound,
    -- Meso-scale Economic layer (Lean/Economic/ folder — Wave 6.5.2)
    `Economic.EconomicDomain,
    `Economic.EconomicTemperature, `Economic.BurdenRecursionIsAdmissible,
    `Economic.StochasticBurdenExpectation, `Economic.DynamicEpsilonCalibration,
    `Economic.SelfReferentialEconomicTensor, `Economic.NPVIsSpecialCaseOfThermodynamicBurden,
    `Economic.HallucinationDetector, `Economic.LowEntropyLieDetector, `Economic.CreativityBudget,
    `Economic.ThermodynamicUncertaintyCertificate, `Economic.PhysicsConstrainedAI,
    `Economic.EpistemicSensingModule, `Economic.KleisliAdmissibilityComposition,
    `Economic.NuanceIsolator, `Economic.HorizonAwareGrounding, `Economic.CollectiveCoherenceCost,
    `Economic.CreativeExplorationTolerance,
    `CreditGreedyOptimal,
    `Dignity,
    `EtaCog,
    `RhoEstimator,
    `MedianConvergence,
    `OrderStatisticsBand,
    `Memory.MergeSafe,
    `Memory.TierDisjoint,
    `DEC, `Adjoint, `RegimeSoundness, `JenningsGelSpace]
  srcDir := "."

/-!
  §14bis.f-M-4 — `Behavior.SDFCanonical` (L-M2 stub). Built standalone; optional target
  `lake build Behavior.SDFCanonical` alongside `Memory.MergeSafe` / `Memory.TierDisjoint`.
-/
lean_lib «Behavior.SDFCanonical» where
  roots := #[`Behavior.SDFCanonical]
  srcDir := "."

/-!
  §14bis.f-S-0 — L-S0..L-S5 Crypto stubs (`lake build Crypto.LWE` … `Crypto.SanitizePatternCoverage`).
-/
lean_lib «Crypto.LWE» where
  roots := #[`Crypto.LWE]
  srcDir := "."

lean_lib «Crypto.EUF_CMA» where
  roots := #[`Crypto.EUF_CMA]
  srcDir := "."

lean_lib «Crypto.Collision» where
  roots := #[`Crypto.Collision]
  srcDir := "."

lean_lib «Crypto.SideChannel» where
  roots := #[`Crypto.SideChannel]
  srcDir := "."

lean_lib «Crypto.Composability» where
  roots := #[`Crypto.Composability]
  srcDir := "."

lean_lib «Crypto.SanitizePatternCoverage» where
  roots := #[`Crypto.SanitizePatternCoverage]
  srcDir := "."
