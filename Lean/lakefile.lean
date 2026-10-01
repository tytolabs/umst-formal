-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import Lake
open Lake DSL

package «umst-formal» where
  -- Package name is provided by the quoted identifier above.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-
  **Lean `roots` (65 modules)** — default `lake build` closure for `UMST`.  Science-cartridge layout:
  `Core.*` (universal laws), `Concrete.*` (OPC cement), `Compat.*` (legacy `UMST` API).
  (Wave 6.5.2 meso-layer).  Sole physics `axiom`: `LandauerLaw.physicalSecondLaw`;
  tier-tagged crypto axioms live under `Crypto/` (GROUND-1 / §14bis.f-S-0).

  Examples (single-module builds):
    lake build UMST.Compat.Gate
    lake build UMST.Economic.EconomicTemperature
  Full inventory + theorem counts: `PROOF-STATUS.md` § Lean 4 Layer Summary; regenerate via
  `python3 scripts/lean_declaration_stats.py`.
-/
/-
  Every `lean_lib` is a `@[default_target]`: `lake build` (and CI) compiles all of them, experiments included.
  A tracked Lean file outside every library must be listed in `lean-unchecked.txt` with its reason
  (`scripts/check_lean_ci_closure.py` enforces this).
-/
/-!
  CHEM-NS-MVP-FORMAL-MESO-DEFECT-CLEAR — SERIAL_ON_LAKEFILE meso acting fiber defect-clear wave.
  Sole writer for `UMST.Chem` lake targets during this SERIAL close. Build: `lake build UMST.Chem`.
  CHEM-FORMAL-MESO-LEAN-CHEM — meso acting chemistry lift (`lake build UMST.Chem`).
  `Chem.+` glob: later `Chem/*.lean` compile without re-editing this lakefile.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Declared before `lean_lib «UMST»` so the `UMST.Chem` target is not shadowed.
-/
@[default_target]
lean_lib UMST.Chem where
  roots := #[`Chem.SecondLaw, `Chem.Conservation]
  globs := #[`Chem.+]
  srcDir := "."

/-!
  URGE-FORMAL-MESO-LEAN-ADMIT-KLEISLI — meso acting Urge lift (`lake build UMST.Urge`).
  `Urge.+` glob: later `Urge/*.lean` compile without re-editing this lakefile.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Declared before `lean_lib «UMST»` so the `UMST.Urge` target is not shadowed.
-/
/-!
  Constants (`lake build UMST.Constants`): `Constants.SI` is generated from constants/constants.json by
  scripts/gen_constants.py (exact rationals: cited SI values, measurements with uncertainty, derived constants
  with their proofs); `Constants.SIBridge` identifies them with the real-valued constants of the Landauer chain.
-/
@[default_target]
lean_lib UMST.Constants where
  globs := #[`Constants.+]
  srcDir := "."

@[default_target]
lean_lib UMST.Urge where
  roots := #[`Urge.AdmitKleisli]
  globs := #[`Urge.+]
  srcDir := "."

/-!
  FORMAL-COMBINATOR-LAKEFILE — `Solver.CombinatorLaws` (`lake build UMST.Solver`).
  `Solver.+` glob: later `Solver/*.lean` compile without re-editing this lakefile.
  Prelude-only combinator laws; no project axioms added here.
-/
@[default_target]
lean_lib UMST.Solver where
  roots := #[`Solver.CombinatorLaws]
  globs := #[`Solver.+]
  srcDir := "."

@[default_target]
lean_lib «UMST» where
  roots := #[`Core.Scalar, `Core.State, `Core.Gate, `Core.Constitutional,
    `Concrete.State, `Concrete.Gate,
    `Real.State, `Real.Gate,
    `Concrete.Helmholtz, `Concrete.Powers, `Concrete.PowersVolume, `Concrete.StiffnessTransition,
    `Concrete.MicroMechanics,
    `Concrete.Convergence, `Concrete.GraphProperties,
    `Concrete.Activation, `Concrete.EndConditions, `Concrete.EnrichedAdmissibility, `Concrete.GaloisGate,
    `Compat.Gate, `Compat.Constitutional,
    `MaterialClass, `DIBKleisli, `FormalFoundations,
    `LandauerEinsteinBridge,
    `LandauerLaw, `Process, `OneInequalitySecondLaw, `ConvexPhiDissipation,
    `CoarseGraining, `InfoTheory, `SemanticSecondLaw, `MeaningState, `SemanticFormal, `InterpretationFunctor, `SemanticEconomicModules,
    `ClassicalMeasurementCost, `CoordinationCost, `CoordinationContract, `LandauerExtension, `FiberedActivation, `MonoidalState, `PrimeSpectralGuidance, `PrimeSpectralCategory,
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
    `DEC, `Adjoint, `RegimeSoundness, `JenningsGelSpace,
    `DualLedger, `Excitement, `ExcitementProofs, `WaveShape, `Concrete.PoromechanicsB3, `Concrete.ShrinkageB4,
    `Web, `Web.WebMat]
  srcDir := "."

/-!
  §14bis.f-M-4 — `Behavior.SDFCanonical` (L-M2 stub). Built standalone; optional target
  `lake build Behavior.SDFCanonical` alongside `Memory.MergeSafe` / `Memory.TierDisjoint`.
-/
@[default_target]
lean_lib «Behavior.SDFCanonical» where
  roots := #[`Behavior.SDFCanonical]
  srcDir := "."

/-!
  LEAN-COORD-COST — `CoordinationCostP6` (A10 P6 spine prep). Built standalone;
  not in default `UMST` roots. See `Docs/COORDINATION_COST_P6_SPINE.md`.
-/
@[default_target]
lean_lib «CoordinationCostP6» where
  roots := #[`CoordinationCostP6]
  srcDir := "."

/-!
  §14bis.f-S-0 — L-S0..L-S5 Crypto stubs (`lake build Crypto.LWE` … `Crypto.SanitizePatternCoverage`).
  Shared metadata: `Crypto.CryptoHypothesis` (GROUND-1 provenance records).
-/
@[default_target]
lean_lib «Crypto.CryptoHypothesis» where
  roots := #[`Crypto.CryptoHypothesis]
  srcDir := "."

@[default_target]
lean_lib «Crypto.LWE» where
  roots := #[`Crypto.LWE]
  srcDir := "."

@[default_target]
lean_lib «Crypto.EUF_CMA» where
  roots := #[`Crypto.EUF_CMA]
  srcDir := "."

@[default_target]
lean_lib «Crypto.Collision» where
  roots := #[`Crypto.Collision]
  srcDir := "."

@[default_target]
lean_lib «Crypto.SideChannel» where
  roots := #[`Crypto.SideChannel]
  srcDir := "."

@[default_target]
lean_lib «Crypto.Composability» where
  roots := #[`Crypto.Composability]
  srcDir := "."

@[default_target]
lean_lib «Crypto.SanitizePatternCoverage» where
  roots := #[`Crypto.SanitizePatternCoverage]
  srcDir := "."

/-- Experiments: proofs outside the constitutional core that CI still checks (Track R obligations, experiment
    boundary types). -/
@[default_target]
lean_lib Experiments where
  globs := #[`experiments.+]
