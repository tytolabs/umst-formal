-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: SemanticEconomicModules.lean

  **HCOM-003 — Economic-like semantic modules** (Human Communication Blueprint §3.2).

  Parameterized `MisunderstandingBurden`, `HallucinationThreshold` (semantic),
  `CreativityMeaningSlack`, and `InterpretationTolerance` — same bookkeeping
  pattern as `Lean/Economic/` meso-layer predicates.

  **Not claimed:** neural NLU, semantic truth detection, or deployed safety products.
  See `SAFETY-LIMITS.md`.

  Single-axiom discipline: zero new Lean `axiom` declarations.
  L₀ boundary: imports `SemanticSecondLaw` + Economic scaffolding only.
-/

import SemanticSecondLaw
import LandauerLaw
import Economic.EconomicDomain
import Economic.CreativityBudget
import Economic.EconomicTemperature
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace UMST.SemanticEconomics

open Rat Real UMST.SemanticSecondLaw UMST.Economics UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist

-- ================================================================
-- SECTION 1: Parameter records (blueprint §3.2)
-- ================================================================

/-- User-scoped misunderstanding charge on the communicative burden axis (`ℚ`). -/
structure MisunderstandingBurden where
  /-- Cumulative misunderstanding charge (Economic burden bookkeeping units). -/
  charge : ℚ

/-- Semantic hallucination alarm threshold on adoption-side Shannon information (nats).
    Classical surrogate — not a neural hallucination detector. -/
structure HallucinationThreshold where
  θ : ℝ

/-- Creative slack for meaning updates (semantic analogue of `CreativeSlack`). -/
structure CreativityMeaningSlack where
  Δ : ℚ

/-- Interpretation tolerance band ε for near-neutral semantic transitions. -/
structure InterpretationTolerance where
  ε : ℝ

/-- Bundled semantic economic parameters (catalog fixture row). -/
structure SemanticEconomicParams where
  misunderstanding : MisunderstandingBurden
  hallucination : HallucinationThreshold
  creativity : CreativityMeaningSlack
  tolerance : InterpretationTolerance

-- ================================================================
-- SECTION 2: Predicates (parameterized — user-scoped)
-- ================================================================

/-- Misunderstanding charge stays within the declared budget ceiling. -/
def withinMisunderstandingBudget (b : MisunderstandingBurden) (maxCharge : ℚ) : Prop :=
  b.charge ≤ maxCharge

/-- Semantic hallucination alarm: adoption marginal entropy exceeds threshold `θ`. -/
def semanticHallucinationAlarm {n m : ℕ} (th : HallucinationThreshold) (J : JointDist n m) : Prop :=
  th.θ < adoptionInformation J

/-- Meaning-update charge within admitted baseline plus creative slack `Δ`. -/
def withinCreativityMeaningSlack (Q Q_admitted : ℚ) (slack : CreativityMeaningSlack) : Prop :=
  withinCreativityBudget Q Q_admitted slack.Δ

/-- Interpretation drift `δ` lies inside the declared tolerance band. -/
def interpretationWithinTolerance (δ : ℝ) (tol : InterpretationTolerance) : Prop :=
  |δ| ≤ tol.ε

/-- Consistency defect within catalog-loaded interpretation tolerance. -/
def meaningConsistencyWithinTolerance (consistencyDefect : ℝ) (params : SemanticEconomicParams) : Prop :=
  interpretationWithinTolerance consistencyDefect params.tolerance

-- ================================================================
-- SECTION 3: Default parameter fixtures (catalog witnesses)
-- ================================================================

/-- Default max misunderstanding before gate escalation (neutral dialogue). -/
def defaultMaxMisunderstandingCharge : ℚ := 1

/-- Default semantic hallucination threshold θ = ln 2 nats (one bit). -/
noncomputable def defaultHallucinationTheta : ℝ := Real.log 2

/-- Default creative meaning slack Δ = 0 (no extra slack). -/
def defaultCreativitySlackDelta : ℚ := 0

/-- Default interpretation tolerance ε_int (matches `Web.defaultIntTolerance` scale). -/
noncomputable def defaultInterpretationEpsilon : ℝ := 1 / (10 ^ 9 : ℕ)

/-- Rational gate-path ε (decidable hot-check mirror of `defaultInterpretationEpsilon`). -/
def defaultInterpretationEpsilonQ : ℚ := 1 / (10 ^ 9 : ℕ)

def defaultMisunderstandingBurden : MisunderstandingBurden :=
  { charge := 0 }

noncomputable def defaultHallucinationThreshold : HallucinationThreshold :=
  { θ := defaultHallucinationTheta }

def defaultCreativityMeaningSlack : CreativityMeaningSlack :=
  { Δ := defaultCreativitySlackDelta }

noncomputable def defaultInterpretationTolerance : InterpretationTolerance :=
  { ε := defaultInterpretationEpsilon }

noncomputable def defaultSemanticEconomicParams : SemanticEconomicParams :=
  { misunderstanding := defaultMisunderstandingBurden
    hallucination := defaultHallucinationThreshold
    creativity := defaultCreativityMeaningSlack
    tolerance := defaultInterpretationTolerance }

-- ================================================================
-- SECTION 4: Catalog read hook (stub — gate loads fixture until JSON lookup)
-- ================================================================

/-- **Catalog read hook (stub):** runtime semantic gate loads threshold bundle from
    catalog witnesses; until JSON lookup lands, returns the canonical Lean fixture. -/
noncomputable def catalogReadSemanticEconomicParams : SemanticEconomicParams :=
  defaultSemanticEconomicParams

/-- Gate-facing alias — reads bundled parameters at microsecond-class decision time. -/
noncomputable def gateReadSemanticEconomicParams : SemanticEconomicParams :=
  catalogReadSemanticEconomicParams

/-- Interpretation drift δ lies inside the declared tolerance band (rational gate path). -/
def interpretationWithinToleranceQ (δ ε : ℚ) : Prop :=
  -ε ≤ δ ∧ δ ≤ ε

/-- Hard gate check: consistency defect within catalog-loaded tolerance (decidable ℚ path). -/
def meaningGateReadsTolerance (consistencyDefect : ℚ) : Bool :=
  let ε := defaultInterpretationEpsilonQ
  decide (-ε ≤ consistencyDefect ∧ consistencyDefect ≤ ε)

theorem meaningGateReadsTolerance_zero :
    meaningGateReadsTolerance 0 = true := by
  native_decide

-- ================================================================
-- SECTION 5: Witness theorems (0 sorry — catalog / gate fixtures)
-- ================================================================

theorem defaultMisunderstanding_withinBudget :
    withinMisunderstandingBudget defaultMisunderstandingBurden defaultMaxMisunderstandingCharge := by
  unfold withinMisunderstandingBudget defaultMisunderstandingBurden defaultMaxMisunderstandingCharge
  norm_num

theorem semanticHallucination_product_off {n m : ℕ} (p : ProbDist n) (q : ProbDist m)
    (hq : shannonEntropy q ≤ defaultHallucinationThreshold.θ) :
    ¬ semanticHallucinationAlarm defaultHallucinationThreshold (JointDist.productJoint p q) := by
  intro h
  unfold semanticHallucinationAlarm at h
  rw [adoptionInformation_product] at h
  exact not_lt.mpr hq h

theorem defaultCreativitySlack_zero :
    withinCreativityMeaningSlack 0 0 defaultCreativityMeaningSlack := by
  unfold withinCreativityMeaningSlack defaultCreativityMeaningSlack defaultCreativitySlackDelta
  exact (creativityBudget_refl 0 0).mpr (le_refl 0)

theorem defaultInterpretation_zero_within :
    interpretationWithinTolerance 0 defaultInterpretationTolerance := by
  unfold interpretationWithinTolerance defaultInterpretationTolerance defaultInterpretationEpsilon
  rw [abs_zero]
  norm_num

theorem catalogRead_eq_default :
    catalogReadSemanticEconomicParams = defaultSemanticEconomicParams := rfl

theorem defaultParams_consistency_within_tolerance :
    meaningConsistencyWithinTolerance 0 defaultSemanticEconomicParams :=
  defaultInterpretation_zero_within

/-- Catalog witness marker: HCOM-003 semantic economic modules are present. -/
theorem semantic_economic_modules_witness : True := trivial

end UMST.SemanticEconomics
