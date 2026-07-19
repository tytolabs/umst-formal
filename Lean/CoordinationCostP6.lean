/-
  UMST-Formal: CoordinationCostP6.lean

  **P6 formal spine prep** — thinnest extension of A7 `CoordinationCost` toward A10
  `SemanticResponse` (`mi_deficit` · `understanding_cost`) and L10 colimit obligations.

  Status: PREP / PARTIAL — definitions + obligation index only.
  Does **not** import `Gate.lean` or discharge epistemic→thermo bridge.

  Build standalone (not in default `lake build` roots):
    cd egoff/umst-formal/Lean && lake build CoordinationCostP6

  Design: `Docs/COORDINATION_COST_P6_SPINE.md`
-/

import CoordinationCost

open Real UMST.CoordinationCost

namespace UMST.CoordinationCost.P6

-- ================================================================
-- SECTION 1: A10 SemanticResponse floor drafts (reporting only)
-- ================================================================

/-- Epistemic `mi_deficit` draft — bits only; no thermodynamic witness. -/
structure EpistemicMiDeficitDraft where
  deficitBits : ℝ

/-- A10 `understanding_cost` hypothesis leg — joules declared, not auto-derived. -/
structure UnderstandingCostDraft where
  declaredJoules : ℝ

/-- A10 semantic cost legs (P3 hypothesis) — mirrors `SemanticResponse` power_input fields. -/
structure SemanticCostLegDraft where
  miDeficitBits : ℝ
  understandingCostJoules : ℝ

/-- Domain guard for semantic cost legs (M6-C01 prep — not a gate witness). -/
def semanticCostLegsDomainValid (draft : SemanticCostLegDraft) : Prop :=
  0 ≤ draft.miDeficitBits ∧ 0 ≤ draft.understandingCostJoules

/-- Witness that epistemic deficit was promoted via a **physical** MI channel. -/
structure PhysicalMiBridgeWitness (n m : ℕ) where
  channel : PhysicalMiChannel n m
  declaredDeficitBits : ℝ
  deficitMatchesChannel :
    declaredDeficitBits = physicalMiBits channel

/-- Lean-bridge fixture row — pins `coordinationSavingJoules` without a full `JointDist`. -/
structure FixtureGridRow where
  miBits : ℝ
  temperatureKelvin : ℝ
  declaredSavingJoules : ℝ
  savingMatchesFormula :
    declaredSavingJoules = coordinationSavingJoules miBits temperatureKelvin

/-- Epistemic-only report — explicitly **not** a joule projection. -/
structure EpistemicOnlyFloorReport where
  miDeficitBits : ℝ
  hasJouleProjection : Bool

/-- `understanding_cost` draft — Landauer floor proxy when physical bridge is supplied. -/
noncomputable def physicalUnderstandingFloorJoules {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) : ℝ :=
  coordinationSavingJoules w.declaredDeficitBits T

/-- Project joules from epistemic deficit **only** when a physical bridge witness is supplied. -/
noncomputable def epistemicUnderstandingFloorJoules? {n m : ℕ}
    (draft : EpistemicMiDeficitDraft) (witness : Option (PhysicalMiBridgeWitness n m)) (T : ℝ) :
    Option ℝ :=
  witness.bind fun w =>
    if w.declaredDeficitBits = draft.deficitBits then
      some (physicalUnderstandingFloorJoules w T)
    else
      none

/-- Honest A10-shaped report — projection fields only. -/
structure SemanticFloorReport where
  miDeficitBits : ℝ
  temperatureKelvin : ℝ
  understandingCostJoules : ℝ
  isPhysicalProjection : Bool

/-- Build report from a physical bridge witness (always `isPhysicalProjection = true`). -/
noncomputable def mkSemanticFloorReport {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) : SemanticFloorReport where
  miDeficitBits := w.declaredDeficitBits
  temperatureKelvin := T
  understandingCostJoules := physicalUnderstandingFloorJoules w T
  isPhysicalProjection := true

-- ================================================================
-- SECTION 2: Definitional alignment (proved — no new physics)
-- ================================================================

theorem physicalUnderstandingFloor_eq_coordinationSaving {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) :
    physicalUnderstandingFloorJoules w T =
      coordinationSavingJoules w.declaredDeficitBits T :=
  rfl

theorem mkSemanticFloorReport_understandingCost {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) :
    (mkSemanticFloorReport w T).understandingCostJoules =
      coordinationSavingJoules w.declaredDeficitBits T := by
  unfold mkSemanticFloorReport physicalUnderstandingFloorJoules
  rfl

theorem mkSemanticFloorReport_mi_deficit {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) :
    (mkSemanticFloorReport w T).miDeficitBits = w.declaredDeficitBits :=
  rfl

theorem mkSemanticFloorReport_is_physical {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) :
    (mkSemanticFloorReport w T).isPhysicalProjection = true :=
  rfl

/-- Build epistemic-only report — never claims joule projection. -/
noncomputable def mkEpistemicOnlyReport (draft : EpistemicMiDeficitDraft) : EpistemicOnlyFloorReport where
  miDeficitBits := draft.deficitBits
  hasJouleProjection := false

theorem fixtureGridRow_saving (row : FixtureGridRow) :
    row.declaredSavingJoules =
      coordinationSavingJoules row.miBits row.temperatureKelvin :=
  row.savingMatchesFormula

theorem fixtureGridRow_eq_mkReport (row : FixtureGridRow) :
    row.declaredSavingJoules = (mkReport row.miBits row.temperatureKelvin).savingJoules := by
  rw [fixtureGridRow_saving, mkReport_saving]

theorem epistemicOnlyReport_no_projection (draft : EpistemicMiDeficitDraft) :
    (mkEpistemicOnlyReport draft).hasJouleProjection = false :=
  rfl

theorem epistemicUnderstandingFloor_some {n m : ℕ}
    (draft : EpistemicMiDeficitDraft) (w : PhysicalMiBridgeWitness n m) (T : ℝ)
    (h : w.declaredDeficitBits = draft.deficitBits) :
    epistemicUnderstandingFloorJoules? draft (some w) T =
      some (coordinationSavingJoules draft.deficitBits T) := by
  unfold epistemicUnderstandingFloorJoules? physicalUnderstandingFloorJoules
  simp [h]

theorem epistemicUnderstandingFloor_none {n m : ℕ}
    (draft : EpistemicMiDeficitDraft) (T : ℝ) :
    @epistemicUnderstandingFloorJoules? n m draft none T = none := by
  rfl

theorem epistemicUnderstandingFloor_mismatch {n m : ℕ}
    (draft : EpistemicMiDeficitDraft) (w : PhysicalMiBridgeWitness n m) (T : ℝ)
    (h : w.declaredDeficitBits ≠ draft.deficitBits) :
    epistemicUnderstandingFloorJoules? draft (some w) T = none := by
  unfold epistemicUnderstandingFloorJoules?
  simp [h]

theorem physicalUnderstandingFloor_nonneg {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ)
    (hmi : 0 ≤ w.declaredDeficitBits) (hT : 0 ≤ T) :
    0 ≤ physicalUnderstandingFloorJoules w T := by
  unfold physicalUnderstandingFloorJoules
  exact coordinationSaving_nonneg w.declaredDeficitBits T hmi hT

theorem semanticCostLegsDomainValid_mk {mi u : ℝ}
    (hmi : 0 ≤ mi) (hu : 0 ≤ u) :
    semanticCostLegsDomainValid ⟨mi, u⟩ := by
  unfold semanticCostLegsDomainValid
  exact ⟨hmi, hu⟩

theorem mkSemanticFloorReport_agrees_mkReport {n m : ℕ}
    (w : PhysicalMiBridgeWitness n m) (T : ℝ) :
    (mkSemanticFloorReport w T).understandingCostJoules =
      (mkReport w.declaredDeficitBits T).savingJoules := by
  unfold mkSemanticFloorReport physicalUnderstandingFloorJoules mkReport
  rfl

-- ================================================================
-- SECTION 3: P6 open obligations (indexed — no `sorry`)
-- ================================================================

/-- Proof targets for P6 / L10 — deferred beyond A7 scaffold. -/
inductive P6OpenObligation
  | mi_deficit_gate
  | understanding_cost_bounded
  | colimit_universal_floor
  | functor_F_conservative
  | joint_erasure_sub_additive
  | finite_time_excess_bound
  | epistemic_mi_witness
  deriving DecidableEq, Repr

/-- Human-readable labels for receipts / cert tooling. -/
def p6OpenObligationDescription : P6OpenObligation → String
  | .mi_deficit_gate =>
      "mi_deficit as SemanticResponse gate conjunct (A10 P2–P3)"
  | .understanding_cost_bounded =>
      "understanding_cost bounded by coordination floor on physical bridge"
  | .colimit_universal_floor =>
      "L10 colimit cocone preserves coordination Landauer floor"
  | .functor_F_conservative =>
      "conservative F : L10 → L0 does not increase floor projection"
  | .joint_erasure_sub_additive =>
      "joint erasure of correlated registers cheaper than independent sum"
  | .finite_time_excess_bound =>
      "finite-time excess dissipation above isothermal Landauer floor"
  | .epistemic_mi_witness =>
      "epistemic MI bridge witness (L10 fiber) — not physical MI"

/-- Map inherited A7 obligations into the P6 audit index. -/
def fromA7OpenObligation : OpenObligation → P6OpenObligation
  | .joint_erasure_sub_additive => .joint_erasure_sub_additive
  | .finite_time_excess_bound => .finite_time_excess_bound
  | .epistemic_mi_witness => .epistemic_mi_witness

end UMST.CoordinationCost.P6
