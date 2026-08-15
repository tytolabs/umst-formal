/-
  UMST-Formal: CoordinationCostP6.lean

  **P6 formal spine prep** — thinnest extension of A7 `CoordinationCost` toward A10
  `SemanticResponse` (`mi_deficit` · `understanding_cost`) and L10 colimit obligations.

  Status: PREP / PARTIAL — definitions + obligation index + A10 gate bind stubs (G75-L07 · N40-L01).
  Does **not** import `Gate.lean` or discharge epistemic→thermo bridge or `gate<SemanticResponse>`.

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

-- ================================================================
-- SECTION 1b: A10 SemanticResponse gate bind (G75-L07 deepen)
-- ================================================================

/-- A10 `SemanticResponse` draft — mirrors M6 scaffold `SemanticResponse.rs.txt`. -/
structure SemanticResponseDraft where
  consistencyDefect : ℝ
  miDeficitBits : ℝ
  understandingCostJoules : ℝ
  miWeight : ℝ
  understandingWeight : ℝ

/-- Core dissipation leg: `−consistency_defect` benefit. -/
noncomputable def semanticDissipation (r : SemanticResponseDraft) : ℝ :=
  -r.consistencyDefect

/-- Core `power_input` leg: `λ·mi_deficit + μ·understanding_cost`. -/
noncomputable def semanticPowerInput (r : SemanticResponseDraft) : ℝ :=
  r.miWeight * r.miDeficitBits + r.understandingWeight * r.understandingCostJoules

/-- Net dissipation `σ_net = dissipation − power_input` (gate conjunct input). -/
noncomputable def semanticNetDissipation (r : SemanticResponseDraft) : ℝ :=
  semanticDissipation r - semanticPowerInput r

/-- Domain conjunct — mirrors Rust `semantic_cost_legs_domain_valid`. -/
def semanticDomainValid (r : SemanticResponseDraft) : Prop :=
  0 ≤ r.consistencyDefect ∧ 0 ≤ r.miDeficitBits ∧ 0 ≤ r.understandingCostJoules

/-- `mi_deficit` gate domain — domain conjunct + nonneg calibration weights. -/
def miDeficitGateDomainValid (r : SemanticResponseDraft) : Prop :=
  semanticDomainValid r ∧ 0 ≤ r.miWeight ∧ 0 ≤ r.understandingWeight

/-- Precondition indexed by `P6OpenObligation.mi_deficit_gate` (discharge still OPEN). -/
def miDeficitGatePrecondition (r : SemanticResponseDraft) : Prop :=
  miDeficitGateDomainValid r

/-- Extract P6 cost legs from a semantic response draft. -/
def semanticCostLegs (r : SemanticResponseDraft) : SemanticCostLegDraft where
  miDeficitBits := r.miDeficitBits
  understandingCostJoules := r.understandingCostJoules

/-- Bind `mi_deficit` field to epistemic draft (bits only — no auto-joules). -/
def epistemicMiFromResponse (r : SemanticResponseDraft) : EpistemicMiDeficitDraft where
  deficitBits := r.miDeficitBits

/-- Bind `understanding_cost` field to hypothesis draft (joules declared). -/
def understandingCostFromResponse (r : SemanticResponseDraft) : UnderstandingCostDraft where
  declaredJoules := r.understandingCostJoules

/-- Admissible chair witness — mirrors `SemanticResponse::consistent()`. -/
def consistentResponse : SemanticResponseDraft where
  consistencyDefect := 0
  miDeficitBits := 0
  understandingCostJoules := 0
  miWeight := 1
  understandingWeight := 1

/-- P3 MI shortfall fixture — mirrors `SemanticResponse::mi_shortfall()`. -/
def miShortfallResponse : SemanticResponseDraft where
  consistencyDefect := 0
  miDeficitBits := 1.5
  understandingCostJoules := 0
  miWeight := 1
  understandingWeight := 1

/-- P2 injection fixture — mirrors `SemanticResponse::inconsistent_no_back()`. -/
def inconsistentNoBackResponse : SemanticResponseDraft where
  consistencyDefect := 1
  miDeficitBits := 0
  understandingCostJoules := 0
  miWeight := 1
  understandingWeight := 1

/-- Over-budget understanding cost — mirrors `SemanticResponse::over_budget()`. -/
def overBudgetResponse : SemanticResponseDraft where
  consistencyDefect := 0
  miDeficitBits := 0
  understandingCostJoules := 2
  miWeight := 1
  understandingWeight := 1

/-- Per-field σ contribution ledger — mirrors Rust `SemanticWitnessLegs`. -/
structure SemanticWitnessLegs where
  defectContribution : ℝ
  miContribution : ℝ
  understandingContribution : ℝ

/-- Extract per-field σ contributions — mirrors Rust `witness_legs`. -/
noncomputable def witnessLegs (r : SemanticResponseDraft) : SemanticWitnessLegs where
  defectContribution := -r.consistencyDefect
  miContribution := -r.miWeight * r.miDeficitBits
  understandingContribution := -r.understandingWeight * r.understandingCostJoules

/-- Sum of witness-field σ contributions — mirrors Rust `SemanticWitnessLegs::net`. -/
noncomputable def semanticWitnessLegsNet (legs : SemanticWitnessLegs) : ℝ :=
  legs.defectContribution + legs.miContribution + legs.understandingContribution

/-- P0 degenerate entropy production — cost legs zeroed. -/
noncomputable def entropyProductionP0 (r : SemanticResponseDraft) : ℝ :=
  -r.consistencyDefect

/-- Full three-leg entropy production alias — equals `semanticNetDissipation`. -/
noncomputable def entropyProduction (r : SemanticResponseDraft) : ℝ :=
  semanticWitnessLegsNet (witnessLegs r)

/-- Indexed bind stub — records gate-domain preconditions; full discharge OPEN. -/
structure MiDeficitGateBindStub where
  response : SemanticResponseDraft
  domainValid : miDeficitGateDomainValid response

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
-- SECTION 2b: SemanticResponse gate bind theorems (G75-L07)
-- ================================================================

theorem semanticCostLegs_domain (r : SemanticResponseDraft) (h : semanticDomainValid r) :
    semanticCostLegsDomainValid (semanticCostLegs r) := by
  unfold semanticDomainValid semanticCostLegs semanticCostLegsDomainValid at *
  exact ⟨h.2.1, h.2.2⟩

theorem epistemicMiFromResponse_deficit (r : SemanticResponseDraft) :
    (epistemicMiFromResponse r).deficitBits = r.miDeficitBits :=
  rfl

theorem understandingCostFromResponse_joules (r : SemanticResponseDraft) :
    (understandingCostFromResponse r).declaredJoules = r.understandingCostJoules :=
  rfl

theorem semanticNetDissipation_def (r : SemanticResponseDraft) :
    semanticNetDissipation r = -r.consistencyDefect - semanticPowerInput r := by
  unfold semanticNetDissipation semanticDissipation semanticPowerInput
  ring

theorem semanticPowerInput_unit_weights (r : SemanticResponseDraft)
    (hMiW : r.miWeight = 1) (hUndW : r.understandingWeight = 1) :
    semanticPowerInput r = r.miDeficitBits + r.understandingCostJoules := by
  unfold semanticPowerInput
  simp [hMiW, hUndW]

theorem consistentResponse_net_zero :
    semanticNetDissipation consistentResponse = 0 := by
  unfold consistentResponse semanticNetDissipation semanticDissipation semanticPowerInput
  norm_num

theorem consistentResponse_domain :
    miDeficitGatePrecondition consistentResponse := by
  unfold miDeficitGatePrecondition miDeficitGateDomainValid semanticDomainValid consistentResponse
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

theorem miShortfallResponse_net :
    semanticNetDissipation miShortfallResponse = -1.5 := by
  unfold miShortfallResponse semanticNetDissipation semanticDissipation semanticPowerInput
  norm_num

theorem miShortfallResponse_domain :
    miDeficitGatePrecondition miShortfallResponse := by
  unfold miDeficitGatePrecondition miDeficitGateDomainValid semanticDomainValid miShortfallResponse
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

noncomputable def understandingFloorFromResponse? {n m : ℕ}
    (r : SemanticResponseDraft) (witness : Option (PhysicalMiBridgeWitness n m)) (T : ℝ) :
    Option ℝ :=
  epistemicUnderstandingFloorJoules? (epistemicMiFromResponse r) witness T

theorem understandingFloorFromResponse_some {n m : ℕ}
    (r : SemanticResponseDraft) (w : PhysicalMiBridgeWitness n m) (T : ℝ)
    (h : w.declaredDeficitBits = r.miDeficitBits) :
    understandingFloorFromResponse? r (some w) T =
      some (coordinationSavingJoules r.miDeficitBits T) := by
  unfold understandingFloorFromResponse? epistemicMiFromResponse
  exact epistemicUnderstandingFloor_some (epistemicMiFromResponse r) w T (by simpa using h)

theorem understandingFloorFromResponse_none {n m : ℕ}
    (r : SemanticResponseDraft) (T : ℝ) :
    @understandingFloorFromResponse? n m r none T = none := by
  unfold understandingFloorFromResponse?
  exact epistemicUnderstandingFloor_none (epistemicMiFromResponse r) T

/-- Build indexed gate bind stub from a domain-valid response. -/
def mkMiDeficitGateBindStub (r : SemanticResponseDraft)
    (h : miDeficitGateDomainValid r) : MiDeficitGateBindStub :=
  { response := r, domainValid := h }

-- ================================================================
-- SECTION 2c: mi_deficit_gate witness-leg bind (N40-L01)
-- ================================================================

theorem semanticDissipation_eq_neg_defect (r : SemanticResponseDraft) :
    semanticDissipation r = -r.consistencyDefect := by
  unfold semanticDissipation
  rfl

theorem witnessLegs_net (r : SemanticResponseDraft) :
    semanticWitnessLegsNet (witnessLegs r) = semanticNetDissipation r := by
  unfold semanticWitnessLegsNet witnessLegs semanticNetDissipation
    semanticDissipation semanticPowerInput
  ring

theorem entropyProduction_eq_semanticNet (r : SemanticResponseDraft) :
    entropyProduction r = semanticNetDissipation r :=
  witnessLegs_net r

theorem entropyProductionP0_eq_neg_defect (r : SemanticResponseDraft) :
    entropyProductionP0 r = -r.consistencyDefect := by
  unfold entropyProductionP0
  rfl

theorem witnessLegs_mi_shortfall :
    let legs := witnessLegs miShortfallResponse
    legs.defectContribution = 0 ∧ legs.miContribution = -1.5 ∧
      legs.understandingContribution = 0 := by
  dsimp [witnessLegs, miShortfallResponse]
  norm_num

theorem inconsistentNoBackResponse_net :
    semanticNetDissipation inconsistentNoBackResponse = -1 := by
  unfold inconsistentNoBackResponse semanticNetDissipation semanticDissipation semanticPowerInput
  norm_num

theorem inconsistentNoBackResponse_domain :
    miDeficitGatePrecondition inconsistentNoBackResponse := by
  unfold miDeficitGatePrecondition miDeficitGateDomainValid semanticDomainValid
    inconsistentNoBackResponse
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

theorem overBudgetResponse_net :
    semanticNetDissipation overBudgetResponse = -2 := by
  unfold overBudgetResponse semanticNetDissipation semanticDissipation semanticPowerInput
  norm_num

theorem overBudgetResponse_domain :
    miDeficitGatePrecondition overBudgetResponse := by
  unfold miDeficitGatePrecondition miDeficitGateDomainValid semanticDomainValid overBudgetResponse
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

theorem entropyProductionP0_matches_net_at_zero_cost_legs
    (r : SemanticResponseDraft) (hmi : r.miDeficitBits = 0) (hu : r.understandingCostJoules = 0) :
    entropyProductionP0 r = semanticNetDissipation r := by
  unfold entropyProductionP0 semanticNetDissipation semanticDissipation semanticPowerInput
  simp [hmi, hu]

theorem mkMiDeficitGateBindStub_response (r : SemanticResponseDraft)
    (h : miDeficitGateDomainValid r) :
    (mkMiDeficitGateBindStub r h).response = r :=
  rfl

theorem mkMiDeficitGateBindStub_domain (r : SemanticResponseDraft)
    (h : miDeficitGateDomainValid r) :
    miDeficitGateDomainValid (mkMiDeficitGateBindStub r h).response :=
  h

theorem miDeficitGateBindStub_precondition (stub : MiDeficitGateBindStub) :
    miDeficitGatePrecondition stub.response :=
  stub.domainValid

theorem semanticPowerInput_nonneg (r : SemanticResponseDraft)
    (h : miDeficitGateDomainValid r) :
    0 ≤ semanticPowerInput r := by
  unfold semanticPowerInput miDeficitGateDomainValid semanticDomainValid at *
  rcases h with ⟨⟨_hdef, hmi, hu⟩, hMiW, hUndW⟩
  exact add_nonneg (mul_nonneg hMiW hmi) (mul_nonneg hUndW hu)

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
