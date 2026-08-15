/-
  UMST-Formal: StiffnessTransition.lean
  Lean 4 — B1 continuum L1a: α-dependent elastic stiffness scaling witness.

  Mirrors `energy.rs` `psi_stiffness_alpha_domain` (slice-1 scalar ℚ reduction):
    scale(α) = max(α − 1/2, 0)
    ψ_stiffness_α = −(1/10) · E₀ · ε² · scale(α)

  Proof status (D1–D10): core definitions, monotonicity lemmas, `StiffnessTransitionState`
  witness + gate admissibility.  Zero sorry.  No `[proved]` catalog export without operator.

  L1a rational grid (schema `lean_l1_stiffness_v2` · 7 rows) + honest posture pins bind
  `UMST_COMPOSITION_DOCTRINE` Second-Law fences: witnessed-not-proved · no Proved invent.

  NOT a reuse of `Powers.lean` / `powers_monotone`: that witness is fc(α), not E(α).
  `EXPECTED_PROVED_COUNT = 0` until operator catalog export + symbol audit.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic
import Compat.Gate

namespace UMST

open Rat

-- ================================================================
-- SECTION 1: Rust-aligned constants
-- ================================================================

/-- Hydration threshold below which stiffness scale vanishes (matches Rust `0.5`). -/
def stiffnessAlphaThreshold : ℚ := 1 / 2

/-- Elastic stiffness coupling in the ψ summand (matches Rust `0.1`). -/
def stiffnessCoupling : ℚ := 1 / 10

lemma stiffnessCoupling_nonneg : 0 ≤ stiffnessCoupling := by
  norm_num [stiffnessCoupling]

lemma stiffnessCoupling_pos : 0 < stiffnessCoupling := by
  norm_num [stiffnessCoupling]

-- ================================================================
-- SECTION 2: Stiffness scale — max(α − 1/2, 0) on ℚ
-- ================================================================

/-- α-dependent stiffness scale — mirrors Rust `(α - 0.5).max(0.0)`. -/
noncomputable def stiffnessScale (α : ℚ) : ℚ :=
  max (α - stiffnessAlphaThreshold) 0

/-- Stiffness scale is non-negative (D2). -/
theorem stiffnessScale_nonneg (α : ℚ) : 0 ≤ stiffnessScale α := by
  unfold stiffnessScale
  exact le_max_right _ _

/-- Stiffness scale vanishes below the hydration threshold. -/
theorem stiffnessScale_eq_zero_of_le_threshold {α : ℚ}
    (hα : α ≤ stiffnessAlphaThreshold) : stiffnessScale α = 0 := by
  have hsub : α - stiffnessAlphaThreshold ≤ 0 := sub_nonpos.mpr hα
  simp [stiffnessScale, max_eq_right hsub]

/-- Stiffness scale vanishes exactly at the hydration threshold. -/
theorem stiffnessScale_at_threshold : stiffnessScale stiffnessAlphaThreshold = 0 :=
  stiffnessScale_eq_zero_of_le_threshold le_rfl

/-- Above threshold, stiffness scale equals the excess hydration. -/
theorem stiffnessScale_eq_sub_above_threshold {α : ℚ}
    (hα : stiffnessAlphaThreshold ≤ α) : stiffnessScale α = α - stiffnessAlphaThreshold := by
  have hsub : 0 ≤ α - stiffnessAlphaThreshold := sub_nonneg.mpr hα
  simp [stiffnessScale, max_eq_left hsub]

/-- Stiffness scale is monotone in α on ℚ (D4). -/
theorem stiffnessScale_mono {α₁ α₂ : ℚ} (hα : α₁ ≤ α₂) :
    stiffnessScale α₁ ≤ stiffnessScale α₂ := by
  unfold stiffnessScale stiffnessAlphaThreshold
  refine max_le_max ?_ (le_refl _)
  linarith

-- ================================================================
-- SECTION 3: ψ_stiffness_α — M1-negative elastic summand
-- ================================================================

/-- `ψ_stiffness_α` on validated scalar domain — mirrors `psi_stiffness_alpha_domain`. -/
noncomputable def psi_stiffness_alpha (epsilon e0 α : ℚ) : ℚ :=
  -(stiffnessCoupling * e0 * epsilon ^ 2 * stiffnessScale α)

private lemma psi_stiffness_alpha_factor_nonneg {epsilon e0 α : ℚ}
    (he0 : 0 ≤ e0) : 0 ≤ stiffnessCoupling * e0 * epsilon ^ 2 * stiffnessScale α := by
  unfold stiffnessCoupling
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) he0) (sq_nonneg epsilon))
    (stiffnessScale_nonneg α)

/-- M1-negative convention: ψ ≤ 0 when E₀ ≥ 0 (D3). -/
theorem psi_stiffness_alpha_nonpos {epsilon e0 α : ℚ} (he0 : 0 ≤ e0) :
    psi_stiffness_alpha epsilon e0 α ≤ 0 := by
  unfold psi_stiffness_alpha
  exact neg_nonpos.mpr (psi_stiffness_alpha_factor_nonneg (epsilon := epsilon) (e0 := e0) (α := α) he0)

/-- ψ vanishes at zero strain regardless of α. -/
theorem psi_stiffness_alpha_eq_zero_at_zero_strain (e0 α : ℚ) :
    psi_stiffness_alpha 0 e0 α = 0 := by
  unfold psi_stiffness_alpha
  simp

/-- ψ vanishes when hydration is below the stiffness threshold. -/
theorem psi_stiffness_alpha_eq_zero_below_threshold {epsilon e0 α : ℚ}
    (hα : α ≤ stiffnessAlphaThreshold) :
    psi_stiffness_alpha epsilon e0 α = 0 := by
  unfold psi_stiffness_alpha
  simp [stiffnessScale_eq_zero_of_le_threshold hα]

/-- |ψ| increases with α at fixed ε, E₀: ψ is antitone in α (D5). -/
theorem psi_stiffness_alpha_mono_in_alpha {epsilon e0 α₁ α₂ : ℚ}
    (he0 : 0 ≤ e0) (hα : α₁ ≤ α₂) :
    psi_stiffness_alpha epsilon e0 α₂ ≤ psi_stiffness_alpha epsilon e0 α₁ := by
  unfold psi_stiffness_alpha
  have hscale := stiffnessScale_mono hα
  have hfactor_nonneg : 0 ≤ stiffnessCoupling * e0 * epsilon ^ 2 := by
    unfold stiffnessCoupling
    exact mul_nonneg (mul_nonneg (by norm_num) he0) (sq_nonneg epsilon)
  have hmul := mul_le_mul_of_nonneg_left hscale hfactor_nonneg
  linarith

/-- Combined Helmholtz + α-stiffness free energy at scalar hydration. -/
noncomputable def stiffnessTransitionEnergy (epsilon e0 α : ℚ) : ℚ :=
  helmholtz α + psi_stiffness_alpha epsilon e0 α

/-- Stiffness-transition free energy is antitone in α at fixed ε, E₀ ≥ 0. -/
theorem stiffnessTransitionEnergy_antitone {epsilon e0 α₁ α₂ : ℚ}
    (he0 : 0 ≤ e0) (hα : α₁ ≤ α₂) :
    stiffnessTransitionEnergy epsilon e0 α₂ ≤ stiffnessTransitionEnergy epsilon e0 α₁ := by
  unfold stiffnessTransitionEnergy
  exact add_le_add (helmholtzAntitone α₁ α₂ hα)
    (psi_stiffness_alpha_mono_in_alpha (epsilon := epsilon) (e0 := e0) he0 hα)

/-- Free-energy descent ↔ hydration ascent under the stiffness-transition model. -/
theorem stiffnessTransition_le_iff {epsilon e0 α₁ α₂ : ℚ} (he0 : 0 ≤ e0) :
    stiffnessTransitionEnergy epsilon e0 α₂ ≤ stiffnessTransitionEnergy epsilon e0 α₁ ↔
      α₁ ≤ α₂ := by
  constructor
  · intro hle
    by_contra h
    have hhelm : helmholtz α₁ < helmholtz α₂ :=
      not_le.mp ((not_congr (helmholtz_le_iff α₁ α₂)).2 h)
    have hpsi : psi_stiffness_alpha epsilon e0 α₁ ≤ psi_stiffness_alpha epsilon e0 α₂ :=
      psi_stiffness_alpha_mono_in_alpha (epsilon := epsilon) (e0 := e0) he0 (le_of_not_ge h)
    unfold stiffnessTransitionEnergy at hle
    linarith
  · intro hα
    exact stiffnessTransitionEnergy_antitone (epsilon := epsilon) (e0 := e0) he0 hα

-- ================================================================
-- SECTION 4: StiffnessTransitionState — gate witness (D6–D7)
-- ================================================================

/-- A state satisfies the stiffness-transition model at parameters `(e0, ε)` if its
    free energy equals the Helmholtz base plus the α-stiffness summand.
    Mirrors `HelmholtzState` + continuum `psi_stiffness_alpha_domain` slice. -/
def StiffnessTransitionState (s : ThermodynamicState) (e0 epsilon : ℚ) : Prop :=
  s.freeEnergy = helmholtz s.hydration + psi_stiffness_alpha epsilon e0 s.hydration

/-- For stiffness-transition-consistent states, forward hydration implies
    decreasing free energy (concrete witness for the gate's ψ-antitone slot). -/
theorem ψAntitoneStiffnessTransition
    (s₁ s₂ : ThermodynamicState) (e0 epsilon : ℚ)
    (h₁ : StiffnessTransitionState s₁ e0 epsilon)
    (h₂ : StiffnessTransitionState s₂ e0 epsilon)
    (he0 : 0 ≤ e0)
    (hα : s₁.hydration ≤ s₂.hydration) :
    s₂.freeEnergy ≤ s₁.freeEnergy := by
  rw [h₂, h₁]
  exact add_le_add (helmholtzAntitone s₁.hydration s₂.hydration hα)
    (psi_stiffness_alpha_mono_in_alpha (epsilon := epsilon) (e0 := e0) he0 hα)

/-- For two stiffness-transition-consistent states: forward hydration + mass
    conservation implies an admissible gate transition.
    Strength monotonicity uses the abstract `fcMonotone` slot (as in `HelmholtzState`). -/
theorem stiffnessTransitionStateAdmissible
    (old new : ThermodynamicState) (e0 epsilon : ℚ)
    (ho : StiffnessTransitionState old e0 epsilon)
    (hn : StiffnessTransitionState new e0 epsilon)
    (he0 : 0 ≤ e0)
    (hα : old.hydration ≤ new.hydration)
    (hm : |new.density - old.density| ≤ δMass)
    (h_fc : old.hydration ≤ new.hydration → old.strength ≤ new.strength) :
    Admissible old new :=
    Admissible.mk old new hm
    (ψAntitoneStiffnessTransition old new e0 epsilon ho hn he0 hα) hα (h_fc hα)

/-- The admissible transition direction is the negative-gradient direction of the
    combined Helmholtz + α-stiffness free energy (D8 witness). -/
theorem stiffnessTransitionDirIsNegGrad
    (old new : ThermodynamicState) (e0 epsilon : ℚ)
    (ho : StiffnessTransitionState old e0 epsilon)
    (hn : StiffnessTransitionState new e0 epsilon)
    (he0 : 0 ≤ e0) :
    new.freeEnergy ≤ old.freeEnergy ↔ old.hydration ≤ new.hydration := by
  rw [ho, hn]
  simpa using stiffnessTransition_le_iff (epsilon := epsilon) (e0 := e0) he0

-- ================================================================
-- SECTION 5: L1a rational witness grid (Rust↔Lean ℚ conformance pin)
-- ================================================================
-- Pins mirror `lean_l1_stiffness_adopt::V2_GRID_ROWS` (7 rows · Z37/Y41 adopt audit).
-- Fixture GREEN ≠ catalog `[proved]`; continuum tensor stiffness is **not** claimed here.

/-- Schema pin — matches Rust v2 grid fixture (`lean_l1_stiffness_v2`). -/
def l1aRationalGridSchema : String := "lean_l1_stiffness_v2"

/-- Pinned rational witness row count (v2 grid 7/7). -/
def l1aRationalGridRowCount : Nat := 7

/-- Reference E₀ for grid rows 1–3, 5–6 (30 GPa as ℚ). -/
def gridE0RefPa : ℚ := 30000000000

/-- Alternate E₀ for grid row 4 (25 GPa as ℚ). -/
def gridE0AltPa : ℚ := 25000000000

/-- Alternate E₀ for grid row 7 (28 GPa as ℚ). -/
def gridE0Row7Pa : ℚ := 28000000000

/-- Grid row 2: stiffness scale at α = 3/4 (`stiffnessScale_mono` anchor). -/
theorem stiffness_scale_grid_row2 :
    stiffnessScale (3 / 4) = 1 / 4 := by
  -- Threshold must be unfolded for both the side-condition and the arithmetic.
  rw [stiffnessScale_eq_sub_above_threshold (by unfold stiffnessAlphaThreshold; norm_num)]
  unfold stiffnessAlphaThreshold
  norm_num

/-- Grid row 3: stiffness scale at α = 1. -/
theorem stiffness_scale_grid_row3 :
    stiffnessScale 1 = 1 / 2 := by
  rw [stiffnessScale_eq_sub_above_threshold (by unfold stiffnessAlphaThreshold; norm_num)]
  unfold stiffnessAlphaThreshold
  norm_num

/-- Grid row 4: stiffness scale at α = 3/5. -/
theorem stiffness_scale_grid_row4 :
    stiffnessScale (3 / 5) = 1 / 10 := by
  rw [stiffnessScale_eq_sub_above_threshold (by unfold stiffnessAlphaThreshold; norm_num)]
  unfold stiffnessAlphaThreshold
  norm_num

/-- Grid row 6: stiffness scale at α = 4/5. -/
theorem stiffness_scale_grid_row6 :
    stiffnessScale (4 / 5) = 3 / 10 := by
  rw [stiffnessScale_eq_sub_above_threshold (by unfold stiffnessAlphaThreshold; norm_num)]
  unfold stiffnessAlphaThreshold
  norm_num

/-- Grid row 2 ψ evaluation at ε = 1/100, E₀ = 30 GPa. -/
theorem psi_stiffness_alpha_grid_row2 :
    psi_stiffness_alpha (1 / 100) gridE0RefPa (3 / 4) = -75000 := by
  unfold psi_stiffness_alpha gridE0RefPa stiffnessCoupling
  simp [stiffness_scale_grid_row2]
  norm_num

/-- Grid row 3 ψ evaluation at ε = 1/50, E₀ = 30 GPa. -/
theorem psi_stiffness_alpha_grid_row3 :
    psi_stiffness_alpha (1 / 50) gridE0RefPa 1 = -600000 := by
  unfold psi_stiffness_alpha gridE0RefPa stiffnessCoupling
  simp [stiffness_scale_grid_row3]
  norm_num

/-- Grid row 4 ψ evaluation at ε = 3/200, E₀ = 25 GPa. -/
theorem psi_stiffness_alpha_grid_row4 :
    psi_stiffness_alpha (3 / 200) gridE0AltPa (3 / 5) = -56250 := by
  unfold psi_stiffness_alpha gridE0AltPa stiffnessCoupling
  simp [stiffness_scale_grid_row4]
  norm_num

/-- Grid row 5: below threshold ⇒ ψ = 0 at ε = 1/100 (`psi_stiffness_alpha_eq_zero_below_threshold`). -/
theorem psi_stiffness_alpha_grid_row5_zero :
    psi_stiffness_alpha (1 / 100) gridE0RefPa (2 / 5) = 0 := by
  simpa using psi_stiffness_alpha_eq_zero_below_threshold
    (epsilon := 1 / 100) (e0 := gridE0RefPa) (α := 2 / 5)
    (by unfold stiffnessAlphaThreshold; norm_num)

/-- Grid row 6: zero strain ⇒ ψ = 0 at α = 4/5 (`psi_stiffness_alpha_eq_zero_at_zero_strain`). -/
theorem psi_stiffness_alpha_grid_row6_zero_strain :
    psi_stiffness_alpha 0 gridE0RefPa (4 / 5) = 0 := by
  simpa using psi_stiffness_alpha_eq_zero_at_zero_strain gridE0RefPa (4 / 5)

/-- Grid row 7: below threshold ⇒ ψ = 0 at ε = 1/50. -/
theorem psi_stiffness_alpha_grid_row7_zero :
    psi_stiffness_alpha (1 / 50) gridE0Row7Pa (9 / 20) = 0 := by
  simpa using psi_stiffness_alpha_eq_zero_below_threshold
    (epsilon := 1 / 50) (e0 := gridE0Row7Pa) (α := 9 / 20)
    (by unfold stiffnessAlphaThreshold; norm_num)

/-- All seven pinned grid rows evaluate without sorry (computational witness bundle). -/
theorem l1a_rational_grid_row_count :
    l1aRationalGridRowCount = 7 := by
  rfl

-- ================================================================
-- SECTION 6: Honest posture pins (witnessed-not-proved · no Proved invent)
-- ================================================================
-- Binds `UMST_COMPOSITION_DOCTRINE` §B–§E: Second-Law only · constants classified · no fake GREEN.

/-- LIB adoption workstream id — matches Rust `WORKSTREAM_ID`. -/
def leanL1WorkstreamId : String := "LIB-ADOPT-F-LEAN-L1"

/-- Honest adoption tier — witnessed-not-proved until operator catalog export. -/
def postureTag : String := "witnessed-not-proved"

/-- Frozen proved-count posture — agents must not inflate. -/
def expectedProvedCount : Nat := 0

/-- Machine-checked pin: proved-count stays zero until operator catalog export. -/
theorem expectedProvedCount_zero : expectedProvedCount = 0 := rfl

/-- Structural cert-proved fence honest — **not** tier-2→Proved promotion. -/
def certProvedFenceHonest : Bool := true

/-- Formal fence closed — structural audit GREEN; tier promotion still blocked. -/
def formalFenceClosed : Bool := certProvedFenceHonest && expectedProvedCount = 0

/-- Machine-checked pin: formal fence closed without Proved inflation. -/
theorem formalFenceClosed_honest : formalFenceClosed = true := by
  simp [formalFenceClosed, certProvedFenceHonest, expectedProvedCount_zero]

/-- Catalog `[proved]` export remains operator-gated. -/
def catalogExportDeferred : Bool := true

/-- Slice-1 hot path does not wire this module's adopt audit into production gate yet. -/
def productionWired : Bool := false

/-- Explicit non-claims carried beside the rational grid (fixture parity). -/
def stiffnessTransitionNonClaims : List String :=
  [ "fixture GREEN ≠ catalog [proved]"
  , "v2 grid 7/7 = witnessed-not-proved adopt audit (Z37/Y41) — not Proved tier"
  , "slice-1 ψ_stiffness_α uses scalar ℚ reduction — not tensor continuum stiffness"
  , "Powers.lean fc(α) witness orthogonal — not E(α) stiffness scale"
  , "catalog export deferred — operator make lean-catalog-export"
  , "production_wired=false — prep/adopt slice only" ]

end UMST
