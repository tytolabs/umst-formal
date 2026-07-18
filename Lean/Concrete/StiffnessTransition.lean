/-
  UMST-Formal: StiffnessTransition.lean
  Lean 4 — B1 continuum L1a: α-dependent elastic stiffness scaling witness.

  Mirrors `energy.rs` `psi_stiffness_alpha_domain` (slice-1 scalar ℚ reduction):
    scale(α) = max(α − 1/2, 0)
    ψ_stiffness_α = −(1/10) · E₀ · ε² · scale(α)

  Proof status (week 1 / D1–D5): core definitions + monotonicity lemmas.
  Zero sorry.  No `[proved]` catalog graduation — symbol audit deferred to week 2.

  NOT a reuse of `Powers.lean` / `powers_monotone`: that witness is fc(α), not E(α).
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

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

end UMST
