-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Powers.lean
  Lean 4 — the Powers gel-space ratio model of strength.

  The Powers (1958) model relates compressive strength to the degree of hydration:
    x(α, w/c) = 0.68·α / (0.32·α + w/c)   (gel-space ratio)
    fc(α, w/c) = S · x³                     (strength, S = 234 MPa, `Constants.SI.powersGelStrength`)

  At fixed water-cement ratio w/c > 0, x is increasing in α, so fc is increasing in α
  (`powers_monotone`): for states of the model the strength leg of the cement gate is derived, not
  assumed (`powersStateFcMonotone`). The gel fits its space, x ≤ 1, exactly when w/c ≥ 0.36·α
  (`gelSpaceRatio_le_one_iff`). The w/c ratio is carried as a parameter (not in ThermodynamicState).
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic
import Compat.Gate
import Constants.SI

namespace UMST

open Rat

-- ================================================================
-- SECTION 1: Physical Constants
-- ================================================================

/-- Intrinsic strength of fully hydrated C-S-H gel (MPa): the cited Powers (1958) gel–space law coefficient
    `Constants.SI.powersGelStrength`, specific to the cements and specimens examined. -/
def S_intrinsic : ℚ := Constants.SI.powersGelStrength

lemma S_intrinsic_pos : 0 < S_intrinsic := by norm_num [S_intrinsic, Constants.SI.powersGelStrength]

-- ================================================================
-- SECTION 2: Gel-Space Ratio (Powers Model)
-- ================================================================

/-- Gel-space ratio x(α, wc) = 0.68·α / (0.32·α + wc), written over integers as 68·α / (32·α + 100·wc).
    Requires wc > 0 (positive water-cement ratio). -/
noncomputable def gelSpaceRatio (α wc : ℚ) : ℚ :=
  (68 * α) / (32 * α + 100 * wc)

/-- Denominator of gel-space ratio is positive for α ≥ 0, wc > 0. -/
lemma gelSpaceRatioDenom_pos {α wc : ℚ} (hα : 0 ≤ α) (hwc : 0 < wc) :
    0 < 32 * α + 100 * wc := by
  have : 0 ≤ 32 * α := mul_nonneg (by norm_num) hα
  linarith

/-- Gel-space ratio is non-negative for α ≥ 0, wc > 0. -/
lemma gelSpaceRatio_nonneg {α wc : ℚ} (hα : 0 ≤ α) (hwc : 0 < wc) :
    0 ≤ gelSpaceRatio α wc := by
  unfold gelSpaceRatio
  apply div_nonneg
  · exact mul_nonneg (by norm_num) hα
  · positivity

/-- **The gel fits its space** exactly when wc ≥ 0.36·α: the gel-space ratio is at most one exactly then
    (Powers' rounding of the space threshold `Constants.SI.criticalWcSpace` = 0.356). -/
theorem gelSpaceRatio_le_one_iff {α wc : ℚ} (hα : 0 ≤ α) (hwc : 0 < wc) :
    gelSpaceRatio α wc ≤ 1 ↔ 36 * α ≤ 100 * wc := by
  unfold gelSpaceRatio
  rw [div_le_one (gelSpaceRatioDenom_pos hα hwc)]
  constructor <;> intro h <;> linarith

-- ================================================================
-- SECTION 3: Strength Model
-- ================================================================

/-- Compressive strength fc(α, wc) = S · x(α, wc)³. -/
noncomputable def powersStrength (α wc : ℚ) : ℚ :=
  S_intrinsic * (gelSpaceRatio α wc) ^ 3

/-- Strength is non-negative. -/
lemma powersStrength_nonneg {α wc : ℚ} (hα : 0 ≤ α) (hwc : 0 < wc) :
    0 ≤ powersStrength α wc := by
  unfold powersStrength
  exact mul_nonneg (le_of_lt S_intrinsic_pos)
    (pow_nonneg (gelSpaceRatio_nonneg hα hwc) 3)

-- ================================================================
-- SECTION 4: Monotonicity of gel-space ratio in α
-- ================================================================

/-- Key lemma: the gel-space ratio is monotone increasing in α at fixed wc > 0.
    x(α₁, wc) ≤ x(α₂, wc) when α₁ ≤ α₂. -/
lemma gelSpaceRatio_mono {α₁ α₂ wc : ℚ}
    (hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) (hwc : 0 < wc) :
    gelSpaceRatio α₁ wc ≤ gelSpaceRatio α₂ wc := by
  unfold gelSpaceRatio
  have hα₂ : 0 ≤ α₂ := le_trans hα₁ hα₁₂
  have hd₁ : 0 < 32 * α₁ + 100 * wc := by positivity
  have hd₂ : 0 < 32 * α₂ + 100 * wc := by positivity
  rw [div_le_div_iff₀ hd₁ hd₂]
  -- Goal: 68 * α₁ * (32 * α₂ + 100 * wc) ≤ 68 * α₂ * (32 * α₁ + 100 * wc), i.e. α₁ * wc ≤ α₂ * wc
  nlinarith [mul_nonneg hα₁ (le_of_lt hwc),
             mul_nonneg hα₂ (le_of_lt hwc)]

-- ================================================================
-- SECTION 5: Monotonicity of strength in α
-- ================================================================

/-- Strength is monotone in hydration at fixed wc > 0.
    The strength leg of the cement gate follows from the Powers model, with no further hypothesis. -/
theorem powers_monotone {α₁ α₂ wc : ℚ}
    (hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) (hwc : 0 < wc) :
    powersStrength α₁ wc ≤ powersStrength α₂ wc := by
  unfold powersStrength
  apply mul_le_mul_of_nonneg_left _ (le_of_lt S_intrinsic_pos)
  apply pow_le_pow_left₀ (gelSpaceRatio_nonneg hα₁ hwc)
  exact gelSpaceRatio_mono hα₁ hα₁₂ hwc

-- ================================================================
-- SECTION 6: PowersState — States Satisfying the Model
-- ================================================================

/-- A state "satisfies the Powers model at w/c ratio wc" if its strength
    field equals powersStrength(hydration, wc).
    This is the strength-analogue of HelmholtzState for free energy. -/
def PowersState (s : ThermodynamicState) (wc : ℚ) : Prop :=
  s.strength = powersStrength s.hydration wc

/-- For states satisfying the Powers model, advancing hydration cannot
    decrease strength. -/
theorem powersStateFcMonotone
    (s₁ s₂ : ThermodynamicState) (wc : ℚ)
    (hp₁ : PowersState s₁ wc)
    (hp₂ : PowersState s₂ wc)
    (hα₁ : 0 ≤ s₁.hydration)
    (hα₂ : s₁.hydration ≤ s₂.hydration)
    (hwc : 0 < wc) :
    s₁.strength ≤ s₂.strength := by
  rw [hp₁, hp₂]
  exact powers_monotone hα₁ hα₂ hwc

/-- For Powers-consistent states, forward hydration + mass conservation
    implies a fully admissible transition.
    This is the Powers-model analogue of helmholtzStateAdmissible. -/
theorem powersStateAdmissible
    (old new : ThermodynamicState) (wc : ℚ)
    (ho  : PowersState old wc)
    (hn  : PowersState new wc)
    (hα₀ : 0 ≤ old.hydration)
    (hα  : old.hydration ≤ new.hydration)
    (hm  : |new.density - old.density| ≤ δMass)
    (hwc : 0 < wc)
    (h_psi : old.hydration ≤ new.hydration → new.freeEnergy ≤ old.freeEnergy) :
    Admissible old new :=
  Admissible.mk old new hm (h_psi hα) hα (powersStateFcMonotone old new wc ho hn hα₀ hα hwc)

end UMST
