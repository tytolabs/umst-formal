/-
  UMST-Formal: Powers.lean
  Lean 4 — Concrete witness for fcMonotone via the Powers gel-space ratio model.

  The Powers (1958) model relates compressive strength to the degree of hydration:
    x(α, w/c) = 0.68·α / (0.32·α + w/c)   (gel-space ratio)
    fc(α, w/c) = S · x³                     (strength, S ≈ 234 MPa)

  At fixed water-cement ratio w/c > 0, x is strictly increasing in α, so fc
  is strictly increasing in α.  This is the concrete physical justification for
  the abstract axiom `fcMonotone` in Gate.lean.

  NOTE: `fcMonotone` in Gate.lean is an abstract interface axiom covering all
  physically reasonable material models.  This file provides the concrete
  WITNESS for Portland cement (OPC) under the Powers model at fixed w/c.
  A fully constructive treatment would carry `PowersState` hypotheses through
  the gate (analogous to `HelmholtzState` for `psiAntitone`).

  Physical constants:
    S_intrinsic = 234 MPa   (Powers intrinsic strength of C-S-H gel)
    The w/c ratio is carried as a parameter (not in ThermodynamicState).
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic
import Gate

namespace UMST

open Rat

-- ================================================================
-- SECTION 1: Physical Constants
-- ================================================================

/-- Intrinsic strength of fully hydrated C-S-H gel (MPa).
    Powers (1958) gives S ≈ 234 MPa for Portland cement. -/
def S_intrinsic : ℚ := 234

lemma S_intrinsic_pos : 0 < S_intrinsic := by norm_num [S_intrinsic]

-- ================================================================
-- SECTION 2: Gel-Space Ratio (Powers Model)
-- ================================================================

/-- Gel-space ratio x(α, wc) = 0.68·α / (0.32·α + wc).
    Requires wc > 0 (positive water-cement ratio). -/
noncomputable def gelSpaceRatio (α wc : ℚ) : ℚ :=
  (68 * α) / (100 * (32 * α + 100 * wc))

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
  have hd₁ : 0 < 100 * (32 * α₁ + 100 * wc) := by positivity
  have hd₂ : 0 < 100 * (32 * α₂ + 100 * wc) := by positivity
  rw [div_le_div_iff hd₁ hd₂]
  -- Goal: 68 * α₁ * (100 * (32 * α₂ + 100 * wc)) ≤ 68 * α₂ * (100 * (32 * α₁ + 100 * wc))
  -- Expand: 68 * 100 * (α₁ * 32 * α₂ + α₁ * 100 * wc) ≤ 68 * 100 * (α₂ * 32 * α₁ + α₂ * 100 * wc)
  -- Simplify: α₁ * 100 * wc ≤ α₂ * 100 * wc (since α₁ ≤ α₂ and wc > 0)
  nlinarith [mul_nonneg hα₁ (le_of_lt hwc),
             mul_nonneg hα₂ (le_of_lt hwc)]

-- ================================================================
-- SECTION 5: Monotonicity of strength in α
-- ================================================================

/-- Strength is monotone in hydration at fixed wc > 0.
    This is the concrete Powers-model witness for the abstract `fcMonotone` axiom. -/
theorem powers_monotone {α₁ α₂ wc : ℚ}
    (hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) (hwc : 0 < wc) :
    powersStrength α₁ wc ≤ powersStrength α₂ wc := by
  unfold powersStrength
  apply mul_le_mul_of_nonneg_left _ (le_of_lt S_intrinsic_pos)
  apply pow_le_pow_left (gelSpaceRatio_nonneg hα₁ hwc)
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
    decrease strength.  This is the concrete witness for `fcMonotone`. -/
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
    (hwc : 0 < wc) :
    Admissible old new :=
  ⟨hm,
   psiAntitone old new hα,
   hα,
   powersStateFcMonotone old new wc ho hn hα₀ hα hwc⟩

end UMST
