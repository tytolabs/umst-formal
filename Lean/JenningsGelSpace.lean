/-
  SPDX-License-Identifier: Apache-2.0

  UMST-Formal: JenningsGelSpace.lean
  Jennings–Brownyard gel-space refit (parallel witness to `Powers.lean`).

  Informal (Powers–Brownyard capillary porosity on ℚ, fixed `wc > 0`):
    • `φ_cap(α, wc) = clamp((wc − 0.36 α) / (wc + 0.32), 0, 1)`.
    • `f_c(α, wc; a, p) = a · (1 − φ_cap)^p` with `a > 0`, `p > 0` (we take `p : ℕ` with `0 < p`).

  Headline:
    • `capillary_porosity_antitone_in_alpha`
    • `jennings_strength_monotone`
    • `jennings_strength_nonneg`

  This is a **parallel** concrete witness to the abstract `fcMonotone` interface (see
  `Powers.lean` for the OPC Powers gel-space ratio line); both are admissible models.
  Reference: Jennings & Johnson, *Cement and Concrete Research* 38 (2008) — CCR 38.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open Rat

namespace UMST

/-- Clamp `x` into `[0, 1]` on `ℚ`. -/
noncomputable def clamp01 (x : ℚ) : ℚ :=
  max 0 (min 1 x)

/-- Capillary porosity `φ_cap` (Jennings–Brownyard form on ℚ). -/
noncomputable def φ_cap (α wc : ℚ) : ℚ :=
  clamp01 ((wc - (36 / 100 : ℚ) * α) / (wc + (32 / 100 : ℚ)))

/-- Jennings gel-space strength model `f_c = a · (1 − φ_cap)^p`. -/
noncomputable def jenningsStrength (α wc a : ℚ) (p : ℕ) : ℚ :=
  a * (1 - φ_cap α wc) ^ p

lemma denom_pos {wc : ℚ} (hwc : 0 < wc) : 0 < wc + (32 / 100 : ℚ) := by
  linarith

lemma clamp01_mono {x y : ℚ} (h : x ≤ y) : clamp01 x ≤ clamp01 y := by
  unfold clamp01
  refine max_le_max (le_refl _) ?_
  exact min_le_min (le_refl (1 : ℚ)) h

lemma φ_cap_num_mono {wc : ℚ} (hwc : 0 < wc) {α₁ α₂ : ℚ} (hα : α₁ ≤ α₂) :
    (wc - (36 / 100 : ℚ) * α₂) / (wc + (32 / 100 : ℚ)) ≤
      (wc - (36 / 100 : ℚ) * α₁) / (wc + (32 / 100 : ℚ)) := by
  have hd := denom_pos hwc
  apply (div_le_div_iff_of_pos_right hd).mpr
  linarith [mul_le_mul_of_nonneg_left hα (show (0 : ℚ) ≤ (36 / 100 : ℚ) from by norm_num)]

theorem capillary_porosity_antitone_in_alpha {wc : ℚ} (hwc : 0 < wc) {α₁ α₂ : ℚ}
    (_hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) :
    φ_cap α₂ wc ≤ φ_cap α₁ wc := by
  unfold φ_cap
  refine clamp01_mono ?_
  exact φ_cap_num_mono hwc hα₁₂

lemma one_sub_φ_nonneg {α wc : ℚ} (_hα : 0 ≤ α) (_hwc : 0 < wc) : 0 ≤ 1 - φ_cap α wc := by
  have hφ : φ_cap α wc ≤ 1 := by
    unfold φ_cap clamp01
    have hm : min 1 ((wc - (36 / 100 : ℚ) * α) / (wc + (32 / 100 : ℚ))) ≤ 1 := min_le_left _ _
    calc
      max 0 (min 1 _) ≤ max 0 1 := max_le_max (le_refl _) hm
      _ = 1 := by norm_num
  linarith

lemma one_sub_φ_mono {wc : ℚ} (hwc : 0 < wc) {α₁ α₂ : ℚ} (hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) :
    1 - φ_cap α₁ wc ≤ 1 - φ_cap α₂ wc := by
  linarith [capillary_porosity_antitone_in_alpha hwc hα₁ hα₁₂]

theorem jennings_strength_monotone {wc a : ℚ} {p : ℕ} (hwc : 0 < wc) (ha : 0 < a) (_hp : 0 < p)
    {α₁ α₂ : ℚ} (hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) :
    jenningsStrength α₁ wc a p ≤ jenningsStrength α₂ wc a p := by
  unfold jenningsStrength
  have h0₁ : 0 ≤ 1 - φ_cap α₁ wc := one_sub_φ_nonneg hα₁ hwc
  have h0₂ : 0 ≤ 1 - φ_cap α₂ wc := one_sub_φ_nonneg (le_trans hα₁ hα₁₂) hwc
  have hbase : (1 - φ_cap α₁ wc) ≤ (1 - φ_cap α₂ wc) :=
    one_sub_φ_mono hwc hα₁ hα₁₂
  have hpow :
      (1 - φ_cap α₁ wc) ^ p ≤ (1 - φ_cap α₂ wc) ^ p :=
    pow_le_pow_left₀ h0₁ hbase p
  exact mul_le_mul_of_nonneg_left hpow (le_of_lt ha)

theorem jennings_strength_nonneg {wc a : ℚ} {p : ℕ} (hwc : 0 < wc) (ha : 0 < a) (_hp : 0 < p)
    {α : ℚ} (hα : 0 ≤ α) : 0 ≤ jenningsStrength α wc a p := by
  unfold jenningsStrength
  refine mul_nonneg (le_of_lt ha) ?_
  exact pow_nonneg (one_sub_φ_nonneg hα hwc) p

#print axioms jennings_strength_monotone
#print axioms jennings_strength_nonneg

end UMST
