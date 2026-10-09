-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UncertaintyRelation.lean

  The thermodynamic uncertainty relation (TUR) of A. C. Barato and U. Seifert, "Thermodynamic uncertainty relation
  for biomolecular processes", Phys. Rev. Lett. 114, 158101 (2015): for a current J_t of a Markov jump process in
  its steady state, Var(J_t) / ⟨J_t⟩² ≥ 2 / σ_t, with σ_t the entropy production in units of k_B.

  Setting proved here. The biased random walk with forward rate k₊ > 0 and backward rate k₋ > 0, equivalently the
  uniform ring of N states with these rates on every link, whose net displacement current J_t is the difference of
  two independent Poisson counts. Its cumulants and entropy production are taken as stated definitions of the
  model:
    ⟨J_t⟩ = (k₊ − k₋) t,  Var(J_t) = (k₊ + k₋) t
      (difference of two Poisson variates: J. G. Skellam, J. R. Stat. Soc. 109(3), 296 (1946));
    σ_t = (k₊ − k₋) · ln(k₊ / k₋) · t
      (Schnakenberg's entropy production of the cycle: J. Schnakenberg, Rev. Mod. Phys. 48, 571 (1976)).
  Theorem `tur_biasedWalk`: 2 ⟨J_t⟩² ≤ Var(J_t) · σ_t for every t ≥ 0, and the ratio form when ⟨J_t⟩ ≠ 0.

  The analytic core is the logarithmic-mean bound 2 (a − b)² ≤ (a + b)(a − b)(ln a − ln b), from
  ln x ≥ 2 (x − 1)/(x + 1) for x ≥ 1, the first term of the series of ln(1 + 1/a) (Mathlib
  `Real.hasSum_log_one_add_inv`).

  Typed absence. The TUR for an arbitrary current of an arbitrary finite Markov jump process in its steady state
  (proved by T. R. Gingrich, J. M. Horowitz, N. Perunov and J. L. England, Phys. Rev. Lett. 116, 120601 (2016),
  through the large-deviation rate function of currents) is not proved here; follow-up cell FORMAL-TUR-GENERAL.

  Zero `axiom`, zero `sorry`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Real

namespace UMST.UncertaintyRelation

/-- ln x ≥ 2 (x − 1)/(x + 1) for x ≥ 1. -/
theorem two_mul_div_le_log {x : ℝ} (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ Real.log x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · set a : ℝ := 1 / (x - 1) with ha
    have hx1 : 0 < x - 1 := by linarith
    have hapos : 0 < a := by positivity
    have hsum := Real.hasSum_log_one_add_inv hapos
    have hxa : 1 + a⁻¹ = x := by rw [ha, one_div, inv_inv]; ring
    rw [hxa] at hsum
    have hle := sum_le_hasSum ({0} : Finset ℕ) (fun k _ => by positivity) hsum
    simp only [Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at hle
    have hfirst : 2 * (1 / (2 * a + 1)) = 2 * (x - 1) / (x + 1) := by
      rw [ha]
      field_simp
      ring
    linarith [hfirst ▸ hle]

/-- **Logarithmic-mean bound**: 2 (a − b)² ≤ (a + b)(a − b)(ln a − ln b) for a, b > 0. -/
theorem log_mean_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * (a - b) ^ 2 ≤ (a + b) * (a - b) * (Real.log a - Real.log b) := by
  -- the statement is symmetric in a and b, so take b ≤ a
  wlog hab : b ≤ a generalizing a b
  · have := this hb ha (le_of_not_le hab)
    nlinarith [this]
  have hx : 1 ≤ a / b := (one_le_div hb).2 hab
  have hlog := two_mul_div_le_log hx
  rw [Real.log_div ha.ne' hb.ne'] at hlog
  have hfrac : 2 * (a / b - 1) / (a / b + 1) = 2 * (a - b) / (a + b) := by
    field_simp
  rw [hfrac] at hlog
  have hs : 0 < a + b := by linarith
  have hd : 0 ≤ a - b := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg hs.le hd)
  have hcancel : (a + b) * (a - b) * (2 * (a - b) / (a + b)) = 2 * (a - b) ^ 2 := by
    field_simp
    ring
  linarith [hcancel ▸ hmul]

/-- The biased random walk (uniform ring) by its forward and backward rates. -/
structure BiasedWalk where
  kPlus : ℝ
  kMinus : ℝ
  kPlus_pos : 0 < kPlus
  kMinus_pos : 0 < kMinus

namespace BiasedWalk

variable (w : BiasedWalk)

/-- Mean of the net displacement current over time `t` (Skellam mean). -/
def meanCurrent (t : ℝ) : ℝ := (w.kPlus - w.kMinus) * t

/-- Variance of the net displacement current over time `t` (Skellam variance). -/
def varCurrent (t : ℝ) : ℝ := (w.kPlus + w.kMinus) * t

/-- Entropy production over time `t`, units of k_B (Schnakenberg). -/
noncomputable def entropyProduction (t : ℝ) : ℝ :=
  (w.kPlus - w.kMinus) * (Real.log w.kPlus - Real.log w.kMinus) * t

/-- The entropy production is non-negative: the second law of the walk. -/
theorem entropyProduction_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ w.entropyProduction t := by
  unfold entropyProduction
  refine mul_nonneg ?_ ht
  rcases le_total w.kMinus w.kPlus with h | h
  · exact mul_nonneg (by linarith) (by
      have := Real.log_le_log w.kMinus_pos h; linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by
      have := Real.log_le_log w.kPlus_pos h; linarith)

/-- **Thermodynamic uncertainty relation for the biased walk**: 2 ⟨J_t⟩² ≤ Var(J_t) · σ_t. -/
theorem tur_biasedWalk {t : ℝ} (_ht : 0 ≤ t) :
    2 * w.meanCurrent t ^ 2 ≤ w.varCurrent t * w.entropyProduction t := by
  unfold meanCurrent varCurrent entropyProduction
  have h := log_mean_bound w.kPlus_pos w.kMinus_pos
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have := mul_le_mul_of_nonneg_right h ht2
  calc 2 * ((w.kPlus - w.kMinus) * t) ^ 2 = 2 * (w.kPlus - w.kMinus) ^ 2 * t ^ 2 := by ring
    _ ≤ (w.kPlus + w.kMinus) * (w.kPlus - w.kMinus) * (Real.log w.kPlus - Real.log w.kMinus) * t ^ 2 := this
    _ = (w.kPlus + w.kMinus) * t *
          ((w.kPlus - w.kMinus) * (Real.log w.kPlus - Real.log w.kMinus) * t) := by ring

/-- **Ratio form**: when the mean current is non-zero, the entropy production is positive and
    Var(J_t) / ⟨J_t⟩² ≥ 2 / σ_t. -/
theorem tur_biasedWalk_ratio {t : ℝ} (ht : 0 ≤ t) (hJ : w.meanCurrent t ≠ 0) :
    0 < w.entropyProduction t ∧ 2 / w.entropyProduction t ≤ w.varCurrent t / w.meanCurrent t ^ 2 := by
  have hJ2 : 0 < w.meanCurrent t ^ 2 := by positivity
  have htur := w.tur_biasedWalk ht
  have hvar : 0 ≤ w.varCurrent t := mul_nonneg (by linarith [w.kPlus_pos, w.kMinus_pos]) ht
  have hσ0 := w.entropyProduction_nonneg ht
  have hσ : 0 < w.entropyProduction t := by
    rcases eq_or_lt_of_le hσ0 with h | h
    · rw [← h, mul_zero] at htur; linarith
    · exact h
  refine ⟨hσ, ?_⟩
  rw [div_le_div_iff₀ hσ hJ2]
  linarith

end BiasedWalk

end UMST.UncertaintyRelation
