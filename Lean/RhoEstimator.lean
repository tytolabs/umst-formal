/-
  UMST-Formal: RhoEstimator.lean

  Gaussian bivariate mutual information in **bits** as a function of Pearson correlation ρ:

  `MI(ρ) = - (1/2) · log₂(1 - ρ²)`  for `ρ² < 1`.

  Monotonicity is proved in the squared variable `t = ρ²` (`rhoMiOfSq_mono`).

  **Theorem 6.** The classical Fisher asymptotic envelope `(1 - ρ²)² / n` is nonnegative (Rust warm-up sizing).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace UMST.Formal.RhoEstimator

open Real

/-- Valid correlation magnitudes for the closed-form MI identity (`ρ² < 1`). -/
def ValidRho (rho : ℝ) : Prop :=
  rho ^ 2 < 1

/-- MI as a function of `t = ρ²` with `t ∈ [0, 1)`. -/
noncomputable def rhoMiOfSq (t : ℝ) (_ht : t < 1) (_hn : 0 ≤ t) : ℝ :=
  - (1 / 2 : ℝ) * logb 2 (1 - t)

private lemma logb_two_nonpos_of_mem_unit_interval {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    logb 2 x ≤ 0 := by
  rw [logb]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (log_nonneg (one_le_two))
  exact (log_nonpos_iff hx0).2 hx1

theorem rhoMiOfSq_nonneg (t : ℝ) (ht : t < 1) (hn : 0 ≤ t) : 0 ≤ rhoMiOfSq t ht hn := by
  unfold rhoMiOfSq
  have hz : 0 < 1 - t := by linarith
  have hle : 1 - t ≤ 1 := by linarith
  have hlog : logb 2 (1 - t) ≤ 0 := logb_two_nonpos_of_mem_unit_interval hz hle
  linarith

theorem rhoMiOfSq_mono (t₁ t₂ : ℝ) (ht₁ : t₁ < 1) (ht₂ : t₂ < 1) (h₀₁ : 0 ≤ t₁) (h₀₂ : 0 ≤ t₂)
    (hle : t₁ ≤ t₂) : rhoMiOfSq t₁ ht₁ h₀₁ ≤ rhoMiOfSq t₂ ht₂ h₀₂ := by
  unfold rhoMiOfSq
  have hz₂ : 0 < 1 - t₂ := by linarith
  have hz₁ : 0 < 1 - t₁ := by linarith
  have hsub : 1 - t₂ ≤ 1 - t₁ := by linarith
  have hlog : logb 2 (1 - t₂) ≤ logb 2 (1 - t₁) :=
    (logb_le_logb (by norm_num : (1 : ℝ) < 2) hz₂ hz₁).2 hsub
  linarith

/-- Closed-form Gaussian MI in bits (depends only on `ρ²`). -/
noncomputable def rhoMi (rho : ℝ) (h : ValidRho rho) : ℝ :=
  rhoMiOfSq (rho ^ 2) h (sq_nonneg rho)

theorem rho_based_mi_formula (rho : ℝ) (h : ValidRho rho) :
    rhoMi rho h = - (1 / 2 : ℝ) * logb 2 (1 - rho ^ 2) := by
  unfold rhoMi rhoMiOfSq
  rfl

theorem rho_mi_nonneg (rho : ℝ) (h : ValidRho rho) : 0 ≤ rhoMi rho h := by
  unfold rhoMi
  exact rhoMiOfSq_nonneg (rho ^ 2) h (sq_nonneg rho)

theorem rho_mi_zero_at_zero_rho : rhoMi 0 (by norm_num [ValidRho]) = 0 := by
  simp [rhoMi, rhoMiOfSq, ValidRho, logb_one]

theorem rho_mi_monotone_in_abs_rho (ρ₁ ρ₂ : ℝ) (h₁ : ValidRho ρ₁) (h₂ : ValidRho ρ₂)
    (habs : |ρ₁| ≤ |ρ₂|) : rhoMi ρ₁ h₁ ≤ rhoMi ρ₂ h₂ := by
  have hsq : ρ₁ ^ 2 ≤ ρ₂ ^ 2 := by
    have h0 : 0 ≤ |ρ₁| := abs_nonneg ρ₁
    have h1 : |ρ₁| ≤ |ρ₂| := habs
    have h2 : |ρ₁| ^ 2 ≤ |ρ₂| ^ 2 := by simpa [pow_two] using mul_self_le_mul_self h0 h1
    simpa [sq_abs] using h2
  unfold rhoMi
  exact rhoMiOfSq_mono (ρ₁ ^ 2) (ρ₂ ^ 2) h₁ h₂ (sq_nonneg _) (sq_nonneg _) hsq

theorem rho_mi_bounded_below_one (ρ ρmax : ℝ) (h : ValidRho ρ) (hmax : ValidRho ρmax)
    (habs : |ρ| ≤ |ρmax|) (_hlt : |ρmax| < 1) : rhoMi ρ h ≤ rhoMi ρmax hmax :=
  rho_mi_monotone_in_abs_rho ρ ρmax h hmax habs

theorem plug_in_variance_bound (n : ℕ) (hn : 0 < n) (rho : ℝ) (_hρ : ValidRho rho) :
    (0 : ℝ) ≤ (1 - rho ^ 2) ^ 2 / (n : ℝ) := by
  have hnum : 0 ≤ (1 - rho ^ 2) ^ 2 := sq_nonneg _
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  exact div_nonneg hnum (le_of_lt hpos)

end UMST.Formal.RhoEstimator
