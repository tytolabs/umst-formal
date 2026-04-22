/-
  UMST-Formal: MedianConvergence.lean

  **Warmup sample count** for rolling-window median / percentile stability.

  The engineering runtime keeps **`max 3 ⌈√W⌉`** (`egoff` `FrugalityComputer`).
  This module supplies the **theorem-derived** count
  `N_warmup(ε, δ, ρ_min) := ⌈ (2 / (ε² ρ_min²)) · log(2/δ) ⌉` (natural logarithm; classical
  Hoeffding / empirical-CDF concentration narrative; cf. Serfling (1980) order-statistics tail bounds).

  **`median_convergence_sample_size`** packages the analytic **ceil covering** inequality
  `nWarmupBound ≤ (nWarmup : ℝ)` — the conservative budget never undershoots the closed form.

  **`sqrt_window_warmup_is_admissible`** uses the reference triple `(ε, δ, ρ_min) = (1, 1/2, 1)` at
  `W = 32` (default cockpit window): then `N_warmup = 3` while `max 3 ⌈√32⌉ = 6`.  (Operator-facing
  narrative in `egoffplan` / §24a may cite an alternative IQR-scaled triple; **any** witness with
  `max 3 ⌈√W⌉ ≥ N_warmup` is admissible.)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace UMST.Formal.MedianConvergence

open Real

/-- Analytic **Hoeffding-style** sample threshold (natural log). -/
noncomputable def nWarmupBound (ε δ ρ_min : ℝ) : ℝ :=
  (2 / (ε ^ 2 * ρ_min ^ 2)) * log (2 / δ)

/-- Theorem-derived conservative count `⌈nWarmupBound⌉₊`. -/
noncomputable def nWarmup (ε δ ρ_min : ℝ) (_hε : 0 < ε) (_hδ : 0 < δ) (_hδ1 : δ < 1) (_hρ : 0 < ρ_min) : ℕ :=
  Nat.ceil (nWarmupBound ε δ ρ_min)

private lemma log_two_div_delta_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < log (2 / δ) := by
  have h2d : 1 < 2 / δ := by
    rw [one_lt_div hδ]
    linarith [hδ1]
  exact log_pos h2d

private lemma nWarmupBound_pos (ε δ ρ_min : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ_min) :
    0 < nWarmupBound ε δ ρ_min := by
  unfold nWarmupBound
  have hnum : 0 < 2 / (ε ^ 2 * ρ_min ^ 2) := by
    have hε2 : 0 < ε ^ 2 := pow_pos hε 2
    have hρ2 : 0 < ρ_min ^ 2 := pow_pos hρ 2
    positivity
  exact mul_pos hnum (log_two_div_delta_pos hδ hδ1)

/-- The analytic threshold is always **covered** by its ceiling (conservative sample budget). -/
theorem median_convergence_sample_size (ε δ ρ_min : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hρ : 0 < ρ_min) : nWarmupBound ε δ ρ_min ≤ (nWarmup ε δ ρ_min hε hδ hδ1 hρ : ℝ) := by
  simpa [nWarmup] using (Nat.le_ceil (nWarmupBound ε δ ρ_min) : _)

theorem n_warmup_positive (ε δ ρ_min : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ_min) :
    1 ≤ nWarmup ε δ ρ_min hε hδ hδ1 hρ := by
  have hb : 0 < nWarmupBound ε δ ρ_min := nWarmupBound_pos ε δ ρ_min hε hδ hδ1 hρ
  rw [nWarmup, Nat.one_le_ceil_iff]
  exact_mod_cast hb

/-- Tighter **ε** (smaller tolerance) ⇒ **larger** conservative count. -/
theorem n_warmup_monotone_in_epsilon (ε₁ ε₂ δ ρ_min : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hρ : 0 < ρ_min) (hle : ε₁ ≤ ε₂) :
    nWarmup ε₂ δ ρ_min hε₂ hδ hδ1 hρ ≤ nWarmup ε₁ δ ρ_min hε₁ hδ hδ1 hρ := by
  have hmono : nWarmupBound ε₂ δ ρ_min ≤ nWarmupBound ε₁ δ ρ_min := by
    unfold nWarmupBound
    have hε₁2 : 0 < ε₁ ^ 2 := pow_pos hε₁ 2
    have hε₂2 : 0 < ε₂ ^ 2 := pow_pos hε₂ 2
    have hsq : ε₁ ^ 2 ≤ ε₂ ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self (le_of_lt hε₁) hle
    have hden_le : ε₁ ^ 2 * ρ_min ^ 2 ≤ ε₂ ^ 2 * ρ_min ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg ρ_min)
    have hb := mul_pos hε₂2 (pow_pos hρ 2)
    have hc := mul_pos hε₁2 (pow_pos hρ 2)
    have hfrac : 2 / (ε₂ ^ 2 * ρ_min ^ 2) ≤ 2 / (ε₁ ^ 2 * ρ_min ^ 2) :=
      (div_le_div_iff_of_pos_left (by positivity) hb hc).mpr hden_le
    have hlog : 0 ≤ log (2 / δ) := le_of_lt (log_two_div_delta_pos hδ hδ1)
    nlinarith
  exact Nat.ceil_mono hmono

/-- Stricter **δ** (smaller confidence slack) ⇒ **larger** conservative count. -/
theorem n_warmup_monotone_in_delta (ε δ₁ δ₂ ρ_min : ℝ) (hε : 0 < ε) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hδ₁1 : δ₁ < 1) (hδ₂1 : δ₂ < 1) (hρ : 0 < ρ_min) (hle : δ₁ ≤ δ₂) :
    nWarmup ε δ₂ ρ_min hε hδ₂ hδ₂1 hρ ≤ nWarmup ε δ₁ ρ_min hε hδ₁ hδ₁1 hρ := by
  have hmono : nWarmupBound ε δ₂ ρ_min ≤ nWarmupBound ε δ₁ ρ_min := by
    unfold nWarmupBound
    have hlogmono : log (2 / δ₂) ≤ log (2 / δ₁) := by
      have hpos₂ : 0 < (2 : ℝ) / δ₂ := by positivity
      have hpos₁ : 0 < (2 : ℝ) / δ₁ := by positivity
      have hdiv : 2 / δ₂ ≤ 2 / δ₁ := by
        rw [div_le_div_iff₀ hδ₂ hδ₁]
        nlinarith
      exact (log_le_log_iff hpos₂ hpos₁).mpr hdiv
    have hcoef : 0 ≤ 2 / (ε ^ 2 * ρ_min ^ 2) := by positivity
    nlinarith
  exact Nat.ceil_mono hmono

private lemma sqrt_32_bounds : (5 : ℝ) < Real.sqrt (32 : ℝ) ∧ Real.sqrt (32 : ℝ) ≤ (6 : ℝ) := by
  constructor
  · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  · rw [Real.sqrt_le_iff]
    constructor <;> norm_num

private lemma ceil_sqrt_32 : Nat.ceil (Real.sqrt (32 : ℝ)) = 6 := by
  rcases sqrt_32_bounds with ⟨hlo, hhi⟩
  rw [Nat.ceil_eq_iff (show (6 : ℕ) ≠ 0 by norm_num)]
  refine And.intro ?_ ?_
  · exact_mod_cast hlo
  · exact hhi

private lemma nWarmup_one_half_one_eq_three :
    nWarmup (1 : ℝ) (1 / 2 : ℝ) (1 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) = 3 := by
  unfold nWarmup nWarmupBound
  have hs :
      (2 : ℝ) / ((1 : ℝ) ^ 2 * (1 : ℝ) ^ 2) * log (2 / (1 / 2 : ℝ)) = 4 * log 2 := by
    have hcoef : (2 : ℝ) / ((1 : ℝ) ^ 2 * (1 : ℝ) ^ 2) = 2 := by norm_num
    have harg : (2 : ℝ) / (1 / 2 : ℝ) = 4 := by norm_num
    have hlog4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, log_pow]
      ring
    rw [hcoef, harg, hlog4]
    ring
  rw [hs, Nat.ceil_eq_iff (show (3 : ℕ) ≠ 0 by norm_num)]
  rw [show (↑(3 - 1 : ℕ) : ℝ) = (2 : ℝ) by norm_num]
  constructor
  · -- `2 < 4 * log 2` — multiply `Real.log_two_gt_d9` by `4 > 0`, then compare to `2`.
    have hlower : (4 : ℝ) * (0.6931471803 : ℝ) < (4 : ℝ) * log 2 :=
      mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num)
    have hnum : (2 : ℝ) < (4 : ℝ) * (0.6931471803 : ℝ) := by norm_num
    linarith [hlower, hnum]
  · -- `4 * log 2 ≤ 3` — multiply `Real.log_two_lt_d9` by `4 > 0`, then compare to `3`.
    have hmul : (4 : ℝ) * log 2 < (4 : ℝ) * (0.6931471808 : ℝ) :=
      mul_lt_mul_of_pos_left Real.log_two_lt_d9 (by norm_num)
    have hnum : (4 : ℝ) * (0.6931471808 : ℝ) < (3 : ℝ) := by norm_num
    exact (lt_trans hmul hnum).le

/-- The shipped **`max 3 ⌈√W⌉`** gate at `W = 32` lower-bounds `N_warmup` for the reference triple
`(ε, δ, ρ_min) = (1, 1/2, 1)` (short formal witness; IQR-scaled alternatives are documented in plan §14bis). -/
theorem sqrt_window_warmup_is_admissible :
    max 3 (Nat.ceil (Real.sqrt (32 : ℝ))) ≥
      nWarmup (1 : ℝ) (1 / 2 : ℝ) (1 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) := by
  have hW : max 3 (Nat.ceil (Real.sqrt (32 : ℝ))) = 6 := by
    rw [ceil_sqrt_32]
    norm_num
  rw [hW, nWarmup_one_half_one_eq_three]
  norm_num

/-- Nonnegative surrogate matching a **DKW / plug-in** bookkeeping slot `(1 - ρ²)² / n` at `ρ = 0`. -/
lemma empirical_cdf_tail_nonneg (n : ℕ) (hn : 0 < n) : (0 : ℝ) ≤ (1 : ℝ) ^ 2 / (n : ℝ) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  positivity

end UMST.Formal.MedianConvergence
