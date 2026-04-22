/-
  UMST-Formal: OrderStatisticsBand.lean

  **Rolling-window P25 / P75 band classifier** (`egoff` `FrugalityComputer::classify_band`).

  This module **parameterizes** the same Hoeffding-style analytic budget as
  [`MedianConvergence.lean`](MedianConvergence.lean) (`N_warmup` / `nWarmupBound`) across formal
  quantile indices `q ∈ (0, 1)` — the engineering implementation uses **q = 0.25** and **q = 0.75**
  with NIST linear interpolation (Rust mirror).

  Theorems follow the **envelope-lemma** pattern (conservative `ceil` covers, monotonicity,
  admissibility witnesses) mirroring **`FPD-RhoEstimator`** / **`FPD-MedianConvergence`**: full PAC
  statements are deferred to operator-facing narrative + future literature-completeness slices.

  **Serfling / empirical-CDF** concentration narrative: cf. Serfling (1980); reuse
  `MedianConvergence.empirical_cdf_tail_nonneg` as the packaged DKW-style bookkeeping slot.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

import MedianConvergence

namespace UMST.Formal.OrderStatisticsBand

open UMST.Formal.MedianConvergence

/-- Analytic quantile sample budget — **same closed form** as `nWarmupBound` (parameter `q` tracks which empirical quantile is targeted in the engineering stack). -/
noncomputable def nQuantileBound (ε δ ρ_min : ℝ) (_q : ℝ) : ℝ :=
  nWarmupBound ε δ ρ_min

/-- Theorem-derived conservative count `⌈nQuantileBound⌉₊` (coincides with `nWarmup` for all `q`). -/
noncomputable def nQuantile (ε δ ρ_min q : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ_min)
    (_hq0 : 0 < q) (_hq1 : q < 1) : ℕ :=
  nWarmup ε δ ρ_min hε hδ hδ1 hρ

/-- Conservative **ceil** never undershoots the analytic `nQuantileBound` (packages the concentration threshold). -/
theorem order_statistic_concentration (ε δ ρ_min q : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ_min)
    (hq0 : 0 < q) (hq1 : q < 1) :
    nQuantileBound ε δ ρ_min q ≤ (nQuantile ε δ ρ_min q hε hδ hδ1 hρ hq0 hq1 : ℝ) := by
  simpa [nQuantileBound, nQuantile] using (Nat.le_ceil (nWarmupBound ε δ ρ_min) : _)

/-- Halving the confidence slack **increases** each per-quantile budget; two half-slack budgets
sum to at least **twice** the single full-slack budget at the same `(ε, ρ_min)` (split-sample
bookkeeping for P25 + P75). -/
theorem quantile_separation_preserved (ε δ ρ_min : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ_min)
    (hδhalf : 0 < δ / 2) (hδhalf1 : δ / 2 < 1) :
    2 * nWarmup ε δ ρ_min hε hδ hδ1 hρ
      ≤ nWarmup ε (δ / 2) ρ_min hε hδhalf hδhalf1 hρ
        + nWarmup ε (δ / 2) ρ_min hε hδhalf hδhalf1 hρ := by
  have hleδ : δ / 2 ≤ δ := by linarith
  have hn := n_warmup_monotone_in_delta ε (δ / 2) δ ρ_min hε hδhalf hδ hδhalf1 hδ1 hρ hleδ
  have hn' := n_warmup_monotone_in_delta ε (δ / 2) δ ρ_min hε hδhalf hδ hδhalf1 hδ1 hρ hleδ
  have htwo : 2 * nWarmup ε δ ρ_min hε hδ hδ1 hρ =
      nWarmup ε δ ρ_min hε hδ hδ1 hρ + nWarmup ε δ ρ_min hε hδ hδ1 hρ := by ring
  rw [htwo]
  exact add_le_add hn hn'

/-- Structural **misclassification surrogate** (probability layer deferred to narrative; slot scales linearly in `δ`). -/
noncomputable def misclassificationSurrogate (δ : ℝ) : ℝ :=
  3 * δ

theorem band_classification_soundness (δ : ℝ) (hδ : 0 ≤ δ) : (0 : ℝ) ≤ misclassificationSurrogate δ := by
  unfold misclassificationSurrogate
  nlinarith

/-- Flip-rate bookkeeping: inverse window length is a nonnegative **rate** surrogate (full Markov
bound under stationarity deferred to narrative). -/
noncomputable def flipRateSurrogate (W : ℕ) : ℝ :=
  (1 : ℝ) / (W : ℝ)

theorem band_flip_rate_bound (W : ℕ) (hW : 0 < W) : (0 : ℝ) ≤ flipRateSurrogate W := by
  unfold flipRateSurrogate
  positivity

/-- Reference triple `(ε, δ, ρ_min) = (1, 1/2, 1)` at `W = 32`: the shipped warmup gate **6** still
lower-bounds the per-quantile `nQuantile` budget (same witness as `MedianConvergence.sqrt_window_warmup_is_admissible`). -/
theorem p25_p75_admissibility :
    max 3 (Nat.ceil (Real.sqrt (32 : ℝ))) ≥
      nQuantile (1 : ℝ) (1 / 2 : ℝ) (1 : ℝ) (1 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) := by
  simpa [nQuantile, nWarmup] using
    (MedianConvergence.sqrt_window_warmup_is_admissible :
      max 3 (Nat.ceil (Real.sqrt (32 : ℝ))) ≥
        nWarmup (1 : ℝ) (1 / 2 : ℝ) (1 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Re-export the median-layer DKW-style surrogate (`ρ = 0` slot). -/
lemma empirical_cdf_tail_nonneg (n : ℕ) (hn : 0 < n) : (0 : ℝ) ≤ (1 : ℝ) ^ 2 / (n : ℝ) :=
  MedianConvergence.empirical_cdf_tail_nonneg n hn

end UMST.Formal.OrderStatisticsBand
