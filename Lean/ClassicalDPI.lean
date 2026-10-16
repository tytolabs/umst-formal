-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: ClassicalDPI.lean

  The classical data-processing inequality for a deterministic summary: for a joint distribution `J` of `X` and `Y`
  on `Fin n × Fin m` and a map `f : Fin m → Fin k`, the joint of `X` and `f(Y)` (`JointDist.summary J f`) carries no
  more mutual information than `J`:

    I(X; f(Y)) ≤ I(X; Y)                                                   (`mutualInformation_summary_le`)

  The proof runs through the two-term log-sum inequality, from the convexity of `x ↦ x log x`
  (`Real.convexOn_mul_log`): for `a, b ≥ 0` and `s, t > 0`,
    (a + b) log((a + b)/(s + t)) ≤ a log(a/s) + b log(b/t)                 (`logSum_two`).
  Summed over the rows, it makes the column functional `G(v) = Σ_i v_i log v_i − (Σ_i v_i) log(Σ_i v_i)` subadditive
  (`colFun_add_le`); merging the columns of each fibre of `f` therefore lowers `Σ_j G(column j)`, which is
  `I(X; Y) − H(X)` (`mutualInformation_eq_add_colSum`), while `H(X)` is unchanged.

  Zero `axiom`, zero `sorry`.
-/

import InfoTheory
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Real Finset UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.ClassicalDPI

/-- `x log x`, the convex function of the log-sum inequality. -/
noncomputable def φ (x : ℝ) : ℝ := x * log x

theorem φ_zero : φ 0 = 0 := by simp [φ]

/-- `s φ(a/s) = φ(a) − a log s` for `s > 0`. -/
theorem scale_φ {a s : ℝ} (hs : 0 < s) : s * φ (a / s) = φ a - a * log s := by
  unfold φ
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hs.ne']
    field_simp
    ring

/-- **Two-term log-sum inequality**, in the form `φ(a+b) − (a+b) log(s+t) ≤ φ(a) − a log s + φ(b) − b log t`. -/
theorem logSum_two {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) (ht : 0 < t) :
    φ (a + b) - (a + b) * log (s + t) ≤ (φ a - a * log s) + (φ b - b * log t) := by
  have hst : 0 < s + t := add_pos hs ht
  have hw1 : 0 ≤ s / (s + t) := (div_pos hs hst).le
  have hw2 : 0 ≤ t / (s + t) := (div_pos ht hst).le
  have hsum : s / (s + t) + t / (s + t) = 1 := by field_simp
  have hu : a / s ∈ Set.Ici (0 : ℝ) := div_nonneg ha hs.le
  have hv : b / t ∈ Set.Ici (0 : ℝ) := div_nonneg hb ht.le
  have hconv := convexOn_mul_log.2 hu hv hw1 hw2 hsum
  simp only [smul_eq_mul] at hconv
  have hpt : s / (s + t) * (a / s) + t / (s + t) * (b / t) = (a + b) / (s + t) := by
    field_simp; ring
  rw [hpt] at hconv
  have hmul := mul_le_mul_of_nonneg_left hconv hst.le
  have h1 : (s + t) * ((a + b) / (s + t) * log ((a + b) / (s + t))) = φ (a + b) - (a + b) * log (s + t) := by
    exact scale_φ hst
  have h2 : (s + t) * (s / (s + t) * (a / s * log (a / s)) + t / (s + t) * (b / t * log (b / t))) =
      s * φ (a / s) + t * φ (b / t) := by
    unfold φ; field_simp; ring
  rw [h1, h2, scale_φ hs, scale_φ ht] at hmul
  linarith

variable {n m k : ℕ}

/-- The column functional `G(v) = Σ_i φ(v_i) − φ(Σ_i v_i)`. -/
noncomputable def colFun (v : Fin n → ℝ) : ℝ := ∑ i, φ (v i) - φ (∑ i, v i)

theorem colFun_zero : colFun (0 : Fin n → ℝ) = 0 := by simp [colFun, φ_zero]

/-- A non-negative vector of sum zero is zero. -/
theorem eq_zero_of_sum_eq_zero {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (h : ∑ i, v i = 0) : v = 0 := by
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hv i)).1 h i (mem_univ i)

/-- **Subadditivity of the column functional**: merging two non-negative columns does not raise it. -/
theorem colFun_add_le {a b : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    colFun (a + b) ≤ colFun a + colFun b := by
  rcases (sum_nonneg fun i _ => ha i).eq_or_lt with hs | hs
  · rw [eq_zero_of_sum_eq_zero ha hs.symm, zero_add, colFun_zero, zero_add]
  rcases (sum_nonneg fun i _ => hb i).eq_or_lt with ht | ht
  · rw [eq_zero_of_sum_eq_zero hb ht.symm, add_zero, colFun_zero, add_zero]
  set s := ∑ i, a i
  set t := ∑ i, b i
  have hrow : ∀ i, φ (a i + b i) - (a i + b i) * log (s + t) ≤
      (φ (a i) - a i * log s) + (φ (b i) - b i * log t) := fun i => logSum_two (ha i) (hb i) hs ht
  have hsumrow := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) => hrow i
  have e1 : ∑ i, (φ (a i + b i) - (a i + b i) * log (s + t)) = ∑ i, φ (a i + b i) - (s + t) * log (s + t) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_add_distrib]
  have e2 : ∑ i, ((φ (a i) - a i * log s) + (φ (b i) - b i * log t)) =
      (∑ i, φ (a i) - s * log s) + (∑ i, φ (b i) - t * log t) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [e1, e2] at hsumrow
  have hl : colFun (a + b) = ∑ i, φ (a i + b i) - (s + t) * log (s + t) := by
    unfold colFun
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    rfl
  have hra : colFun a = ∑ i, φ (a i) - s * log s := rfl
  have hrb : colFun b = ∑ i, φ (b i) - t * log t := rfl
  rw [hl, hra, hrb]
  linarith

/-- Merging any finite family of non-negative columns does not raise the column functional. -/
theorem colFun_sum_le {ι : Type*} (S : Finset ι) (col : ι → Fin n → ℝ) (hcol : ∀ j i, 0 ≤ col j i) :
    colFun (∑ j ∈ S, col j) ≤ ∑ j ∈ S, colFun (col j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [colFun_zero]
  | insert hj ih =>
    rename_i j S
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hS : ∀ i, 0 ≤ (∑ j ∈ S, col j) i := fun i => by
      rw [Finset.sum_apply]; exact sum_nonneg fun j _ => hcol j i
    calc colFun (col j + ∑ j ∈ S, col j) ≤ colFun (col j) + colFun (∑ j ∈ S, col j) :=
          colFun_add_le (hcol j) hS
      _ ≤ colFun (col j) + ∑ j ∈ S, colFun (col j) := by linarith

/-- The columns of a joint: column `j` is `i ↦ J(i, j)`. -/
def column (J : JointDist n m) (j : Fin m) : Fin n → ℝ := fun i => J.mass (i, j)

/-- `I(X; Y) = H(X) + Σ_j G(column j)`. -/
theorem mutualInformation_eq_add_colSum (J : JointDist n m) :
    mutualInformation J = shannonEntropy (marginalX J) + ∑ j, colFun (column J j) := by
  unfold mutualInformation jointEntropy shannonEntropy colFun column φ
  simp only [marginalY, Fintype.sum_prod_type, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => J.mass (i, j) * log (J.mass (i, j)))]
  ring

/-- The joint of `X` and the summary `f(Y)`: mass `(i, c) ↦ Σ_{j : f j = c} J(i, j)`. -/
noncomputable def summary (J : JointDist n m) (f : Fin m → Fin k) : JointDist n k where
  mass ic := ∑ j ∈ univ.filter (fun j => f j = ic.2), J.mass (ic.1, j)
  nonneg := fun ic => sum_nonneg fun j _ => J.nonneg (ic.1, j)
  sumOne := by
    rw [Fintype.sum_prod_type]
    have h : ∀ i : Fin n, ∑ c : Fin k, ∑ j ∈ univ.filter (fun j => f j = c), J.mass (i, j) = ∑ j, J.mass (i, j) :=
      fun i => Finset.sum_fiberwise univ f (fun j => J.mass (i, j))
    simp only [h]
    rw [← Fintype.sum_prod_type (f := fun xy : Fin n × Fin m => J.mass xy)]
    exact J.sumOne

theorem marginalX_summary (J : JointDist n m) (f : Fin m → Fin k) :
    (marginalX (summary J f)).mass = (marginalX J).mass := by
  funext i
  simp only [marginalX, summary]
  exact Finset.sum_fiberwise univ f (fun j => J.mass (i, j))

theorem column_summary (J : JointDist n m) (f : Fin m → Fin k) (c : Fin k) :
    column (summary J f) c = ∑ j ∈ univ.filter (fun j => f j = c), column J j := by
  funext i
  simp [column, summary, Finset.sum_apply]

/-- **The classical data-processing inequality for a deterministic summary**: `I(X; f(Y)) ≤ I(X; Y)`. -/
theorem mutualInformation_summary_le (J : JointDist n m) (f : Fin m → Fin k) :
    mutualInformation (summary J f) ≤ mutualInformation J := by
  rw [mutualInformation_eq_add_colSum, mutualInformation_eq_add_colSum]
  have hX : shannonEntropy (marginalX (summary J f)) = shannonEntropy (marginalX J) := by
    unfold shannonEntropy; rw [marginalX_summary]
  rw [hX]
  have hcol : ∀ j i, 0 ≤ column J j i := fun j i => J.nonneg (i, j)
  have hmerge : ∑ c, colFun (column (summary J f) c) ≤ ∑ c, ∑ j ∈ univ.filter (fun j => f j = c), colFun (column J j) :=
    Finset.sum_le_sum fun c _ => by
      rw [column_summary]; exact colFun_sum_le _ (column J) hcol
  rw [Finset.sum_fiberwise univ f (fun j => colFun (column J j))] at hmerge
  linarith

end UMST.ClassicalDPI
