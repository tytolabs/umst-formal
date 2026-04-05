/-
  UMST-Formal: Economic/HorizonAwareGrounding.lean

  Convex combination of local vs global cost scalars for `α ∈ [0,1]`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Economic.EconomicDomain

namespace UMST.Economics

open Real

/-- Horizon-weighted cost `α·c_local + (1-α)·c_global`. -/
noncomputable def horizonCost (α c_local c_global : ℝ) : ℝ :=
  α * c_local + (1 - α) * c_global

/-- Convex combination lies between `min` and `max` of the endpoints when `0 ≤ α ≤ 1`. -/
theorem horizonCost_mem_Icc (α c_local c_global : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    horizonCost α c_local c_global ∈ Set.Icc (min c_local c_global) (max c_local c_global) := by
  rw [Set.mem_Icc, horizonCost]
  set m := min c_local c_global
  set M := max c_local c_global
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  constructor
  · -- lower bound: `m ≤ α·c_local + (1-α)·c_global`
    have hlo : α * m ≤ α * c_local := mul_le_mul_of_nonneg_left (min_le_left c_local c_global) hα0
    have hhi : (1 - α) * m ≤ (1 - α) * c_global :=
      mul_le_mul_of_nonneg_left (min_le_right c_local c_global) h1α
    calc
      m = α * m + (1 - α) * m := by ring
      _ ≤ α * c_local + (1 - α) * c_global := add_le_add hlo hhi
  · -- upper bound
    have hlo : α * c_local ≤ α * M := mul_le_mul_of_nonneg_left (le_max_left c_local c_global) hα0
    have hhi : (1 - α) * c_global ≤ (1 - α) * M :=
      mul_le_mul_of_nonneg_left (le_max_right c_local c_global) h1α
    calc
      α * c_local + (1 - α) * c_global ≤ α * M + (1 - α) * M := add_le_add hlo hhi
      _ = M := by ring

end UMST.Economics
