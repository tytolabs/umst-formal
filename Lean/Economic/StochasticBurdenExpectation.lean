/-
  UMST-Formal: Economic/StochasticBurdenExpectation.lean

  Symmetric two-point noise (mean-zero) and geometric collapse under |1+μ| < 1.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Economic.BurdenRecursionIsAdmissible

namespace UMST.Economics

open Rat Real Filter Topology

theorem burden_expectation_symmetric_two_point (B μ σ : ℝ) :
    (1 / 2 : ℝ) * (B * (1 + μ + σ)) + (1 / 2 : ℝ) * (B * (1 + μ - σ)) = B * (1 + μ) := by
  ring

theorem exploration_buffer_geom_tendsto_zero (μ : ℝ) (h : |1 + μ| < 1) :
    Tendsto (fun n : ℕ => (1 + μ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

theorem exploration_buffer_geom_tendsto_zero_of_lt_one (μ : ℝ) (hlt : 1 + μ < 1) (hnneg : 0 ≤ 1 + μ) :
    Tendsto (fun n : ℕ => (1 + μ) ^ n) atTop (𝓝 0) := by
  have habs : |1 + μ| < 1 := by
    rw [abs_lt]
    constructor
    · linarith [hnneg]
    · linarith [hlt]
  exact exploration_buffer_geom_tendsto_zero μ habs

theorem burden_scale_admissible (B r : ℚ) (hB : |B| * |r - 1| ≤ δMass) :
    Admissible (stateOfBurden B) (stateOfBurden (r * B)) := by
  constructor
  · simp only [stateOfBurden]
    have hcalc : r * B - B = B * (r - 1) := by ring
    rw [hcalc]
    simpa [abs_mul] using hB
  · simp [stateOfBurden]
  · simp [stateOfBurden]
  · simp [stateOfBurden]

end UMST.Economics
