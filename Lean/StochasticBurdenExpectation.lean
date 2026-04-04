/-
  UMST-Formal: StochasticBurdenExpectation.lean

  Finite **symmetric two-point** noise around a deterministic burden drift, and **geometric**
  collapse of a nonnegative scalar under multiplicative factors `< 1`.

  Interprets Wave-5-style exploration buffers: iid mean-zero noise does not bias the **expected**
  one-step multiplicative factor; long-run decay follows a **negative** log-drift (here: `|1+μ| < 1`).
-/

import Mathlib.Analysis.SpecificLimits.Basic
import BurdenRecursionIsAdmissible

namespace UMST.Economics

open Rat Real Filter Topology

/-- Expectation of `B * (1 + μ + ξ)` under symmetric `±σ` with probability `1/2` each. -/
theorem burden_expectation_symmetric_two_point (B μ σ : ℝ) :
    (1 / 2 : ℝ) * (B * (1 + μ + σ)) + (1 / 2 : ℝ) * (B * (1 + μ - σ)) = B * (1 + μ) := by
  ring

/-- **Geometric collapse:** if `|1 + μ| < 1`, then `(1 + μ)^n → 0`. -/
theorem exploration_buffer_geom_tendsto_zero (μ : ℝ) (h : |1 + μ| < 1) :
    Tendsto (fun n : ℕ => (1 + μ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

/-- Same conclusion under `0 ≤ 1 + μ < 1` (real factor, no oscillation). -/
theorem exploration_buffer_geom_tendsto_zero_of_lt_one (μ : ℝ) (hlt : 1 + μ < 1) (hnneg : 0 ≤ 1 + μ) :
    Tendsto (fun n : ℕ => (1 + μ) ^ n) atTop (𝓝 0) := by
  have habs : |1 + μ| < 1 := by
    rw [abs_lt]
    constructor
    · linarith [hnneg]
    · linarith [hlt]
  exact exploration_buffer_geom_tendsto_zero μ habs

/-- Rational burden embedded in `ThermodynamicState` stays **admissible** along deterministic
geometric scaling `B ↦ r * B` when `|r-1|·|B| ≤ δMass` (linear macroscopic bookkeeping). -/
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
