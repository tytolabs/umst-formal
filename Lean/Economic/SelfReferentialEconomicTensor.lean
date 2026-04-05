/-
  UMST-Formal: Economic/SelfReferentialEconomicTensor.lean

  **Contractive** burden dynamics when `g < ε`: each iterate strictly decreases (no unconstrained
  self-referential fixed point). Full Field/Core functor story is future work.
-/

import Economic.BurdenRecursionIsAdmissible

namespace UMST.Economics

open Rat

/-- After one step, burden is strictly below the start when entropy dominates growth. -/
theorem selfRef_burden_one_step_lt (B g ε : ℚ) (h : g < ε) : burdenIterate 1 g ε B < B := by
  simpa [burdenIterate, burdenStep] using burden_decreases_when_entropy_dominates B g ε h

/-- Strict contraction per step implies `burdenIterate (n+1) g ε B < B` for all `n`. -/
theorem selfRef_burden_iterate_lt_initial (B g ε : ℚ) (h : g < ε) (n : ℕ) :
    burdenIterate (n + 1) g ε B < B := by
  induction n with
  | zero =>
    simpa [burdenIterate, burdenStep] using burden_decreases_when_entropy_dominates B g ε h
  | succ n ih =>
    calc
      burdenIterate (n + 2) g ε B
          = burdenStep (burdenIterate (n + 1) g ε B) g ε := by
              simp [burdenIterate, Function.iterate_succ_apply']
      _ < burdenIterate (n + 1) g ε B := burden_decreases_when_entropy_dominates _ g ε h
      _ < B := ih

end UMST.Economics
