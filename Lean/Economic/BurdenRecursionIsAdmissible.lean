/-
  UMST-Formal: Economic/BurdenRecursionIsAdmissible.lean

  Burden axis embedded in `ThermodynamicState`; one-step and iterated updates.
-/

import Gate

namespace UMST.Economics

open Rat

/-- Embed burden `B` in the classical gate carrier (schematic: only `density` varies). -/
def stateOfBurden (B : ℚ) : ThermodynamicState :=
  ⟨B, 0, 0, 0⟩

/-- One-step burden evolution with net drift `g` and local entropy tax `ε`. -/
def burdenStep (B g ε : ℚ) : ℚ :=
  B + g - ε

theorem burdenStep_eq_endo (B g ε : ℚ) : burdenStep B g ε = B + (g - ε) := by
  unfold burdenStep
  ring

/-- **Shrinking** along the burden axis when the entropy tax dominates growth (`ε > g`). -/
theorem burden_decreases_when_entropy_dominates (B g ε : ℚ) (h : g < ε) :
    burdenStep B g ε < B := by
  unfold burdenStep
  linarith

/-- **Admissible** one-step recursion whenever `|g - ε| ≤ δMass`. -/
theorem burdenRecursion_admissible (B g ε : ℚ) (hδ : |g - ε| ≤ δMass) :
    Admissible (stateOfBurden B) (stateOfBurden (burdenStep B g ε)) := by
  constructor
  · simp only [stateOfBurden, burdenStep]
    rw [show B + g - ε - B = g - ε by ring]
    exact hδ
  · simp [stateOfBurden]
  · simp [stateOfBurden]
  · simp [stateOfBurden]

/-- N-fold iteration (endofunctor power on the burden axis). -/
def burdenIterate (n : ℕ) (g ε : ℚ) (B : ℚ) : ℚ :=
  (burdenStep · g ε)^[n] B

theorem burdenIterate_zero (g ε B : ℚ) : burdenIterate 0 g ε B = B := by
  simp [burdenIterate]

theorem burdenIterate_succ (n : ℕ) (g ε B : ℚ) :
    burdenIterate (n + 1) g ε B = burdenStep (burdenIterate n g ε B) g ε := by
  simp [burdenIterate, Function.iterate_succ_apply']

/-- Strict single-step decrease along the burden axis when `g < ε`. -/
theorem burdenStep_strict_lt (B g ε : ℚ) (h : g < ε) : burdenStep B g ε < B :=
  burden_decreases_when_entropy_dominates B g ε h

/-- Iterated burden strictly decreases at each positive step when entropy dominates growth. -/
theorem burdenIterate_succ_lt (B g ε : ℚ) (h : g < ε) (n : ℕ) :
    burdenIterate (n + 1) g ε B < burdenIterate n g ε B := by
  simp only [burdenIterate, Function.iterate_succ_apply']
  exact burden_decreases_when_entropy_dominates _ g ε h

end UMST.Economics
