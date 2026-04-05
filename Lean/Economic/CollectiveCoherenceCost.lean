/-
  UMST-Formal: Economic/CollectiveCoherenceCost.lean

  Sum of nonnegative **penalty** terms (classical surrogate for multi-agent divergence).
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Tactic.Linarith

namespace UMST.Economics

open Rat

/-- Collective penalty is sum of nonnegative contributions. -/
def collectivePenalty (xs : List ℚ) : ℚ :=
  xs.sum

theorem collectivePenalty_nonneg (xs : List ℚ) (hx : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ collectivePenalty xs := by
  induction xs with
  | nil => simp [collectivePenalty, List.sum_nil]
  | cons x xs ih =>
    simp only [collectivePenalty, List.sum_cons]
    have hx0 : 0 ≤ x := hx x (List.mem_cons_self _ _)
    have htail : 0 ≤ xs.sum := ih fun y hy => hx y (List.mem_cons_of_mem x hy)
    linarith

end UMST.Economics
