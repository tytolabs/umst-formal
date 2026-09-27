-- problem size is evidence of orthogonality loss, not an unfold stop (Converged, Stalled, BudgetSpent).

namespace UMST.Solver.ProblemSize

def escalates (n steps : Nat) : Bool :=
  n > 0 && steps >= n

theorem escalates_zero_unknowns (steps : Nat) : escalates 0 steps = false := by
  simp [escalates]

theorem escalates_at_unknowns (n : Nat) (h : n > 0) : escalates n n = true := by
  simp [escalates, h]

end UMST.Solver.ProblemSize
