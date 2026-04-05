/-
  UMST-Formal: Economic/CreativityBudget.lean

  Bookkeeping: output charge `Q` is **within** admitted baseline plus creative slack `Δ`.
-/

import Economic.EconomicDomain
import Mathlib.Tactic.Linarith

namespace UMST.Economics

open Rat

/-- Creative slack allows `Q ≤ Q_admitted + Δ`. -/
def withinCreativityBudget (Q Q_admitted Δ : ℚ) : Prop :=
  Q ≤ Q_admitted + Δ

theorem creativityBudget_refl (Q Q_admitted : ℚ) : withinCreativityBudget Q Q_admitted 0 ↔ Q ≤ Q_admitted := by
  simp [withinCreativityBudget]

theorem creativityBudget_monotoneΔ (Q Q_admitted Δ₁ Δ₂ : ℚ) (h : Δ₁ ≤ Δ₂)
    (hB : withinCreativityBudget Q Q_admitted Δ₁) : withinCreativityBudget Q Q_admitted Δ₂ := by
  unfold withinCreativityBudget at *
  linarith

end UMST.Economics
