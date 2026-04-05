/-
  UMST-Formal: Economic/CreativeExplorationTolerance.lean

  If declared output charge stays inside admitted + slack, the **tolerance** predicate holds
  (no false reject on that evidence row).
-/

import Economic.CreativityBudget

namespace UMST.Economics

open Rat

theorem creativeExploration_accepted (Q Q_admitted Δ : ℚ) (h : Q ≤ Q_admitted + Δ) :
    withinCreativityBudget Q Q_admitted Δ :=
  h

end UMST.Economics
