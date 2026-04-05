/-
  UMST-Formal: Economic/NuanceIsolator.lean

  **Bookkeeping split** `Q = Q_productive + Q_waste` on `ℚ` (user assigns components).
  “Nuance score” ratios belong in analytics, not as hidden axioms here.
-/

import Economic.EconomicDomain
import Mathlib.Tactic.Linarith

namespace UMST.Economics

open Rat

theorem cost_split_sum (Q_productive Q_waste : ℚ) : Q_productive + Q_waste = Q_productive + Q_waste :=
  rfl

/-- If both parts are nonnegative, total charge is nonnegative. -/
theorem cost_split_nonneg_of_nonneg (Q_productive Q_waste : ℚ)
    (hp : 0 ≤ Q_productive) (hw : 0 ≤ Q_waste) : 0 ≤ Q_productive + Q_waste := by
  linarith

end UMST.Economics
