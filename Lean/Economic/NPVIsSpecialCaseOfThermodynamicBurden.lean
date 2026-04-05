/-
  UMST-Formal: Economic/NPVIsSpecialCaseOfThermodynamicBurden.lean

  With **zero entropy tax** (`ε = 0`), iterated burden is arithmetic growth `B + n·g` — the discrete
  analogue of constant-cashflow NPV accumulation without thermodynamic correction.
-/

import Economic.BurdenRecursionIsAdmissible

namespace UMST.Economics

open Rat

/-- One step with no entropy tax is pure drift `B ↦ B + g`. -/
theorem burdenStep_no_entropy (B g : ℚ) : burdenStep B g 0 = B + g := by
  simp [burdenStep]

/-- Iterated burden with `ε = 0` equals `B + n * g`. -/
theorem npv_as_burden_iterate_no_entropy (n : ℕ) (B g : ℚ) :
    burdenIterate n g 0 B = B + n * g := by
  induction n with
  | zero => simp [burdenIterate]
  | succ n ih =>
    simp [burdenIterate, Function.iterate_succ_apply', burdenStep, ih]
    ring

end UMST.Economics
