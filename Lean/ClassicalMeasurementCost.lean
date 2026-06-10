/-
  UMST-Formal: ClassicalMeasurementCost.lean

  Classical (probabilistic) measurement-energy lower bounds linking mutual
  information to Landauer's principle. Renamed from `MeasurementCost` to avoid
  collision with `umst-formal-double-slit/Lean/MeasurementCost.lean` (quantum
  path-probe layer).
-/

import InfoTheory
import LandauerLaw

open Real UMST LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist

namespace UMST.ClassicalMeasurementCost

/-- Minimum energy to correlate system X with probe Y gaining MI I(X;Y) (nats × k_B T). -/
noncomputable def measurementEnergyLowerBound {n m : ℕ} (T : ℝ) (J : JointDist n m) : ℝ :=
  mutualInformation J * (kB * T)

/-- Zero information (product joint) → zero acquisition lower bound. -/
theorem zero_info_zero_energy {n m : ℕ} (T : ℝ) (p : ProbDist n) (q : ProbDist m) :
    measurementEnergyLowerBound T (JointDist.productJoint p q) = 0 := by
  unfold measurementEnergyLowerBound
  rw [mutualInformation_product_zero p q]
  ring

end UMST.ClassicalMeasurementCost
