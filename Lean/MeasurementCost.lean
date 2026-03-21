/-
  UMST-Formal: MeasurementCost.lean
  
  Formal bounds on the physical energy required to perform a measurement,
  linking information gain (mutual information) to Landauer's principle.
-/

import InfoTheory
import LandauerLaw

open Real UMST LandauerLaw UMST.InfoTheory

namespace UMST.MeasurementCost

/-- 
  The absolute minimum energy required to perform a measurement that correlates 
  the system state X with a probe Y, gaining Mutual Information I(X;Y).
  By Landauer's Principle, erasing the generated records requires energy
  equal to `kB * T * I` (where I is in nats). This sets a physical
  lower bound on the acquisition/erasure cycle cost.
-/
noncomputable def measurementEnergyLowerBound {n m : ℕ} (T : ℝ) (J : JointDist n m) : ℝ :=
  mutualInformation J * (kB * T)

/-- 
  A trivial bound: if the measurement gains zero information (product joint), 
  the theoretic lower energy bound for the acquisition is zero.
-/
theorem zero_info_zero_energy {n m : ℕ} (T : ℝ) (p : ProbDist n) (q : ProbDist m) :
    measurementEnergyLowerBound T (JointDist.productJoint p q) = 0 := by
  unfold measurementEnergyLowerBound
  rw [JointDist.mutualInformation_product_zero p q]
  ring

end UMST.MeasurementCost
