/-
  UMST-Formal: Economic/EpistemicSensingModule.lean

  **MI minimization** on independent product joints: `I(X:Y)=0` for `p⊗q` (no wasted probing).
-/

import InfoTheory

namespace UMST.Economics

open UMST.InfoTheory JointDist UMST.LandauerLaw

theorem epistemicSensing_product_mutualInformation_zero (n m : ℕ) (p : ProbDist n) (q : ProbDist m) :
    mutualInformation (JointDist.productJoint p q) = 0 :=
  mutualInformation_product_zero p q

end UMST.Economics
