/-
  UMST-Formal: Economic/HallucinationDetector.lean

  **Classical surrogate:** high adoption-side Shannon information vs a user threshold `θ`.
  Not a neural “hallucination” detector — see SAFETY-LIMITS.md.
-/

import Economic.EconomicDomain
import Economic.EconomicTemperature
import InfoTheory

namespace UMST.Economics

open UMST.InfoTheory UMST.LandauerLaw

/-- Surrogate flag: adoption marginal entropy exceeds threshold. -/
def highAdoptionInformation {n m : ℕ} (J : JointDist n m) (th : InfoThreshold) : Prop :=
  th.θ < adoptionInformation J

/-- Product joint carries only `S(q)` on the adoption side; if `S(q) ≤ θ`, the alarm is **off**. -/
theorem highAdoptionInformation_product_off {n m : ℕ} (p : ProbDist n) (q : ProbDist m) (th : InfoThreshold)
    (hq : shannonEntropy q ≤ th.θ) : ¬ highAdoptionInformation (JointDist.productJoint p q) th := by
  intro h
  rw [highAdoptionInformation, adoptionInformation_product] at h
  linarith [hq, h]

end UMST.Economics
