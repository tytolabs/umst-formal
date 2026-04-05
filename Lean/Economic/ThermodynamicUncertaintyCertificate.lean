/-
  UMST-Formal: Economic/ThermodynamicUncertaintyCertificate.lean

  Certificate **tuple** packaging macroscopic rationals for audit trails (no new physics).
-/

import Economic.EconomicTemperature
import Economic.BurdenRecursionIsAdmissible
import InfoTheory

namespace UMST.Economics

open UMST.InfoTheory

/-- Audit record: adoption information (nats), Landauer-scale joules bracket, burden scalar. -/
structure ThermodynamicUncertaintyCertificate (n m : ℕ) where
  adoptionInfo : ℝ
  econJoules : ℝ
  burden : ℚ

noncomputable def mkCertificate {n m : ℕ} (T : ℝ) (J : JointDist n m) (B : ℚ) :
    ThermodynamicUncertaintyCertificate n m :=
  ⟨adoptionInformation J, Tecon_joules T J, B⟩

theorem mkCertificate_adoption {n m : ℕ} (T : ℝ) (J : JointDist n m) (B : ℚ) :
    (mkCertificate T J B).adoptionInfo = adoptionInformation J := rfl

end UMST.Economics
