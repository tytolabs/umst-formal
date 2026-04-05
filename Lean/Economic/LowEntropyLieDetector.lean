/-
  UMST-Formal: Economic/LowEntropyLieDetector.lean

  **Classical surrogate:** compare a declared marginal bound to adoption information.
  “Lie” here means only: hypothesis `H_small` contradicts measured lower bound.
-/

import Economic.EconomicTemperature
import InfoTheory

namespace UMST.Economics

open UMST.InfoTheory

/-- If adoption information **exceeds** a claimed upper bound `H_decl`, the pair is inconsistent. -/
def inconsistentInformationClaim {n m : ℕ} (J : JointDist n m) (H_decl : ℝ) : Prop :=
  H_decl < adoptionInformation J

theorem inconsistentInformationClaim_of_lt {n m : ℕ} (J : JointDist n m) (H_decl : ℝ)
    (h : H_decl < adoptionInformation J) : inconsistentInformationClaim J H_decl :=
  h

end UMST.Economics
