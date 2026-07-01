/-
  UMST.Real.Gate — ℝ instantiation of universal `CoreAdmissible` (subsumes double-slit mirror).
-/
import Core.Gate
import Real.State

namespace UMST.Real

/-- `CoreAdmissible` at `K = ℝ` — structurally identical to legacy `RealAdmissible`. -/
abbrev RealAdmissible (old new : RealThermodynamicState) : Prop :=
  UMST.Core.CoreAdmissible ℝ RealThermodynamicState old new

theorem realAdmissibleRefl (s : RealThermodynamicState) : RealAdmissible s s :=
  (UMST.Core.coreAdmissibleN_one ℝ RealThermodynamicState s s).mp
    (UMST.Core.coreAdmissibleN_refl ℝ RealThermodynamicState 1 s)

theorem realAdmissible_eq_core (old new : RealThermodynamicState) :
    RealAdmissible old new ↔ UMST.Core.CoreAdmissible ℝ RealThermodynamicState old new :=
  Iff.rfl

end UMST.Real
