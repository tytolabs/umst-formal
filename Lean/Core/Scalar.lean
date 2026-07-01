/-
  UMST.Core.Scalar — per-field mass tolerance and minimal ordered-field structure for K.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Real.Basic

namespace UMST.Core

/-- Minimal scalar-field data for thermodynamic gate laws.

    Extends `LinearOrderedField` because Core proofs use `abs_add`, `ring`, `Nat.cast`,
    and `mul_nonneg` on `δMass` (see `Core.Gate.coreAdmissibleN_compose` / `coreAdmissibleN_refl`). -/
class ThermodynamicScalar (K : Type) [LinearOrderedField K] where
  /-- Mass conservation tolerance (kg/m³); cementitious SSOT = `100`. -/
  δMass : K
  δMass_nonneg : 0 ≤ δMass

/-- Mass tolerance for the active scalar field `K`. -/
def δMass {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] : K :=
  ThermodynamicScalar.δMass

instance thermodynamicScalarRat : ThermodynamicScalar ℚ where
  δMass := 100
  δMass_nonneg := by norm_num

@[simp] theorem δMass_rat_def : (δMass (K := ℚ) : ℚ) = 100 := rfl

instance thermodynamicScalarReal : ThermodynamicScalar ℝ where
  δMass := 100
  δMass_nonneg := by norm_num

@[simp] theorem δMass_real_def : (δMass (K := ℝ) : ℝ) = 100 := rfl

end UMST.Core
