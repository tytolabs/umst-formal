/-
  UMST.Core.Gate — universal thermodynamic bounds (all cartridges).
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Core.Scalar
import Core.State

namespace UMST.Core

@[simp] theorem δMass_def_rat : (δMass (K := ℚ) : ℚ) = 100 := δMass_rat_def

private def densityAt {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] (s : S) : K :=
  ThermodynamicSystem.density (K := K) (S := S) s

private def freeEnergyAt {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] (s : S) : K :=
  ThermodynamicSystem.freeEnergy (K := K) (S := S) s

/-- Universal 1-step admissibility: metric ball + free-energy descent. -/
structure CoreAdmissible (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] (old new : S) : Prop where
  massDensity : |densityAt (K := K) (S := S) new - densityAt (K := K) (S := S) old| ≤ δMass (K := K)
  clausiusDuhem : freeEnergyAt (K := K) (S := S) new ≤ freeEnergyAt (K := K) (S := S) old

/-- N-step mass budget: `n * δMass` via Lawvere-metric composition. -/
structure CoreAdmissibleN (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] (n : ℕ) (old new : S) : Prop where
  massDensity :
    |densityAt (K := K) (S := S) new - densityAt (K := K) (S := S) old| ≤ (n : K) * δMass (K := K)
  clausiusDuhem : freeEnergyAt (K := K) (S := S) new ≤ freeEnergyAt (K := K) (S := S) old

/-- Core mass condition (single-step metric edge). -/
def CoreMassCond (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] (old new : S) : Prop :=
  |densityAt (K := K) (S := S) new - densityAt (K := K) (S := S) old| ≤ δMass (K := K)

/-- Core Clausius–Duhem condition (dissipation). -/
def CoreDissipCond (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] (old new : S) : Prop :=
  freeEnergyAt (K := K) (S := S) new ≤ freeEnergyAt (K := K) (S := S) old

theorem coreAdmissible_iff_mass_dissip (K : Type) [LinearOrderedField K] [ThermodynamicScalar K]
    (S : Type) [ThermodynamicSystem K S] (old new : S) :
    CoreAdmissible K S old new ↔ CoreMassCond K S old new ∧ CoreDissipCond K S old new := by
  constructor
  · intro ⟨hm, hd⟩; exact ⟨hm, hd⟩
  · intro ⟨hm, hd⟩; exact ⟨hm, hd⟩

/-- Core mass budget composes by the triangle inequality (proved once, any cartridge). -/
theorem coreAdmissibleN_compose (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] {m n : ℕ} {s s' s'' : S}
    (h1 : CoreAdmissibleN K S m s s') (h2 : CoreAdmissibleN K S n s' s'') :
    CoreAdmissibleN K S (m + n) s s'' where
  massDensity := by
    have tri :
        |densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s| ≤
          |densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s'| +
            |densityAt (K := K) (S := S) s' - densityAt (K := K) (S := S) s| := by
      have heq :
          densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s =
            (densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s') +
              (densityAt (K := K) (S := S) s' - densityAt (K := K) (S := S) s) := by ring
      calc
        |densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s| =
            |(densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s') +
                (densityAt (K := K) (S := S) s' - densityAt (K := K) (S := S) s)| := by rw [heq]
        _ ≤ |densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s'| +
              |densityAt (K := K) (S := S) s' - densityAt (K := K) (S := S) s| := abs_add _ _
    have cast_eq : ((m + n : ℕ) : K) * δMass (K := K) = (m : K) * δMass (K := K) + (n : K) * δMass (K := K) := by
      push_cast; ring
    rw [cast_eq]
    have hsum :
        |densityAt (K := K) (S := S) s'' - densityAt (K := K) (S := S) s'| +
            |densityAt (K := K) (S := S) s' - densityAt (K := K) (S := S) s| ≤
          (m : K) * δMass (K := K) + (n : K) * δMass (K := K) := by
      simpa [add_comm] using add_le_add h1.massDensity h2.massDensity
    exact le_trans tri hsum
  clausiusDuhem := le_trans h2.clausiusDuhem h1.clausiusDuhem

theorem coreAdmissibleN_refl (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] (n : ℕ) (s : S) :
    CoreAdmissibleN K S n s s :=
  ⟨by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (ThermodynamicScalar.δMass_nonneg (K := K)),
   le_refl _⟩

theorem coreAdmissibleN_one (K : Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] (old new : S) :
    CoreAdmissibleN K S 1 old new ↔ CoreAdmissible K S old new := by
  constructor
  · intro h; exact ⟨by simpa [one_mul] using h.massDensity, h.clausiusDuhem⟩
  · intro h; exact ⟨by simpa [one_mul] using h.massDensity, h.clausiusDuhem⟩

end UMST.Core
