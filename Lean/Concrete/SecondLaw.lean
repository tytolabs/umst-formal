-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Concrete/SecondLaw.lean

  The cement cartridge composes over the one predicate `UMST.ProcessFamily.SecondLaw`. A cement state is seen by
  the predicate through `toReal` (density and free energy cast from ℚ to ℝ); the cast is an order embedding that
  carries the mass tolerance δMass = 100 to itself, so

  * the universal core of the cement gate is exactly the `transition` instance (`coreAdmissible_iff_secondLaw`);
  * cement admissibility is the `transition` instance with the constitutive order constraints, hydration and
    strength non-decreasing (`concreteAdmissible_iff_secondLaw`), and a passing runtime `gateCheck` is a member of
    the predicate (`gateCheck_secondLaw`);
  * for states of the Helmholtz model ψ = −Q_hyd·α, a step within the mass tolerance is a member of the predicate
    exactly when hydration does not go backwards (`helmholtz_secondLaw_iff`): the irreversibility of hydration is
    the second law, derived here and not assumed.
-/

import Process
import Concrete.Helmholtz

open UMST.Core UMST.Real UMST.ProcessFamily

namespace UMST.Concrete.SecondLaw

/-- The cement state as the predicate's continuous thermodynamic state. -/
noncomputable def toReal (s : ConcreteState) : RealThermodynamicState :=
  ⟨(s.density : ℝ), (s.freeEnergy : ℝ)⟩

/-- The universal core of the cement gate is exactly the `transition` instance of the second law. -/
theorem coreAdmissible_iff_secondLaw (old new : ConcreteState) :
    CoreAdmissible ℚ ConcreteState old new ↔
      SecondLaw .transition (.thermodynamic (toReal old) (toReal new)) := by
  show CoreAdmissible ℚ ConcreteState old new ↔ CoreAdmissible ℝ RealThermodynamicState (toReal old) (toReal new)
  rw [coreAdmissible_iff_mass_dissip, coreAdmissible_iff_mass_dissip]
  have hm : (|(new.density : ℝ) - old.density| ≤ (100 : ℝ)) ↔ |new.density - old.density| ≤ (100 : ℚ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs, show (100 : ℝ) = ((100 : ℚ) : ℝ) by norm_num, Rat.cast_le]
  simp only [CoreMassCond, CoreDissipCond, toReal]
  exact and_congr (by simpa [δMass] using hm.symm) (Rat.cast_le).symm

/-- Cement admissibility is the `transition` instance of the second law with the constitutive order constraints. -/
theorem concreteAdmissible_iff_secondLaw (old new : ConcreteState) :
    ConcreteAdmissible old new ↔
      SecondLaw .transition (.thermodynamic (toReal old) (toReal new)) ∧
        old.hydration ≤ new.hydration ∧ old.strength ≤ new.strength := by
  rw [← coreAdmissible_iff_secondLaw]
  exact ⟨fun h => ⟨h.core, h.hydrationMono, h.strengthMono⟩, fun ⟨c, hh, hs⟩ => ⟨c, hh, hs⟩⟩

/-- A step the runtime gate passes is a member of the second-law predicate. -/
theorem gateCheck_secondLaw (old new : ConcreteState) (h : gateCheck old new = true) :
    SecondLaw .transition (.thermodynamic (toReal old) (toReal new)) :=
  ((concreteAdmissible_iff_secondLaw old new).1 (gateCheckSound old new h)).1

/-- **Hydration is irreversible by the second law.** For states of the Helmholtz model, a step within the mass
    tolerance is a member of the predicate exactly when hydration does not go backwards. -/
theorem helmholtz_secondLaw_iff (old new : ConcreteState) (ho : HelmholtzState old) (hn : HelmholtzState new)
    (mass : |new.density - old.density| ≤ δMass) :
    SecondLaw .transition (.thermodynamic (toReal old) (toReal new)) ↔ old.hydration ≤ new.hydration := by
  rw [← coreAdmissible_iff_secondLaw, coreAdmissible_iff_mass_dissip]
  have hd : CoreDissipCond ℚ ConcreteState old new ↔ new.freeEnergy ≤ old.freeEnergy := Iff.rfl
  rw [hd]
  unfold HelmholtzState at ho hn
  rw [ho, hn, UMST.helmholtz, helmholtz_le_iff]
  exact ⟨fun h => h.2, fun h => ⟨mass, h⟩⟩

end UMST.Concrete.SecondLaw
