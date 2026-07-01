/-
  UMST.Core.Gate — universal thermodynamic bounds (all cartridges).
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic
import Core.State

open Rat

namespace UMST.Core

/-- Mass conservation tolerance (kg/m³); SSOT across Agda / Coq / Lean / Rust.

    **Provenance:** `100` is currently calibrated to cementitious bulk-density scales
    (OPC paste / normal-weight concrete). It is **not** yet material-parameterized;
    a second cartridge should supply its own tolerance via `ThermodynamicSystem` +
  `CoreAdmissible` without editing this literal until Core is generalized. -/
def δMass : ℚ := 100

@[simp] theorem δMass_def : δMass = 100 := rfl

/-- Universal 1-step admissibility: metric ball + free-energy descent. -/
structure CoreAdmissible {S : Type} [ThermodynamicSystem S] (old new : S) : Prop where
  massDensity :
    |ThermodynamicSystem.density new - ThermodynamicSystem.density old| ≤ δMass
  clausiusDuhem :
    ThermodynamicSystem.freeEnergy new ≤ ThermodynamicSystem.freeEnergy old

/-- N-step mass budget: `n * δMass` via Lawvere-metric composition. -/
structure CoreAdmissibleN {S : Type} [ThermodynamicSystem S] (n : ℕ) (old new : S) : Prop where
  massDensity :
    |ThermodynamicSystem.density new - ThermodynamicSystem.density old| ≤ (n : ℚ) * δMass
  clausiusDuhem :
    ThermodynamicSystem.freeEnergy new ≤ ThermodynamicSystem.freeEnergy old

/-- Core mass condition (single-step metric edge). -/
def CoreMassCond {S : Type} [ThermodynamicSystem S] (old new : S) : Prop :=
  |ThermodynamicSystem.density new - ThermodynamicSystem.density old| ≤ δMass

/-- Core Clausius–Duhem condition (dissipation). -/
def CoreDissipCond {S : Type} [ThermodynamicSystem S] (old new : S) : Prop :=
  ThermodynamicSystem.freeEnergy new ≤ ThermodynamicSystem.freeEnergy old

theorem coreAdmissible_iff_mass_dissip {S : Type} [ThermodynamicSystem S] (old new : S) :
    CoreAdmissible old new ↔ CoreMassCond old new ∧ CoreDissipCond old new := by
  constructor
  · intro ⟨hm, hd⟩; exact ⟨hm, hd⟩
  · intro ⟨hm, hd⟩; exact ⟨hm, hd⟩

/-- Core mass budget composes by the triangle inequality (proved once, any cartridge). -/
theorem coreAdmissibleN_compose {S : Type} [ThermodynamicSystem S] {m n : ℕ}
    {s s' s'' : S} (h1 : CoreAdmissibleN m s s') (h2 : CoreAdmissibleN n s' s'') :
    CoreAdmissibleN (m + n) s s'' where
  massDensity := by
    have tri :
        |ThermodynamicSystem.density s'' - ThermodynamicSystem.density s| ≤
          |ThermodynamicSystem.density s'' - ThermodynamicSystem.density s'| +
            |ThermodynamicSystem.density s' - ThermodynamicSystem.density s| := by
      have heq :
          ThermodynamicSystem.density s'' - ThermodynamicSystem.density s =
            (ThermodynamicSystem.density s'' - ThermodynamicSystem.density s') +
              (ThermodynamicSystem.density s' - ThermodynamicSystem.density s) := by ring
      calc
        |ThermodynamicSystem.density s'' - ThermodynamicSystem.density s|
            = |(ThermodynamicSystem.density s'' - ThermodynamicSystem.density s') +
                (ThermodynamicSystem.density s' - ThermodynamicSystem.density s)| := by rw [heq]
        _ ≤ |ThermodynamicSystem.density s'' - ThermodynamicSystem.density s'| +
              |ThermodynamicSystem.density s' - ThermodynamicSystem.density s| := abs_add _ _
    have cast_eq : ((m + n : ℕ) : ℚ) * δMass = (m : ℚ) * δMass + (n : ℚ) * δMass := by
      push_cast; ring
    rw [cast_eq]
    have hsum :
        |ThermodynamicSystem.density s'' - ThermodynamicSystem.density s'| +
            |ThermodynamicSystem.density s' - ThermodynamicSystem.density s| ≤
          (m : ℚ) * δMass + (n : ℚ) * δMass := by
      simpa [add_comm] using add_le_add h1.massDensity h2.massDensity
    exact le_trans tri hsum
  clausiusDuhem := le_trans h2.clausiusDuhem h1.clausiusDuhem

theorem coreAdmissibleN_refl {S : Type} [ThermodynamicSystem S] (n : ℕ) (s : S) :
    CoreAdmissibleN n s s :=
  ⟨by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (by norm_num [δMass]),
   le_refl _⟩

theorem coreAdmissibleN_one {S : Type} [ThermodynamicSystem S] (old new : S) :
    CoreAdmissibleN 1 old new ↔ CoreAdmissible old new := by
  constructor
  · intro h; exact ⟨by simpa [one_mul] using h.massDensity, h.clausiusDuhem⟩
  · intro h; exact ⟨by simpa [one_mul] using h.massDensity, h.clausiusDuhem⟩

end UMST.Core
