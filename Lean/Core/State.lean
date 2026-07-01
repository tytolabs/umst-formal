/-
  UMST.Core.State — material-agnostic thermodynamic interfaces.
-/
import Core.Scalar

namespace UMST.Core

/-- Any thermodynamic state carries density and Helmholtz free energy over scalar field `K`. -/
class ThermodynamicSystem (K : outParam Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type) where
  density    : S → K
  freeEnergy : S → K

/-- Graded admissibility graph on states: 1-step edge predicate + N-step path predicate. -/
class AdmissibleSystem (K : outParam Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type)
    [ThermodynamicSystem K S] where
  admissibleStep  : S → S → Prop
  admissibleNStep : ℕ → S → S → Prop
  admissible_iff_admissibleN1 :
    ∀ s s', admissibleStep s s' ↔ admissibleNStep 1 s s'
  admissibleN_refl : ∀ n s, admissibleNStep n s s
  admissibleN_compose :
    ∀ {m n s s' s''},
      admissibleNStep m s s' → admissibleNStep n s' s'' → admissibleNStep (m + n) s s''

/-- Single-step admissibility (edge in the state transition graph). -/
abbrev Admissible {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (s s' : S) : Prop :=
  @AdmissibleSystem.admissibleStep K _ _ S _ _ s s'

/-- N-step admissibility (path of length ≤ n in the weighted graph). -/
abbrev AdmissibleN {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (n : ℕ) (s s' : S) : Prop :=
  @AdmissibleSystem.admissibleNStep K _ _ S _ _ n s s'

end UMST.Core
