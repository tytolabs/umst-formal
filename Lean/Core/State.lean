/-
  UMST.Core.State — material-agnostic thermodynamic interfaces.
-/
import Mathlib.Algebra.Order.Field.Rat

namespace UMST.Core

/-- Any thermodynamic state carries density and Helmholtz free energy (ℚ-exact). -/
class ThermodynamicSystem (S : Type) where
  density    : S → ℚ
  freeEnergy : S → ℚ

/-- Graded admissibility graph on states: 1-step edge predicate + N-step path predicate. -/
class AdmissibleSystem (S : Type) [ThermodynamicSystem S] where
  admissibleStep  : S → S → Prop
  admissibleNStep : ℕ → S → S → Prop
  admissible_iff_admissibleN1 :
    ∀ s s', admissibleStep s s' ↔ admissibleNStep 1 s s'
  admissibleN_refl : ∀ n s, admissibleNStep n s s
  admissibleN_compose :
    ∀ {m n s s' s''},
      admissibleNStep m s s' → admissibleNStep n s' s'' → admissibleNStep (m + n) s s''

variable {S : Type} [ThermodynamicSystem S] [AdmissibleSystem S]

/-- Single-step admissibility (edge in the state transition graph). -/
abbrev Admissible (s s' : S) : Prop :=
  AdmissibleSystem.admissibleStep s s'

/-- N-step admissibility (path of length ≤ n in the weighted graph). -/
abbrev AdmissibleN (n : ℕ) (s s' : S) : Prop :=
  AdmissibleSystem.admissibleNStep n s s'

end UMST.Core
