-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
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

/-- Joint thermodynamic fields for Excitement's free-energy functional (distinct from Helmholtz `freeEnergy`). -/
class JointThermo (K : outParam Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type) where
  internalEnergy : S → K
  entropy        : S → K
  mutualInfo     : S → K
  temperature    : S → K
  temperature_pos : ∀ s, 0 < temperature s

end UMST.Core
