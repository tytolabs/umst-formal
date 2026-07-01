/-
  UMST.Compat.Gate — legacy `UMST` API over the concrete cement cartridge.
-/
import Concrete.Gate
import Concrete.State
import Core.Constitutional
import Core.Gate

open UMST.Concrete
open UMST.Core

namespace UMST

abbrev ThermodynamicState := ConcreteState
abbrev Admissible := ConcreteAdmissible
abbrev AdmissibleN := ConcreteAdmissibleN

def δMass : ℚ := UMST.Core.δMass

theorem δMass_eq : δMass = 100 := rfl
def Q_hyd := UMST.Concrete.Q_hyd
def helmholtz := UMST.Concrete.helmholtz

@[simp] theorem Q_hyd_eq : Q_hyd = 450 := rfl

@[inherit_doc UMST.Concrete.helmholtz_formula] abbrev helmholtz_formula := UMST.Concrete.helmholtz_formula
@[inherit_doc UMST.Concrete.helmholtzAntitone] abbrev helmholtzAntitone := UMST.Concrete.helmholtzAntitone
@[inherit_doc UMST.Concrete.helmholtz_le_iff] abbrev helmholtz_le_iff := UMST.Concrete.helmholtz_le_iff
theorem helmholtz_ge_neg_Q_hyd {α : ℚ} (hα : α ≤ 1) : -(Q_hyd) ≤ helmholtz α :=
  UMST.Concrete.helmholtz_ge_neg_Q_hyd hα
@[inherit_doc UMST.Concrete.helmholtzGradient] abbrev helmholtzGradient := UMST.Concrete.helmholtzGradient
@[inherit_doc UMST.Concrete.helmholtzAdditive] abbrev helmholtzAdditive := UMST.Concrete.helmholtzAdditive

@[inherit_doc UMST.Concrete.gateCheck] abbrev gateCheck := UMST.Concrete.gateCheck
@[inherit_doc UMST.Concrete.gateCheckSound] abbrev gateCheckSound := UMST.Concrete.gateCheckSound
@[inherit_doc UMST.Concrete.gateCheckComplete] abbrev gateCheckComplete := UMST.Concrete.gateCheckComplete
@[inherit_doc UMST.Concrete.clausiusDuhemFwd] abbrev clausiusDuhemFwd := UMST.Concrete.clausiusDuhemFwd
@[inherit_doc UMST.Concrete.forwardHydrationAdmissible] abbrev forwardHydrationAdmissible :=
  UMST.Concrete.forwardHydrationAdmissible
@[inherit_doc UMST.Concrete.admissibleRefl] abbrev admissibleRefl := UMST.Concrete.admissibleRefl

def MassCond := UMST.Concrete.MassCond
def DissipCond := UMST.Concrete.DissipCond
def HydratCond := UMST.Concrete.HydratCond
def StrengthCond := UMST.Concrete.StrengthCond

@[inherit_doc UMST.Concrete.admissibleIffCSG] abbrev admissibleIffCSG := UMST.Concrete.admissibleIffCSG
@[inherit_doc UMST.Concrete.admissible_iff_admissibleN1] abbrev admissible_iff_admissibleN1 :=
  UMST.Concrete.admissible_iff_admissibleN1
@[inherit_doc UMST.Concrete.admissibleNRefl] abbrev admissibleNRefl := UMST.Concrete.admissibleNRefl
theorem admissibleN_compose {m n : ℕ} {s s' s'' : ThermodynamicState}
    (h1 : AdmissibleN m s s') (h2 : AdmissibleN n s' s'') :
    AdmissibleN (m + n) s s'' :=
  UMST.Concrete.admissibleN_compose h1 h2

/-- Legacy constitutional path type over cement states. -/
abbrev ConstitutionalSeq := @UMST.Core.ConstitutionalSeq ConcreteState _ _

theorem subjectReduction (s1 s2 : ThermodynamicState) (rest : List ThermodynamicState) :
    ConstitutionalSeq (s1 :: s2 :: rest) → ConstitutionalSeq (s2 :: rest) :=
  @UMST.Core.subjectReduction ConcreteState _ _ s1 s2 rest

theorem kleisliAdmissibility (seq : List ThermodynamicState) (hseq : ConstitutionalSeq seq) :
    ∀ (i : Nat) (s1 s2 : ThermodynamicState),
      seq.get? i = some s1 → seq.get? (i + 1) = some s2 → Admissible s1 s2 :=
  @UMST.Core.kleisliAdmissibility ConcreteState _ _ seq hseq

/-- Flat constructor (legacy four-conjunct API). -/
def Admissible.mk (old new : ThermodynamicState)
    (massDensity : |new.density - old.density| ≤ δMass)
    (clausiusDuhem : new.freeEnergy ≤ old.freeEnergy)
    (hydrationMono : old.hydration ≤ new.hydration)
    (strengthMono : old.strength ≤ new.strength) : Admissible old new :=
  ⟨⟨massDensity, clausiusDuhem⟩, hydrationMono, strengthMono⟩

namespace Admissible
def massDensity {old new} (h : Admissible old new) := h.core.massDensity
def clausiusDuhem {old new} (h : Admissible old new) := h.core.clausiusDuhem
end Admissible

def AdmissibleN.mk (n : ℕ) (old new : ThermodynamicState)
    (massDensity : |new.density - old.density| ≤ (n : ℚ) * δMass)
    (clausiusDuhem : new.freeEnergy ≤ old.freeEnergy)
    (hydrationMono : old.hydration ≤ new.hydration)
    (strengthMono : old.strength ≤ new.strength) : AdmissibleN n old new :=
  ⟨⟨massDensity, clausiusDuhem⟩, hydrationMono, strengthMono⟩

namespace AdmissibleN
def massDensity {n old new} (h : AdmissibleN n old new) := h.core.massDensity
def clausiusDuhem {n old new} (h : AdmissibleN n old new) := h.core.clausiusDuhem
end AdmissibleN

end UMST
