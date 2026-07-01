/-
  UMST.Concrete.Gate — OPC cement cartridge.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic
import Core.Gate
import Core.State
import Concrete.State

open Rat
open UMST.Core

namespace UMST.Concrete

/-- ℚ mass tolerance (cementitious SSOT = 100). -/
def δMass : ℚ := @UMST.Core.δMass ℚ _ _

@[simp] theorem δMass_val : δMass = 100 := UMST.Core.δMass_def_rat

/-- Latent heat of hydration (J/kg); SSOT with Agda / Coq / Rust. -/
def Q_hyd : ℚ := 450

@[simp] theorem Q_hyd_val : Q_hyd = 450 := rfl

def helmholtz (α : ℚ) : ℚ := -(Q_hyd * α)

@[simp] theorem helmholtz_formula (α : ℚ) : helmholtz α = -(Q_hyd * α) := rfl

theorem helmholtzAntitone : ∀ α₁ α₂ : ℚ, α₁ ≤ α₂ → helmholtz α₂ ≤ helmholtz α₁ := by
  intro α₁ α₂ h
  unfold helmholtz Q_hyd
  nlinarith

/-- Free-energy descent ↔ hydration ascent (Q_hyd > 0). -/
theorem helmholtz_le_iff : ∀ α₁ α₂ : ℚ, helmholtz α₂ ≤ helmholtz α₁ ↔ α₁ ≤ α₂ := by
  intro α₁ α₂
  unfold helmholtz Q_hyd
  constructor <;> intro h <;> linarith

theorem helmholtz_one : helmholtz 1 = -(Q_hyd) := by
  unfold helmholtz Q_hyd
  ring

theorem helmholtz_ge_neg_Q_hyd {α : ℚ} (hα : α ≤ 1) : -(Q_hyd) ≤ helmholtz α := by
  have := helmholtzAntitone α 1 hα
  rwa [helmholtz_one] at this

theorem helmholtzGradient : ∀ α ε : ℚ, helmholtz (α + ε) - helmholtz α = -(Q_hyd * ε) := by
  intro α ε
  unfold helmholtz
  ring

theorem helmholtzAdditive : ∀ α₁ α₂ : ℚ, helmholtz (α₁ + α₂) = helmholtz α₁ + helmholtz α₂ := by
  intro α₁ α₂
  unfold helmholtz
  ring

/-- Cement 1-step admissibility = universal core + constitutive order constraints. -/
structure ConcreteAdmissible (old new : ConcreteState) : Prop where
  core          : CoreAdmissible ℚ ConcreteState old new
  hydrationMono : old.hydration ≤ new.hydration
  strengthMono  : old.strength ≤ new.strength

/-- Graded cement admissibility (N-step mass budget). -/
structure ConcreteAdmissibleN (n : ℕ) (old new : ConcreteState) : Prop where
  core          : CoreAdmissibleN ℚ ConcreteState n old new
  hydrationMono : old.hydration ≤ new.hydration
  strengthMono  : old.strength ≤ new.strength

def gateCheck (old new : ConcreteState) : Bool :=
  decide (|new.density - old.density| ≤ δMass) &&
  decide (new.freeEnergy ≤ old.freeEnergy) &&
  decide (old.hydration ≤ new.hydration) &&
  decide (old.strength ≤ new.strength)

theorem gateCheckSound (old new : ConcreteState) :
    gateCheck old new = true → ConcreteAdmissible old new := by
  simp only [gateCheck, Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨⟨⟨hm, hd⟩, hh⟩, hs⟩
  exact ⟨⟨hm, hd⟩, hh, hs⟩

theorem gateCheckComplete (old new : ConcreteState) :
    ConcreteAdmissible old new → gateCheck old new = true := by
  intro ⟨⟨hm, hd⟩, hh, hs⟩
  simp only [gateCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hm, hd⟩, hh⟩, hs⟩

theorem clausiusDuhemFwd (s1 s2 : ConcreteState)
    (h_psi : s1.hydration ≤ s2.hydration → s2.freeEnergy ≤ s1.freeEnergy)
    (h : s1.hydration ≤ s2.hydration) : s2.freeEnergy ≤ s1.freeEnergy :=
  h_psi h

theorem forwardHydrationAdmissible (old new : ConcreteState)
    (hyd : old.hydration ≤ new.hydration)
    (mass : |new.density - old.density| ≤ δMass)
    (h_psi : old.hydration ≤ new.hydration → new.freeEnergy ≤ old.freeEnergy)
    (h_fc : old.hydration ≤ new.hydration → old.strength ≤ new.strength) :
    ConcreteAdmissible old new :=
  ⟨⟨mass, h_psi hyd⟩, hyd, h_fc hyd⟩

theorem admissibleRefl (s : ConcreteState) : ConcreteAdmissible s s := by
  constructor
  · constructor
    · simp [sub_self, abs_zero, δMass]
    · exact le_refl _
  · exact le_refl _
  · exact le_refl _

def MassCond (old new : ConcreteState) : Prop :=
  |new.density - old.density| ≤ δMass

def DissipCond (old new : ConcreteState) : Prop :=
  new.freeEnergy ≤ old.freeEnergy

def HydratCond (old new : ConcreteState) : Prop :=
  old.hydration ≤ new.hydration

def StrengthCond (old new : ConcreteState) : Prop :=
  old.strength ≤ new.strength

theorem admissibleIffCSG (old new : ConcreteState) :
    ConcreteAdmissible old new ↔
      MassCond old new ∧ DissipCond old new ∧ HydratCond old new ∧ StrengthCond old new := by
  constructor
  · intro ⟨⟨hm, hd⟩, hh, hs⟩; exact ⟨hm, hd, hh, hs⟩
  · intro ⟨hm, hd, hh, hs⟩; exact ⟨⟨hm, hd⟩, hh, hs⟩

theorem admissible_iff_admissibleN1 (old new : ConcreteState) :
    ConcreteAdmissible old new ↔ ConcreteAdmissibleN 1 old new := by
  constructor
  · intro ⟨⟨hm, hd⟩, hh, hs⟩
    refine ⟨⟨?_, hd⟩, hh, hs⟩
    simpa [one_mul] using hm
  · intro ⟨⟨hm, hd⟩, hh, hs⟩
    refine ⟨⟨?_, hd⟩, hh, hs⟩
    simpa [one_mul] using hm

theorem admissibleNRefl (n : ℕ) (s : ConcreteState) : ConcreteAdmissibleN n s s :=
  ⟨coreAdmissibleN_refl ℚ ConcreteState n s, le_refl _, le_refl _⟩

theorem admissibleN_compose {m n : ℕ} {s s' s'' : ConcreteState}
    (h1 : ConcreteAdmissibleN m s s') (h2 : ConcreteAdmissibleN n s' s'') :
    ConcreteAdmissibleN (m + n) s s'' :=
  ⟨coreAdmissibleN_compose ℚ ConcreteState h1.core h2.core,
    le_trans h1.hydrationMono h2.hydrationMono,
    le_trans h1.strengthMono h2.strengthMono⟩

instance concreteAdmissibleSystem : AdmissibleSystem ℚ ConcreteState where
  admissibleStep := ConcreteAdmissible
  admissibleNStep := ConcreteAdmissibleN
  admissible_iff_admissibleN1 := admissible_iff_admissibleN1
  admissibleN_refl := admissibleNRefl
  admissibleN_compose := admissibleN_compose

end UMST.Concrete
