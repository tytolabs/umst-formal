-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- Convex.PassiveRoute — the passive route into the transition case of SecondLaw (twin of
-- Lean/Convex/PassiveRoute.lean, of the passive cartridge law of Lean/ConvexPhiDissipation.lean and of
-- Coq/Convex/PassiveRoute.v).
--
-- A passive step supplies no power: (ψ_new − ψ_old) + D = 0 with the mass condition of the gate. On such a step the
-- transition case of SecondLaw holds exactly when D ≥ 0 (passive-secondLaw-⇔). Forward, a convex dissipation
-- potential φ ≥ 0 with φ 0 = 0 makes the power D = x · dφ x non-negative (gsmCartridge-passive-secondLaw); backward,
-- a SecondLaw step whose dissipation has a constitutive form bounds the coefficient
-- (dissipation-nonneg-of-secondLaw). Agda carries a potential over the rationals in supporting-line form: φ with a
-- slope dφ such that φ x + dφ x · (y − x) ≤ φ y, convexity with a subgradient, the rational twin of Lean's convex
-- differentiable φ with its derivative.
------------------------------------------------------------------------

module Convex.PassiveRoute where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_; _+_; _*_; _-_; -_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-irrefl; +-monoˡ-≤; +-monoʳ-≤;
  +-identityˡ; +-identityʳ; +-inverseʳ; neg-antimono-≤)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Concrete.Gate using (ThermodynamicState; mkState)
open import Core.Gate using (δ-mass; CoreAdmissible)
open import Process using (SecondLaw; transition; thermodynamic)

open ThermodynamicState using (density; free-energy)
open +-*-Solver

------------------------------------------------------------------------
-- The passive balance and the passive route
------------------------------------------------------------------------

-- The mass condition of the gate.
MassBall : ThermodynamicState → ThermodynamicState → Set
MassBall old new = (density new - density old ≤ δ-mass) × (density old - density new ≤ δ-mass)

-- Passive balance of one step dissipating d: the mass condition and Δψ + d = 0 (no supplied power).
record PassiveBalance (d : ℚ) (old new : ThermodynamicState) : Set where
  field
    mass    : MassBall old new
    balance : (free-energy new - free-energy old) + d ≡ 0ℚ

open PassiveBalance

private
  -- Δψ + d ≤ 0 with d ≥ 0 gives descent: b ≤ a.
  descent : ∀ {a b d} → 0ℚ ≤ d → (b - a) + d ≤ 0ℚ → b ≤ a
  descent {a} {b} {d} hd h =
    ≤-trans (subst₂ _≤_ (e₁ a b d) (+-identityˡ (a - d)) (+-monoˡ-≤ (a - d) h))
            (subst (a - d ≤_) (+-identityʳ a) (+-monoʳ-≤ a (neg-antimono-≤ hd)))
    where
      e₁ : ∀ a b d → (b - a) + d + (a - d) ≡ b
      e₁ = solve 3 (λ a b d → (b :- a) :+ d :+ (a :- d) := b) refl

  -- b ≤ a with (b − a) + d = 0 gives d ≥ 0.
  released-nonneg : ∀ {a b d} → b ≤ a → (b - a) + d ≡ 0ℚ → 0ℚ ≤ d
  released-nonneg {a} {b} {d} hba hb = subst (0ℚ ≤_) (sym deq) h0
    where
      h0 : 0ℚ ≤ a - b
      h0 = subst (_≤ a - b) (+-inverseʳ b) (+-monoˡ-≤ (- b) hba)
      e : ∀ a b d → d ≡ ((b - a) + d) + (a - b)
      e = solve 3 (λ a b d → d := ((b :- a) :+ d) :+ (a :- b)) refl
      deq : d ≡ a - b
      deq = trans (e a b d) (trans (cong (_+ (a - b)) hb) (+-identityˡ (a - b)))

-- The passive route: on a passive balance the transition case of SecondLaw holds exactly when d ≥ 0.
passive-secondLaw-⇔ : ∀ {d old new} → PassiveBalance d old new → SecondLaw transition (thermodynamic old new) ⇔ (0ℚ ≤ d)
passive-secondLaw-⇔ h = mk⇔
  (λ s → released-nonneg (CoreAdmissible.dissipation-nonneg s) (balance h))
  (λ hd → record { mass-conserved = mass h ; dissipation-nonneg = descent hd (≤-reflexive (balance h)) })

-- The released free energy ψ_old − ψ_new is the dissipation of a passive balance in the mass ball.
passiveBalance-released : ∀ {old new} → MassBall old new → PassiveBalance (free-energy old - free-energy new) old new
passiveBalance-released {old} {new} m = record { mass = m ; balance = e (free-energy old) (free-energy new) }
  where
    e : ∀ a b → (b - a) + (a - b) ≡ 0ℚ
    e = solve 2 (λ a b → (b :- a) :+ (a :- b) := con 0ℚ) refl

-- Bounds through the passive route: a SecondLaw step whose balance names its dissipation d has d ≥ 0.
dissipation-nonneg-of-secondLaw : ∀ {d old new} → SecondLaw transition (thermodynamic old new) →
  (free-energy new - free-energy old) + d ≡ 0ℚ → 0ℚ ≤ d
dissipation-nonneg-of-secondLaw s hb =
  Equivalence.to (passive-secondLaw-⇔ (record { mass = CoreAdmissible.mass-conserved s ; balance = hb })) s

-- A step from free energy ψ that dissipates d obeys the second law only with d ≥ 0.
step-dissipation-nonneg : ∀ ρ ρ' ψ d →
  SecondLaw transition (thermodynamic (mkState ρ ψ 0ℚ 0ℚ) (mkState ρ' (ψ - d) 0ℚ 0ℚ)) → 0ℚ ≤ d
step-dissipation-nonneg ρ ρ' ψ d s = dissipation-nonneg-of-secondLaw s (e ψ d)
  where
    e : ∀ ψ d → ((ψ - d) - ψ) + d ≡ 0ℚ
    e = solve 2 (λ ψ d → ((ψ :- d) :- ψ) :+ d := con 0ℚ) refl

-- A passive relaxation from a stored free energy ψ to the natural state dissipates ψ: ψ ≥ 0.
relaxation-stored-nonneg : ∀ ρ ρ' ψ →
  SecondLaw transition (thermodynamic (mkState ρ ψ 0ℚ 0ℚ) (mkState ρ' 0ℚ 0ℚ 0ℚ)) → 0ℚ ≤ ψ
relaxation-stored-nonneg ρ ρ' ψ s = dissipation-nonneg-of-secondLaw s (e ψ)
  where
    e : ∀ ψ → (0ℚ - ψ) + ψ ≡ 0ℚ
    e = solve 1 (λ ψ → (con 0ℚ :- ψ) :+ ψ := con 0ℚ) refl

-- Inequality form: Δψ + d ≤ 0 with d ≥ 0 and the mass condition is a SecondLaw step.
passive-inequality-secondLaw : ∀ {d old new} → MassBall old new → 0ℚ ≤ d →
  (free-energy new - free-energy old) + d ≤ 0ℚ → SecondLaw transition (thermodynamic old new)
passive-inequality-secondLaw {d} {old} {new} m hd hb =
  Equivalence.from (passive-secondLaw-⇔ (passiveBalance-released m))
    (released-nonneg {free-energy old} {free-energy new} (descent {free-energy old} {free-energy new} hd hb)
      (balance (passiveBalance-released {old} {new} m)))

-- Refusal through the passive route: a balance Δψ + d = 0 with d < 0 is refused.
passive-refused-of-neg : ∀ {d old new} → (free-energy new - free-energy old) + d ≡ 0ℚ → d < 0ℚ →
  ¬ SecondLaw transition (thermodynamic old new)
passive-refused-of-neg hb hn s = <-irrefl refl (≤-<-trans (dissipation-nonneg-of-secondLaw s hb) hn)

------------------------------------------------------------------------
-- The convex dissipation potential and the passive cartridge law
------------------------------------------------------------------------

-- A GSM dissipation potential: convex in supporting-line form, non-negative, zero at zero.
record GsmDissipationPotential : Set where
  field
    φ        : ℚ → ℚ
    dφ       : ℚ → ℚ
    support  : ∀ x y → φ x + dφ x * (y - x) ≤ φ y
    φ-nonneg : ∀ x → 0ℚ ≤ φ x
    φ-zero   : φ 0ℚ ≡ 0ℚ

open GsmDissipationPotential

-- Dissipation power at rate x: D = x · dφ x.
dissipationPower : GsmDissipationPotential → ℚ → ℚ
dissipationPower P x = x * dφ P x

-- The supporting line at x through 0: φ x ≤ x · dφ x.
convex-phi-le-dissipationPower : ∀ P x → φ P x ≤ dissipationPower P x
convex-phi-le-dissipationPower P x =
  subst₂ _≤_ (e₁ (φ P x) (dφ P x) x) (+-identityˡ (x * dφ P x)) (+-monoˡ-≤ (x * dφ P x) h)
  where
    h : φ P x + dφ P x * (0ℚ - x) ≤ 0ℚ
    h = subst (φ P x + dφ P x * (0ℚ - x) ≤_) (φ-zero P) (support P x 0ℚ)
    e₁ : ∀ a d x → a + d * (0ℚ - x) + x * d ≡ a
    e₁ = solve 3 (λ a d x → a :+ d :* (con 0ℚ :- x) :+ x :* d := a) refl

-- Non-negative dissipation from a convex, non-negative potential pinned at zero.
convex-phi-dissipation-nonneg : ∀ P x → 0ℚ ≤ dissipationPower P x
convex-phi-dissipation-nonneg P x = ≤-trans (φ-nonneg P x) (convex-phi-le-dissipationPower P x)

-- A GSM cartridge packages a dissipation potential.
record GsmCartridge : Set where
  field
    dissip : GsmDissipationPotential

open GsmCartridge

-- One-step passive energy balance of a cartridge: Δψ + D = 0 with D = x · dφ x.
PassiveGsmEnergyBalance : GsmCartridge → ThermodynamicState → ThermodynamicState → ℚ → Set
PassiveGsmEnergyBalance C old new x = PassiveBalance (dissipationPower (dissip C) x) old new

-- Passive SecondLaw for a GSM cartridge: convexity gives D ≥ 0 and the passive route closes the step.
gsmCartridge-passive-secondLaw : ∀ C {old new} x → PassiveGsmEnergyBalance C old new x →
  SecondLaw transition (thermodynamic old new)
gsmCartridge-passive-secondLaw C x h =
  Equivalence.from (passive-secondLaw-⇔ h) (convex-phi-dissipation-nonneg (dissip C) x)
