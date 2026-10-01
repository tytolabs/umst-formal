-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Concrete/SecondLaw.agda
--
-- Twin of Lean/Concrete/SecondLaw.lean: the cement cartridge composes over the one predicate. Cement admissibility is
-- the transition instance with hydration and strength non-decreasing; a passing gate is a member of the predicate; for
-- Helmholtz states a step within the mass tolerance is a member exactly when hydration does not go backwards (the
-- irreversibility of hydration, derived).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Concrete.SecondLaw where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; _≤_; _-_; -_; Positive)
open import Data.Rational.Properties using (neg-antimono-≤; *-cancelˡ-≤-pos)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import Relation.Nullary.Decidable.Core using (True; toWitness)

open import Core.Gate using (δ-mass; CoreAdmissible)
open import Concrete.Gate using (ThermodynamicState; Admissible; mkAdmissible; gate)
open import Concrete.Helmholtz using (Q-hyd; helmholtz; helmholtz-antitone; HelmholtzState)
open import Process using (SecondLaw; transition; thermodynamic)
open ThermodynamicState

-- Cement admissibility is the transition instance of the second law with the constitutive order constraints.
admissible⇔secondLaw : ∀ old new → Admissible old new ⇔
  (SecondLaw transition (thermodynamic old new) × hydration old ≤ hydration new × strength old ≤ strength new)
admissible⇔secondLaw old new = mk⇔
  (λ a → record { mass-conserved = Admissible.mass-conserved a ; dissipation-nonneg = Admissible.dissipation-nonneg a }
         , Admissible.hydration-monotone a , Admissible.strength-monotone a)
  (λ (c , h , s) → mkAdmissible (CoreAdmissible.mass-conserved c) (CoreAdmissible.dissipation-nonneg c) h s)

-- A step the gate passes is a member of the second-law predicate.
gate-secondLaw : ∀ old new → True (gate old new) → SecondLaw transition (thermodynamic old new)
gate-secondLaw old new t = proj₁ (Equivalence.to (admissible⇔secondLaw old new) (toWitness t))

open +-*-Solver

neg-neg : ∀ x → - (- x) ≡ x
neg-neg = solve 1 (λ x → :- (:- x) := x) refl

instance
  Q-hyd-pos : Positive Q-hyd
  Q-hyd-pos = _

-- The Helmholtz free energy decreases exactly when hydration advances.
helmholtz-≤⇔ : ∀ α₁ α₂ → (helmholtz α₂ ≤ helmholtz α₁) ⇔ (α₁ ≤ α₂)
helmholtz-≤⇔ α₁ α₂ = mk⇔
  (λ h → *-cancelˡ-≤-pos Q-hyd
           (subst₂ _≤_ (neg-neg _) (neg-neg _) (neg-antimono-≤ h)))
  (helmholtz-antitone α₁ α₂)

-- Hydration is irreversible by the second law: for Helmholtz states within the mass tolerance, a step is a member of
-- the predicate exactly when hydration does not go backwards.
helmholtz-secondLaw⇔ : ∀ old new → HelmholtzState old → HelmholtzState new →
  (density new - density old ≤ δ-mass) × (density old - density new ≤ δ-mass) →
  SecondLaw transition (thermodynamic old new) ⇔ (hydration old ≤ hydration new)
helmholtz-secondLaw⇔ old new ho hn mass = mk⇔
  (λ c → Equivalence.to (helmholtz-≤⇔ (hydration old) (hydration new))
           (subst₂ _≤_ hn ho (CoreAdmissible.dissipation-nonneg c)))
  (λ h → record { mass-conserved = mass
                ; dissipation-nonneg = subst₂ _≤_ (sym hn) (sym ho)
                    (Equivalence.from (helmholtz-≤⇔ (hydration old) (hydration new)) h) })
