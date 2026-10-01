-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST.Concrete.Helmholtz — Helmholtz free-energy model (OPC cartridge).
--
-- FORMAL-AGDA-HELMHOLTZ: zero postulate lines; ordered-field proofs on ℚ.
-- Concrete arithmetic witness (Gate ψ-antitone
-- remains a separate physical-model interface).
------------------------------------------------------------------------

module Concrete.Helmholtz where

open import Data.Rational as ℚ using (ℚ; 0ℚ; normalize; _+_; _*_; _-_; _≤_; -_; NonNegative)
open import Data.Rational.Properties as ℚ-Props
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)
  renaming (sym to ≡-sym)
open import Data.Product using (_×_; _,_)

open import Concrete.Gate using (ThermodynamicState)
import Constants.SI as SI
open ThermodynamicState

------------------------------------------------------------------------
-- 1. Physical Constants
------------------------------------------------------------------------

-- Heat of complete hydration [J/g = kJ/kg]: the policy row hydrationHeatDefault of Constants/SI.agda, proved to lie
-- between the least and greatest cited phase heats (hydrationHeatDefault-in-range).
Q-hyd : ℚ
Q-hyd = ℚ.fromℚᵘ SI.hydrationHeatDefault

private
  instance
    nonNeg-Q-hyd : NonNegative Q-hyd
    nonNeg-Q-hyd = _

------------------------------------------------------------------------
-- 2. The Helmholtz Free-Energy Model
------------------------------------------------------------------------

helmholtz : ℚ → ℚ
helmholtz α = - (Q-hyd * α)

------------------------------------------------------------------------
-- 3. Antitone Lemma (Concrete Arithmetic)
------------------------------------------------------------------------

helmholtz-antitone : ∀ (α₁ α₂ : ℚ) → α₁ ≤ α₂ → helmholtz α₂ ≤ helmholtz α₁
helmholtz-antitone α₁ α₂ α₁≤α₂ =
  ℚ-Props.neg-antimono-≤ (ℚ-Props.*-monoˡ-≤-nonNeg Q-hyd α₁≤α₂)

------------------------------------------------------------------------
-- 4. HelmholtzState: States Satisfying the Model
------------------------------------------------------------------------

HelmholtzState : ThermodynamicState → Set
HelmholtzState s = free-energy s ≡ helmholtz (hydration s)

------------------------------------------------------------------------
-- 5. ψ-antitone for Helmholtz States
------------------------------------------------------------------------

ψ-antitone-helmholtz :
  ∀ (s₁ s₂ : ThermodynamicState) →
  HelmholtzState s₁ →
  HelmholtzState s₂ →
  hydration s₁ ≤ hydration s₂ →
  free-energy s₂ ≤ free-energy s₁
ψ-antitone-helmholtz s₁ s₂ h₁ h₂ α-adv =
  ℚ-Props.≤-trans
    (ℚ-Props.≤-trans
      (ℚ-Props.≤-reflexive h₂)
      (helmholtz-antitone (hydration s₁) (hydration s₂) α-adv))
    (ℚ-Props.≤-reflexive (≡-sym h₁))

------------------------------------------------------------------------
-- 6. Linearity and Gradient Theorem (SDF Interpretation)
------------------------------------------------------------------------

helmholtz-linear : ∀ (α₁ α₂ : ℚ) →
  helmholtz (α₁ + α₂) ≡ helmholtz α₁ + helmholtz α₂
helmholtz-linear α₁ α₂ =
  trans
    (cong -_ (ℚ-Props.*-distribˡ-+ Q-hyd α₁ α₂))
    (ℚ-Props.neg-distrib-+ (Q-hyd * α₁) (Q-hyd * α₂))

private
  helmholtz-add-cancel : ∀ (α ε : ℚ) →
    helmholtz α + helmholtz ε - helmholtz α ≡ helmholtz ε
  helmholtz-add-cancel α ε =
    trans
      (ℚ-Props.+-assoc (helmholtz α) (helmholtz ε) (- helmholtz α))
      (trans
        (cong (λ x → helmholtz α + x) (ℚ-Props.+-comm (helmholtz ε) (- helmholtz α)))
        (trans
          (≡-sym (ℚ-Props.+-assoc (helmholtz α) (- helmholtz α) (helmholtz ε)))
          (trans
            (cong (λ x → x + helmholtz ε) (ℚ-Props.+-inverseʳ (helmholtz α)))
            (ℚ-Props.+-identityˡ (helmholtz ε)))))

helmholtz-gradient-const : ∀ (α ε : ℚ) →
  helmholtz (α + ε) - helmholtz α ≡ -(Q-hyd * ε)
helmholtz-gradient-const α ε =
  trans (cong (_- helmholtz α) (helmholtz-linear α ε)) (helmholtz-add-cancel α ε)
