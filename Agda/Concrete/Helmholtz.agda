------------------------------------------------------------------------
-- UMST.Concrete.Helmholtz — Helmholtz free-energy model (OPC cartridge).
------------------------------------------------------------------------

module Concrete.Helmholtz where

open import Data.Integer.Base as ℤ using (ℤ; +_; ∣_∣)
open import Data.Nat.Coprimality as ℕ using (sym; 1-coprimeTo)
open import Data.Rational as ℚ using (ℚ; 0ℚ; mkℚ; _+_; _*_; _-_; _≤_; -_)
open import Data.Rational.Properties as ℚ-Props
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)
  renaming (sym to ≡-sym)
open import Data.Product using (_×_; _,_)

open import Concrete.Gate using (ThermodynamicState)
open ThermodynamicState

------------------------------------------------------------------------
-- 1. Physical Constants
------------------------------------------------------------------------

Q-hyd : ℚ
Q-hyd = mkℚ (+ 450) 0 (ℕ.sym (ℕ.1-coprimeTo ∣ + 450 ∣))

------------------------------------------------------------------------
-- 2. The Helmholtz Free-Energy Model
------------------------------------------------------------------------

helmholtz : ℚ → ℚ
helmholtz α = - (Q-hyd * α)

------------------------------------------------------------------------
-- 3. Antitone Lemma (Concrete Arithmetic)
------------------------------------------------------------------------

postulate
  helmholtz-antitone : ∀ (α₁ α₂ : ℚ) → α₁ ≤ α₂ → helmholtz α₂ ≤ helmholtz α₁

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

postulate
  helmholtz-linear : ∀ (α₁ α₂ : ℚ) →
    helmholtz (α₁ + α₂) ≡ helmholtz α₁ + helmholtz α₂

postulate
  helmholtz-gradient-const : ∀ (α ε : ℚ) →
    helmholtz (α + ε) - helmholtz α ≡ -(Q-hyd * ε)
