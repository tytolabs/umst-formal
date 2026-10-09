-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawDissipation — dissipation coefficients bounded by the second law (twin of
-- Lean/Constants/SecondLawDissipation.lean and Coq/Constants/SecondLawDissipation.v).
--
-- A passive step whose dissipated energy D leaves the free energy (ψ_new = ψ_old − D) satisfies the transition case
-- of SecondLaw only when D ≥ 0; writing D as a coefficient times a positive measure of the step bounds the
-- coefficient. Agda carries quantities as rationals: a squared rate enters as a positive rational q, the Bingham law
-- is stated at every positive rate (where |r| = r), and the loss-modulus cycle measure π·ε₀² enters as a positive q.
-- Each result is a bound, never a value.
------------------------------------------------------------------------

module Constants.SecondLawDissipation where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_; _-_; -_; 1/_; Positive; positive; nonNegative)
open import Data.Rational.Properties using (*-cancelʳ-≤-pos; *-zeroˡ; *-identityʳ; *-inverseʳ; +-identityʳ;
  +-mono-≤; +-monoˡ-≤; +-mono-<-≤; +-mono-≤-<; ≤-reflexive; <-≤-trans; ≤-<-trans; <-irrefl; <-cmp; <⇒≤;
  neg-antimono-<; pos⇒nonZero; pos⇒nonNeg; 1/pos⇒pos; pos*pos⇒pos; pos+pos⇒pos; nonNeg*nonNeg⇒nonNeg;
  nonNegative⁻¹)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Concrete.Gate using (mkState)
open import Core.Gate using (CoreAdmissible)
open import Process using (Prior; SecondLaw; transition; thermodynamic)

open +-*-Solver

-- A passive step from free energy ψ that dissipates d.
dissipates : ℚ → ℚ → ℚ → ℚ → Prior
dissipates ρ ρ' ψ d = thermodynamic (mkState ρ ψ 0ℚ 0ℚ) (mkState ρ' (ψ - d) 0ℚ 0ℚ)

private
  ≤-≡ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
  ≤-≡ h eq = subst (_ ≤_) eq h

  ≡-≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
  ≡-≤ eq h = subst (_≤ _) (sym eq) h

  -- A nonnegative product with a positive right factor has a nonnegative left factor.
  cancelʳ : ∀ c r .{{_ : Positive r}} → 0ℚ ≤ c * r → 0ℚ ≤ c
  cancelʳ c r h = *-cancelʳ-≤-pos r (≡-≤ (*-zeroˡ r) h)

  -- A nonnegative quantity is not negative.
  ¬neg : ∀ {x} → 0ℚ ≤ x → x < 0ℚ → ∀ {A : Set} → A
  ¬neg h n = ⊥-elim (<-irrefl refl (≤-<-trans h n))

dissipates-nonneg : ∀ ρ ρ' ψ d → SecondLaw transition (dissipates ρ ρ' ψ d) → 0ℚ ≤ d
dissipates-nonneg ρ ρ' ψ d h = ≡-≤ (e₀ ψ) (≤-≡ (+-monoˡ-≤ (- ψ) step) (e₁ ψ d))
  where
    e₀ : ∀ ψ → 0ℚ ≡ ψ + - ψ
    e₀ = solve 1 (λ ψ → con 0ℚ := ψ :+ :- ψ) refl
    e₁ : ∀ ψ d → (ψ + d) + - ψ ≡ d
    e₁ = solve 2 (λ ψ d → (ψ :+ d) :+ :- ψ := d) refl
    e₂ : ∀ ψ d → ψ ≡ (ψ - d) + d
    e₂ = solve 2 (λ ψ d → ψ := (ψ :- d) :+ d) refl
    -- ψ − d ≤ ψ gives ψ ≤ ψ + d, then 0 ≤ d after adding −ψ.
    step : ψ ≤ ψ + d
    step = ≡-≤ (e₂ ψ d) (+-monoˡ-≤ d (CoreAdmissible.dissipation-nonneg h))

-- Dissipation coefficient: a passive step dissipating c·q (q > 0) obeys the second law only when c ≥ 0.
dissipation-coefficient-nonneg : ∀ ρ ρ' ψ c q .{{_ : Positive q}} →
  SecondLaw transition (dissipates ρ ρ' ψ (c * q)) → 0ℚ ≤ c
dissipation-coefficient-nonneg ρ ρ' ψ c q h = cancelʳ c q (dissipates-nonneg ρ ρ' ψ (c * q) h)

-- Viscosity: a dashpot at a rate with r² = q > 0 over dt > 0 dissipates η·q·dt; the second law gives η ≥ 0.
viscosity-nonneg : ∀ ρ ρ' ψ η q dt .{{_ : Positive q}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (η * q * dt)) → 0ℚ ≤ η
viscosity-nonneg ρ ρ' ψ η q dt h = cancelʳ η q (dissipation-coefficient-nonneg ρ ρ' ψ (η * q) dt h)

-- Bingham fluid: dissipating (τ₀·r + η_p·r²)·dt at every positive rate r under the second law gives a yield stress
-- τ₀ ≥ 0 and a plastic viscosity η_p ≥ 0.
bingham-nonneg : ∀ ρ ρ' ψ τ0 ηp dt .{{_ : Positive dt}} →
  (∀ r .{{_ : Positive r}} → SecondLaw transition (dissipates ρ ρ' ψ ((τ0 * r + ηp * (r * r)) * dt))) →
  (0ℚ ≤ τ0) × (0ℚ ≤ ηp)
bingham-nonneg ρ ρ' ψ τ0 ηp dt h = yield , plastic
  where
    -- At every positive rate the dissipation per unit rate, τ₀ + η_p·r, is nonnegative.
    per : ∀ r .{{_ : Positive r}} → 0ℚ ≤ τ0 + ηp * r
    per r = cancelʳ (τ0 + ηp * r) r
      (≤-≡ (dissipation-coefficient-nonneg ρ ρ' ψ (τ0 * r + ηp * (r * r)) dt (h r)) (fac τ0 ηp r))
      where
        fac : ∀ τ η r → τ * r + η * (r * r) ≡ (τ + η * r) * r
        fac = solve 3 (λ τ η r → τ :* r :+ η :* (r :* r) := (τ :+ η :* r) :* r) refl

    -- At the unit rate, τ₀ + η_p ≥ 0.
    unit : 0ℚ ≤ τ0 + ηp
    unit = ≤-≡ (per 1ℚ) (cong (τ0 +_) (*-identityʳ ηp))

    -- Two nonpositive summands, one of them negative, have a negative sum.
    neg-sum : ∀ {x y} → x < 0ℚ → y ≤ 0ℚ → x + y < 0ℚ
    neg-sum x<0 y≤0 = <-≤-trans (+-mono-<-≤ x<0 y≤0) (≤-reflexive (+-identityʳ 0ℚ))

    yield : 0ℚ ≤ τ0
    yield with <-cmp τ0 0ℚ
    ... | tri≈ _ τ0≡0 _ = ≤-reflexive (sym τ0≡0)
    ... | tri> _ _ τ0>0 = <⇒≤ τ0>0
    ... | tri< τ0<0 _ _ with <-cmp ηp 0ℚ
    ...   | tri< ηp<0 _ _ = ¬neg unit (neg-sum τ0<0 (<⇒≤ ηp<0))
    ...   | tri≈ _ ηp≡0 _ = ¬neg unit (neg-sum τ0<0 (≤-reflexive ηp≡0))
    ...   | tri> _ _ ηp>0 = ¬neg (≤-≡ twice halve) τ0<0
      where
        -- A negative yield stress is undone at the rate r = −τ₀ / (2·η_p).
        instance
          pη : Positive ηp
          pη = positive ηp>0
          p-τ : Positive (- τ0)
          p-τ = positive (neg-antimono-< τ0<0)
          p2η : Positive (ηp + ηp)
          p2η = pos+pos⇒pos ηp ηp
        i : ℚ
        i = (1/ (ηp + ηp)) {{pos⇒nonZero (ηp + ηp)}}
        instance
          pi : Positive i
          pi = 1/pos⇒pos (ηp + ηp)
          pr : Positive (- τ0 * i)
          pr = pos*pos⇒pos (- τ0) i
        twice : 0ℚ ≤ (τ0 + ηp * (- τ0 * i)) + (τ0 + ηp * (- τ0 * i))
        twice = +-mono-≤ (per (- τ0 * i)) (per (- τ0 * i))
        e₁ : ∀ τ m i → (τ + m * (- τ * i)) + (τ + m * (- τ * i)) ≡ (τ + τ) - τ * ((m + m) * i)
        e₁ = solve 3 (λ τ m i → (τ :+ m :* (:- τ :* i)) :+ (τ :+ m :* (:- τ :* i)) := (τ :+ τ) :- τ :* ((m :+ m) :* i))
               refl
        e₂ : ∀ τ → (τ + τ) - τ ≡ τ
        e₂ = solve 1 (λ τ → (τ :+ τ) :- τ := τ) refl
        halve : (τ0 + ηp * (- τ0 * i)) + (τ0 + ηp * (- τ0 * i)) ≡ τ0
        halve = trans (e₁ τ0 ηp i) (trans (cong (λ x → (τ0 + τ0) - τ0 * x) (*-inverseʳ (ηp + ηp) {{pos⇒nonZero (ηp + ηp)}}))
                  (trans (cong (λ x → (τ0 + τ0) - x) (*-identityʳ τ0)) (e₂ τ0)))

    plastic : 0ℚ ≤ ηp
    plastic with <-cmp ηp 0ℚ
    ... | tri≈ _ ηp≡0 _ = ≤-reflexive (sym ηp≡0)
    ... | tri> _ _ ηp>0 = <⇒≤ ηp>0
    ... | tri< ηp<0 _ _ with <-cmp τ0 0ℚ
    ...   | tri< τ0<0 _ _ = ¬neg unit (neg-sum τ0<0 (<⇒≤ ηp<0))
    ...   | tri≈ _ τ0≡0 _ = ¬neg unit (<-≤-trans (+-mono-≤-< (≤-reflexive τ0≡0) ηp<0) (≤-reflexive (+-identityʳ 0ℚ)))
    ...   | tri> _ _ τ0>0 = ¬neg (≤-≡ (per ((τ0 + τ0) * i)) undo) (neg-antimono-< τ0>0)
      where
        -- A negative plastic viscosity is undone at the rate r = 2·τ₀ / (−η_p).
        instance
          pn : Positive (- ηp)
          pn = positive (neg-antimono-< ηp<0)
          pτ : Positive τ0
          pτ = positive τ0>0
          p2τ : Positive (τ0 + τ0)
          p2τ = pos+pos⇒pos τ0 τ0
        i : ℚ
        i = (1/ (- ηp)) {{pos⇒nonZero (- ηp)}}
        instance
          pi : Positive i
          pi = 1/pos⇒pos (- ηp)
          pr : Positive ((τ0 + τ0) * i)
          pr = pos*pos⇒pos (τ0 + τ0) i
        e₁ : ∀ τ η i → τ + η * ((τ + τ) * i) ≡ τ - (τ + τ) * ((- η) * i)
        e₁ = solve 3 (λ τ η i → τ :+ η :* ((τ :+ τ) :* i) := τ :- (τ :+ τ) :* ((:- η) :* i)) refl
        e₂ : ∀ τ → τ - (τ + τ) ≡ - τ
        e₂ = solve 1 (λ τ → τ :- (τ :+ τ) := :- τ) refl
        undo : τ0 + ηp * ((τ0 + τ0) * i) ≡ - τ0
        undo = trans (e₁ τ0 ηp i) (trans (cong (λ x → τ0 - (τ0 + τ0) * x) (*-inverseʳ (- ηp) {{pos⇒nonZero (- ηp)}}))
                 (trans (cong (λ x → τ0 - x) (*-identityʳ (τ0 + τ0))) (e₂ τ0)))

-- Loss modulus: a harmonic cycle with positive measure q (π·ε₀²) that dissipates E″·q obeys the second law only
-- when E″ ≥ 0; for a storage modulus E′ > 0 the loss factor E″·(1/E′) is nonnegative.
lossModulus-nonneg : ∀ ρ ρ' ψ E′ E″ q .{{_ : Positive q}} .{{_ : Positive E′}} →
  SecondLaw transition (dissipates ρ ρ' ψ (E″ * q)) →
  (0ℚ ≤ E″) × (0ℚ ≤ E″ * (1/ E′) {{pos⇒nonZero E′}})
lossModulus-nonneg ρ ρ' ψ E′ E″ q h = E″≥0 , nonNegative⁻¹ (E″ * inv) {{nonNeg*nonNeg⇒nonNeg E″ {{nonNegative E″≥0}} inv
  {{pos⇒nonNeg inv {{1/pos⇒pos E′}}}}}}
  where
    inv : ℚ
    inv = (1/ E′) {{pos⇒nonZero E′}}
    E″≥0 : 0ℚ ≤ E″
    E″≥0 = dissipation-coefficient-nonneg ρ ρ' ψ E″ q h
