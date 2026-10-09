-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawSolidInelastic — material parameters of an inelastic solid bounded by the second law (twin of
-- Lean/Constants/SecondLawSolidInelastic.lean and Coq/Constants/SecondLawSolidInelastic.v).
--
-- Each hypothesis is the transition case of SecondLaw: the relaxation of a loaded state to its natural state, or a
-- passive step that dissipates energy out of the free energy. Agda carries quantities as rationals: the coupled
-- well takes k > 0 and states −1 ≤ c ≤ 1 as 0 ≤ 1 + c and 0 ≤ 1 − c; the double-well envelope φ²(1 − φ)², a power
-- σⁿ, the factor 1/(2x) and a root √f_c enter as positive rationals; the toughness bound is on the radicand E·G_c.
-- Each result is a bound, never a value.
------------------------------------------------------------------------

module Constants.SecondLawSolidInelastic where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _/_; _≤_; _<_; _+_; _*_; _-_; -_; Positive; nonNegative)
open import Data.Rational.Properties using (*-cancelˡ-≤-pos; *-cancelʳ-≤-pos; *-zeroʳ; *-zeroˡ; <⇒≤;
  pos*pos⇒pos; nonNeg*nonNeg⇒nonNeg; nonNegative⁻¹)
open import Data.Integer using (+_)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process using (SecondLaw; transition)
open import Constants.SecondLawElastic using (relaxation; relaxation-nonneg; relaxation-modulus-pos)
open import Constants.SecondLawDissipation using (dissipates; dissipation-coefficient-nonneg)

open +-*-Solver

private
  two : ℚ
  two = + 2 / 1

  -- A nonnegative product with a positive left factor has a nonnegative right factor.
  cancelˡ : ∀ r .{{_ : Positive r}} d → 0ℚ ≤ r * d → 0ℚ ≤ d
  cancelˡ r d h = *-cancelˡ-≤-pos r (subst (_≤ r * d) (sym (*-zeroʳ r)) h)

  -- A nonnegative product with a positive right factor has a nonnegative left factor.
  cancelʳ : ∀ c r .{{_ : Positive r}} → 0ℚ ≤ c * r → 0ℚ ≤ c
  cancelʳ c r h = *-cancelʳ-≤-pos r (subst (_≤ c * r) (sym (*-zeroˡ r)) h)

  -- A second-law step whose dissipation is rewritten by an equation.
  step≡ : ∀ {ρ ρ' ψ d d'} → d ≡ d' → SecondLaw transition (dissipates ρ ρ' ψ d) →
    SecondLaw transition (dissipates ρ ρ' ψ d')
  step≡ {ρ} {ρ'} {ψ} eq h = subst (λ x → SecondLaw transition (dissipates ρ ρ' ψ x)) eq h

-- Free energy of a plastic strain x and a hardening variable y with modulus k and cross coupling c.
coupledWell : ℚ → ℚ → ℚ → ℚ → ℚ
coupledWell k c x y = ½ * k * (x * x + y * y + two * c * x * y)

-- Coupled well: relaxing passively from every (x, y) with k > 0 gives −1 ≤ c ≤ 1, as 0 ≤ 1 + c and 0 ≤ 1 − c.
coupledWell-bounds : ∀ ρ ρ' k c .{{_ : Positive k}} →
  (∀ x y → SecondLaw transition (relaxation ρ ρ' (coupledWell k c x y))) → (0ℚ ≤ 1ℚ + c) × (0ℚ ≤ 1ℚ - c)
coupledWell-bounds ρ ρ' k c h = lower , upper
  where
    instance
      _ = pos*pos⇒pos ½ k
      _ = pos*pos⇒pos (½ * k) two
    e₊ : ∀ k c → ½ * k * (1ℚ * 1ℚ + 1ℚ * 1ℚ + two * c * 1ℚ * 1ℚ) ≡ ½ * k * two * (1ℚ + c)
    e₊ = solve 2 (λ k c → con ½ :* k :* (con 1ℚ :* con 1ℚ :+ con 1ℚ :* con 1ℚ :+ con two :* c :* con 1ℚ :* con 1ℚ)
                         := con ½ :* k :* con two :* (con 1ℚ :+ c)) refl
    e₋ : ∀ k c → ½ * k * (1ℚ * 1ℚ + - 1ℚ * - 1ℚ + two * c * 1ℚ * - 1ℚ) ≡ ½ * k * two * (1ℚ - c)
    e₋ = solve 2 (λ k c → con ½ :* k :* (con 1ℚ :* con 1ℚ :+ (:- con 1ℚ) :* (:- con 1ℚ)
                                         :+ con two :* c :* con 1ℚ :* (:- con 1ℚ))
                         := con ½ :* k :* con two :* (con 1ℚ :- c)) refl
    lower : 0ℚ ≤ 1ℚ + c
    lower = cancelˡ (½ * k * two) (1ℚ + c) (subst (0ℚ ≤_) (e₊ k c) (relaxation-nonneg ρ ρ' _ (h 1ℚ 1ℚ)))
    upper : 0ℚ ≤ 1ℚ - c
    upper = cancelˡ (½ * k * two) (1ℚ - c) (subst (0ℚ ≤_) (e₋ k c) (relaxation-nonneg ρ ρ' _ (h 1ℚ (- 1ℚ))))

-- Double well: a phase field whose envelope φ²(1 − φ)² = q > 0 stores k·q and relaxes passively has k ≥ 0.
doubleWell-modulus-nonneg : ∀ ρ ρ' k q .{{_ : Positive q}} →
  SecondLaw transition (relaxation ρ ρ' (k * q)) → 0ℚ ≤ k
doubleWell-modulus-nonneg ρ ρ' k q h = cancelʳ k q (relaxation-nonneg ρ ρ' _ h)

-- Griffith fracture energy: a crack extension dA > 0 dissipating G_c·dA obeys the second law only when G_c ≥ 0.
griffith-fracture-energy-nonneg : ∀ ρ ρ' ψ Gc dA .{{_ : Positive dA}} →
  SecondLaw transition (dissipates ρ ρ' ψ (Gc * dA)) → 0ℚ ≤ Gc
griffith-fracture-energy-nonneg ρ ρ' ψ Gc dA h = dissipation-coefficient-nonneg ρ ρ' ψ Gc dA h

-- Fracture toughness: with G_c ≥ 0 from a crack extension and E > 0 from the relaxation of a body held at a stress
-- with σ² = q > 0 (stored ψ with ψ·E = ½·q), the radicand E·G_c of K = √(E·G_c) is nonnegative.
griffith-toughness-nonneg : ∀ ρ ρ' ψ Gc dA E q ψe .{{_ : Positive dA}} .{{_ : Positive q}} → ψe * E ≡ ½ * q →
  SecondLaw transition (dissipates ρ ρ' ψ (Gc * dA)) → SecondLaw transition (relaxation ρ ρ' ψe) → 0ℚ ≤ E * Gc
griffith-toughness-nonneg ρ ρ' ψ Gc dA E q ψe eq hG hR = nonNegative⁻¹ (E * Gc) {{nonNeg*nonNeg⇒nonNeg E Gc}}
  where
    instance
      _ = nonNegative (<⇒≤ (relaxation-modulus-pos ρ ρ' E q ψe eq hR))
      _ = nonNegative (griffith-fracture-energy-nonneg ρ ρ' ψ Gc dA hG)

-- Norton creep: steady creep at stress σ > 0 with rate A·p (p = σⁿ > 0) over dt > 0 dissipates σ·(A·p)·dt; A ≥ 0.
norton-coefficient-nonneg : ∀ ρ ρ' ψ A σ p dt .{{_ : Positive σ}} .{{_ : Positive p}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (σ * (A * p) * dt)) → 0ℚ ≤ A
norton-coefficient-nonneg ρ ρ' ψ A σ p dt h =
  dissipation-coefficient-nonneg ρ ρ' ψ A (σ * p * dt) {{pos*pos⇒pos (σ * p) {{pos*pos⇒pos σ p}} dt}}
    (step≡ (e A σ p dt) h)
  where
    e : ∀ A σ p dt → σ * (A * p) * dt ≡ A * (σ * p * dt)
    e = solve 4 (λ A σ p dt → σ :* (A :* p) :* dt := A :* (σ :* p :* dt)) refl

-- Parabolic scaling: a scale growing at k_p·w (w = 1/(2x) > 0) under a reaction affinity a > 0 over dt > 0
-- dissipates a·(k_p·w)·dt; k_p ≥ 0.
parabolic-rate-nonneg : ∀ ρ ρ' ψ a kp w dt .{{_ : Positive a}} .{{_ : Positive w}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (a * (kp * w) * dt)) → 0ℚ ≤ kp
parabolic-rate-nonneg ρ ρ' ψ a kp w dt h =
  dissipation-coefficient-nonneg ρ ρ' ψ kp (a * w * dt) {{pos*pos⇒pos (a * w) {{pos*pos⇒pos a w}} dt}}
    (step≡ (e a kp w dt) h)
  where
    e : ∀ a kp w dt → a * (kp * w) * dt ≡ kp * (a * w * dt)
    e = solve 4 (λ a kp w dt → a :* (kp :* w) :* dt := kp :* (a :* w :* dt)) refl

-- Frictional bond: a fibre whose bond stress is b·r (r = √f_c > 0) sliding over a slip area s > 0 dissipates b·r·s;
-- b ≥ 0.
frictional-bond-nonneg : ∀ ρ ρ' ψ b r s .{{_ : Positive r}} .{{_ : Positive s}} →
  SecondLaw transition (dissipates ρ ρ' ψ (b * r * s)) → 0ℚ ≤ b
frictional-bond-nonneg ρ ρ' ψ b r s h =
  dissipation-coefficient-nonneg ρ ρ' ψ b (r * s) {{pos*pos⇒pos r s}} (step≡ (e b r s) h)
  where
    e : ∀ b r s → b * r * s ≡ b * (r * s)
    e = solve 3 (λ b r s → b :* r :* s := b :* (r :* s)) refl
