-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawElectromagnetic — four electromagnetic constants bounded by the second law (twin of
-- Lean/Constants/SecondLawElectromagnetic.lean and Coq/Constants/SecondLawElectromagnetic.v).
--
-- A passive step at fixed density is the transition case of SecondLaw exactly when the free energy does not rise. A
-- vacuum field relaxing from ½·ε·E² to zero, and a Joule step dissipating G·V²·dt (or R·I²·dt), are admitted for
-- every field or voltage exactly when the coefficient is nonnegative; a field storing B²/(2μ) relaxes only for μ > 0,
-- and relaxes from every flux density when μ > 0. Agda carries quantities as rationals, so a squared field enters as
-- a nonnegative rational q (q = E², V², I² or B²) and the magnetic energy ψ = q/(2μ) is stated with its denominator
-- cleared (ψ·μ = ½·q). The exact SI values of Constants/SI.agda lie inside each bound. Each result is a bound,
-- never a value.
------------------------------------------------------------------------

module Constants.SecondLawElectromagnetic where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _<_; _+_; _*_; _-_; -_; Positive; NonNegative; fromℚᵘ;
  nonNegative; negative; positive)
open import Data.Rational.Properties using (*-cancelʳ-≤-pos; *-zeroˡ; *-zeroʳ; *-comm; *-identityʳ; +-identityʳ;
  +-inverseʳ; +-monoʳ-≤; neg-antimono-≤; ≤-refl; ≤-<-trans; <-irrefl; <-cmp; <⇒≤; positive⁻¹; negative⁻¹;
  nonNegative⁻¹; nonNeg*nonNeg⇒nonNeg; neg*pos⇒neg)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Concrete.Gate using (mkState)
open import Core.Gate using (CoreAdmissible; δ-mass)
open import Process using (Prior; SecondLaw; transition; thermodynamic)
open import Constants.SecondLawElastic using (relaxation-modulus-pos)
import Constants.SI as SI

-- A passive step of the vacuum at density ρ from free energy ψ to ψ'.
passiveStep : ℚ → ℚ → ℚ → Prior
passiveStep ρ ψ ψ' = thermodynamic (mkState ρ ψ 0ℚ 0ℚ) (mkState ρ ψ' 0ℚ 0ℚ)

private
  ρ-ρ≤δ : ∀ ρ → ρ - ρ ≤ δ-mass
  ρ-ρ≤δ ρ = subst (_≤ δ-mass) (sym (+-inverseʳ ρ)) (nonNegative⁻¹ δ-mass)

  -- ψ − d ≤ ψ for d ≥ 0.
  sub-le : ∀ ψ d → 0ℚ ≤ d → ψ - d ≤ ψ
  sub-le ψ d h = subst (ψ - d ≤_) (+-identityʳ ψ) (+-monoʳ-≤ ψ (neg-antimono-≤ h))

  -- ψ − d ≤ ψ gives d ≥ 0.
  le-sub : ∀ ψ d → ψ - d ≤ ψ → 0ℚ ≤ d
  le-sub ψ d h with <-cmp d 0ℚ
  ... | tri< d<0 _ _ = ⊥-elim (<-irrefl refl (≤-<-trans h (lt ψ d d<0)))
    where
      lt : ∀ ψ d → d < 0ℚ → ψ < ψ - d
      lt ψ d d<0 = subst (_< ψ - d) (+-identityʳ ψ) (+-monoʳ-< ψ (neg-antimono-< d<0))
        where open import Data.Rational.Properties using (+-monoʳ-<; neg-antimono-<)
  ... | tri≈ _ d≡0 _ = subst (0ℚ ≤_) (sym d≡0) ≤-refl
  ... | tri> _ _ d>0 = <⇒≤ d>0

  half-nonneg : ∀ k → 0ℚ ≤ ½ * k → 0ℚ ≤ k
  half-nonneg k h = *-cancelʳ-≤-pos ½ (subst (_≤ k * ½) (sym (*-zeroˡ ½)) (subst (0ℚ ≤_) (*-comm ½ k) h))

  nonneg3 : ∀ k q → 0ℚ ≤ k → 0ℚ ≤ q → 0ℚ ≤ ½ * k * q
  nonneg3 k q hk hq = nonNegative⁻¹ (½ * k * q)
    {{nonNeg*nonNeg⇒nonNeg (½ * k) {{nonNeg*nonNeg⇒nonNeg ½ k {{nonNegative hk}}}} q {{nonNegative hq}}}}

-- A passive step at fixed density is admitted exactly when the free energy does not rise.
passiveStep-secondLaw-⇔ : ∀ ρ ψ ψ' → SecondLaw transition (passiveStep ρ ψ ψ') ⇔ ψ' ≤ ψ
passiveStep-secondLaw-⇔ ρ ψ ψ' = mk⇔ CoreAdmissible.dissipation-nonneg
  (λ h → record { mass-conserved = ρ-ρ≤δ ρ , ρ-ρ≤δ ρ ; dissipation-nonneg = h })

-- Electric field energy: every relaxation from ½·ε·q (q = E² ≥ 0) to zero is admitted exactly when ε ≥ 0.
electricRelaxation-secondLaw-⇔ : ∀ ε →
  (∀ ρ q → 0ℚ ≤ q → SecondLaw transition (passiveStep ρ (½ * ε * q) 0ℚ)) ⇔ (0ℚ ≤ ε)
electricRelaxation-secondLaw-⇔ ε = mk⇔
  (λ h → half-nonneg ε (subst (0ℚ ≤_) (*-identityʳ (½ * ε))
    (Equivalence.to (passiveStep-secondLaw-⇔ 0ℚ _ 0ℚ) (h 0ℚ 1ℚ (nonNegative⁻¹ 1ℚ)))))
  (λ hε ρ q hq → Equivalence.from (passiveStep-secondLaw-⇔ ρ _ 0ℚ) (nonneg3 ε q hε hq))
  where open import Function.Bundles using (Equivalence)

-- Magnetic field energy, denominator cleared: a field storing ψ with ψ·μ = ½·q (q = B² > 0) that relaxes passively
-- forces μ > 0; and for μ > 0 every field storing ψ·μ = ½·q (q ≥ 0) relaxes.
magneticRelaxation-secondLaw-⇔ : ∀ μ →
  (∀ ρ q ψ → .{{_ : Positive q}} → ψ * μ ≡ ½ * q → SecondLaw transition (passiveStep ρ ψ 0ℚ) → 0ℚ < μ) ×
  (0ℚ < μ → ∀ ρ q ψ → 0ℚ ≤ q → ψ * μ ≡ ½ * q → SecondLaw transition (passiveStep ρ ψ 0ℚ))
magneticRelaxation-secondLaw-⇔ μ =
  (λ ρ q ψ eq h → relaxation-modulus-pos ρ ρ μ q ψ eq h) ,
  (λ μ>0 ρ q ψ hq eq → record { mass-conserved = ρ-ρ≤δ ρ , ρ-ρ≤δ ρ ; dissipation-nonneg = ψ≥0 μ>0 q ψ hq eq })
  where
    ψ≥0 : 0ℚ < μ → ∀ q ψ → 0ℚ ≤ q → ψ * μ ≡ ½ * q → 0ℚ ≤ ψ
    ψ≥0 μ>0 q ψ hq eq with <-cmp ψ 0ℚ
    ... | tri< ψ<0 _ _ = ⊥-elim (<-irrefl refl (≤-<-trans half-q≥0 ψμ<0))
      where
        half-q≥0 : 0ℚ ≤ ψ * μ
        half-q≥0 = subst (0ℚ ≤_) (sym eq) (nonNegative⁻¹ (½ * q) {{nonNeg*nonNeg⇒nonNeg ½ q {{nonNegative hq}}}})
        ψμ<0 : ψ * μ < 0ℚ
        ψμ<0 = negative⁻¹ (ψ * μ) {{neg*pos⇒neg ψ {{negative ψ<0}} μ {{positive μ>0}}}}
    ... | tri≈ _ ψ≡0 _ = subst (0ℚ ≤_) (sym ψ≡0) ≤-refl
    ... | tri> _ _ ψ>0 = <⇒≤ ψ>0

-- Conductance: every Joule step dissipating G·q·dt (q = V² ≥ 0, dt > 0) is admitted exactly when G ≥ 0.
conductanceDissipation-secondLaw-⇔ : ∀ G →
  (∀ ρ ψ q dt → 0ℚ ≤ q → 0ℚ < dt → SecondLaw transition (passiveStep ρ ψ (ψ - G * q * dt))) ⇔ (0ℚ ≤ G)
conductanceDissipation-secondLaw-⇔ G = mk⇔
  (λ h → subst (0ℚ ≤_) (trans (*-identityʳ (G * 1ℚ)) (*-identityʳ G))
    (le-sub 0ℚ _ (Equivalence.to (passiveStep-secondLaw-⇔ 0ℚ 0ℚ _) (h 0ℚ 0ℚ 1ℚ 1ℚ (nonNegative⁻¹ 1ℚ) (positive⁻¹ 1ℚ)))))
  (λ hG ρ ψ q dt hq hdt → Equivalence.from (passiveStep-secondLaw-⇔ ρ ψ _)
    (sub-le ψ (G * q * dt) (nonNegative⁻¹ (G * q * dt)
      {{nonNeg*nonNeg⇒nonNeg (G * q) {{nonNeg*nonNeg⇒nonNeg G {{nonNegative hG}} q {{nonNegative hq}}}} dt
        {{nonNegative (<⇒≤ hdt)}}}})))
  where open import Function.Bundles using (Equivalence)

-- Resistance: every Joule step dissipating R·q·dt (q = I² ≥ 0, dt > 0) is admitted exactly when R ≥ 0.
resistanceDissipation-secondLaw-⇔ : ∀ R →
  (∀ ρ ψ q dt → 0ℚ ≤ q → 0ℚ < dt → SecondLaw transition (passiveStep ρ ψ (ψ - R * q * dt))) ⇔ (0ℚ ≤ R)
resistanceDissipation-secondLaw-⇔ = conductanceDissipation-secondLaw-⇔

------------------------------------------------------------------------
-- The exact SI values lie inside the bounds.
------------------------------------------------------------------------

ε₀ μ₀ G₀ R_K : ℚ
ε₀ = fromℚᵘ SI.vacuumPermittivity
μ₀ = fromℚᵘ SI.vacuumPermeability
G₀ = fromℚᵘ SI.conductanceQuantum
R_K = fromℚᵘ SI.vonKlitzing

vacuumPermittivity-relaxation-secondLaw : ∀ ρ q → 0ℚ ≤ q → SecondLaw transition (passiveStep ρ (½ * ε₀ * q) 0ℚ)
vacuumPermittivity-relaxation-secondLaw = Equivalence.from (electricRelaxation-secondLaw-⇔ ε₀) (nonNegative⁻¹ ε₀)
  where open import Function.Bundles using (Equivalence)

vacuumPermeability-relaxation-secondLaw : ∀ ρ q ψ → 0ℚ ≤ q → ψ * μ₀ ≡ ½ * q →
  SecondLaw transition (passiveStep ρ ψ 0ℚ)
vacuumPermeability-relaxation-secondLaw = proj₂ (magneticRelaxation-secondLaw-⇔ μ₀) (positive⁻¹ μ₀)

conductanceQuantum-dissipation-secondLaw : ∀ ρ ψ q dt → 0ℚ ≤ q → 0ℚ < dt →
  SecondLaw transition (passiveStep ρ ψ (ψ - G₀ * q * dt))
conductanceQuantum-dissipation-secondLaw =
  Equivalence.from (conductanceDissipation-secondLaw-⇔ G₀) (nonNegative⁻¹ G₀)
  where open import Function.Bundles using (Equivalence)

vonKlitzing-dissipation-secondLaw : ∀ ρ ψ q dt → 0ℚ ≤ q → 0ℚ < dt →
  SecondLaw transition (passiveStep ρ ψ (ψ - R_K * q * dt))
vonKlitzing-dissipation-secondLaw = Equivalence.from (resistanceDissipation-secondLaw-⇔ R_K) (nonNegative⁻¹ R_K)
  where open import Function.Bundles using (Equivalence)
