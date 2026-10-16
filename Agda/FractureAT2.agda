-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: FractureAT2.agda
--
-- Twin of Lean/Concrete/FractureAT2.lean and Coq/FractureAT2.v over exact rationals: the AT2 stored energy
-- g(φ) ψ_e with g(φ) = (1 − φ)², the crack energy (c/2)(φ'² − φ²) spent as dissipation (c = G_c / l), and the
-- irreversible alternate-minimisation step φ' = φ ⊔ φ*. The unconstrained minimiser φ* = 2 ψ_e / (2 ψ_e + c) is
-- carried with its defining equation (ψ_e + c/2) φ* = ψ_e (TargetEq). The step stays in [0, 1], minimises the total
-- energy over φ' ≥ φ and is a SecondLaw transition through the passive route on the whole domain; Griffith is the
-- passive inequality; a loading step is refused, its missing term the supplied power W_in.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FractureAT2 where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _-_; -_; _≤_; _<_; _⊔_; nonNegative; positive)
open import Data.Rational.Properties
  using ( ≤-refl; ≤-reflexive; ≤-trans; <-≤-trans; ≤-<-trans; <⇒≤; ≤-total; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤
        ; neg-antimono-≤; neg-antimono-<; +-inverseʳ; +-mono-≤-<; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; *-monoʳ-<-pos
        ; *-cancelˡ-≤-pos; *-zeroʳ; *-identityʳ; nonNegative⁻¹
        ; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p; <-irrefl; ≤-antisym )
open import Data.Rational.Solver using (module +-*-Solver)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Concrete.Gate using (ThermodynamicState; mkState)
open import Core.Gate using (δ-mass)
open import Process using (SecondLaw; transition; thermodynamic)
open import Convex.PassiveRoute using (MassBall; passive-inequality-secondLaw)
open +-*-Solver

degradation : ℚ → ℚ
degradation φ = (1ℚ - φ) * (1ℚ - φ)

stored : ℚ → ℚ → ℚ
stored ψ φ = degradation φ * ψ

crackSpent : ℚ → ℚ → ℚ → ℚ
crackSpent c φ φ' = ½ * c * (φ' * φ' - φ * φ)

total : ℚ → ℚ → ℚ → ℚ
total c ψ φ = stored ψ φ + ½ * c * (φ * φ)

-- The defining equation of the unconstrained minimiser φ* = 2 ψ_e / (2 ψ_e + c).
TargetEq : ℚ → ℚ → ℚ → Set
TargetEq c ψ t = (ψ + ½ * c) * t ≡ ψ

damageUpdate : ℚ → ℚ → ℚ
damageUpdate φ t = φ ⊔ t

private
  sub-nonneg : ∀ {p q} → p ≤ q → 0ℚ ≤ q - p
  sub-nonneg {p} {q} h = ≤-trans (≤-reflexive (sym (+-inverseʳ q))) (+-monoʳ-≤ q (neg-antimono-≤ h))

  mul-nonneg : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
  mul-nonneg {a} ha hb = ≤-trans (≤-reflexive (sym (*-zeroʳ a))) (*-monoˡ-≤-nonNeg a {{nonNegative ha}} hb)

  mul-le-left : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → r * p ≤ r * q
  mul-le-left {r} hr h = *-monoˡ-≤-nonNeg r {{nonNegative hr}} h

  sq-mono : ∀ {a b} → 0ℚ ≤ a → a ≤ b → a * a ≤ b * b
  sq-mono {a} {b} ha h =
    ≤-trans (*-monoˡ-≤-nonNeg a {{nonNegative ha}} h) (*-monoʳ-≤-nonNeg b {{nonNegative (≤-trans ha h)}} h)

  sq-nonneg : ∀ y → 0ℚ ≤ y * y
  sq-nonneg y with ≤-total 0ℚ y
  ... | inj₁ h = mul-nonneg h h
  ... | inj₂ h = ≤-trans (mul-nonneg (sub-nonneg h) (sub-nonneg h))
                         (≤-reflexive (solve 1 (λ y → (con 0ℚ :- y) :* (con 0ℚ :- y) := y :* y) refl y))

  -- a ≤ b from 0 ≤ b − a
  le-of-sub : ∀ {a b} → 0ℚ ≤ b - a → a ≤ b
  le-of-sub {a} {b} h =
    ≤-trans (≤-reflexive (solve 1 (λ a → a := con 0ℚ :+ a) refl a))
      (≤-trans (+-monoˡ-≤ a h) (≤-reflexive (solve 2 (λ a b → (b :- a) :+ a := b) refl a b)))

  0≤½ : 0ℚ ≤ ½
  0≤½ = nonNegative⁻¹ ½

  cross : ℚ → ℚ → ℚ → ℚ → ℚ
  cross c ψ x t = (1ℚ + 1ℚ) * (x - t) * (ψ - (ψ + ½ * c) * t)

  -- The vertex form: E(x) = E(t) + (ψ + c/2)(x − t)² − 2 (x − t)(ψ − (ψ + c/2) t).
  vertex : ∀ c ψ x t → total c ψ x ≡ (total c ψ t + (ψ + ½ * c) * ((x - t) * (x - t))) - cross c ψ x t
  vertex c ψ x t = solve 4 (λ c ψ x t →
      ((con 1ℚ :- x) :* (con 1ℚ :- x)) :* ψ :+ con ½ :* c :* (x :* x)
    := (((con 1ℚ :- t) :* (con 1ℚ :- t)) :* ψ :+ con ½ :* c :* (t :* t)
         :+ (ψ :+ con ½ :* c) :* ((x :- t) :* (x :- t)))
         :- (con (1ℚ + 1ℚ) :* (x :- t) :* (ψ :- (ψ :+ con ½ :* c) :* t))) refl c ψ x t

  cross-zero : ∀ c ψ x t → TargetEq c ψ t → cross c ψ x t ≡ 0ℚ
  cross-zero c ψ x t eq =
    trans (cong (λ z → (1ℚ + 1ℚ) * (x - t) * (ψ - z)) eq)
      (solve 3 (λ x t ψ → con (1ℚ + 1ℚ) :* (x :- t) :* (ψ :- ψ) := con 0ℚ) refl x t ψ)

  vertex' : ∀ c ψ x t → TargetEq c ψ t → total c ψ x ≡ total c ψ t + (ψ + ½ * c) * ((x - t) * (x - t))
  vertex' c ψ x t eq =
    trans (vertex c ψ x t)
      (trans (cong (λ z → (total c ψ t + (ψ + ½ * c) * ((x - t) * (x - t))) - z) (cross-zero c ψ x t eq))
        (solve 1 (λ a → a :- con 0ℚ := a) refl _))

  sub-pos : ∀ {p q} → p < q → 0ℚ < q - p
  sub-pos {p} {q} h = ≤-<-trans (≤-reflexive (sym (+-inverseʳ q))) (+-mono-≤-< (≤-refl {q}) (neg-antimono-< h))

  pos-mul : ∀ {a b} → 0ℚ < a → 0ℚ < b → 0ℚ < a * b
  pos-mul {a} {b} ha hb = ≤-<-trans (≤-reflexive (sym (*-zeroʳ a))) (*-monoʳ-<-pos a {{positive ha}} hb)

  sub-nonpos : ∀ {a b} → a ≤ b → a - b ≤ 0ℚ
  sub-nonpos {a} {b} h = ≤-trans (+-monoˡ-≤ (- b) h) (≤-reflexive (+-inverseʳ b))

  shift : ∀ {a b d} → (b - a) + d ≤ 0ℚ → d ≤ a - b
  shift {a} {b} {d} h =
    ≤-trans (≤-reflexive (solve 3 (λ a b d → d := ((b :- a) :+ d) :+ (a :- b)) refl a b d))
      (≤-trans (+-monoˡ-≤ (a - b) h) (≤-reflexive (solve 2 (λ a b → con 0ℚ :+ (a :- b) := a :- b) refl a b)))

  unshift : ∀ {a b d} → d ≤ a - b → (b - a) + d ≤ 0ℚ
  unshift {a} {b} {d} h =
    ≤-trans (+-monoʳ-≤ (b - a) h) (≤-reflexive (solve 2 (λ a b → (b :- a) :+ (a :- b) := con 0ℚ) refl a b))

  half-c-pos : ∀ {c} → 0ℚ < c → 0ℚ < ½ * c
  half-c-pos hc = pos-mul (≤-<-trans (≤-refl {0ℚ}) (*<*-half)) hc
    where open import Data.Rational.Properties using (positive⁻¹)
          *<*-half : 0ℚ < ½
          *<*-half = positive⁻¹ ½

  a-pos : ∀ {c ψ} → 0ℚ < c → 0ℚ ≤ ψ → 0ℚ < ψ + ½ * c
  a-pos {c} {ψ} hc hψ = ≤-<-trans (≤-reflexive (solve 0 (con 0ℚ := con 0ℚ :+ con 0ℚ) refl)) (+-mono-≤-< hψ (half-c-pos hc))

  target-mem : ∀ {c ψ t} → 0ℚ < c → 0ℚ ≤ ψ → TargetEq c ψ t → 0ℚ ≤ t × t ≤ 1ℚ
  target-mem {c} {ψ} {t} hc hψ eq =
    *-cancelˡ-≤-pos a {{positive ha}} (≤-trans (≤-reflexive (*-zeroʳ a)) (≤-trans hψ (≤-reflexive (sym eq)))) ,
    *-cancelˡ-≤-pos a {{positive ha}}
      (≤-trans (≤-reflexive eq) (≤-trans (le-of-sub (≤-trans (<⇒≤ (half-c-pos hc))
        (≤-reflexive (solve 2 (λ ψ h → h := (ψ :+ h) :- ψ) refl ψ (½ * c))))) (≤-reflexive (sym (*-identityʳ a)))))
    where
      a = ψ + ½ * c
      ha = a-pos hc hψ

  total-le : ∀ c ψ t y x → TargetEq c ψ t → 0ℚ ≤ ψ + ½ * c → (y - t) * (y - t) ≤ (x - t) * (x - t) →
    total c ψ y ≤ total c ψ x
  total-le c ψ t y x eq ha h =
    ≤-trans (≤-reflexive (vertex' c ψ y t eq))
      (≤-trans (+-monoʳ-≤ (total c ψ t) (mul-le-left ha h)) (≤-reflexive (sym (vertex' c ψ x t eq))))

-- The damage step stays in [0, 1], never heals, and minimises the total energy over φ' ≥ φ.
at2-damage-update : ∀ c ψ φ t → 0ℚ < c → 0ℚ ≤ ψ → 0ℚ ≤ φ → φ ≤ 1ℚ → TargetEq c ψ t →
  φ ≤ damageUpdate φ t × 0ℚ ≤ damageUpdate φ t × damageUpdate φ t ≤ 1ℚ ×
  (∀ x → φ ≤ x → total c ψ (damageUpdate φ t) ≤ total c ψ x)
at2-damage-update c ψ φ t hc hψ h0 h1 eq with ≤-total φ t | target-mem hc hψ eq
... | inj₁ φ≤t | (t0 , t1) =
  subst (φ ≤_) (sym e) φ≤t , subst (0ℚ ≤_) (sym e) t0 , subst (_≤ 1ℚ) (sym e) t1 ,
  λ x hx → subst (λ z → total c ψ z ≤ total c ψ x) (sym e)
    (total-le c ψ t t x eq (<⇒≤ (a-pos hc hψ))
      (≤-trans (≤-reflexive (solve 1 (λ t → (t :- t) :* (t :- t) := con 0ℚ) refl t)) (sq-nonneg (x - t))))
  where e = p≤q⇒p⊔q≡q φ≤t
... | inj₂ t≤φ | _ =
  subst (φ ≤_) (sym e) ≤-refl , subst (0ℚ ≤_) (sym e) h0 , subst (_≤ 1ℚ) (sym e) h1 ,
  λ x hx → subst (λ z → total c ψ z ≤ total c ψ x) (sym e)
    (total-le c ψ t φ x eq (<⇒≤ (a-pos hc hψ)) (sq-mono (sub-nonneg t≤φ) (+-monoˡ-≤ (- t) hx)))
  where e = p≥q⇒p⊔q≡p t≤φ

-- The total energy does not increase on the whole domain [0, 1].
at2-energy-nonincreasing : ∀ c ψ φ t → 0ℚ < c → 0ℚ ≤ ψ → 0ℚ ≤ φ → φ ≤ 1ℚ → TargetEq c ψ t →
  total c ψ (damageUpdate φ t) ≤ total c ψ φ
at2-energy-nonincreasing c ψ φ t hc hψ h0 h1 eq with at2-damage-update c ψ φ t hc hψ h0 h1 eq
... | _ , _ , _ , hmin = hmin φ ≤-refl

-- The two readings agree: the passive balance with the crack energy spent is the change of total energy.
at2-balance-eq-total : ∀ c ψ φ φ' → (stored ψ φ' - stored ψ φ) + crackSpent c φ φ' ≡ total c ψ φ' - total c ψ φ
at2-balance-eq-total c ψ φ φ' = solve 4 (λ c ψ φ φ' →
    (((con 1ℚ :- φ') :* (con 1ℚ :- φ')) :* ψ :- ((con 1ℚ :- φ) :* (con 1ℚ :- φ)) :* ψ)
      :+ con ½ :* c :* (φ' :* φ' :- φ :* φ)
  := (((con 1ℚ :- φ') :* (con 1ℚ :- φ')) :* ψ :+ con ½ :* c :* (φ' :* φ'))
      :- (((con 1ℚ :- φ) :* (con 1ℚ :- φ)) :* ψ :+ con ½ :* c :* (φ :* φ))) refl c ψ φ φ'

crackSpent-nonneg : ∀ c φ φ' → 0ℚ < c → 0ℚ ≤ φ → φ ≤ φ' → 0ℚ ≤ crackSpent c φ φ'
crackSpent-nonneg c φ φ' hc h0 h = mul-nonneg (mul-nonneg 0≤½ (<⇒≤ hc)) (sub-nonneg (sq-mono h0 h))

-- Release of degraded elastic energy by any irreversible step in [0, 1].
at2-degradation-release-nonneg : ∀ ψ φ φ' → 0ℚ ≤ ψ → φ ≤ φ' → φ' ≤ 1ℚ → 0ℚ ≤ stored ψ φ - stored ψ φ'
at2-degradation-release-nonneg ψ φ φ' hψ h h1 =
  sub-nonneg (*-monoʳ-≤-nonNeg ψ {{nonNegative hψ}} (sq-mono (sub-nonneg h1) (+-monoʳ-≤ 1ℚ (neg-antimono-≤ h))))

-- Griffith: the passive inequality with the crack energy spent holds exactly when the release covers it.
at2-griffith-⇔ : ∀ c ψ φ φ' →
  ((stored ψ φ' - stored ψ φ) + crackSpent c φ φ' ≤ 0ℚ) ⇔ (crackSpent c φ φ' ≤ stored ψ φ - stored ψ φ')
at2-griffith-⇔ c ψ φ φ' = mk⇔ (shift {stored ψ φ} {stored ψ φ'}) (unshift {stored ψ φ} {stored ψ φ'})

-- The damage step is a SecondLaw transition through the passive route.
at2-damage-step-secondLaw : ∀ c ψ φ t ρ → 0ℚ < c → 0ℚ ≤ ψ → 0ℚ ≤ φ → φ ≤ 1ℚ → TargetEq c ψ t →
  SecondLaw transition (thermodynamic (mkState ρ (stored ψ φ) 0ℚ 0ℚ) (mkState ρ (stored ψ (damageUpdate φ t)) 0ℚ 0ℚ))
at2-damage-step-secondLaw c ψ φ t ρ hc hψ h0 h1 eq with at2-damage-update c ψ φ t hc hψ h0 h1 eq
... | hirr , _ , _ , _ =
  passive-inequality-secondLaw (ball , ball) (crackSpent-nonneg c φ (damageUpdate φ t) hc h0 hirr)
    (≤-trans (≤-reflexive (at2-balance-eq-total c ψ φ (damageUpdate φ t)))
      (sub-nonpos (at2-energy-nonincreasing c ψ φ t hc hψ h0 h1 eq)))
  where
    ball : ρ - ρ ≤ δ-mass
    ball = ≤-trans (≤-reflexive (+-inverseʳ ρ)) (nonNegative⁻¹ δ-mass)

-- Typed absence, the loading step: raising the strain energy at fixed damage is refused; the missing term is W_in.
at2-loading-refused : ∀ ψ ψ' φ ρ ρ' → φ < 1ℚ → ψ < ψ' →
  ¬ SecondLaw transition (thermodynamic (mkState ρ (stored ψ φ) 0ℚ 0ℚ) (mkState ρ' (stored ψ' φ) 0ℚ 0ℚ))
at2-loading-refused ψ ψ' φ ρ ρ' h1 hl s =
  <-irrefl refl (<-≤-trans hl (*-cancelˡ-≤-pos (degradation φ) {{positive hg}} (CoreAdmissible.dissipation-nonneg s)))
  where
    open import Core.Gate using (CoreAdmissible)
    hg : 0ℚ < degradation φ
    hg = pos-mul (sub-pos h1) (sub-pos h1)
