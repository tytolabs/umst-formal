-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: UnfoldProxStepLaws.agda
--
-- Twin of Lean/UnfoldProxStepLaws.lean and Coq/UnfoldProxStepLaws.v over exact rationals (law L3): a step minimising
-- ψ x − w x + τ φ (d x), with φ 0 = 0 and d x₀ = 0, satisfies ψ x⁺ − ψ x₀ + τ φ (d x⁺) ≤ w x⁺ − w x₀; with φ ≥ 0 the
-- free-energy change is at most the supplied work; a candidate breaking the inequality is no minimiser; on a scalar
-- state supporting lines of the convex ψ and φ at a stationary point give the same inequality, and the slope of φ
-- makes b v ≥ φ v ≥ 0.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module UnfoldProxStepLaws where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; _<_; nonNegative)
open import Data.Rational.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-identityʳ; *-zeroʳ; <-irrefl; ≤-<-trans; *-monoˡ-≤-nonNeg)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open +-*-Solver

private
  mul-le-left : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → r * p ≤ r * q
  mul-le-left {r} hr h = *-monoˡ-≤-nonNeg r {{nonNegative hr}} h

  mul-nonneg : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
  mul-nonneg {a} ha hb = ≤-trans (≤-reflexive (sym (*-zeroʳ a))) (mul-le-left ha hb)

module _ {X : Set} where

  incremental : (ψ w : X → ℚ) (φ : ℚ → ℚ) (d : X → ℚ) (τ : ℚ) (x : X) → ℚ
  incremental ψ w φ d τ x = ψ x - w x + τ * φ (d x)

  IsProxStep : (ψ w : X → ℚ) (φ : ℚ → ℚ) (d : X → ℚ) (τ : ℚ) (xp : X) → Set
  IsProxStep ψ w φ d τ xp = ∀ x → incremental ψ w φ d τ xp ≤ incremental ψ w φ d τ x

  -- L3 from minimality.
  prox-step-le : ∀ (ψ w : X → ℚ) (φ : ℚ → ℚ) (d : X → ℚ) (τ : ℚ) (x₀ xp : X) → φ 0ℚ ≡ 0ℚ → d x₀ ≡ 0ℚ →
    IsProxStep ψ w φ d τ xp → ψ xp - ψ x₀ + τ * φ (d xp) ≤ w xp - w x₀
  prox-step-le ψ w φ d τ x₀ xp hφ0 hd0 hmin =
    ≤-trans (≤-reflexive e1) (≤-trans (+-monoˡ-≤ (w xp - ψ x₀) (hmin x₀)) (≤-reflexive e2))
    where
      z : τ * φ (d x₀) ≡ 0ℚ
      z = trans (cong (λ u → τ * φ u) hd0) (trans (cong (τ *_) hφ0) (*-zeroʳ τ))
      e1 : ψ xp - ψ x₀ + τ * φ (d xp) ≡ (ψ xp - w xp + τ * φ (d xp)) + (w xp - ψ x₀)
      e1 = solve 4 (λ a b c p → a :- b :+ c := (a :- p :+ c) :+ (p :- b)) refl (ψ xp) (ψ x₀) (τ * φ (d xp)) (w xp)
      e2 : (ψ x₀ - w x₀ + τ * φ (d x₀)) + (w xp - ψ x₀) ≡ w xp - w x₀
      e2 = trans (cong (λ k → (ψ x₀ - w x₀ + k) + (w xp - ψ x₀)) z)
             (solve 3 (λ b q p → (b :- q :+ con 0ℚ) :+ (p :- b) := p :- q) refl (ψ x₀) (w x₀) (w xp))

  -- L3, the inequality ΔF ≤ W_in, with a non-negative dissipation potential.
  prox-step-deltaF-le : ∀ (ψ w : X → ℚ) (φ : ℚ → ℚ) (d : X → ℚ) (τ : ℚ) (x₀ xp : X) → 0ℚ ≤ τ → (∀ v → 0ℚ ≤ φ v) →
    φ 0ℚ ≡ 0ℚ → d x₀ ≡ 0ℚ → IsProxStep ψ w φ d τ xp → ψ xp - ψ x₀ ≤ w xp - w x₀
  prox-step-deltaF-le ψ w φ d τ x₀ xp hτ hφ hφ0 hd0 hmin =
    ≤-trans (≤-trans (≤-reflexive (sym (+-identityʳ (ψ xp - ψ x₀)))) (+-monoʳ-≤ (ψ xp - ψ x₀) (mul-nonneg hτ (hφ (d xp)))))
      (prox-step-le ψ w φ d τ x₀ xp hφ0 hd0 hmin)

  -- L3 refusal: a candidate that breaks the discrete inequality is no minimiser.
  prox-step-refused : ∀ (ψ w : X → ℚ) (φ : ℚ → ℚ) (d : X → ℚ) (τ : ℚ) (x₀ xp : X) → φ 0ℚ ≡ 0ℚ → d x₀ ≡ 0ℚ →
    w xp - w x₀ < ψ xp - ψ x₀ + τ * φ (d xp) → ¬ IsProxStep ψ w φ d τ xp
  prox-step-refused ψ w φ d τ x₀ xp hφ0 hd0 hanti hmin = <-irrefl refl (≤-<-trans (prox-step-le ψ w φ d τ x₀ xp hφ0 hd0 hmin) hanti)

-- The supporting line of φ at v with φ 0 = 0 gives φ v ≤ b v.
private
  slope-le : ∀ (φ : ℚ → ℚ) (v b : ℚ) → φ 0ℚ ≡ 0ℚ → φ v + b * (0ℚ - v) ≤ φ 0ℚ → φ v ≤ b * v
  slope-le φ v b hφ0 hφ =
    ≤-trans (≤-reflexive (solve 3 (λ p b v → p := (p :+ b :* (con 0ℚ :- v)) :+ b :* v) refl (φ v) b v))
      (≤-trans (+-monoˡ-≤ (b * v) (≤-trans hφ (≤-reflexive hφ0)))
        (≤-reflexive (solve 1 (λ k → con 0ℚ :+ k := k) refl (b * v))))

-- L3 from stationarity (scalar state, τ v = x⁺ − x₀).
prox-step-stationary-le : ∀ (ψ φ : ℚ → ℚ) (τ x₀ xp v a b f : ℚ) → τ * v ≡ xp - x₀ → φ 0ℚ ≡ 0ℚ → 0ℚ ≤ τ →
  ψ xp + a * (x₀ - xp) ≤ ψ x₀ → φ v + b * (0ℚ - v) ≤ φ 0ℚ → a + b ≡ f →
  ψ xp - ψ x₀ + τ * φ v ≤ f * (xp - x₀)
prox-step-stationary-le ψ φ τ x₀ xp v a b f hv hφ0 hτ hψ hφ hstat =
  ≤-trans (+-mono-≤ hΔψ hD) (≤-reflexive eq)
  where
    -- ψ x⁺ − ψ x₀ ≤ a (x⁺ − x₀)
    hΔψ : ψ xp - ψ x₀ ≤ a * (xp - x₀)
    hΔψ = ≤-trans (≤-reflexive (solve 5 (λ p q a d e → p :- q := (p :+ a :* (e :- d)) :+ (a :* (d :- e) :- q)) refl (ψ xp) (ψ x₀) a xp x₀))
            (≤-trans (+-monoˡ-≤ (a * (xp - x₀) - ψ x₀) hψ)
              (≤-reflexive (solve 4 (λ q a d e → q :+ (a :* (d :- e) :- q) := a :* (d :- e)) refl (ψ x₀) a xp x₀)))
    -- τ φ v ≤ b (x⁺ − x₀)
    hD : τ * φ v ≤ b * (xp - x₀)
    hD = ≤-trans (mul-le-left hτ (slope-le φ v b hφ0 hφ))
           (≤-reflexive (trans (solve 3 (λ t b v → t :* (b :* v) := b :* (t :* v)) refl τ b v) (cong (b *_) hv)))
    eq : a * (xp - x₀) + b * (xp - x₀) ≡ f * (xp - x₀)
    eq = trans (solve 3 (λ a b d → a :* d :+ b :* d := (a :+ b) :* d) refl a b (xp - x₀)) (cong (_* (xp - x₀)) hstat)

-- The slope of a convex φ with φ 0 = 0 and φ ≥ 0 makes the dissipation rate non-negative: b v ≥ φ v ≥ 0.
prox-dissipation-rate-nonneg : ∀ (φ : ℚ → ℚ) (v b : ℚ) → φ 0ℚ ≡ 0ℚ → 0ℚ ≤ φ v → φ v + b * (0ℚ - v) ≤ φ 0ℚ →
  (φ v ≤ b * v) × (0ℚ ≤ b * v)
prox-dissipation-rate-nonneg φ v b hφ0 hv hφ = slope-le φ v b hφ0 hφ , ≤-trans hv (slope-le φ v b hφ0 hφ)
