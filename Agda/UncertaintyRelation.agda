-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UncertaintyRelation.agda
--
-- Twin of Lean/UncertaintyRelation.lean and Coq/UncertaintyRelation.v: the thermodynamic uncertainty relation
-- (A. C. Barato and U. Seifert, Phys. Rev. Lett. 114, 158101 (2015)) for the biased random walk with rates
-- k₊, k₋ > 0: mean current (k₊ − k₋) t and variance (k₊ + k₋) t (J. G. Skellam, J. R. Stat. Soc. 109, 296 (1946)),
-- entropy production (k₊ − k₋)(ln k₊ − ln k₋) t (J. Schnakenberg, Rev. Mod. Phys. 48, 571 (1976)):
--   2 ⟨J_t⟩² ≤ Var(J_t) · σ_t.
--
-- The standard library has no real logarithm, so the logarithm is a parameter, as in NaturalLog.agda: a function on
-- ℚ with the logarithmic-mean bound 2 (a − b)² ≤ (a + b)(a − b)(ln a − ln b) for a, b > 0. Lean
-- (UncertaintyRelation.log_mean_bound) and Coq (log_mean_bound) prove that bound for the real logarithm; here the
-- relation is derived from it for every such function. The record is a parameter of each statement, never a
-- postulate. The general TUR for any current of any finite Markov jump process is a typed absence
-- (follow-up FORMAL-TUR-GENERAL).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module UncertaintyRelation where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; Positive; nonNegative)
open import Data.Rational.Properties using (*-monoʳ-≤-nonNeg; nonNeg*nonNeg⇒nonNeg)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)

open +-*-Solver

two : ℚ
two = 1ℚ + 1ℚ

-- A logarithm on the rationals, by the logarithmic-mean bound of the real logarithm.
record LogMean : Set where
  field
    ln             : ℚ → ℚ
    log-mean-bound : ∀ a b → Positive a → Positive b →
                     two * ((a - b) * (a - b)) ≤ (a + b) * (a - b) * (ln a - ln b)

open LogMean

-- The biased random walk by its forward and backward rates.
record BiasedWalk : Set where
  field
    kPlus      : ℚ
    kMinus     : ℚ
    kPlus-pos  : Positive kPlus
    kMinus-pos : Positive kMinus

open BiasedWalk

meanCurrent : BiasedWalk → ℚ → ℚ
meanCurrent w t = (kPlus w - kMinus w) * t

varCurrent : BiasedWalk → ℚ → ℚ
varCurrent w t = (kPlus w + kMinus w) * t

entropyProduction : LogMean → BiasedWalk → ℚ → ℚ
entropyProduction L w t = (kPlus w - kMinus w) * (ln L (kPlus w) - ln L (kMinus w)) * t

-- Thermodynamic uncertainty relation for the biased walk: 2 ⟨J_t⟩² ≤ Var(J_t) · σ_t.
tur-biasedWalk : ∀ (L : LogMean) (w : BiasedWalk) (t : ℚ) → 0ℚ ≤ t →
  two * (meanCurrent w t * meanCurrent w t) ≤ varCurrent w t * entropyProduction L w t
tur-biasedWalk L w t ht =
  subst₂ _≤_
    (solve 3 (λ a b t → (con two :* ((a :- b) :* (a :- b))) :* (t :* t)
                        := con two :* (((a :- b) :* t) :* ((a :- b) :* t))) refl a b t)
    (solve 4 (λ a b l t → ((a :+ b) :* (a :- b) :* l) :* (t :* t)
                          := ((a :+ b) :* t) :* ((a :- b) :* l :* t)) refl a b (ln L a - ln L b) t)
    (*-monoʳ-≤-nonNeg (t * t) {{nonNeg*nonNeg⇒nonNeg t {{nonNegative ht}} t {{nonNegative ht}}}}
      (log-mean-bound L a b (kPlus-pos w) (kMinus-pos w)))
  where
  a = kPlus w
  b = kMinus w
