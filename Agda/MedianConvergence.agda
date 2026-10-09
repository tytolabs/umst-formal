-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: MedianConvergence.agda — the median warm-up budget (twin of Lean/MedianConvergence.lean and
-- Coq/MedianConvergence.v).
--
-- At the reference triple (ε, δ, ρ_min) = (1, ½, 1) the Hoeffding-style threshold (2 / (ε²·ρ_min²))·ln(2/δ) is
-- 2·ln 4, and the default cockpit window W = 32 gives the warm-up count max 3 ⌈√32⌉ = 6. Ceilings are stated by
-- their defining inequalities: ⌈√32⌉ = 6 because 5² < 32 ≤ 6², and ⌈x⌉ ≤ 6 because x ≤ 6. The standard library has
-- no real logarithm, so ln 4 enters as a rational ℓ with ℓ ≤ 3 (Lean and Coq prove ln 4 < 3 from 4 < e³).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MedianConvergence where

open import Data.Integer using (+_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; _≤_; _*_; _/_; _⊔_)
open import Data.Rational.Properties using (*-monoˡ-≤-nonNeg)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary.Decidable using (toWitness)

-- Analytic sample threshold at (ε, δ, ρ_min) = (1, ½, 1): (2 / (1·1))·ln 4 with ln 4 = ℓ.
nWarmupBound-ref : ℚ → ℚ
nWarmupBound-ref ℓ = (+ 2 / 1) * ℓ

sqrt-window-warmup-is-admissible : ((5 ℕ.* 5 ℕ.< 32) × (32 ℕ.≤ 6 ℕ.* 6)) ×
  (∀ ℓ → ℓ ≤ + 3 / 1 → nWarmupBound-ref ℓ ≤ (+ 3 / 1) ⊔ (+ 6 / 1))
sqrt-window-warmup-is-admissible =
  (toWitness {a? = 5 ℕ.* 5 ℕ.<? 32} _ , toWitness {a? = 32 ℕ.≤? 6 ℕ.* 6} _) ,
  λ ℓ h → *-monoˡ-≤-nonNeg (+ 2 / 1) h
