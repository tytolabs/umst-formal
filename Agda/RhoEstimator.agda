-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: RhoEstimator.agda — Gaussian bivariate mutual information in bits from the Pearson correlation
-- (twin of Lean/RhoEstimator.lean and Coq/RhoEstimator.v): MI(ρ) = −½·log₂(1 − ρ²) for ρ² < 1, a function of ρ².
--
-- The standard library has no real logarithm, so the base-2 logarithm is a parameter of the definitions; the
-- closed form holds for every choice of it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module RhoEstimator where

open import Data.Rational using (ℚ; 1ℚ; ½; _<_; _*_; _-_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Correlations for which the closed form holds.
ValidRho : ℚ → Set
ValidRho ρ = ρ * ρ < 1ℚ

-- Mutual information (bits) as a function of t = ρ².
rhoMiOfSq : (log₂ : ℚ → ℚ) → ℚ → ℚ
rhoMiOfSq log₂ t = - ½ * log₂ (1ℚ - t)

-- Mutual information (bits) of a bivariate Gaussian with correlation ρ.
rhoMi : (log₂ : ℚ → ℚ) → ℚ → ℚ
rhoMi log₂ ρ = rhoMiOfSq log₂ (ρ * ρ)

rho-based-mi-formula : ∀ log₂ ρ → ValidRho ρ → rhoMi log₂ ρ ≡ - ½ * log₂ (1ℚ - ρ * ρ)
rho-based-mi-formula log₂ ρ _ = refl
