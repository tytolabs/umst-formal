-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Dignity.agda — the dignity scalar on [0, d-max] (twin of Lean/Dignity.lean and Coq/Dignity.v).
--
-- d-max = 10. A step raises the scalar by the claimed mutual information (bits), capped at d-max, only on honest
-- spend: the measured energy covers the Landauer cost of the claimed bits. That cost is k_B·T·ln 2 per bit, which is
-- not rational, so the bit energy of the bath enters as a rational parameter (Lean and Coq compute it). The step is
-- monotone in the claimed information when both steps are honest.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Dignity where

open import Data.Integer using (+_)
open import Data.Rational using (ℚ; _≤_; _+_; _*_; _⊓_; _/_)
open import Data.Rational.Properties using (_≤?_; ⊓-monoʳ-≤; +-monoʳ-≤)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Upper end of the dignity range [0, d-max].
d-max : ℚ
d-max = + 10 / 1

-- Honest spend: the bit energy times the claimed bits is covered by the measured energy.
HonestSpend : (bitEnergy mi energy : ℚ) → Set
HonestSpend bitEnergy mi energy = bitEnergy * mi ≤ energy

-- One step on the scalar d: on honest spend add the claimed bits, capped at d-max; otherwise unchanged.
dignity-step : (bitEnergy d mi energy : ℚ) → ℚ
dignity-step bitEnergy d mi energy with bitEnergy * mi ≤? energy
... | yes _ = d-max ⊓ (d + mi)
... | no _  = d

dignity-step-honest : ∀ bitEnergy d mi energy → HonestSpend bitEnergy mi energy →
  dignity-step bitEnergy d mi energy ≡ d-max ⊓ (d + mi)
dignity-step-honest bitEnergy d mi energy h with bitEnergy * mi ≤? energy
... | yes _ = refl
... | no ¬h = ⊥-elim (¬h h)

-- Monotonicity in the claimed information when both steps are honest.
dignity-monotone-under-mi-gain : ∀ bitEnergy d mi₁ e₁ mi₂ e₂ →
  HonestSpend bitEnergy mi₁ e₁ → HonestSpend bitEnergy mi₂ e₂ → mi₁ ≤ mi₂ →
  dignity-step bitEnergy d mi₁ e₁ ≤ dignity-step bitEnergy d mi₂ e₂
dignity-monotone-under-mi-gain bitEnergy d mi₁ e₁ mi₂ e₂ h₁ h₂ le
  rewrite (dignity-step-honest bitEnergy d mi₁ e₁ h₁) | (dignity-step-honest bitEnergy d mi₂ e₂ h₂) =
  ⊓-monoʳ-≤ d-max (+-monoʳ-≤ d le)
