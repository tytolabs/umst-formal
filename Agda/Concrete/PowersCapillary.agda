-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Concrete/PowersCapillary.agda
--
-- Twin of Lean/Concrete/PowersCapillary.lean and Coq/Concrete/PowersCapillary.v. The capillary pores of a paste,
-- capillary water together with chemical-shrinkage voids, fill p − (w/c)_s·(ρ_c/ρ_w)·(1 − p)·α of the paste at
-- initial water fraction p and degree of hydration α; with p/(1 − p) = w·ρ_c/ρ_w this is the Lean and Coq closed form
-- (w − (w/c)_s·α)/(w + ρ_w/ρ_c), stated here with the denominator cleared. The runtime closures carry the rounded
-- coefficients 0.36, 0.32 and 0.317, each the rounding ⌊x + ½⌋ of its derived value, the two-decimal ones within
-- 1/200 of it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Concrete.PowersCapillary where

open import Data.Integer using (ℤ; +_)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _≤_; _/_; ½; floor; ∣_∣; 1/_)
open import Data.Rational.Properties using (_≤?_)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)
open import Concrete.PowersVolume using
  (capillaryWater; shrinkage; one; densityRatio; criticalWcSpace; capillaryConsumption; shrinkageVolume)

-- Capillary pore fraction of the paste: capillary water plus chemical-shrinkage voids.
capillaryPorosity : ℚ → ℚ → ℚ
capillaryPorosity p a = capillaryWater p a + shrinkage p a

open +-*-Solver

-- Capillary porosity in closed form, the denominator cleared: p − (w/c)_s·(ρ_c/ρ_w)·(1 − p)·α.
capillaryPorosity-eq : ∀ p a → capillaryPorosity p a ≡ p - criticalWcSpace * densityRatio * (one - p) * a
capillaryPorosity-eq = solve 2 (λ p a →
  (p :- con capillaryConsumption :* (con one :- p) :* a) :+ con shrinkageVolume :* (con one :- p) :* a
  := p :- con (criticalWcSpace * densityRatio) :* (con one :- p) :* a) refl

-- x rounded to two and to three decimals, ⌊x + ½⌋ at that scale.
round2 round3 : ℚ → ℚ
round2 x = floor (+ 100 / 1 * x + ½) / 100
round3 x = floor (+ 1000 / 1 * x + ½) / 1000

powersCapillaryWaterCoeff powersPasteOffsetCoeff powersCementVolumeCoeff : ℚ
powersCapillaryWaterCoeff = round2 criticalWcSpace
powersPasteOffsetCoeff = round2 (1/ densityRatio)
powersCementVolumeCoeff = round3 (1/ densityRatio)

powersCapillaryWaterCoeff-value : powersCapillaryWaterCoeff ≡ + 36 / 100
powersCapillaryWaterCoeff-value = refl

powersPasteOffsetCoeff-value : powersPasteOffsetCoeff ≡ + 32 / 100
powersPasteOffsetCoeff-value = refl

powersCementVolumeCoeff-value : powersCementVolumeCoeff ≡ + 317 / 1000
powersCementVolumeCoeff-value = refl

-- The rounded capillary-water coefficient lies within 1/200 of (w/c)_s.
powersCapillaryWaterCoeff-err : ∣ powersCapillaryWaterCoeff - criticalWcSpace ∣ ≤ + 1 / 200
powersCapillaryWaterCoeff-err = toWitness {a? = ∣ powersCapillaryWaterCoeff - criticalWcSpace ∣ ≤? + 1 / 200} _

-- The rounded paste-offset coefficient lies within 1/200 of ρ_w/ρ_c.
powersPasteOffsetCoeff-err : ∣ powersPasteOffsetCoeff - 1/ densityRatio ∣ ≤ + 1 / 200
powersPasteOffsetCoeff-err = toWitness {a? = ∣ powersPasteOffsetCoeff - 1/ densityRatio ∣ ≤? + 1 / 200} _
