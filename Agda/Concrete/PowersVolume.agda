-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Concrete/PowersVolume.agda
--
-- Powers' volume model with the coefficients derived in Constants/SI.agda (normalised here); twin of Lean/Concrete/PowersVolume.lean
-- and Coq/Concrete/PowersVolume.v: the coefficients conserve volume, so at every initial water fraction p and
-- degree of hydration α the phases fill the paste; at complete hydration capillary water remains exactly when
-- w ≥ 0.42 and the products fit exactly when w ≥ 0.356. The thresholds are stated per unit volume of cement (the
-- Lean and Coq fractions divided by the cement fraction 1 − p, with p/(1 − p) = w·d), which has their sign.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Concrete.PowersVolume where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; fromℚᵘ; Positive)
open import Data.Rational.Properties using (+-mono-≤; ≤-refl; *-monoʳ-≤-nonNeg; *-cancelʳ-≤-pos)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
import Constants.SI as SI

-- The derived coefficients of Constants/SI.agda, as normalised rationals.
gelSolidsVolume gelWaterVolume capillaryConsumption shrinkageVolume : ℚ
gelSolidsVolume = fromℚᵘ SI.gelSolidsVolume
gelWaterVolume = fromℚᵘ SI.gelWaterVolume
capillaryConsumption = fromℚᵘ SI.capillaryConsumption
shrinkageVolume = fromℚᵘ SI.shrinkageVolume

densityRatio criticalWcSealed criticalWcSpace : ℚ
densityRatio = fromℚᵘ SI.densityRatio
criticalWcSealed = fromℚᵘ SI.criticalWcSealed
criticalWcSpace = fromℚᵘ SI.criticalWcSpace

one : ℚ
one = 1ℚ

cement gelSolids gelWaterV capillaryWater shrinkage : ℚ → ℚ → ℚ
cement p a = (one - p) * (one - a)
gelSolids p a = gelSolidsVolume * (one - p) * a
gelWaterV p a = gelWaterVolume * (one - p) * a
capillaryWater p a = p - capillaryConsumption * (one - p) * a
shrinkage p a = shrinkageVolume * (one - p) * a

-- The coefficients conserve volume.
coefficient-balance : gelSolidsVolume + gelWaterVolume + shrinkageVolume - capillaryConsumption ≡ one
coefficient-balance = refl

open +-*-Solver

-- Volume balance: at every initial water fraction and degree of hydration the phases fill the paste.
volume-balance : ∀ p a → cement p a + gelSolids p a + gelWaterV p a + capillaryWater p a + shrinkage p a ≡ one
volume-balance = solve 2 (λ p a →
  (con one :- p) :* (con one :- a) :+ con gelSolidsVolume :* (con one :- p) :* a
    :+ con gelWaterVolume :* (con one :- p) :* a :+ (p :- con capillaryConsumption :* (con one :- p) :* a)
    :+ con shrinkageVolume :* (con one :- p) :* a
  := con one) refl

-- The sign of a difference.
nonneg-diff : ∀ x y → (0ℚ ≤ x - y) ⇔ (y ≤ x)
nonneg-diff x y = mk⇔
  (λ h → subst₂ _≤_ (solve 1 (λ y → con 0ℚ :+ y := y) refl y) (solve 2 (λ x y → (x :- y) :+ y := x) refl x y)
           (+-mono-≤ h (≤-refl {y})))
  (λ h → subst₂ _≤_ (solve 1 (λ y → y :- y := con 0ℚ) refl y) refl (+-mono-≤ h ≤-refl))

instance
  densityRatio-pos : Positive densityRatio
  densityRatio-pos = _

-- Scaling by the positive density ratio preserves order both ways.
scale-≤ : ∀ x y → (x * densityRatio ≤ y * densityRatio) ⇔ (x ≤ y)
scale-≤ x y = mk⇔ (*-cancelʳ-≤-pos densityRatio) (*-monoʳ-≤-nonNeg densityRatio)

-- Capillary water and shrinkage voids at complete hydration, per unit volume of cement, for water-cement ratio w.
capillaryPerCement spacePerCement : ℚ → ℚ
capillaryPerCement w = w * densityRatio - capillaryConsumption
spacePerCement w = capillaryPerCement w + shrinkageVolume

-- Sealed-curing threshold: capillary water remains at complete hydration exactly when w ≥ 0.42.
capillaryPerCement-nonneg-iff : ∀ w → (0ℚ ≤ capillaryPerCement w) ⇔ (criticalWcSealed ≤ w)
capillaryPerCement-nonneg-iff w = mk⇔
  (λ h → Equivalence.to (scale-≤ criticalWcSealed w) (Equivalence.to (nonneg-diff (w * densityRatio) capillaryConsumption) h))
  (λ h → Equivalence.from (nonneg-diff (w * densityRatio) capillaryConsumption) (Equivalence.from (scale-≤ criticalWcSealed w) h))

space-eq : ∀ w → spacePerCement w ≡ w * densityRatio - criticalWcSpace * densityRatio
space-eq = solve 1 (λ w → (w :* con densityRatio :- con capillaryConsumption) :+ con shrinkageVolume
  := w :* con densityRatio :- con (criticalWcSpace * densityRatio)) refl

-- Space threshold: the products fit at complete hydration exactly when w ≥ 0.356.
spacePerCement-nonneg-iff : ∀ w → (0ℚ ≤ spacePerCement w) ⇔ (criticalWcSpace ≤ w)
spacePerCement-nonneg-iff w = mk⇔
  (λ h → Equivalence.to (scale-≤ criticalWcSpace w)
           (Equivalence.to (nonneg-diff (w * densityRatio) (criticalWcSpace * densityRatio)) (subst (0ℚ ≤_) (space-eq w) h)))
  (λ h → subst (0ℚ ≤_) (sym (space-eq w))
           (Equivalence.from (nonneg-diff (w * densityRatio) (criticalWcSpace * densityRatio)) (Equivalence.from (scale-≤ criticalWcSpace w) h)))
