-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: CostOfInformation.agda
--
-- Twin of Lean/CostOfInformation.lean and Coq/CostOfInformation.v. Entropies are carried as rationals and k_B T
-- as a nonnegative rational; the information of one bit (ln 2 nats) is carried as data h, so the uniform
-- distribution on 2^b states carries b·h nats. Bounds with a division are stated with cleared denominators.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module CostOfInformation where

open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; NonNegative)
open import Data.Rational.Properties
  using (*-monoˡ-≤-nonNeg; ≤-reflexive; ≤-trans; +-mono-≤; nonNegative⁻¹; nonNeg*nonNeg⇒nonNeg)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process
open +-*-Solver

-- In joules: an erasure obeying the predicate dissipates at least k_B T times the entropy it removes.
entropyDrop-joules-le : ∀ kT .{{_ : NonNegative kT}} e Hp Hq → SecondLaw (erase e) (transformation Hp Hq) →
  kT * (Hp - Hq) ≤ kT * ErasureProcess.dissipatedEntropy e
entropyDrop-joules-le kT e Hp Hq h = *-monoˡ-≤-nonNeg kT h

-- The cost of b bits: erasing a distribution of b·h nats to a point costs at least b · k_B T h joules.
bitErasure-cost : ∀ kT .{{_ : NonNegative kT}} h bits e → SecondLaw (erase e) (transformation (bits * h) 0ℚ) →
  bits * (kT * h) ≤ kT * ErasureProcess.dissipatedEntropy e
bitErasure-cost kT h bits e hs =
  ≤-trans (≤-reflexive (solve 3 (λ k h b → b :* (k :* h) := k :* (b :* h :- con 0ℚ)) refl kT h bits))
          (entropyDrop-joules-le kT e (bits * h) 0ℚ hs)

-- The cockpit's honest spend: the Landauer bit energy L times the bits claimed is at most the energy spent.
honestSpend : ℚ → ℚ → ℚ → Set
honestSpend L bits energy = L * bits ≤ energy

-- Honest spend from the second law: a claim of b bits whose energy is the work, in joules, of an erasure of b bits
-- obeying the predicate pays the Landauer floor L = k_B T h.
honest-spend-of-secondLaw : ∀ kT .{{_ : NonNegative kT}} h bits e → SecondLaw (erase e) (transformation (bits * h) 0ℚ) →
  honestSpend (kT * h) bits (kT * ErasureProcess.dissipatedEntropy e)
honest-spend-of-secondLaw kT h bits e hs =
  ≤-trans (≤-reflexive (solve 3 (λ k h b → (k :* h) :* b := b :* (k :* h)) refl kT h bits)) (bitErasure-cost kT h bits e hs)

-- η_cog = d · bits / (E + L) is at most d / L for an honest claim; cleared of its positive denominators:
-- d · bits · L ≤ d · (E + L).
eta-cog-le-of-honest : ∀ d .{{_ : NonNegative d}} L .{{_ : NonNegative L}} bits E → honestSpend L bits E →
  d * bits * L ≤ d * (E + L)
eta-cog-le-of-honest d L bits E hh =
  ≤-trans (≤-reflexive (solve 3 (λ d b L → d :* b :* L := d :* (L :* b) :+ con 0ℚ) refl d bits L))
    (≤-trans (+-mono-≤ (*-monoˡ-≤-nonNeg d hh) (nonNegative⁻¹ (d * L) {{nonNeg*nonNeg⇒nonNeg d L}}))
             (≤-reflexive (solve 3 (λ d E L → d :* E :+ d :* L := d :* (E :+ L)) refl d E L)))

-- The bound composed over the predicate.
eta-cog-le-of-secondLaw : ∀ d .{{_ : NonNegative d}} kT .{{_ : NonNegative kT}} h .{{_ : NonNegative h}} bits e →
  SecondLaw (erase e) (transformation (bits * h) 0ℚ) →
  d * bits * (kT * h) ≤ d * (kT * ErasureProcess.dissipatedEntropy e + kT * h)
eta-cog-le-of-secondLaw d kT h bits e hs =
  eta-cog-le-of-honest d (kT * h) {{nonNeg*nonNeg⇒nonNeg kT h}} bits _ (honest-spend-of-secondLaw kT h bits e hs)
