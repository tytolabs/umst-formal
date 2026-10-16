-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: UnfoldTermination.agda
--
-- Twin of Lean/UnfoldTermination.lean and Coq/UnfoldTermination.v over exact rationals (law L-E): spends each at
-- least ε summing to at most B number n with n ε ≤ B; a step erasing bits ≥ b bits at a cost of at least
-- bits · kT · l with l ≥ l_lo spends at least b · kT · l_lo, l_lo = 6931471803 / 10¹⁰ the lower end of the
-- enclosure of ln 2.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module UnfoldTermination where

open import Data.List using (List; []; _∷_; foldr)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; nonNegative)
open import Data.Rational.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; *-zeroˡ; *-zeroʳ)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open +-*-Solver

qsum : List ℚ → ℚ
qsum = foldr _+_ 0ℚ

-- The number of steps, as a rational.
count : List ℚ → ℚ
count = foldr (λ _ n → 1ℚ + n) 0ℚ

private
  mul-le-left : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → r * p ≤ r * q
  mul-le-left {r} hr h = *-monoˡ-≤-nonNeg r {{nonNegative hr}} h

  mul-le-right : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → p * r ≤ q * r
  mul-le-right {r} hr h = *-monoʳ-≤-nonNeg r {{nonNegative hr}} h

  count-mul-le : ∀ ε l → All (ε ≤_) l → count l * ε ≤ qsum l
  count-mul-le ε []      []       = ≤-reflexive (*-zeroˡ ε)
  count-mul-le ε (w ∷ l) (h ∷ hs) =
    ≤-trans (≤-reflexive (solve 2 (λ e n → (con 1ℚ :+ n) :* e := e :+ n :* e) refl ε (count l)))
      (+-mono-≤ h (count-mul-le ε l hs))

-- L-E: n ε ≤ B.
steps-mul-le : ∀ ε B l → All (ε ≤_) l → qsum l ≤ B → count l * ε ≤ B
steps-mul-le ε B l hf hB = ≤-trans (count-mul-le ε l hf) hB

-- The lower end of the enclosure of ln 2.
ln2Lower : ℚ
ln2Lower = + 6931471803 / 10000000000

-- The Landauer floor enclosed from below: b ≤ bits and ln2Lower ≤ l give b kT ln2Lower ≤ bits kT l ≤ W.
erase-spend-ge-enclosure : ∀ (kT l W b bits : ℚ) → 0ℚ ≤ kT → 0ℚ ≤ ln2Lower → 0ℚ ≤ bits → ln2Lower ≤ l → b ≤ bits →
  bits * (kT * l) ≤ W → b * (kT * ln2Lower) ≤ W
erase-spend-ge-enclosure kT l W b bits hk hlo hbits hl hb hc =
  ≤-trans (mul-le-right (mul-nonneg hk hlo) hb) (≤-trans (mul-le-left hbits (mul-le-left hk hl)) hc)
  where
    mul-nonneg : ∀ {a c} → 0ℚ ≤ a → 0ℚ ≤ c → 0ℚ ≤ a * c
    mul-nonneg {a} ha hc' = ≤-trans (≤-reflexive (sym (*-zeroʳ a))) (mul-le-left ha hc')
