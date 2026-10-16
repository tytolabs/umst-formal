-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: ClassicalDPI.agda
--
-- Twin of Lean/ClassicalDPI.lean and Coq/ClassicalDPI.v. The standard library has no real logarithm, so the
-- analytic step (the two-term log-sum inequality, which makes the column functional
-- G(v) = Σ v_i log v_i − (Σ v_i) log(Σ v_i) subadditive on non-negative columns) is carried as data: G is any
-- functional, zero on the zero column and subadditive on non-negative columns. The combinatorial step is proved:
-- merging the columns of each group of a summary does not raise the sum of G (summary-colsum-le), which is
-- I(X; f(Y)) − H(X) ≤ I(X; Y) − H(X).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module ClassicalDPI where

open import Data.List using (List; []; _∷_; _++_; foldr; concat)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-identityˡ; +-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

module Merge {c} (C : Set c) (_⊕_ : C → C → C) (zero : C) (N : C → Set)
  (N-zero : N zero) (N-⊕ : ∀ {a b} → N a → N b → N (a ⊕ b))
  (G : C → ℚ) (G-zero : G zero ≡ 0ℚ) (G-sub : ∀ {a b} → N a → N b → G (a ⊕ b) ≤ G a + G b) where

  mergeAll : List C → C
  mergeAll = foldr _⊕_ zero

  sumG : List C → ℚ
  sumG = foldr (λ x acc → G x + acc) 0ℚ

  N-mergeAll : ∀ {cs} → All N cs → N (mergeAll cs)
  N-mergeAll []       = N-zero
  N-mergeAll (h ∷ hs) = N-⊕ h (N-mergeAll hs)

  -- Merging a family of non-negative columns does not raise the sum of G.
  merge-le : ∀ cs → All N cs → G (mergeAll cs) ≤ sumG cs
  merge-le []       []       = ≤-reflexive G-zero
  merge-le (x ∷ cs) (h ∷ hs) = ≤-trans (G-sub h (N-mergeAll hs)) (+-mono-≤ (≤-refl {G x}) (merge-le cs hs))

  sumG-++ : ∀ xs ys → sumG (xs ++ ys) ≡ sumG xs + sumG ys
  sumG-++ []       ys = sym (+-identityˡ (sumG ys))
  sumG-++ (x ∷ xs) ys = trans (cong (G x +_) (sumG-++ xs ys)) (sym (+-assoc (G x) (sumG xs) (sumG ys)))

  sumMerged : List (List C) → ℚ
  sumMerged = foldr (λ g acc → G (mergeAll g) + acc) 0ℚ

  -- The summary merges the columns of each group; the receipts are all the columns.
  summary-colsum-le : ∀ groups → All (All N) groups → sumMerged groups ≤ sumG (concat groups)
  summary-colsum-le []       []       = ≤-refl
  summary-colsum-le (g ∷ gs) (h ∷ hs) =
    ≤-trans (+-mono-≤ (merge-le g h) (summary-colsum-le gs hs)) (≤-reflexive (sym (sumG-++ g (concat gs))))
