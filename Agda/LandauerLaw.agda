-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: LandauerLaw.agda — the entropy of the uniform bit (twin of LandauerLaw.uniformBinaryEntropy in
-- Lean/LandauerLaw.lean and shannon2_uniform2 in Coq/Process.v).
--
-- The standard library has no real logarithm, so the statement is made for every logarithm: any function on the
-- positive rationals that turns products into sums. Under it the uniform distribution on two states, with masses
-- ½ and ½, has Shannon entropy −(½·log ½ + ½·log ½) = log 2. With the natural logarithm this is ln 2.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module LandauerLaw where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; -_; Positive)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open +-*-Solver

two : ℚ
two = 1ℚ + 1ℚ

-- Shannon entropy (nats, for the logarithm `log`) of the distribution with masses p and 1 − p.
binaryEntropy : (ℚ → ℚ) → ℚ → ℚ → ℚ
binaryEntropy log p q = - (p * log p + q * log q)

-- The uniform bit has entropy log 2 under every logarithm.
uniformBinaryEntropy : (log : ℚ → ℚ) →
  (log-mul : ∀ x y → .{{_ : Positive x}} → .{{_ : Positive y}} → log (x * y) ≡ log x + log y) →
  binaryEntropy log ½ ½ ≡ log two
uniformBinaryEntropy log log-mul = trans (e (log ½)) (neg-log½ )
  where
    log1≡0 : log 1ℚ ≡ 0ℚ
    log1≡0 = trans (h (log 1ℚ)) (trans (cong (_+ - log 1ℚ) (sym (log-mul 1ℚ 1ℚ))) (k (log 1ℚ)))
      where
        h : ∀ a → a ≡ (a + a) + - a
        h = solve 1 (λ a → a := (a :+ a) :+ :- a) refl
        k : ∀ a → a + - a ≡ 0ℚ
        k = solve 1 (λ a → a :+ :- a := con 0ℚ) refl
    -- log ½ + log 2 = log (½ · 2) = log 1 = 0.
    sum0 : log ½ + log two ≡ 0ℚ
    sum0 = trans (sym (log-mul ½ two)) log1≡0
    e : ∀ a → - (½ * a + ½ * a) ≡ - a
    e = solve 1 (λ a → :- (con ½ :* a :+ con ½ :* a) := :- a) refl
    neg-log½ : - (log ½) ≡ log two
    neg-log½ = trans (f (log ½) (log two)) (trans (cong (_+ log two) (cong -_ sum0)) (+-identityˡ′ (log two)))
      where
        f : ∀ a b → - a ≡ - (a + b) + b
        f = solve 2 (λ a b → :- a := :- (a :+ b) :+ b) refl
        +-identityˡ′ : ∀ b → - 0ℚ + b ≡ b
        +-identityˡ′ = solve 1 (λ b → :- con 0ℚ :+ b := b) refl
