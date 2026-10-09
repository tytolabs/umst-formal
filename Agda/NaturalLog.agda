-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: NaturalLog.agda
--
-- The standard library has no real logarithm and ln 2 is not rational, so Agda carries the logarithm as a
-- parameter: a function ln on the rationals with the two values of the real logarithm that the entropies of the
-- uniform bit and of the Dirac state use, ln 1 = 0 and ln ½ = −ln 2. Shannon entropy is then the same sum as in
-- Lean (LandauerLaw.shannonEntropy) and Coq, computed from the distribution; with the real logarithm each theorem
-- below is the Lean or Coq statement. The record is a parameter of each statement, never a postulate.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module NaturalLog where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _-_; -_)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

open +-*-Solver

two : ℚ
two = 1ℚ + 1ℚ

-- A natural logarithm on the rationals, by the two values of the real logarithm that the entropies below use.
record NaturalLog : Set where
  field
    ln      : ℚ → ℚ
    ln-one  : ln 1ℚ ≡ 0ℚ
    ln-half : ln ½ ≡ - ln two

open NaturalLog

-- Shannon entropy (nats) of the binary distribution (p, 1 − p): −Σ pᵢ ln pᵢ.
binaryEntropy : (ℚ → ℚ) → ℚ → ℚ
binaryEntropy ln p = - (p * ln p + (1ℚ - p) * ln (1ℚ - p))

-- The uniform bit carries ln 2 nats (twin of LandauerLaw.uniformBinaryEntropy).
uniformBinaryEntropy : ∀ L → binaryEntropy (ln L) ½ ≡ ln L two
uniformBinaryEntropy L =
  trans (solve 1 (λ a → :- (con ½ :* a :+ con ½ :* a) := :- a) refl (ln L ½))
        (trans (cong -_ (ln-half L)) (solve 1 (λ x → :- (:- x) := x) refl (ln L two)))

-- The Dirac state carries no entropy (twin of LandauerLaw.diracEntropy).
diracEntropy : ∀ L → binaryEntropy (ln L) 1ℚ ≡ 0ℚ
diracEntropy L =
  trans (solve 2 (λ c z → :- (con 1ℚ :* c :+ con 0ℚ :* z) := :- c) refl (ln L 1ℚ) (ln L 0ℚ))
        (trans (cong -_ (ln-one L)) refl)

-- Erasing the uniform bit to the Dirac state removes ln 2 nats (twin of LandauerLaw.binaryErasureEntropyDrop).
binaryErasureEntropyDrop : ∀ L → binaryEntropy (ln L) ½ - binaryEntropy (ln L) 1ℚ ≡ ln L two
binaryErasureEntropyDrop L =
  trans (cong₂ _-_ (uniformBinaryEntropy L) (diracEntropy L)) (solve 1 (λ x → x :- con 0ℚ := x) refl (ln L two))
