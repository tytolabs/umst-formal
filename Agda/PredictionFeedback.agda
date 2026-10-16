-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: PredictionFeedback.agda
--
-- Twin of Lean/PredictionFeedback.lean and Coq/PredictionFeedback.v: a prediction-then-observation turn of the
-- learning loop is an instance of the measureFeedback case of the one predicate SecondLaw, judged against the
-- mutual information between prediction and outcome (nats, carried as a rational as in Process.agda). A summary of
-- receipts carrying no more information than the receipts (the data-processing inequality, a hypothesis) admits no
-- work the receipts refuse; over the loop's decisions the gated choices err in sum by at most the prediction errors
-- plus the gate's moves.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module PredictionFeedback where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; foldr)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; ∣_∣; NonNegative)
open import Data.Rational.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoʳ-≤; *-monoˡ-≤-nonNeg; ∣p+q∣≤∣p∣+∣q∣; +-comm)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

open import Process
open +-*-Solver

-- One turn: the work extracted by acting on the prediction, the free-energy change, k_B T of the bath and the mutual
-- information between prediction and outcome.
record Turn : Set where
  constructor turn
  field
    extWork deltaF kBT info : ℚ
open Turn

turnProcess : Turn → Process
turnProcess t = measureFeedback (record { extWork = extWork t ; deltaFreeEnergy = deltaF t ; kBT = kBT t })

TurnAdmissible : Turn → Set
TurnAdmissible t = SecondLaw (turnProcess t) (feedback (info t))

-- The turn is a measureFeedback instance: admissibility is the Sagawa–Ueda inequality at its information.
turn-work-le : ∀ t → TurnAdmissible t → extWork t ≤ (- deltaF t) + kBT t * info t
turn-work-le t h = h

turn-work-le⁻¹ : ∀ t → extWork t ≤ (- deltaF t) + kBT t * info t → TurnAdmissible t
turn-work-le⁻¹ t h = h

-- A cyclic turn extracts at most k_B T times the information its prediction carries.
turn-cyclic-work-le : ∀ t → TurnAdmissible t → deltaF t ≡ 0ℚ → extWork t ≤ kBT t * info t
turn-cyclic-work-le (turn w f k i) h refl = ≤-trans h (≤-reflexive (solve 2 (λ k i → (:- con 0ℚ) :+ k :* i := k :* i) refl k i))

-- Two admissible turns at one bath add.
turn-pair-work-le : ∀ s t → kBT s ≡ kBT t → TurnAdmissible s → TurnAdmissible t →
  extWork s + extWork t ≤ (- (deltaF s + deltaF t)) + kBT s * (info s + info t)
turn-pair-work-le (turn w₁ f₁ k i₁) (turn w₂ f₂ .k i₂) refl h₁ h₂ =
  ≤-trans (+-mono-≤ h₁ h₂)
    (≤-reflexive (solve 5 (λ f₁ f₂ k i₁ i₂ → ((:- f₁) :+ k :* i₁) :+ ((:- f₂) :+ k :* i₂) := (:- (f₁ :+ f₂)) :+ k :* (i₁ :+ i₂))
      refl f₁ f₂ k i₁ i₂))

-- The same turn judged against another information (the receipts', or a summary's).
against : Turn → ℚ → Turn
against (turn w f k _) i = turn w f k i

-- Data-processing corollary: a summary carrying no more information than the receipts admits only works the
-- receipts admit.
summary-admitted-receipts : ∀ t .{{_ : NonNegative (kBT t)}} iSummary iReceipts → iSummary ≤ iReceipts →
  TurnAdmissible (against t iSummary) → TurnAdmissible (against t iReceipts)
summary-admitted-receipts (turn w f k _) iS iR hDPI h = ≤-trans h (+-monoʳ-≤ (- f) (*-monoˡ-≤-nonNeg k hDPI))

receipts-refused-summary : ∀ t .{{_ : NonNegative (kBT t)}} iSummary iReceipts → iSummary ≤ iReceipts →
  ¬ TurnAdmissible (against t iReceipts) → ¬ TurnAdmissible (against t iSummary)
receipts-refused-summary t iS iR hDPI h hs = h (summary-admitted-receipts t iS iR hDPI hs)

-- One decision: the gated choice errs by at most the prediction's error plus the gate's move.
gated-error-le : ∀ p g y δ → ∣ g - p ∣ ≤ δ → ∣ g - y ∣ ≤ ∣ p - y ∣ + δ
gated-error-le p g y δ hδ =
  ≤-trans (≤-reflexive (cong ∣_∣ (solve 3 (λ p g y → g :- y := (g :- p) :+ (p :- y)) refl p g y)))
    (≤-trans (∣p+q∣≤∣p∣+∣q∣ (g - p) (p - y))
      (≤-trans (+-mono-≤ hδ (≤-refl {∣ p - y ∣})) (≤-reflexive (+-comm δ ∣ p - y ∣))))

-- A gated decision: prediction, gated choice, outcome and the gate's move bound.
Decision : Set
Decision = ℚ × ℚ × ℚ × ℚ

MoveOk : Decision → Set
MoveOk (p , g , _ , δ) = ∣ g - p ∣ ≤ δ

gatedErr predErr move : Decision → ℚ
gatedErr (_ , g , y , _) = ∣ g - y ∣
predErr  (p , _ , y , _) = ∣ p - y ∣
move     (_ , _ , _ , δ) = δ

sumOver : (Decision → ℚ) → List Decision → ℚ
sumOver f = foldr (λ q acc → f q + acc) 0ℚ

-- Separation corollary, over the loop's decisions: the summed error of the gated choices is at most the summed
-- prediction error plus the summed moves.
gated-error-sum-le : ∀ l → All MoveOk l → sumOver gatedErr l ≤ sumOver predErr l + sumOver move l
gated-error-sum-le []                    []        = ≤-refl
gated-error-sum-le ((p , g , y , δ) ∷ l) (h ∷ hs) =
  ≤-trans (+-mono-≤ (gated-error-le p g y δ h) (gated-error-sum-le l hs))
    (≤-reflexive (solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
      ∣ p - y ∣ δ (sumOver predErr l) (sumOver move l)))
