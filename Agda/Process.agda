-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Process.agda
--
-- The one second law, twin of Lean/Process.lean and Coq/Process.v: a process family (erasure, measurement with
-- feedback, gate transition) and one predicate SecondLaw : Process → Prior → Set. A prior of the wrong kind for its
-- process gives ⊥.
--
-- The standard library has no real logarithm, so an erasure prior carries the entropy it removes (nats) and a
-- feedback prior the mutual information it acquired (nats), as rationals; Lean and Coq compute both from the
-- distribution. The predicates have the same shape:
--   erase            ΔS ≤ W / T   (the erasure's dissipated entropy)
--   measureFeedback  W_ext ≤ −ΔF + k_B T · I
--   transition       the gate's admissibility of the state move
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Process where

open import Data.Empty using (⊥)
open import Data.Rational using (ℚ; _≤_; _+_; _*_; -_)
open import Data.Rational.Properties using (+-mono-≤)
open import Relation.Nullary using (¬_)

open import Concrete.Gate using (ThermodynamicState; Admissible)

-- An erasure, by the entropy its work dissipates into the bath: W / T in nats.
record ErasureProcess : Set where
  field
    dissipatedEntropy : ℚ

-- A measurement with feedback: external work, free-energy change, and k_B T of its bath.
record FeedbackProcess : Set where
  field
    extWork         : ℚ
    deltaFreeEnergy : ℚ
    kBT             : ℚ

data Process : Set where
  erase           : ErasureProcess → Process
  measureFeedback : FeedbackProcess → Process
  transition      : Process

data Prior : Set where
  erasure       : (entropyDrop : ℚ) → Prior
  feedback      : (mutualInformation : ℚ) → Prior
  thermodynamic : (old new : ThermodynamicState) → Prior

-- The second law: one predicate over the process family.
SecondLaw : Process → Prior → Set
SecondLaw (erase e)           (erasure ΔS)             = ΔS ≤ ErasureProcess.dissipatedEntropy e
SecondLaw (measureFeedback f) (feedback I)             =
  FeedbackProcess.extWork f ≤ (- FeedbackProcess.deltaFreeEnergy f) + FeedbackProcess.kBT f * I
SecondLaw transition          (thermodynamic old new) = Admissible old new
SecondLaw (erase _)           (feedback _)            = ⊥
SecondLaw (erase _)           (thermodynamic _ _)     = ⊥
SecondLaw (measureFeedback _) (erasure _)             = ⊥
SecondLaw (measureFeedback _) (thermodynamic _ _)     = ⊥
SecondLaw transition          (erasure _)             = ⊥
SecondLaw transition          (feedback _)            = ⊥

-- A prior of the wrong kind is refused.
erase-feedback-refused : ∀ e I → ¬ SecondLaw (erase e) (feedback I)
erase-feedback-refused e I ()

-- Erasures in sequence: the entropy removed by both is at most the entropy both dissipate
-- (twin of Lean LandauerLaw.secondLaw_sequential_compose).
sequential : ∀ e₁ e₂ ΔS₁ ΔS₂ → SecondLaw (erase e₁) (erasure ΔS₁) → SecondLaw (erase e₂) (erasure ΔS₂) →
  ΔS₁ + ΔS₂ ≤ ErasureProcess.dissipatedEntropy e₁ + ErasureProcess.dissipatedEntropy e₂
sequential e₁ e₂ ΔS₁ ΔS₂ h₁ h₂ = +-mono-≤ h₁ h₂
