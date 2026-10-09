-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: SzilardEngine.agda
--
-- The Szilard engine on the one predicate, twin of SECTION 5 of Lean/Process.lean and of Coq/Process.v: the joint
-- entropy and the mutual information of the Szilard joint (Process.szilardJoint) are ln 2, and the engine that
-- extracts k_B T ln 2 at no free-energy change obeys SecondLaw (measureFeedback _) (feedback I) at equality, with I
-- the mutual information computed from the joint. The logarithm is the parameter of NaturalLog.agda.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module SzilardEngine where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _-_; -_; Positive)
open import Data.Rational.Properties using (≤-reflexive)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process
open import NaturalLog

open +-*-Solver
open NaturalLog.NaturalLog
open JointDist2

-- Joint entropy (nats) of a joint distribution on two binary variables: −Σ p ln p over the four cells
-- (twin of InfoTheory.jointEntropy).
jointEntropy : (ℚ → ℚ) → JointDist2 → ℚ
jointEntropy ln J = - (j00 J * ln (j00 J) + j01 J * ln (j01 J) + j10 J * ln (j10 J) + j11 J * ln (j11 J))

-- Mutual information (nats): H(X) + H(Y) − H(X, Y), from the marginals (twin of InfoTheory.mutualInformation).
mutualInformation : (ℚ → ℚ) → JointDist2 → ℚ
mutualInformation ln J = binaryEntropy ln (marginalX2 J) + binaryEntropy ln (marginalY2 J) - jointEntropy ln J

private
  -- The joint entropy of the Szilard joint is −ln ½ for every function ln.
  szilardJoint-entropy-half : ∀ ln → jointEntropy ln szilardJoint ≡ - ln ½
  szilardJoint-entropy-half ln =
    solve 2 (λ a z → :- (con ½ :* a :+ con 0ℚ :* z :+ con 0ℚ :* z :+ con ½ :* a) := :- a) refl (ln ½) (ln 0ℚ)

  neg-half : ∀ L → - ln L ½ ≡ ln L two
  neg-half L = trans (cong -_ (ln-half L)) (solve 1 (λ x → :- (:- x) := x) refl (ln L two))

-- The Szilard joint carries ln 2 nats.
szilardJoint-entropy : ∀ L → jointEntropy (ln L) szilardJoint ≡ ln L two
szilardJoint-entropy L = trans (szilardJoint-entropy-half (ln L)) (neg-half L)

-- Its mutual information is ln 2: one bit of correlation.
szilardJoint-mutualInformation : ∀ L → mutualInformation (ln L) szilardJoint ≡ ln L two
szilardJoint-mutualInformation L =
  trans (solve 2 (λ a z → (:- (con ½ :* a :+ con ½ :* a) :+ :- (con ½ :* a :+ con ½ :* a))
                            :- (:- (con ½ :* a :+ con 0ℚ :* z :+ con 0ℚ :* z :+ con ½ :* a)) := :- a)
               refl (ln L ½) (ln L 0ℚ))
        (neg-half L)

-- Szilard-limited feedback at a bath of positive temperature T: work k_B T ln 2 extracted, free energy unchanged.
szilardEngine : NaturalLog → (T : ℚ) → .{{Positive T}} → FeedbackProcess
szilardEngine L T = record { extWork = kB * T * ln L two ; deltaFreeEnergy = 0ℚ ; kBT = kB * T }

-- The engine obeys the second law at equality against the information of the Szilard joint.
SecondLaw-szilardEngine : ∀ L T .{{_ : Positive T}} →
  SecondLaw (measureFeedback (szilardEngine L T)) (feedback (mutualInformation (ln L) szilardJoint))
SecondLaw-szilardEngine L T =
  ≤-reflexive (trans (solve 3 (λ k t x → k :* t :* x := :- con 0ℚ :+ k :* t :* x) refl kB T (ln L two))
                     (cong (λ I → - 0ℚ + kB * T * I) (sym (szilardJoint-mutualInformation L))))
