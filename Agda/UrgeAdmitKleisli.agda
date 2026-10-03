-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeAdmitKleisli.agda
--
-- Twin of Lean/Urge/AdmitKleisli.lean and Coq/UrgeAdmitKleisli.v. A history move carries the gate admissibility of
-- its head move and the erasure that pays for it; the move is admissible exactly when that erasure is an instance of
-- the one predicate SecondLaw. History head moves are Kleisli arrows over thermodynamic states, whose category laws
-- hold pointwise (inherited from Chem.KleisliInteract, the twin of Compat.Constitutional).
--
-- Agda carries entropies as rationals: the erased distribution is carried by its entropy (nats), the Dirac state's
-- entropy is 0, and the erasure carries the entropy W / T its work dissipates. The Clausius bound of Lean,
-- shannonEntropy erased ≤ work / bathTemp, is then erasedEntropy ≤ dissipatedEntropy.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module UrgeAdmitKleisli where

open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _-_)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Concrete.Gate using (ThermodynamicState; Admissible)
open import Chem.KleisliInteract
  using (KleisliArrow; kleisli-compose; interact-identity; kleisli-compose-assoc; kleisli-left-unit; kleisli-right-unit)
open import Process using (ErasureProcess; SecondLaw; erase; erasure)

-- Content-addressed history snapshot: commit id and gate-checked head state.
record HistorySnapshot : Set where
  field
    commitId : ℕ
    snapHead : ThermodynamicState

open HistorySnapshot

-- A move of the history head and the erasure that pays for it: the head move passes the gate, and the erasure erases
-- the distribution of entropy erasedEntropy (the information the move discards).
record HistoryTransition : Set where
  field
    prior          : HistorySnapshot
    post           : HistorySnapshot
    gateAdmissible : Admissible (snapHead prior) (snapHead post)
    erasureProcess : ErasureProcess
    erasedEntropy  : ℚ

open HistoryTransition

-- The entropy of the Dirac state the erasure ends in.
diracEntropy : ℚ
diracEntropy = 0ℚ

-- A history move is admissible when its erasure is an instance of the one second law.
AdmissibleHistoryTransition : HistoryTransition → Set
AdmissibleHistoryTransition t = SecondLaw (erase (erasureProcess t)) (erasure (erasedEntropy t - diracEntropy))

-- Admissibility is the Clausius bound of the erasure: the erased entropy is at most the entropy the work dissipates.
admissible-history-transition-iff : ∀ t →
  AdmissibleHistoryTransition t ⇔ erasedEntropy t ≤ ErasureProcess.dissipatedEntropy (erasureProcess t)
admissible-history-transition-iff t = mk⇔
  (subst (_≤ bound) (minus-zero H))
  (subst (_≤ bound) (sym (minus-zero H)))
  where
  open +-*-Solver
  H = erasedEntropy t
  bound = ErasureProcess.dissipatedEntropy (erasureProcess t)
  minus-zero : ∀ a → a - diracEntropy ≡ a
  minus-zero = solve 1 (λ a → a :- con 0ℚ := a) refl

-- Kleisli identity on history head states.
admit-identity : KleisliArrow
admit-identity = interact-identity

-- Associativity at a state.
kleisli-compose-assoc-at : ∀ (f g h : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose (kleisli-compose f g) h s ≡ kleisli-compose f (kleisli-compose g h) s
kleisli-compose-assoc-at = kleisli-compose-assoc

-- Left unit law at a state.
kleisli-left-unit-at : ∀ (f : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose admit-identity f s ≡ f s
kleisli-left-unit-at = kleisli-left-unit

-- Right unit law at a state.
kleisli-right-unit-at : ∀ (f : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose f admit-identity s ≡ f s
kleisli-right-unit-at = kleisli-right-unit
