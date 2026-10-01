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
--   transition       mass within δ-mass and free energy not rising (the universal core; cement constraints compose
--                    over it in Concrete/SecondLaw.agda)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Process where

open import Data.Empty using (⊥)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _+_; _*_; _-_; -_)
open import Data.Rational.Properties using (+-mono-≤; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Core.Gate using (CoreAdmissible)
open import Concrete.Gate using (ThermodynamicState; Admissible; admissible-refl; concrete-thermodynamic-system)

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
  -- a transformation of a distribution, by the entropies (nats) before and after
  transformation : (entropyPrior entropyPost : ℚ) → Prior

-- The second law: one predicate over the process family.
SecondLaw : Process → Prior → Set
SecondLaw (erase e)           (erasure ΔS)             = ΔS ≤ ErasureProcess.dissipatedEntropy e
SecondLaw (measureFeedback f) (feedback I)             =
  FeedbackProcess.extWork f ≤ (- FeedbackProcess.deltaFreeEnergy f) + FeedbackProcess.kBT f * I
SecondLaw transition          (thermodynamic old new) = CoreAdmissible concrete-thermodynamic-system old new
SecondLaw (erase e)           (transformation Hp Hq)  = Hp - Hq ≤ ErasureProcess.dissipatedEntropy e
SecondLaw (measureFeedback _) (transformation _ _)    = ⊥
SecondLaw transition          (transformation _ _)    = ⊥
SecondLaw (erase _)           (feedback _)            = ⊥
SecondLaw (erase _)           (thermodynamic _ _)     = ⊥
SecondLaw (measureFeedback _) (erasure _)             = ⊥
SecondLaw (measureFeedback _) (thermodynamic _ _)     = ⊥
SecondLaw transition          (erasure _)             = ⊥
SecondLaw transition          (feedback _)            = ⊥

-- A prior of the wrong kind is refused.
erase-feedback-refused : ∀ e I → ¬ SecondLaw (erase e) (feedback I)
erase-feedback-refused e I ()

-- Binary erasure is the transformation whose target has zero entropy (the Dirac state).
erasure-is-transformation : ∀ e ΔS → SecondLaw (erase e) (erasure ΔS) → SecondLaw (erase e) (transformation ΔS 0ℚ)
erasure-is-transformation e ΔS h = ≤-trans (≤-reflexive (minus-zero ΔS)) h
  where
  open +-*-Solver
  minus-zero : ∀ a → a - 0ℚ ≡ a
  minus-zero = solve 1 (λ a → a :- con 0ℚ := a) refl

private
  open +-*-Solver
  self-minus : ∀ a → a - a ≡ 0ℚ
  self-minus = solve 1 (λ a → a :- a := con 0ℚ) refl
  telescope : ∀ a b c → a - c ≡ (a - b) + (b - c)
  telescope = solve 3 (λ a b c → a :- c := (a :- b) :+ (b :- c)) refl

-- An erasure that dissipates no entropy.
idle : ErasureProcess
idle = record { dissipatedEntropy = 0ℚ }

-- Leaving a distribution unchanged costs nothing.
transformation-id : ∀ H → SecondLaw (erase idle) (transformation H H)
transformation-id H = ≤-reflexive (self-minus H)

-- The erasure dissipating both erasures' entropy.
_⊕_ : ErasureProcess → ErasureProcess → ErasureProcess
e₁ ⊕ e₂ = record { dissipatedEntropy = ErasureProcess.dissipatedEntropy e₁ + ErasureProcess.dissipatedEntropy e₂ }

-- Composition: transformations p → q and q → r that obey the second law compose into p → r, whose cost is the
-- sum (entropy drops telescope).
transformation-comp : ∀ e₁ e₂ Hp Hq Hr → SecondLaw (erase e₁) (transformation Hp Hq) →
  SecondLaw (erase e₂) (transformation Hq Hr) → SecondLaw (erase (e₁ ⊕ e₂)) (transformation Hp Hr)
transformation-comp e₁ e₂ Hp Hq Hr h₁ h₂ = ≤-trans (≤-reflexive (telescope Hp Hq Hr)) (+-mono-≤ h₁ h₂)

-- A state move that changes nothing is admissible.
transition-refl : ∀ s → SecondLaw transition (thermodynamic s s)
transition-refl s = record { mass-conserved = Admissible.mass-conserved (admissible-refl s)
                           ; dissipation-nonneg = Admissible.dissipation-nonneg (admissible-refl s) }

-- The predicate is satisfiable: an erasure that removes no entropy and dissipates none obeys it.
satisfiable : SecondLaw (erase idle) (erasure 0ℚ)
satisfiable = ≤-refl

-- Independent erasures: the entropy both remove is at most the entropy both dissipate.
erasure-additive : ∀ e₁ e₂ ΔS₁ ΔS₂ → SecondLaw (erase e₁) (erasure ΔS₁) → SecondLaw (erase e₂) (erasure ΔS₂) →
  ΔS₁ + ΔS₂ ≤ ErasureProcess.dissipatedEntropy e₁ + ErasureProcess.dissipatedEntropy e₂
erasure-additive e₁ e₂ ΔS₁ ΔS₂ h₁ h₂ = +-mono-≤ h₁ h₂

------------------------------------------------------------------------
-- Witness: the Szilard joint (one bit of correlation). Its entropy and mutual information are ln 2, which is not
-- rational; the joint and its uniform marginals are.
------------------------------------------------------------------------

open import Data.Rational using (½; 1ℚ; _≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

-- A joint distribution on two binary variables, by the masses of (0,0), (0,1), (1,0), (1,1).
record JointDist2 : Set where
  field
    j00 j01 j10 j11 : ℚ
    j00-nonneg : 0ℚ ≤ j00
    j01-nonneg : 0ℚ ≤ j01
    j10-nonneg : 0ℚ ≤ j10
    j11-nonneg : 0ℚ ≤ j11
    j-sum      : j00 + j01 + j10 + j11 ≡ 1ℚ

open JointDist2

-- Marginals, by the probability of the first state.
marginalX2 marginalY2 : JointDist2 → ℚ
marginalX2 J = j00 J + j01 J
marginalY2 J = j00 J + j10 J

szilardJoint : JointDist2
szilardJoint = record
  { j00 = ½ ; j01 = 0ℚ ; j10 = 0ℚ ; j11 = ½
  ; j00-nonneg = toWitness {a? = 0ℚ ≤? ½} _ ; j01-nonneg = ≤-refl ; j10-nonneg = ≤-refl
  ; j11-nonneg = toWitness {a? = 0ℚ ≤? ½} _ ; j-sum = refl }

szilardJoint-marginalX : marginalX2 szilardJoint ≡ ½
szilardJoint-marginalX = refl

szilardJoint-marginalY : marginalY2 szilardJoint ≡ ½
szilardJoint-marginalY = refl

------------------------------------------------------------------------
-- SI Clausius form: an entropy drop dS (nats) with work W in joules at a positive temperature T obeys
-- dS ≤ W / (k_B T), with the exact k_B of Constants/SI.agda.
------------------------------------------------------------------------

open import Data.Rational using (Positive; fromℚᵘ; _÷_)
open import Data.Rational.Properties using (pos*pos⇒pos; pos⇒nonZero)
import Constants.SI as SI

kB : ℚ
kB = fromℚᵘ SI.boltzmann

instance
  kB-pos : Positive kB
  kB-pos = _

eraseSecondLawSI : (T : ℚ) → .{{Positive T}} → (dS W : ℚ) → Set
eraseSecondLawSI T dS W = dS ≤ _÷_ W (kB * T) {{pos⇒nonZero (kB * T) {{pos*pos⇒pos kB T}}}}

-- Units bridge: the erase instance carries the dissipated entropy σ = W / T (natural units); in joules the work is
-- k_B T σ, and the instance is exactly the SI Clausius form at that work. One law, two unit systems.
open import Data.Rational using (NonZero; 1/_)
open import Data.Rational.Properties using (*-inverseʳ; *-identityʳ)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (trans; cong)

private
  ÷-cancel : ∀ a .{{_ : NonZero a}} σ → _÷_ (a * σ) a ≡ σ
  ÷-cancel a σ = trans (solve 3 (λ a σ i → (a :* σ) :* i := σ :* (a :* i)) refl a σ (1/ a))
                       (trans (cong (σ *_) (*-inverseʳ a)) (*-identityʳ σ))

transformation-iff-SI : ∀ T .{{_ : Positive T}} σ Hp Hq →
  SecondLaw (erase (record { dissipatedEntropy = σ })) (transformation Hp Hq) ⇔ eraseSecondLawSI T (Hp - Hq) (kB * T * σ)
transformation-iff-SI T σ Hp Hq = mk⇔
  (λ h → subst (Hp - Hq ≤_) (sym (÷-cancel (kB * T) {{nz}} σ)) h)
  (λ h → subst (Hp - Hq ≤_) (÷-cancel (kB * T) {{nz}} σ) h)
  where nz = pos⇒nonZero (kB * T) {{pos*pos⇒pos kB T}}
