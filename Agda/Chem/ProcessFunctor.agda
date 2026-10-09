-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem/ProcessFunctor.agda
--
-- Chemistry as an instance of the one predicate SecondLaw (Process.agda), twin of Lean/Chem/ProcessFunctor.lean and
-- Coq/Chem/ProcessFunctor.v. An update is sent to the erasure that pays for it, judged against the transformation of
-- its state distribution. Updates form a category (the identity update, the composite update) and the map is a
-- functor that preserves admissibility. Entropies and the dissipated entropy W / T are rationals carried as data,
-- as in Chem/SecondLaw.agda, so the Lean statement "at non-negative work" reads "at non-negative dissipated entropy"
-- here; at a positive bath temperature the two agree.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Chem.ProcessFunctor where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; -_; _≤_; Positive; _÷_)
open import Data.Rational.Properties
  using (≤-reflexive; ≤-trans; ≤-antisym; neg-antimono-≤; +-identityˡ; +-identityʳ; +-assoc; pos⇒nonZero)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔; id; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Process hiding (transition)
open import NaturalLog
open NaturalLog.NaturalLog
open import Chem.SecondLaw
open import Chem.SecondLawAtBath

open ThermochemicalTransition
open +-*-Solver

------------------------------------------------------------------------
-- SECTION 1: The image of an update in the process family
------------------------------------------------------------------------

-- The process an update is: the erasure that pays for it.
processOf : ThermochemicalTransition → Process
processOf t = erase (erasureOf t)

-- The prior an update is judged against: the transformation of its state distribution.
transformationOf : ThermochemicalTransition → Prior
transformationOf t = transformation (entropyPrior t) (entropyPost t)

chemSecondLaw-iff-process : ∀ t → chemSecondLaw t ⇔ (structurallyCoherent t × SecondLaw (processOf t) (transformationOf t))
chemSecondLaw-iff-process t = mk⇔ id id

-- The erasure and the entropy drop, typed through the erase case.
secondLaw-iff-entropyDrop : ∀ t →
  SecondLaw (erase (erasureOf t)) (transformation (entropyPrior t) (entropyPost t)) ⇔
    (assemblageEntropyDrop t ≤ dissipatedEntropy t)
secondLaw-iff-entropyDrop t = mk⇔ id id

-- The Landauer work floor, typed through the erase case: an update at a bath obeys the erase case on its
-- transformation exactly when its work meets the floor T · ΔS.
secondLaw-iff-workFloor : ∀ t →
  SecondLaw (processOf (asTransition t)) (transformationOf (asTransition t)) ⇔ refinementWorkAccounted t
secondLaw-iff-workFloor t = mk⇔ (Equivalence.from (refinementWorkAccounted-iff t)) (Equivalence.to (refinementWorkAccounted-iff t))

------------------------------------------------------------------------
-- SECTION 2: The category of updates and the functor
------------------------------------------------------------------------

-- The identity update of a distribution carrying entropy H: no change, no dissipation, no defect.
idAt : ℚ → ThermochemicalTransition
idAt H = record { entropyPrior = H ; entropyPost = H ; dissipatedEntropy = 0ℚ ; structuralDefect = 0ℚ }

-- The composite of t₁ then t₂: dissipations and defects added.
seq : ThermochemicalTransition → ThermochemicalTransition → ThermochemicalTransition
seq t₁ t₂ = record
  { entropyPrior      = entropyPrior t₁
  ; entropyPost       = entropyPost t₂
  ; dissipatedEntropy = dissipatedEntropy t₁ + dissipatedEntropy t₂
  ; structuralDefect  = structuralDefect t₁ + structuralDefect t₂ }

private
  transition-ext : ∀ {a b c d a′ b′ c′ d′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
    record { entropyPrior = a ; entropyPost = b ; dissipatedEntropy = c ; structuralDefect = d } ≡
    record { entropyPrior = a′ ; entropyPost = b′ ; dissipatedEntropy = c′ ; structuralDefect = d′ }
  transition-ext refl refl refl refl = refl

seq-idAt-left : ∀ t → seq (idAt (entropyPrior t)) t ≡ t
seq-idAt-left t = transition-ext refl refl (+-identityˡ (dissipatedEntropy t)) (+-identityˡ (structuralDefect t))

seq-idAt-right : ∀ t → seq t (idAt (entropyPost t)) ≡ t
seq-idAt-right t = transition-ext refl refl (+-identityʳ (dissipatedEntropy t)) (+-identityʳ (structuralDefect t))

seq-assoc : ∀ t₁ t₂ t₃ → seq (seq t₁ t₂) t₃ ≡ seq t₁ (seq t₂ t₃)
seq-assoc t₁ t₂ t₃ = transition-ext refl refl
  (+-assoc (dissipatedEntropy t₁) (dissipatedEntropy t₂) (dissipatedEntropy t₃))
  (+-assoc (structuralDefect t₁) (structuralDefect t₂) (structuralDefect t₃))

-- The functor sends an identity update to the identity transformation of the idle erasure.
process-idAt : ∀ H → (processOf (idAt H) ≡ erase idle) × (transformationOf (idAt H) ≡ transformation H H)
process-idAt H = refl , refl

-- The functor sends a composite update to the composite transformation of the summed erasure.
process-seq : ∀ t₁ t₂ → (processOf (seq t₁ t₂) ≡ erase (erasureOf t₁ ⊕ erasureOf t₂)) ×
  (transformationOf (seq t₁ t₂) ≡ transformation (entropyPrior t₁) (entropyPost t₂))
process-seq t₁ t₂ = refl , refl

-- Admissibility of identities.
chemSecondLaw-idAt : ∀ H → chemSecondLaw (idAt H)
chemSecondLaw-idAt H = refl , transformation-id H

-- Admissibility is closed under composition.
chemSecondLaw-seq : ∀ t₁ t₂ → entropyPost t₁ ≡ entropyPrior t₂ → chemSecondLaw t₁ → chemSecondLaw t₂ →
  chemSecondLaw (seq t₁ t₂)
chemSecondLaw-seq t₁ t₂ hp h₁ h₂ =
  trans (cong₂ _+_ (proj₁ h₁) (proj₁ h₂)) (+-identityʳ 0ℚ) , chemSecondLaw-comp t₁ t₂ hp h₁ h₂

------------------------------------------------------------------------
-- SECTION 3: The binary bridge transports the erase case
------------------------------------------------------------------------

private
  bridge-transport : ∀ Hp Hq A B W W′ T T′ .{{_ : Positive T}} .{{_ : Positive T′}} →
    Hp ≡ A → Hq ≡ B → W′ ≡ W → T′ ≡ T →
    (A - B ≤ _÷_ W T {{pos⇒nonZero T}}) ⇔ (Hp - Hq ≤ _÷_ W′ T′ {{pos⇒nonZero T′}})
  bridge-transport Hp Hq A B W W′ T T′ refl refl refl refl = mk⇔ id id

-- The bridge preserves and reflects admissibility: the erasure obeys the erase case on the uniform bit exactly when
-- the update it realises obeys SecondLaw on its transformation.
PhysicalChemBridge-secondLaw-iff : ∀ {L} (b : PhysicalChemBridge L) →
  physicalSecondLawUniformBinary L (PhysicalChemBridge.proc b) ⇔
    SecondLaw (processOf (asTransition (PhysicalChemBridge.transition b)))
              (transformationOf (asTransition (PhysicalChemBridge.transition b)))
PhysicalChemBridge-secondLaw-iff {L} b =
  bridge-transport (entropyPrior′ tr) (entropyPost′ tr) (binaryEntropy (ln L) ½) (binaryEntropy (ln L) 1ℚ)
    (PhysicalChemBridge.procWork b) (dissipatedWork tr) (PhysicalChemBridge.procTemp b) (bathTemp tr)
    {{PhysicalChemBridge.procTemp-pos b}} {{bathTemp-pos tr}}
    (PhysicalChemBridge.priorEq b) (PhysicalChemBridge.postEq b) (PhysicalChemBridge.workEq b) (PhysicalChemBridge.bathEq b)
  where
  open ThermochemicalTransitionAtBath renaming (entropyPrior to entropyPrior′; entropyPost to entropyPost′)
  tr = PhysicalChemBridge.transition b

------------------------------------------------------------------------
-- SECTION 4: Identity transformations and the P0 fixture
------------------------------------------------------------------------

private
  self-minus : ∀ a → a - a ≡ 0ℚ
  self-minus = solve 1 (λ a → a :- a := con 0ℚ) refl
  swap-minus : ∀ a b → b - a ≡ - (a - b)
  swap-minus = solve 2 (λ a b → b :- a := :- (a :- b)) refl
  neg-zero : - 0ℚ ≡ 0ℚ
  neg-zero = refl

-- An identity transformation obeys the erase case exactly at non-negative dissipation.
secondLaw-identity-iff-nonneg : ∀ e H →
  SecondLaw (erase e) (transformation H H) ⇔ (0ℚ ≤ ErasureProcess.dissipatedEntropy e)
secondLaw-identity-iff-nonneg e H = mk⇔
  (λ h → ≤-trans (≤-reflexive (sym (self-minus H))) h)
  (λ h → ≤-trans (≤-reflexive (self-minus H)) h)

-- Reversibility at zero dissipation: an update and its reverse both obey the erase case of the idle erasure exactly
-- when the update removes no entropy.
zeroWork-reversible-iff : ∀ t →
  (SecondLaw (erase idle) (transformation (entropyPrior t) (entropyPost t)) ×
   SecondLaw (erase idle) (transformation (entropyPost t) (entropyPrior t))) ⇔ (assemblageEntropyDrop t ≡ 0ℚ)
zeroWork-reversible-iff t = mk⇔ to from
  where
  a = entropyPrior t
  b = entropyPost t
  to : SecondLaw (erase idle) (transformation a b) × SecondLaw (erase idle) (transformation b a) → a - b ≡ 0ℚ
  to (h₁ , h₂) = ≤-antisym h₁ (≤-trans (≤-reflexive (sym neg-zero))
                   (≤-trans (neg-antimono-≤ (≤-trans (≤-reflexive (sym (swap-minus a b))) h₂))
                            (≤-reflexive (solve 2 (λ a b → :- (:- (a :- b)) := a :- b) refl a b))))
  from : a - b ≡ 0ℚ → SecondLaw (erase idle) (transformation a b) × SecondLaw (erase idle) (transformation b a)
  from h = ≤-reflexive h , ≤-reflexive (trans (swap-minus a b) (trans (cong -_ h) neg-zero))

-- The coherent P0 fixture is the identity update.
coherentP0-eq-idAt : ∀ H → coherentP0Transition H ≡ idAt H
coherentP0-eq-idAt H = refl

-- The P0 update obeys the erase case of an erasure exactly when the erasure dissipates non-negative entropy.
coherentP0-secondLaw-iff-nonneg : ∀ H e →
  SecondLaw (erase e) (transformation (entropyPrior (coherentP0Transition H)) (entropyPost (coherentP0Transition H)))
    ⇔ (0ℚ ≤ ErasureProcess.dissipatedEntropy e)
coherentP0-secondLaw-iff-nonneg H e = secondLaw-identity-iff-nonneg e H

-- The P0 update is reversible at zero dissipation.
coherentP0-reversible : ∀ H →
  SecondLaw (erase idle) (transformation (entropyPrior (coherentP0Transition H)) (entropyPost (coherentP0Transition H))) ×
  SecondLaw (erase idle) (transformation (entropyPost (coherentP0Transition H)) (entropyPrior (coherentP0Transition H)))
coherentP0-reversible H = Equivalence.from (zeroWork-reversible-iff (coherentP0Transition H)) (coherentP0-zero-entropy-drop H)
