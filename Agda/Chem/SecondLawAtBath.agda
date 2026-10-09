-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem/SecondLawAtBath.agda
--
-- The chemical second law at a bath temperature, twin of SECTIONS 3 and 4 of Lean/Chem/SecondLaw.lean and of
-- Coq/Chem/SecondLaw.v. An update at a bath carries its positive bath temperature T and its dissipated work W; its
-- transition (Chem/SecondLaw.agda) dissipates the entropy W / T of the erasure Process.atBath T W, so every
-- statement below is a statement about chemSecondLaw, the erase instance of the one predicate.
--
-- Section 3: the Landauer work floor T · ΔS and the theorem that it is the entropy clause of the second law.
-- Section 4: a binary assemblage erasure (uniform bit to the Dirac state) realised by an erasure at the bath; the
-- erase instance of SecondLaw bounds the update's entropy drop, and the update dissipates at least T ln 2, with the
-- logarithm the parameter of NaturalLog.agda. The bridge fixes the prior and post entropies to those of the uniform
-- bit and the Dirac state; Lean and Coq fix the distributions themselves, which carry those entropies.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Chem.SecondLawAtBath where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _-_; _*_; _≤_; Positive; NonZero; _÷_; 1/_)
open import Data.Rational.Properties
  using (≤-reflexive; ≤-trans; *-cancelˡ-≤-pos; pos⇒nonZero; *-inverseʳ; *-identityʳ)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Process hiding (transition)
open import NaturalLog
open import Chem.SecondLaw

open +-*-Solver
open NaturalLog.NaturalLog

-- A thermochemical update at a bath: the entropies (nats) of its state distribution before and after, the bath
-- temperature, the work it dissipates (units of k_B times kelvin) and a structural defect scalar.
record ThermochemicalTransitionAtBath : Set where
  field
    entropyPrior     : ℚ
    entropyPost      : ℚ
    bathTemp         : ℚ
    bathTemp-pos     : Positive bathTemp
    dissipatedWork   : ℚ
    structuralDefect : ℚ

open ThermochemicalTransitionAtBath

-- The transition it is: the dissipated entropy is that of the erasure atBath T W, namely W / T.
asTransition : ThermochemicalTransitionAtBath → ThermochemicalTransition
asTransition t = record
  { entropyPrior      = entropyPrior t
  ; entropyPost       = entropyPost t
  ; dissipatedEntropy = ErasureProcess.dissipatedEntropy (atBath (bathTemp t) {{bathTemp-pos t}} (dissipatedWork t))
  ; structuralDefect  = structuralDefect t }

-- W / T at the bath of an update.
workOverTemp : ThermochemicalTransitionAtBath → ℚ
workOverTemp t = _÷_ (dissipatedWork t) (bathTemp t) {{pos⇒nonZero (bathTemp t) {{bathTemp-pos t}}}}

------------------------------------------------------------------------
-- SECTION 3: Landauer refinement floor
------------------------------------------------------------------------

-- The Landauer work floor of an entropy drop at bath temperature T.
refinementWorkFloor : (entropyDrop T : ℚ) → ℚ
refinementWorkFloor entropyDrop T = T * entropyDrop

-- The dissipated work meets the floor of the update's entropy drop.
refinementWorkAccounted : ThermochemicalTransitionAtBath → Set
refinementWorkAccounted t = refinementWorkFloor (assemblageEntropyDrop (asTransition t)) (bathTemp t) ≤ dissipatedWork t

private
  mul-÷-cancel : ∀ a .{{_ : NonZero a}} W → a * (_÷_ W a) ≡ W
  mul-÷-cancel a W = trans (solve 3 (λ a W i → a :* (W :* i) := W :* (a :* i)) refl a W (1/ a))
                           (trans (cong (W *_) (*-inverseʳ a)) (*-identityʳ W))

-- The floor is the entropy clause of the second law: at a positive bath temperature, T · ΔS ≤ W exactly when
-- ΔS ≤ W / T.
refinementWorkAccounted-iff : ∀ t → refinementWorkAccounted t ⇔ assemblageEntropyDrop (asTransition t) ≤ workOverTemp t
refinementWorkAccounted-iff t = mk⇔
  (λ h → *-cancelˡ-≤-pos T {{T-pos}}
           (≤-trans h (≤-reflexive (sym (mul-÷-cancel T {{pos⇒nonZero T {{T-pos}}}} (dissipatedWork t))))))
  (λ h → landauerBound T {{T-pos}} (dissipatedWork t) (assemblageEntropyDrop (asTransition t)) h)
  where
  T = bathTemp t
  T-pos = bathTemp-pos t

-- The refinement floor is the chemical second law: a coherent update obeys it exactly when its dissipated work meets
-- the Landauer floor of its entropy drop.
chemSecondLaw-iff-accounted : ∀ t →
  chemSecondLaw (asTransition t) ⇔ (structurallyCoherent (asTransition t) × refinementWorkAccounted t)
chemSecondLaw-iff-accounted t = mk⇔
  (λ { (c , h) → c , Equivalence.from (refinementWorkAccounted-iff t) h })
  (λ { (c , a) → c , Equivalence.to (refinementWorkAccounted-iff t) a })

------------------------------------------------------------------------
-- SECTION 4: Bridge to the erase instance
------------------------------------------------------------------------

-- The erase instance on the uniform bit: erasing it to the Dirac state removes no more entropy than the erasure
-- dissipates (twin of LandauerLaw.physicalSecondLawUniformBinary).
physicalSecondLawUniformBinary : NaturalLog → ErasureProcess → Set
physicalSecondLawUniformBinary L e =
  SecondLaw (erase e) (transformation (binaryEntropy (ln L) ½) (binaryEntropy (ln L) 1ℚ))

-- Physical realisation of a binary assemblage erasure (uniform bit to the Dirac state) by the erasure at a bath of
-- temperature procTemp dissipating work procWork.
record PhysicalChemBridge (L : NaturalLog) : Set where
  field
    procTemp     : ℚ
    procTemp-pos : Positive procTemp
    procWork     : ℚ
    transition   : ThermochemicalTransitionAtBath
    bathEq       : bathTemp transition ≡ procTemp
    workEq       : dissipatedWork transition ≡ procWork
    priorEq      : entropyPrior transition ≡ binaryEntropy (ln L) ½
    postEq       : entropyPost transition ≡ binaryEntropy (ln L) 1ℚ
    coherent     : structurallyCoherent (asTransition transition)

  proc : ErasureProcess
  proc = atBath procTemp {{procTemp-pos}} procWork

open PhysicalChemBridge

private
  transport-bound : ∀ Hp Hq A B W W′ T T′ .{{_ : Positive T}} .{{_ : Positive T′}} →
    Hp ≡ A → Hq ≡ B → W′ ≡ W → T′ ≡ T →
    A - B ≤ _÷_ W T {{pos⇒nonZero T}} → Hp - Hq ≤ _÷_ W′ T′ {{pos⇒nonZero T′}}
  transport-bound Hp Hq A B W W′ T T′ refl refl refl refl h = h

-- The erase instance bounds the bridged update's entropy drop by W / T.
chem-entropy-bound-from-physical : ∀ {L} (b : PhysicalChemBridge L) → physicalSecondLawUniformBinary L (proc b) →
  assemblageEntropyDrop (asTransition (transition b)) ≤ workOverTemp (transition b)
chem-entropy-bound-from-physical {L} b hSL =
  transport-bound (entropyPrior tr) (entropyPost tr) (binaryEntropy (ln L) ½) (binaryEntropy (ln L) 1ℚ)
    (procWork b) (dissipatedWork tr) (procTemp b) (bathTemp tr) {{procTemp-pos b}} {{bathTemp-pos tr}}
    (priorEq b) (postEq b) (workEq b) (bathEq b) hSL
  where tr = transition b

-- A bridged update dissipates at least T ln 2.
refinementLandauerBound : ∀ {L} (b : PhysicalChemBridge L) → physicalSecondLawUniformBinary L (proc b) →
  bathTemp (transition b) * ln L two ≤ dissipatedWork (transition b)
refinementLandauerBound {L} b hSL =
  ≤-trans (≤-reflexive (cong (bathTemp tr *_) (sym drop≡ln2)))
          (landauerBound (bathTemp tr) {{bathTemp-pos tr}} (dissipatedWork tr) (assemblageEntropyDrop (asTransition tr))
            (chem-entropy-bound-from-physical b hSL))
  where
  tr = transition b
  drop≡ln2 : assemblageEntropyDrop (asTransition tr) ≡ ln L two
  drop≡ln2 = trans (cong₂ _-_ (priorEq b) (postEq b)) (binaryErasureEntropyDrop L)

-- A bridged coherent update obeys the chemical second law.
chemSecondLaw-from-physical : ∀ {L} (b : PhysicalChemBridge L) → physicalSecondLawUniformBinary L (proc b) →
  chemSecondLaw (asTransition (transition b))
chemSecondLaw-from-physical b hSL = coherent b , chem-entropy-bound-from-physical b hSL
