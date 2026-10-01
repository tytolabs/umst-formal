-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: CoarseGraining.agda
--
-- Twin of Lean/CoarseGraining.lean and Coq/CoarseGraining.v: a coarse-graining map on the process family, the
-- Esposito conditions on its erase branch (dissipated entropy preserved, coarse entropy drop at most the fine one),
-- and fine admissibility implying coarse admissibility. Entropies are carried as rationals: for the pair lump, the
-- joint entropy of a product is carried as H(X) + H(Y) with H(Y) ≥ 0.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module CoarseGraining where

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _≤_)
open import Data.Rational.Properties using (≤-trans; ≤-refl; +-mono-≤; ≤-reflexive)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Relation.Nullary using (¬_)

open import Process
open +-*-Solver

record CoarseGrainMap : Set where
  field
    mapProcess : Process → Process
    mapPrior   : Prior → Prior

open CoarseGrainMap

idCoarseGrainMap : CoarseGrainMap
idCoarseGrainMap = record { mapProcess = λ p → p ; mapPrior = λ pr → pr }

-- Composition (fine to meso to macro).
comp : CoarseGrainMap → CoarseGrainMap → CoarseGrainMap
comp g f = record { mapProcess = λ p → mapProcess g (mapProcess f p) ; mapPrior = λ pr → mapPrior g (mapPrior f pr) }

-- Esposito conditions (PRE 85, 041125) on the erase branch.
record EspositoConditions (cg : CoarseGrainMap) : Set where
  field
    erase-work-preservation : ∀ e e′ → mapProcess cg (erase e) ≡ erase e′ →
      ErasureProcess.dissipatedEntropy e′ ≡ ErasureProcess.dissipatedEntropy e
    erase-entropy-drop-lower-bound : ∀ ΔS ΔS′ → mapPrior cg (erasure ΔS) ≡ erasure ΔS′ → ΔS′ ≤ ΔS
    erase-process-image : ∀ e → ∃[ e′ ] (mapProcess cg (erase e) ≡ erase e′)
    erase-erasure-prior-image : ∀ ΔS → ∃[ ΔS′ ] (mapPrior cg (erasure ΔS) ≡ erasure ΔS′)

open EspositoConditions

-- Fine erase admissibility implies coarse erase admissibility under the Esposito conditions.
secondLaw-coarse-from-fine : ∀ cg → EspositoConditions cg → ∀ e ΔS →
  SecondLaw (erase e) (erasure ΔS) → SecondLaw (mapProcess cg (erase e)) (mapPrior cg (erasure ΔS))
secondLaw-coarse-from-fine cg h e ΔS hFine with erase-process-image h e | erase-erasure-prior-image h ΔS
... | e′ , hP | ΔS′ , hQ rewrite hP | hQ =
  ≤-trans (erase-entropy-drop-lower-bound h ΔS ΔS′ hQ)
          (subst (ΔS ≤_) (sym (erase-work-preservation h e e′ hP)) hFine)

espositoConditions-id : EspositoConditions idCoarseGrainMap
espositoConditions-id = record
  { erase-work-preservation = λ { e .e refl → refl }
  ; erase-entropy-drop-lower-bound = λ { ΔS .ΔS refl → ≤-refl }
  ; erase-process-image = λ e → e , refl
  ; erase-erasure-prior-image = λ ΔS → ΔS , refl }

-- Coarse refusal is sound: a refused coarse erasure refuses the fine one.
coarse-refusal-sound-erase : ∀ cg → EspositoConditions cg → ∀ e ΔS →
  ¬ SecondLaw (mapProcess cg (erase e)) (mapPrior cg (erasure ΔS)) → ¬ SecondLaw (erase e) (erasure ΔS)
coarse-refusal-sound-erase cg h e ΔS bad fine = bad (secondLaw-coarse-from-fine cg h e ΔS fine)

-- The pair lump: erasing the pair (joint entropy H(X) + H(Y) for a product) admits erasing its first factor.
lumpPair-secondLaw-coarse-from-fine-joint : ∀ e HX HY → 0ℚ ≤ HY →
  HX + HY ≤ ErasureProcess.dissipatedEntropy e → SecondLaw (erase e) (erasure HX)
lumpPair-secondLaw-coarse-from-fine-joint e HX HY hY hFine =
  ≤-trans (subst (_≤ HX + HY) (solve 1 (λ x → x :+ con 0ℚ := x) refl HX) (+-mono-≤ (≤-refl {HX}) hY)) hFine

-- The conditions are satisfiable.
coarse-graining-satisfiable : ∃[ cg ] EspositoConditions cg
coarse-graining-satisfiable = idCoarseGrainMap , espositoConditions-id
