-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: SemanticSecondLaw.agda
--
-- Twin of Lean/SemanticSecondLaw.lean and Coq/SemanticSecondLaw.v: a communicative transition obeys the one
-- predicate on its shared model (its entropy clause is the erase instance on the model's transformation), with
-- structural consistency and mutual information preserved above a threshold. Entropies are carried as rationals;
-- a proposal–outcome witness carries its marginal and joint entropies.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module SemanticSecondLaw where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _≤_)
open import Data.Rational.Properties using (≤-reflexive)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process
open +-*-Solver

-- A communicative transition: model entropies before and after, the entropy its work dissipates and a
-- consistency defect.
record CommunicativeTransition : Set where
  field
    entropyPrior      : ℚ
    entropyPost       : ℚ
    dissipatedEntropy : ℚ
    consistencyDefect : ℚ

open CommunicativeTransition

-- A proposal–outcome witness by its entropies: H(X), H(Y) and H(X, Y).
record Witness : Set where
  field
    entropyX  : ℚ
    entropyY  : ℚ
    entropyXY : ℚ

mutualInformation : Witness → ℚ
mutualInformation w = Witness.entropyX w + Witness.entropyY w - Witness.entropyXY w

structurallyConsistent : CommunicativeTransition → Set
structurallyConsistent t = consistencyDefect t ≡ 0ℚ

modelUncertaintyDrop : CommunicativeTransition → ℚ
modelUncertaintyDrop t = entropyPrior t - entropyPost t

miPreserved : ℚ → Witness → Set
miPreserved threshold w = threshold ≤ mutualInformation w

semanticSecondLaw : ℚ → CommunicativeTransition → Witness → Set
semanticSecondLaw threshold t w =
  structurallyConsistent t × modelUncertaintyDrop t ≤ dissipatedEntropy t × miPreserved threshold w

-- The semantic second law is the one predicate on the shared model, with consistency and preserved information.
semanticSecondLaw-iff : ∀ threshold t w → semanticSecondLaw threshold t w ⇔
  (structurallyConsistent t × SecondLaw (erase (record { dissipatedEntropy = dissipatedEntropy t }))
                                        (transformation (entropyPrior t) (entropyPost t)) × miPreserved threshold w)
semanticSecondLaw-iff threshold t w = mk⇔ id id

-- The erase instance discharges the entropy clause of a transition realising an erasure of drop ΔS at entropy σ.
semantic-entropy-bound-from-physical : ∀ e ΔS t → SecondLaw (erase e) (erasure ΔS) →
  modelUncertaintyDrop t ≡ ΔS → dissipatedEntropy t ≡ ErasureProcess.dissipatedEntropy e →
  modelUncertaintyDrop t ≤ dissipatedEntropy t
semantic-entropy-bound-from-physical e ΔS t h hd hw rewrite hd | hw = h

semanticSecondLaw-from-physical-bridge : ∀ threshold e ΔS t w → structurallyConsistent t → miPreserved threshold w →
  SecondLaw (erase e) (erasure ΔS) → modelUncertaintyDrop t ≡ ΔS → dissipatedEntropy t ≡ ErasureProcess.dissipatedEntropy e →
  semanticSecondLaw threshold t w
semanticSecondLaw-from-physical-bridge threshold e ΔS t w hc hm h hd hw =
  hc , semantic-entropy-bound-from-physical e ΔS t h hd hw , hm

-- The consistent identity transition of a model of entropy H, dissipating nothing.
consistentP0Transition : ℚ → CommunicativeTransition
consistentP0Transition H = record { entropyPrior = H ; entropyPost = H ; dissipatedEntropy = 0ℚ ; consistencyDefect = 0ℚ }

consistentP0-zero-uncertainty-drop : ∀ H → modelUncertaintyDrop (consistentP0Transition H) ≡ 0ℚ
consistentP0-zero-uncertainty-drop = solve 1 (λ H → H :- H := con 0ℚ) refl

consistentP0-structurallyConsistent : ∀ H → structurallyConsistent (consistentP0Transition H)
consistentP0-structurallyConsistent H = refl

-- A product witness: its joint entropy is the sum of its marginals'.
productWitness : ℚ → ℚ → Witness
productWitness HX HY = record { entropyX = HX ; entropyY = HY ; entropyXY = HX + HY }

productWitness-mi-zero : ∀ HX HY → mutualInformation (productWitness HX HY) ≡ 0ℚ
productWitness-mi-zero = solve 2 (λ x y → (x :+ y) :- (x :+ y) := con 0ℚ) refl

productWitness-miPreserved-at-zero : ∀ HX HY → miPreserved 0ℚ (productWitness HX HY)
productWitness-miPreserved-at-zero HX HY = ≤-reflexive (sym (productWitness-mi-zero HX HY))
