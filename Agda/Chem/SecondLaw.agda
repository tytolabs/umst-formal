-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem/SecondLaw.agda
--
-- The chemical second law as an instance of the one predicate (Process.agda): a structurally coherent update of
-- an assemblage obeys the law when its erasure obeys SecondLaw on the transformation of its state distribution.
-- Twin of Lean/Chem/SecondLaw.lean and Coq/Chem/SecondLaw.v; entropies are rationals carried as data.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Chem.SecondLaw where

open import Data.Product using (_×_; _,_; proj₂)
open import Data.Rational using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Process

-- A thermochemical update: entropies of the state distribution before and after (nats), the entropy its work
-- dissipates into the bath, and a structural defect scalar.
record ThermochemicalTransition : Set where
  field
    entropyPrior      : ℚ
    entropyPost       : ℚ
    dissipatedEntropy : ℚ
    structuralDefect  : ℚ

open ThermochemicalTransition

structurallyCoherent : ThermochemicalTransition → Set
structurallyCoherent t = structuralDefect t ≡ 0ℚ

-- The erasure that pays for a transition.
erasureOf : ThermochemicalTransition → ErasureProcess
erasureOf t = record { dissipatedEntropy = dissipatedEntropy t }

chemSecondLaw : ThermochemicalTransition → Set
chemSecondLaw t = structurallyCoherent t × SecondLaw (erase (erasureOf t)) (transformation (entropyPrior t) (entropyPost t))

-- Two coherent updates, the second starting where the first ends, compose: the whole update obeys the second law
-- at the summed dissipation.
chemSecondLaw-comp : ∀ t₁ t₂ → entropyPost t₁ ≡ entropyPrior t₂ → chemSecondLaw t₁ → chemSecondLaw t₂ →
  SecondLaw (erase (erasureOf t₁ ⊕ erasureOf t₂)) (transformation (entropyPrior t₁) (entropyPost t₂))
chemSecondLaw-comp t₁ t₂ hp (_ , h₁) (_ , h₂) =
  transformation-comp (erasureOf t₁) (erasureOf t₂) (entropyPrior t₁) (entropyPost t₁) (entropyPost t₂) h₁
    (subst (λ H → SecondLaw (erase (erasureOf t₂)) (transformation H (entropyPost t₂))) (Relation.Binary.PropositionalEquality.sym hp) h₂)
