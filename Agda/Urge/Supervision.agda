-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-# OPTIONS --exact-split #-}
module Urge.Supervision where

open import Chem.SecondLaw
open import Urge.Transport
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data SupervisionPhase : Set where
  observe reconcile selfHeal verify recordStep : SupervisionPhase

data SupervisionTier : Set where
  fast slow : SupervisionTier

budgetUs : SupervisionTier → ℕ
budgetUs fast = 100000
budgetUs slow = 1000000

phaseOrder : List SupervisionPhase
phaseOrder = observe ∷ reconcile ∷ selfHeal ∷ verify ∷ recordStep ∷ []

_ : length phaseOrder ≡ 5
_ = refl

localCycleAdmissible : Transport → Bool
localCycleAdmissible = canCarry

_ : localCycleAdmissible local ≡ true
_ = refl

_ : localCycleAdmissible offline ≡ false
_ = refl

supervisionPhysicsGreen : Bool
supervisionPhysicsGreen = false

_ : supervisionPhysicsGreen ≡ false
_ = refl
