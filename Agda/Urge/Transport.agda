-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.Transport — BP II §5.3 channel set. Zero sorry.
------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

module Urge.Transport where

open import Chem.SecondLaw

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Transport : Set where
  local git mesh remote offline : Transport

canCarry : Transport → Bool
canCarry local   = true
canCarry git     = true
canCarry mesh    = true
canCarry remote  = true
canCarry offline = false

data TransportError : Set where
  offlineCannotCarry : TransportError

admitCarry : Transport → Maybe TransportError
admitCarry t with canCarry t
... | true  = nothing
... | false = just offlineCannotCarry

_ : canCarry local ≡ true
_ = refl

_ : canCarry offline ≡ false
_ = refl

_ : admitCarry local ≡ nothing
_ = refl

_ : admitCarry offline ≡ just offlineCannotCarry
_ = refl

channelSet : List Transport
channelSet = local ∷ git ∷ mesh ∷ remote ∷ offline ∷ []

_ : length channelSet ≡ 5
_ = refl

transportPhysicsGreen : Bool
transportPhysicsGreen = false

transportPhysicsGreenFalse : transportPhysicsGreen ≡ false
transportPhysicsGreenFalse = refl
