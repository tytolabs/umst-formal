-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.Reconcile — BP II §5.2 both-way union-preserving.
-- Imports Chem.SecondLaw (sole physics postulate). Zero sorry.
------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

module Urge.Reconcile where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; _∨_; _∧_; not)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

record Head : Set where
  constructor mkHead
  field
    id     : ℕ
    digest : ℕ

record StateSummary : Set where
  constructor mkSummary
  field
    heads : List Head

lookupDigest : List Head → ℕ → Maybe ℕ
lookupDigest [] _ = nothing
lookupDigest (h ∷ hs) id with Head.id h ≟ id
... | yes _ = just (Head.digest h)
... | no  _ = lookupDigest hs id

hasId : List Head → ℕ → Bool
hasId hs id with lookupDigest hs id
... | just _  = true
... | nothing = false

inUnionBool : StateSummary → StateSummary → ℕ → Bool
inUnionBool left right id =
  hasId (StateSummary.heads left) id ∨ hasId (StateSummary.heads right) id

eqDigestBool : Maybe ℕ → Maybe ℕ → Bool
eqDigestBool (just dL) (just dR) = dL ≡ᵇ dR
eqDigestBool (just _)  nothing   = false
eqDigestBool nothing   (just _)  = false
eqDigestBool nothing   nothing   = true

bothPresent : Maybe ℕ → Maybe ℕ → Bool
bothPresent (just _) (just _) = true
bothPresent (just _) nothing  = false
bothPresent nothing  (just _) = false
bothPresent nothing  nothing  = false

contentConflictBool : StateSummary → StateSummary → ℕ → Bool
contentConflictBool left right id =
  let mL = lookupDigest (StateSummary.heads left) id
      mR = lookupDigest (StateSummary.heads right) id
  in bothPresent mL mR ∧ not (eqDigestBool mL mR)

reconcilePhysicsGreen : Bool
reconcilePhysicsGreen = false

reconcilePhysicsGreenFalse : reconcilePhysicsGreen ≡ false
reconcilePhysicsGreenFalse = refl

fixtureLeft : StateSummary
fixtureLeft = mkSummary (mkHead 1 10 ∷ mkHead 2 20 ∷ [])

fixtureRight : StateSummary
fixtureRight = mkSummary (mkHead 2 20 ∷ mkHead 3 30 ∷ [])

fixtureConflictL : StateSummary
fixtureConflictL = mkSummary (mkHead 1 1 ∷ [])

fixtureConflictR : StateSummary
fixtureConflictR = mkSummary (mkHead 1 9 ∷ [])

_ : inUnionBool fixtureLeft fixtureRight 1 ≡ true
_ = refl

_ : inUnionBool fixtureLeft fixtureRight 3 ≡ true
_ = refl

_ : contentConflictBool fixtureConflictL fixtureConflictR 1 ≡ true
_ = refl

_ : contentConflictBool fixtureLeft fixtureRight 2 ≡ false
_ = refl
