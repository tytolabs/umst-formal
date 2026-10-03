-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeProvenancePreserve.agda
--
-- Twin of Lean/Urge/ProvenancePreserve.lean and Coq/UrgeProvenancePreserve.v. Provenance is a stamp chain, an
-- admitted DAG commit and a second-law witness slot. A move preserves provenance when the post chain extends the
-- prior chain by the prior commit, the DAG endpoints align with the move, the witness is retained and a held witness
-- is the admissibility of the move under the one second law. An admissible move from the prior commit preserves
-- provenance.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module UrgeProvenancePreserve where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import UrgeAdmitKleisli

-- Typed provenance: stamp chain, admitted DAG commit and second-law witness slot.
record Provenance : Set₁ where
  field
    ucrsChain       : List ℕ
    dagCommit       : ℕ
    landauerWitness : Set

open Provenance

-- Preservation: the post extends the stamp chain, aligns the DAG endpoints, retains the witness.
Preserves : HistoryTransition → Provenance → Provenance → Set
Preserves t prior post =
  dagCommit prior ≡ HistorySnapshot.commitId (HistoryTransition.prior t) ×
  dagCommit post ≡ HistorySnapshot.commitId (HistoryTransition.post t) ×
  ucrsChain post ≡ ucrsChain prior ++ (dagCommit prior ∷ []) ×
  (landauerWitness prior → landauerWitness post) ×
  (landauerWitness post → AdmissibleHistoryTransition t)

preserves-chain-append : ∀ t prior post → Preserves t prior post →
  ucrsChain post ≡ ucrsChain prior ++ (dagCommit prior ∷ [])
preserves-chain-append t prior post h = proj₁ (proj₂ (proj₂ h))

preserves-witness-retained : ∀ t prior post → Preserves t prior post →
  landauerWitness prior → landauerWitness post
preserves-witness-retained t prior post h = proj₁ (proj₂ (proj₂ (proj₂ h)))

-- The provenance after a move: the stamp chain extended by the prior commit, the DAG at the move's target.
postProvenance : HistoryTransition → Provenance → Provenance
postProvenance t prior = record
  { ucrsChain = ucrsChain prior ++ (dagCommit prior ∷ [])
  ; dagCommit = HistorySnapshot.commitId (HistoryTransition.post t)
  ; landauerWitness = ⊤
  }

-- An admissible move from the prior's commit preserves provenance; the second law discharges the witness.
postProvenance-preserves : ∀ t prior →
  dagCommit prior ≡ HistorySnapshot.commitId (HistoryTransition.prior t) → AdmissibleHistoryTransition t →
  Preserves t prior (postProvenance t prior)
postProvenance-preserves t prior hPrior hSL = hPrior , refl , refl , (λ _ → tt) , (λ _ → hSL)
