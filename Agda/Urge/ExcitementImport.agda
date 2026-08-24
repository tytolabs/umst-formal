-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ExcitementImport — meso/acting §5.2 / §22.5 excitement import.
--
-- URGE-FORMAL-MESO-AGDA-EXCITEMENT-IMPORT (umst-formal acting fiber only).
-- Urge history recovery **is** `excitement-select` over admissible history
-- successors; refuse a second argmin / f64 F compare.
--
-- Meso hook `excitement-select` mirrors `Urge.AdmitKleisli.excitement-select`
-- (§3 — no local argmin re-derivation; full `UMST.Excitement.select` lives
-- in `Lean/Excitement.lean`).
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

module Urge.ExcitementImport where

open import Chem.SecondLaw
open import Concrete.Gate using (ThermodynamicState; Admissible)
open ThermodynamicState
open Admissible

open import Data.Bool using (Bool; false)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- SECTION 1: Excitement hook (mirrors Urge.AdmitKleisli §3 — no local argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
excitement-select src [] = inj₂ exc-no-candidates
excitement-select src (c ∷ _) = inj₁ c

------------------------------------------------------------------------
-- SECTION 2: History recovery carrier (typed successor list)
------------------------------------------------------------------------

record history-recovery-ctx (src : ThermodynamicState) : Set where
  field
    recovery-successors : List (history-candidate src)

------------------------------------------------------------------------
-- SECTION 3: Recovery **is** excitement-select (no local argmin)
------------------------------------------------------------------------

urge-recovery :
  (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  history-candidate src ⊎ excitement-residue
urge-recovery src ctx =
  excitement-select src (history-recovery-ctx.recovery-successors ctx)

urge-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

urge-recovery-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  urge-recovery src ctx ≡
  excitement-select src (history-recovery-ctx.recovery-successors ctx)
urge-recovery-eq-excitement-select src ctx = refl

urge-recovery-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (successors : List (history-candidate src)) →
  urge-recovery-select src successors ≡ excitement-select src successors
urge-recovery-select-eq-excitement-select src successors = refl

urge-recovery-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  urge-recovery src ctx ≡
  urge-recovery-select src (history-recovery-ctx.recovery-successors ctx)
urge-recovery-eq-urge-recovery-select src ctx = refl

------------------------------------------------------------------------
-- SECTION 4: Imported selector properties (no local re-proof of argmin)
------------------------------------------------------------------------

urge-recovery-empty :
  ∀ (src : ThermodynamicState) →
  urge-recovery-select src [] ≡ inj₂ exc-no-candidates
urge-recovery-empty src = refl

urge-recovery-admissible :
  ∀ (src : ThermodynamicState) (successors : List (history-candidate src))
    (c : history-candidate src) →
  urge-recovery-select src successors ≡ inj₁ c →
  Admissible src (history-candidate.cand-tgt c)
urge-recovery-admissible src (h ∷ _) c eq with eq
... | refl = history-candidate.cand-admissible h

------------------------------------------------------------------------
-- SECTION 5: Axiom discipline + honesty flags
------------------------------------------------------------------------

urge-excitement-physics-green : Bool
urge-excitement-physics-green = false

urge-excitement-physics-green-false :
  urge-excitement-physics-green ≡ false
urge-excitement-physics-green-false = refl

excitement-import-production-wired : Bool
excitement-import-production-wired = false

excitement-import-production-wired-false :
  excitement-import-production-wired ≡ false
excitement-import-production-wired-false = refl

excitement-import-module-witness : ⊤
excitement-import-module-witness = tt

urge-recovery-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : history-recovery-ctx src) →
  urge-recovery src ctx ≡
  excitement-select src (history-recovery-ctx.recovery-successors ctx)
urge-recovery-no-local-argmin src ctx = refl
