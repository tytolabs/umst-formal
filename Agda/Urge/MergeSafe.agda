-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.MergeSafe — meso/acting Urge history merge safety.
--
-- URGE-FORMAL-MESO-AGDA-MERGE-SAFE (umst-formal acting fiber only).
-- §4 / §12: federated history merge-safe iff matching canonical content id
-- and theorem binding; honest refuse on mismatch — no CRDT auto-merge.
--
-- Predicate mirrors Lean `Memory.Federation.mergeSafePred` (import-only pin).
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.MergeSafe where

open import Chem.SecondLaw
open import Data.Rational using (ℚ)

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≟_; 0<1+n; ≟-diag)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Decidable.Core using (Dec)

------------------------------------------------------------------------
-- SECTION 1: History memory carriers (parallel to Rust HistoryObject)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ

record HistoryMemoryEntry : Set where
  field
    history-content-id : ℕ
    history-theorem-id : ℕ

record HistoryObject : Set where
  field
    snapshot : HistorySnapshot
    theorem-id : ℕ

toMemoryEntry : HistoryObject → HistoryMemoryEntry
toMemoryEntry h = record
  { history-content-id = HistorySnapshot.commit-id (HistoryObject.snapshot h)
  ; history-theorem-id = HistoryObject.theorem-id h
  }

------------------------------------------------------------------------
-- SECTION 2: Merge-safe predicate (L-M5 / GMD-8 mirror)
------------------------------------------------------------------------

mergeSafePred : HistoryMemoryEntry → HistoryMemoryEntry → Set
mergeSafePred eₐ eᵦ =
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ ×
  HistoryMemoryEntry.history-theorem-id eₐ ≡ HistoryMemoryEntry.history-theorem-id eᵦ

mergeSafePred-intro :
  (eₐ eᵦ : HistoryMemoryEntry) →
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ →
  HistoryMemoryEntry.history-theorem-id eₐ ≡ HistoryMemoryEntry.history-theorem-id eᵦ →
  mergeSafePred eₐ eᵦ
mergeSafePred-intro eₐ eᵦ hid hth = hid , hth

MergeSafe :
  (eₐ eᵦ : HistoryMemoryEntry) (t : ℕ) →
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ →
  (HistoryMemoryEntry.history-theorem-id eₐ ≡ t × HistoryMemoryEntry.history-theorem-id eᵦ ≡ t) →
  ⊤ →
  mergeSafePred eₐ eᵦ
MergeSafe eₐ eᵦ t hid (hthₐ , hthᵦ) _ =
  mergeSafePred-intro eₐ eᵦ hid (trans hthₐ (sym hthᵦ))

historyMergeSafePred : HistoryObject → HistoryObject → Set
historyMergeSafePred hₐ hᵦ = mergeSafePred (toMemoryEntry hₐ) (toMemoryEntry hᵦ)

------------------------------------------------------------------------
-- SECTION 3: Honest refuse verdicts (no CRDT auto-merge)
------------------------------------------------------------------------

data mergeSafeVerdict : Set where
  merge-safe-admit : mergeSafeVerdict
  merge-safe-refuse-mismatch : mergeSafeVerdict

merge-safe-core :
  {m n k l : ℕ} → Dec (m ≡ n) → Dec (k ≡ l) → mergeSafeVerdict
merge-safe-core cidDec thmDec =
  if does cidDec then
    if does thmDec then merge-safe-admit else merge-safe-refuse-mismatch
  else merge-safe-refuse-mismatch

merge-safe : HistoryMemoryEntry → HistoryMemoryEntry → mergeSafeVerdict
merge-safe left right =
  merge-safe-core
    (ℕ-Props._≟_ (HistoryMemoryEntry.history-content-id left)
                (HistoryMemoryEntry.history-content-id right))
    (ℕ-Props._≟_ (HistoryMemoryEntry.history-theorem-id left)
                (HistoryMemoryEntry.history-theorem-id right))

merge-safe-pred→admit :
  (left right : HistoryMemoryEntry) →
  mergeSafePred left right →
  merge-safe left right ≡ merge-safe-admit
merge-safe-pred→admit left right (hid , hth)
  rewrite
    cong
      (λ cidDec → merge-safe-core cidDec
        (ℕ-Props._≟_ (HistoryMemoryEntry.history-theorem-id left)
                    (HistoryMemoryEntry.history-theorem-id right)))
      (≟-diag hid)
  rewrite cong (merge-safe-core (yes hid)) (≟-diag hth)
  = refl

------------------------------------------------------------------------
-- SECTION 4: CRDT auto-merge positive refuse
------------------------------------------------------------------------

data crdt-auto-merge-refused : Set where
  crdt-auto-merge-refused-tag : crdt-auto-merge-refused

refuse-crdt-auto-merge : crdt-auto-merge-refused
refuse-crdt-auto-merge = crdt-auto-merge-refused-tag

refuse-crdt-auto-merge-is-tag :
  refuse-crdt-auto-merge ≡ crdt-auto-merge-refused-tag
refuse-crdt-auto-merge-is-tag = refl

------------------------------------------------------------------------
-- SECTION 5: Landauer anchor + honesty flags (zero new postulates)
------------------------------------------------------------------------

memory-merge-safe-lean-pin : ℕ
memory-merge-safe-lean-pin = 0

memory-merge-safe-lean-pin-marker :
  memory-merge-safe-lean-pin ≡ 0
memory-merge-safe-lean-pin-marker = refl

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

merge-safe-production-wired : Bool
merge-safe-production-wired = false

merge-safe-production-wired-false :
  merge-safe-production-wired ≡ false
merge-safe-production-wired-false = refl

merge-safe-history-marker : ℕ
merge-safe-history-marker = 1

merge-safe-history-marker-pos : 0 < merge-safe-history-marker
merge-safe-history-marker-pos = 0<1+n

merge-safe-module-witness : ⊤
merge-safe-module-witness = tt

historyMergeSafePred-eq-imported :
  (hₐ hᵦ : HistoryObject) →
  historyMergeSafePred hₐ hᵦ ≡ mergeSafePred (toMemoryEntry hₐ) (toMemoryEntry hᵦ)
historyMergeSafePred-eq-imported hₐ hᵦ = refl

landauer-anchor-cited :
  ∀ (proc : ErasureProcess) (ΔS : ℚ) → PhysicalSecondLaw proc ΔS → ⊤
landauer-anchor-cited _ _ _ = tt
