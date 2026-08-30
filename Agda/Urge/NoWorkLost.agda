-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.NoWorkLost — meso/acting Urge BP II §1 No-Loss pin.
--
-- URGE-II-FORMAL-NOLOSS-AGDA (umst-formal acting fiber only — NOT
-- umst-formal-double-slit knowing fiber).
--
-- Once a change is admitted on any replica, it stays reachable from the
-- system as a whole. Eight named mechanisms; honest absent flags for
-- reconcile/transport until those modules are wired.
--
-- Sole physics postulate remains Chem.SecondLaw.physicalSecondLaw
-- (imported, not re-declared). Zero new postulates. Zero sorry.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

module Urge.NoWorkLost where

open import Chem.SecondLaw

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- SECTION 1: Eight No-Loss mechanisms (BP II §1)
------------------------------------------------------------------------

data no-loss-mechanism : Set where
  nlm-provenance-on-every-change        : no-loss-mechanism
  nlm-append-only-admitted-history      : no-loss-mechanism
  nlm-content-addressing                : no-loss-mechanism
  nlm-union-preserving-reconcile        : no-loss-mechanism
  nlm-refusal-holds-never-discards      : no-loss-mechanism
  nlm-compaction-supersedes-not-deletes : no-loss-mechanism
  nlm-replica-coalgebra-typed-backup    : no-loss-mechanism
  nlm-multi-transport-redundancy        : no-loss-mechanism

eight-mechanisms : List no-loss-mechanism
eight-mechanisms =
  nlm-provenance-on-every-change ∷
  nlm-append-only-admitted-history ∷
  nlm-content-addressing ∷
  nlm-union-preserving-reconcile ∷
  nlm-refusal-holds-never-discards ∷
  nlm-compaction-supersedes-not-deletes ∷
  nlm-replica-coalgebra-typed-backup ∷
  nlm-multi-transport-redundancy ∷
  []

eight-mechanisms-length : length eight-mechanisms ≡ 8
eight-mechanisms-length = refl

mechanism-wired : no-loss-mechanism → Bool
mechanism-wired nlm-provenance-on-every-change = true
mechanism-wired nlm-append-only-admitted-history = true
mechanism-wired nlm-content-addressing = true
mechanism-wired nlm-union-preserving-reconcile = false
mechanism-wired nlm-refusal-holds-never-discards = true
mechanism-wired nlm-compaction-supersedes-not-deletes = true
mechanism-wired nlm-replica-coalgebra-typed-backup = true
mechanism-wired nlm-multi-transport-redundancy = false

reconcile-absent-honest : mechanism-wired nlm-union-preserving-reconcile ≡ false
reconcile-absent-honest = refl

transport-absent-honest : mechanism-wired nlm-multi-transport-redundancy ≡ false
transport-absent-honest = refl

------------------------------------------------------------------------
-- SECTION 2: Admitted change + replica reachability
------------------------------------------------------------------------

record AdmittedChange : Set where
  field
    change-id  : ℕ
    content-id : ℕ
    commit-id  : ℕ

record ReplicaReachability : Set where
  field
    replica-id    : ℕ
    reachable-ids : List ℕ

elemᵇ : ℕ → List ℕ → Bool
elemᵇ _ [] = false
elemᵇ x (y ∷ ys) = if x ≡ᵇ y then true else elemᵇ x ys

reachable-from-some-replica : AdmittedChange → List ReplicaReachability → Bool
reachable-from-some-replica c [] = false
reachable-from-some-replica c (r ∷ rs) =
  if elemᵇ (AdmittedChange.change-id c) (ReplicaReachability.reachable-ids r)
  then true
  else reachable-from-some-replica c rs

orphans-admitted-change : AdmittedChange → List ReplicaReachability → Bool
orphans-admitted-change c rs = not (reachable-from-some-replica c rs)

no-work-lost : AdmittedChange → List ReplicaReachability → Set
no-work-lost c rs = reachable-from-some-replica c rs ≡ true

------------------------------------------------------------------------
-- SECTION 3: Honesty flags (acting fiber — not knowing GREEN)
------------------------------------------------------------------------

no-work-lost-physics-green : Bool
no-work-lost-physics-green = false

no-work-lost-physics-green-false : no-work-lost-physics-green ≡ false
no-work-lost-physics-green-false = refl

no-work-lost-production-wired : Bool
no-work-lost-production-wired = false

no-work-lost-guard-built : Bool
no-work-lost-guard-built = false

no-new-axiom : Bool
no-new-axiom = true

-- Header documents: knowing/EpistemicMI → umst-formal-double-slit (not this module).
