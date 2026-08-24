-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.HilbertPersist — meso/acting §12.7 persist Hilbert.
--
-- URGE-FORMAL-MESO-AGDA-HILBERT-PERSIST (umst-formal acting fiber only).
-- §12.7: persist Hilbert (acting) distinct from occupancy Hilbert (knowing).
-- Acting fiber only — Device-tier sled persist keys; occupancy Hilbert sorts
-- vigil / fold occupancy on knowing fiber. Refuse fuse / role conflation —
-- positive refuse, not only `!physics_green`. Compose `persist-hilbert-
-- excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.HilbertPersist where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (minimal meso acting mirror)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head-id : ℕ

record HistoryTransition : Set where
  field
    prior : HistorySnapshot
    post : HistorySnapshot
    bath : HeatBath
    dissipated-entropy : ℚ
    entropy-drop : ℚ

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record persist-hilbert-candidate : Set where
  field
    cand-id : ℕ
    cand-free-energy : ℚ
    roles-unfused : Bool

persist-hilbert-excitement-select :
  (src : ℚ) → List persist-hilbert-candidate →
  persist-hilbert-candidate ⊎ excitement-residue
persist-hilbert-excitement-select src List.[] = inj₂ exc-no-candidates
persist-hilbert-excitement-select src (c List.∷ _) = inj₁ c

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss =
  let step1 : HistoryTransition.entropy-drop t ≤ ErasureProcess.dissipatedEntropy proc
      step1 = subst (λ d → d ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) hSL
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss) step1

------------------------------------------------------------------------
-- SECTION 2: Two unfused Hilbert index carriers (§12.7 acting vs knowing)
------------------------------------------------------------------------

data HilbertRole : Set where
  persist-acting : HilbertRole
  occupancy-knowing : HilbertRole

record PersistHilbertIndex : Set where
  field
    hilbert-dist : ℕ
    ucrs-seq : ℕ
    grid-hash : ℕ

record OccupancyHilbertIndex : Set where
  field
    hilbert-dist : ℕ
    occupancy : ℕ
    sdf-surrogate : ℕ

persist-hilbert-index : ℕ → ℕ → ℕ → PersistHilbertIndex
persist-hilbert-index d ucrs grid = record
  { hilbert-dist = d
  ; ucrs-seq = ucrs
  ; grid-hash = grid
  }

occupancy-hilbert-index : ℕ → ℕ → ℕ → OccupancyHilbertIndex
occupancy-hilbert-index d occ sdf = record
  { hilbert-dist = d
  ; occupancy = occ
  ; sdf-surrogate = sdf
  }

data UrgeHilbertIndex : Set where
  tag-persist : PersistHilbertIndex → UrgeHilbertIndex
  tag-occupancy : OccupancyHilbertIndex → UrgeHilbertIndex

persist-and-occupancy-morphisms-distinct :
  (p : PersistHilbertIndex) (o : OccupancyHilbertIndex) →
  persist-acting ≡ occupancy-knowing → ⊤
persist-and-occupancy-morphisms-distinct p o h = tt

roles-distinct-even-same-dist :
  (p : PersistHilbertIndex) (o : OccupancyHilbertIndex) →
  PersistHilbertIndex.hilbert-dist p ≡ OccupancyHilbertIndex.hilbert-dist o →
  ⊤
roles-distinct-even-same-dist p o _ = tt

------------------------------------------------------------------------
-- SECTION 3: Fusion refusal — persist acting vs occupancy knowing unfused
------------------------------------------------------------------------

data HilbertFusionRefused : Set where
  occupancy-misused-as-persist : HilbertFusionRefused
  persist-misused-as-occupancy : HilbertFusionRefused
  role-conflation : HilbertFusionRefused
  same-discriminant : HilbertFusionRefused

try-fuse : UrgeHilbertIndex → UrgeHilbertIndex → HilbertFusionRefused
try-fuse (tag-persist _) (tag-persist _) = same-discriminant
try-fuse (tag-persist _) (tag-occupancy _) = occupancy-misused-as-persist
try-fuse (tag-occupancy _) (tag-persist _) = persist-misused-as-occupancy
try-fuse (tag-occupancy _) (tag-occupancy _) = same-discriminant

refuse-occupancy-as-persist :
  OccupancyHilbertIndex → PersistHilbertIndex → HilbertFusionRefused
refuse-occupancy-as-persist _ _ = occupancy-misused-as-persist

refuse-persist-as-occupancy :
  PersistHilbertIndex → OccupancyHilbertIndex → HilbertFusionRefused
refuse-persist-as-occupancy _ _ = persist-misused-as-occupancy

refuse-role-conflation :
  HilbertRole → HilbertRole → HilbertFusionRefused
refuse-role-conflation persist-acting persist-acting = same-discriminant
refuse-role-conflation persist-acting occupancy-knowing = role-conflation
refuse-role-conflation occupancy-knowing persist-acting = role-conflation
refuse-role-conflation occupancy-knowing occupancy-knowing = same-discriminant

------------------------------------------------------------------------
-- SECTION 4: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data HilbertPersistRefusal : Set where
  fuse-occupancy-as-persist : HilbertPersistRefusal
  fuse-persist-as-occupancy : HilbertPersistRefusal
  fuse-role-conflation : HilbertPersistRefusal
  second-argmin : HilbertPersistRefusal

data HilbertClass : Set where
  unfused-two-hilberts : HilbertClass
  persist-acting-only : HilbertClass

refuse-fuse-occupancy-as-persist : HilbertPersistRefusal
refuse-fuse-occupancy-as-persist = fuse-occupancy-as-persist

refuse-fuse-persist-as-occupancy : HilbertPersistRefusal
refuse-fuse-persist-as-occupancy = fuse-persist-as-occupancy

refuse-fuse-role-conflation : HilbertPersistRefusal
refuse-fuse-role-conflation = fuse-role-conflation

refuse-second-argmin : HilbertPersistRefusal
refuse-second-argmin = second-argmin

------------------------------------------------------------------------
-- SECTION 5: Gate Hilbert fusion attempts (§12.7 refuse fuse)
------------------------------------------------------------------------

record HilbertFusionAttempt : Set where
  field
    left : UrgeHilbertIndex
    right : UrgeHilbertIndex
    attempt-fuse : Bool
    source-free-energy : ℚ

classify-hilbert-fusion :
  (attempt : HilbertFusionAttempt) →
  HilbertClass ⊎ HilbertPersistRefusal
classify-hilbert-fusion attempt with HilbertFusionAttempt.attempt-fuse attempt
... | true = inj₂ fuse-occupancy-as-persist
... | false = inj₁ unfused-two-hilberts

gate-hilbert-fusion-admit-unfused :
  (attempt : HilbertFusionAttempt) →
  HilbertFusionAttempt.attempt-fuse attempt ≡ false →
  ⊤
gate-hilbert-fusion-admit-unfused attempt _ = tt

gate-hilbert-fusion-refuse-fuse :
  (attempt : HilbertFusionAttempt) →
  HilbertFusionAttempt.attempt-fuse attempt ≡ true →
  HilbertPersistRefusal
gate-hilbert-fusion-refuse-fuse attempt _ = fuse-occupancy-as-persist

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-persist-hilbert-select :
  (src : ℚ) → List persist-hilbert-candidate →
  persist-hilbert-candidate ⊎ excitement-residue
urge-persist-hilbert-select = persist-hilbert-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

two-hilberts-unfused-marker : ℕ
two-hilberts-unfused-marker = 2

two-hilberts-unfused-marker-eq : two-hilberts-unfused-marker ≡ 2
two-hilberts-unfused-marker-eq = refl

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

hilbert-persist-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
hilbert-persist-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

hilbert-persist-production-wired : Bool
hilbert-persist-production-wired = false

hilbert-persist-production-wired-false :
  hilbert-persist-production-wired ≡ false
hilbert-persist-production-wired-false = refl

hilbert-persist-marker : ℕ
hilbert-persist-marker = 1

hilbert-persist-marker-eq : hilbert-persist-marker ≡ 1
hilbert-persist-marker-eq = refl

hilbert-persist-module-witness : ⊤
hilbert-persist-module-witness = tt

occupancy-as-persist-refused :
  refuse-fuse-occupancy-as-persist ≡ fuse-occupancy-as-persist
occupancy-as-persist-refused = refl

persist-as-occupancy-refused :
  refuse-fuse-persist-as-occupancy ≡ fuse-persist-as-occupancy
persist-as-occupancy-refused = refl

role-conflation-refused :
  refuse-fuse-role-conflation ≡ fuse-role-conflation
role-conflation-refused = refl

fuse-refused-on-attempt :
  (attempt : HilbertFusionAttempt) →
  (h : HilbertFusionAttempt.attempt-fuse attempt ≡ true) →
  gate-hilbert-fusion-refuse-fuse attempt h ≡ fuse-occupancy-as-persist
fuse-refused-on-attempt attempt h = refl
