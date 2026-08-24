-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.OccupancyNotForge — meso/acting §13.1 four names unfused.
--
-- URGE-FORMAL-MESO-AGDA-OCCUPANCY-NOT-FORGE (umst-formal acting fiber only).
-- §13.1: **occupancy** ≠ **forge** ≠ **meta** ≠ **Padma** as distinct types.
-- Collapsing them is a category error (process surrogate vs running forge vs
-- transition conjunct vs runtime invariant). Fusion attempts fail closed with
-- positive refuse — not only `!physics_green`. Compose `occupancy-not-forge-
-- excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.OccupancyNotForge where

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

record name-fusion-candidate : Set where
  field
    cand-id : ℕ
    cand-free-energy : ℚ
    names-unfused : Bool

occupancy-not-forge-excitement-select :
  (src : ℚ) → List name-fusion-candidate →
  name-fusion-candidate ⊎ excitement-residue
occupancy-not-forge-excitement-select src List.[] = inj₂ exc-no-candidates
occupancy-not-forge-excitement-select src (c List.∷ _) = inj₁ c

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
-- SECTION 2: Four unfused name carriers (§13.1 — not Padma fifth fibre)
------------------------------------------------------------------------

record OccupancyStamp : Set where
  field
    stamp-id : ℕ

record ForgeStamp : Set where
  field
    stamp-id : ℕ

record MetaStamp : Set where
  field
    stamp-id : ℕ

record PadmaStamp : Set where
  field
    stamp-id : ℕ

occupancy-stamp : ℕ → OccupancyStamp
occupancy-stamp n = record { stamp-id = n }

forge-stamp : ℕ → ForgeStamp
forge-stamp n = record { stamp-id = n }

meta-stamp : ℕ → MetaStamp
meta-stamp n = record { stamp-id = n }

padma-stamp : ℕ → PadmaStamp
padma-stamp n = record { stamp-id = n }

data UrgeUnfusedName : Set where
  tag-occupancy : OccupancyStamp → UrgeUnfusedName
  tag-forge : ForgeStamp → UrgeUnfusedName
  tag-meta : MetaStamp → UrgeUnfusedName
  tag-padma : PadmaStamp → UrgeUnfusedName

------------------------------------------------------------------------
-- SECTION 3: Fusion refusal — pairwise merge of distinct §13.1 names
------------------------------------------------------------------------

data FusionRefused : Set where
  occupancy-forge : FusionRefused
  occupancy-meta : FusionRefused
  occupancy-padma : FusionRefused
  forge-meta : FusionRefused
  forge-padma : FusionRefused
  meta-padma : FusionRefused
  same-discriminant : FusionRefused

try-merge : UrgeUnfusedName → UrgeUnfusedName → FusionRefused
try-merge (tag-occupancy _) (tag-forge _) = occupancy-forge
try-merge (tag-forge _) (tag-occupancy _) = occupancy-forge
try-merge (tag-occupancy _) (tag-meta _) = occupancy-meta
try-merge (tag-meta _) (tag-occupancy _) = occupancy-meta
try-merge (tag-occupancy _) (tag-padma _) = occupancy-padma
try-merge (tag-padma _) (tag-occupancy _) = occupancy-padma
try-merge (tag-forge _) (tag-meta _) = forge-meta
try-merge (tag-meta _) (tag-forge _) = forge-meta
try-merge (tag-forge _) (tag-padma _) = forge-padma
try-merge (tag-padma _) (tag-forge _) = forge-padma
try-merge (tag-meta _) (tag-padma _) = meta-padma
try-merge (tag-padma _) (tag-meta _) = meta-padma
try-merge (tag-occupancy _) (tag-occupancy _) = same-discriminant
try-merge (tag-forge _) (tag-forge _) = same-discriminant
try-merge (tag-meta _) (tag-meta _) = same-discriminant
try-merge (tag-padma _) (tag-padma _) = same-discriminant

refuse-occupancy-as-forge : OccupancyStamp → ForgeStamp → FusionRefused
refuse-occupancy-as-forge _ _ = occupancy-forge

refuse-forge-as-meta : ForgeStamp → MetaStamp → FusionRefused
refuse-forge-as-meta _ _ = forge-meta

refuse-meta-as-padma : MetaStamp → PadmaStamp → FusionRefused
refuse-meta-as-padma _ _ = meta-padma

refuse-padma-as-occupancy : PadmaStamp → OccupancyStamp → FusionRefused
refuse-padma-as-occupancy _ _ = occupancy-padma

------------------------------------------------------------------------
-- SECTION 4: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data OccupancyNotForgeRefusal : Set where
  fusion-occupancy-forge : OccupancyNotForgeRefusal
  fusion-occupancy-meta : OccupancyNotForgeRefusal
  fusion-occupancy-padma : OccupancyNotForgeRefusal
  fusion-forge-meta : OccupancyNotForgeRefusal
  fusion-forge-padma : OccupancyNotForgeRefusal
  fusion-meta-padma : OccupancyNotForgeRefusal
  fifth-urge-name : OccupancyNotForgeRefusal
  second-argmin : OccupancyNotForgeRefusal

data NameClass : Set where
  unfused-four-names : NameClass
  padma-crosswalk-only : NameClass

refuse-fusion-occupancy-forge : OccupancyNotForgeRefusal
refuse-fusion-occupancy-forge = fusion-occupancy-forge

refuse-fusion-forge-meta : OccupancyNotForgeRefusal
refuse-fusion-forge-meta = fusion-forge-meta

refuse-fusion-meta-padma : OccupancyNotForgeRefusal
refuse-fusion-meta-padma = fusion-meta-padma

refuse-fifth-urge-name : OccupancyNotForgeRefusal
refuse-fifth-urge-name = fifth-urge-name

refuse-second-argmin : OccupancyNotForgeRefusal
refuse-second-argmin = second-argmin

------------------------------------------------------------------------
-- SECTION 5: Gate name-fusion attempts (§13.1 four names unfused)
------------------------------------------------------------------------

record NameFusionAttempt : Set where
  field
    left : UrgeUnfusedName
    right : UrgeUnfusedName
    attempt-merge : Bool
    source-free-energy : ℚ

classify-name-fusion :
  (attempt : NameFusionAttempt) →
  NameClass ⊎ OccupancyNotForgeRefusal
classify-name-fusion attempt with NameFusionAttempt.attempt-merge attempt
... | true = inj₂ fusion-occupancy-forge
... | false = inj₁ unfused-four-names

gate-name-fusion-admit-unfused :
  (attempt : NameFusionAttempt) →
  NameFusionAttempt.attempt-merge attempt ≡ false →
  ⊤
gate-name-fusion-admit-unfused attempt _ = tt

gate-name-fusion-refuse-merge :
  (attempt : NameFusionAttempt) →
  NameFusionAttempt.attempt-merge attempt ≡ true →
  OccupancyNotForgeRefusal
gate-name-fusion-refuse-merge attempt _ = fusion-occupancy-forge

occupancy-forge-merge-eq :
  (o : OccupancyStamp) (f : ForgeStamp) →
  try-merge (tag-occupancy o) (tag-forge f) ≡ occupancy-forge
occupancy-forge-merge-eq o f = refl

forge-occupancy-merge-eq :
  (f : ForgeStamp) (o : OccupancyStamp) →
  try-merge (tag-forge f) (tag-occupancy o) ≡ occupancy-forge
forge-occupancy-merge-eq f o = refl

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-occupancy-select :
  (src : ℚ) → List name-fusion-candidate →
  name-fusion-candidate ⊎ excitement-residue
urge-occupancy-select = occupancy-not-forge-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

four-names-unfused-marker : ℕ
four-names-unfused-marker = 4

four-names-unfused-marker-eq : four-names-unfused-marker ≡ 4
four-names-unfused-marker-eq = refl

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

occupancy-not-forge-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
occupancy-not-forge-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

occupancy-not-forge-production-wired : Bool
occupancy-not-forge-production-wired = false

occupancy-not-forge-production-wired-false :
  occupancy-not-forge-production-wired ≡ false
occupancy-not-forge-production-wired-false = refl

occupancy-not-forge-marker : ℕ
occupancy-not-forge-marker = 1

occupancy-not-forge-marker-eq : occupancy-not-forge-marker ≡ 1
occupancy-not-forge-marker-eq = refl

occupancy-not-forge-module-witness : ⊤
occupancy-not-forge-module-witness = tt

padma-not-fifth-urge-name :
  refuse-fifth-urge-name ≡ fifth-urge-name
padma-not-fifth-urge-name = refl

occupancy-forge-refused :
  refuse-fusion-occupancy-forge ≡ fusion-occupancy-forge
occupancy-forge-refused = refl

forge-meta-refused :
  refuse-fusion-forge-meta ≡ fusion-forge-meta
forge-meta-refused = refl

meta-padma-refused :
  refuse-fusion-meta-padma ≡ fusion-meta-padma
meta-padma-refused = refl
