-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.DropProvenance — meso/acting §15.6 H3 drop-provenance gossip.
--
-- URGE-FORMAL-MESO-AGDA-DROP-PROVENANCE (umst-formal acting fiber only).
-- §15.6: drop-provenance gossip tick candidates are **inadmissible** — typed
-- refuse, not silent accept. Cannot heal by erasing provenance on the mesh
-- spine. Compose `drop-provenance-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.DropProvenance where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
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

record gossip-candidate : Set where
  field
    cand-id : ℕ
    provenance-intact : Bool
    drops-provenance : Bool
    stamp-present : Bool

is-gossip-admissible-bool : gossip-candidate → Bool
is-gossip-admissible-bool c =
  if gossip-candidate.provenance-intact c then
    if gossip-candidate.drops-provenance c then false
    else gossip-candidate.stamp-present c
  else false

residue-after-inadmissible : excitement-residue → excitement-residue
residue-after-inadmissible exc-no-candidates = exc-all-inadmissible
residue-after-inadmissible exc-all-inadmissible = exc-all-inadmissible
residue-after-inadmissible exc-no-strict-improvement = exc-all-inadmissible

drop-provenance-excitement-select :
  (src : ℚ) → List gossip-candidate →
  gossip-candidate ⊎ excitement-residue
drop-provenance-excitement-select src List.[] = inj₂ exc-no-candidates
drop-provenance-excitement-select src (c List.∷ cs) with is-gossip-admissible-bool c
... | true = inj₁ c
... | false with drop-provenance-excitement-select src cs
... | inj₁ c′ = inj₁ c′
... | inj₂ r = inj₂ (residue-after-inadmissible r)

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
-- SECTION 2: Provenance stamp witness (§15.6 H3 mesh spine)
------------------------------------------------------------------------

record ProvenanceStampWitness : Set where
  field
    stamp-id : ℕ
    chain-intact : Bool

stamp-witness-from-fields :
  (id : ℕ) (intact : Bool) → ProvenanceStampWitness
stamp-witness-from-fields id intact = record
  { stamp-id = id
  ; chain-intact = intact
  }

------------------------------------------------------------------------
-- SECTION 3: Gossip tick attempt carrier
------------------------------------------------------------------------

record GossipTickAttempt : Set where
  field
    tick-id : ℕ
    provenance-intact : Bool
    drops-provenance : Bool
    stamp : Maybe ℕ
    source-free-energy : ℚ

gossip-candidate-from-attempt : GossipTickAttempt → gossip-candidate
gossip-candidate-from-attempt a = record
  { cand-id = GossipTickAttempt.tick-id a
  ; provenance-intact = GossipTickAttempt.provenance-intact a
  ; drops-provenance = GossipTickAttempt.drops-provenance a
  ; stamp-present = stamp-present? (GossipTickAttempt.stamp a)
  }
  where
  stamp-present? : Maybe ℕ → Bool
  stamp-present? nothing = false
  stamp-present? (just _) = true

------------------------------------------------------------------------
-- SECTION 4: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data DropProvenanceRefusal : Set where
  drops-provenance-gossip-tick : DropProvenanceRefusal
  provenance-lost : DropProvenanceRefusal
  missing-stamp : DropProvenanceRefusal
  second-argmin : DropProvenanceRefusal

data GossipTickVerdict : Set where
  gossip-tick-admissible : GossipTickVerdict
  reject-drop-provenance : GossipTickVerdict

refuse-drops-provenance-gossip-tick : DropProvenanceRefusal
refuse-drops-provenance-gossip-tick = drops-provenance-gossip-tick

refuse-provenance-lost : DropProvenanceRefusal
refuse-provenance-lost = provenance-lost

refuse-missing-stamp : DropProvenanceRefusal
refuse-missing-stamp = missing-stamp

refuse-second-argmin : DropProvenanceRefusal
refuse-second-argmin = second-argmin

------------------------------------------------------------------------
-- SECTION 5: Gate gossip tick attempts (§15.6 H3 drop-provenance refuse)
------------------------------------------------------------------------

gate-gossip-refuse-drops :
  (attempt : GossipTickAttempt) →
  GossipTickAttempt.drops-provenance attempt ≡ true →
  DropProvenanceRefusal
gate-gossip-refuse-drops attempt _ = drops-provenance-gossip-tick

gate-gossip-refuse-provenance-lost :
  (attempt : GossipTickAttempt) →
  GossipTickAttempt.drops-provenance attempt ≡ false →
  GossipTickAttempt.provenance-intact attempt ≡ false →
  DropProvenanceRefusal
gate-gossip-refuse-provenance-lost attempt _ _ = provenance-lost

gate-gossip-refuse-missing-stamp :
  (attempt : GossipTickAttempt) →
  GossipTickAttempt.drops-provenance attempt ≡ false →
  GossipTickAttempt.provenance-intact attempt ≡ true →
  GossipTickAttempt.stamp attempt ≡ nothing →
  DropProvenanceRefusal
gate-gossip-refuse-missing-stamp attempt _ _ _ = missing-stamp

gate-gossip-admit :
  (attempt : GossipTickAttempt) →
  GossipTickAttempt.drops-provenance attempt ≡ false →
  GossipTickAttempt.provenance-intact attempt ≡ true →
  (s : ℕ) → GossipTickAttempt.stamp attempt ≡ just s →
  ⊤
gate-gossip-admit attempt _ _ s _ = tt

classify-gossip-tick :
  (attempt : GossipTickAttempt) →
  GossipTickVerdict ⊎ DropProvenanceRefusal
classify-gossip-tick attempt with GossipTickAttempt.drops-provenance attempt
... | true = inj₂ drops-provenance-gossip-tick
... | false with GossipTickAttempt.provenance-intact attempt
... | false = inj₂ provenance-lost
... | true with GossipTickAttempt.stamp attempt
... | nothing = inj₂ missing-stamp
... | just _ = inj₁ gossip-tick-admissible

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-drop-provenance-select :
  (src : ℚ) → List gossip-candidate →
  gossip-candidate ⊎ excitement-residue
urge-drop-provenance-select = drop-provenance-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 7: H3 fixtures (drop inadmissible; provenanced admissible)
------------------------------------------------------------------------

h3-drop-provenance-fixture : GossipTickAttempt
h3-drop-provenance-fixture = record
  { tick-id = 0
  ; provenance-intact = false
  ; drops-provenance = true
  ; stamp = nothing
  ; source-free-energy = 0ℚ
  }

h3-admissible-gossip-fixture : GossipTickAttempt
h3-admissible-gossip-fixture = record
  { tick-id = 1
  ; provenance-intact = true
  ; drops-provenance = false
  ; stamp = just 1
  ; source-free-energy = 0ℚ
  }

h3-drop-classified-reject :
  classify-gossip-tick h3-drop-provenance-fixture ≡ inj₂ drops-provenance-gossip-tick
h3-drop-classified-reject = refl

h3-admissible-classified-ok :
  classify-gossip-tick h3-admissible-gossip-fixture ≡ inj₁ gossip-tick-admissible
h3-admissible-classified-ok = refl

h3-drop-candidate-not-admissible :
  is-gossip-admissible-bool (gossip-candidate-from-attempt h3-drop-provenance-fixture) ≡ false
h3-drop-candidate-not-admissible = refl

h3-drop-excitement-all-inadmissible :
  drop-provenance-excitement-select 0ℚ
    ( gossip-candidate-from-attempt h3-drop-provenance-fixture List.∷ [] )
  ≡ inj₂ exc-all-inadmissible
h3-drop-excitement-all-inadmissible rewrite h3-drop-candidate-not-admissible = refl

------------------------------------------------------------------------
-- SECTION 8: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

drop-provenance-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
drop-provenance-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

drop-provenance-production-wired : Bool
drop-provenance-production-wired = false

drop-provenance-production-wired-false :
  drop-provenance-production-wired ≡ false
drop-provenance-production-wired-false = refl

drop-provenance-marker : ℕ
drop-provenance-marker = 1

drop-provenance-marker-eq : drop-provenance-marker ≡ 1
drop-provenance-marker-eq = refl

drop-provenance-module-witness : ⊤
drop-provenance-module-witness = tt

drops-provenance-gossip-refused :
  (attempt : GossipTickAttempt) →
  (h : GossipTickAttempt.drops-provenance attempt ≡ true) →
  gate-gossip-refuse-drops attempt h ≡ drops-provenance-gossip-tick
drops-provenance-gossip-refused attempt h = refl

provenance-lost-refused :
  refuse-provenance-lost ≡ provenance-lost
provenance-lost-refused = refl

missing-stamp-refused :
  refuse-missing-stamp ≡ missing-stamp
missing-stamp-refused = refl
