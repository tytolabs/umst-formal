-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.GossipTick — meso/acting §15.6 H3 gossip tick.
--
-- URGE-FORMAL-MESO-AGDA-GOSSIP-TICK (umst-formal acting fiber only).
-- §15.6: gossip tick as typed `Unmeasured | Measured` wrapper — UNKNOWN
-- ≠ false-as-GREEN. Positive refuse, not silent accept. Compose
-- `gossip-tick-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.GossipTick where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head carriers (no K-infective import)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    density free-energy hydration strength : ℚ

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    admissible-witness : ⊤

admissible-any : ∀ {old new : ThermodynamicState} → Admissible old new
admissible-any = mkAdmissible tt

open ThermodynamicState

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
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

urge-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers + Landauer bridge
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
-- SECTION 2: §15.6 H3 gossip tick measurement + morphism carriers
------------------------------------------------------------------------

data GossipTickMeasure : Set where
  gtm-unmeasured : GossipTickMeasure
  gtm-measured : Bool → String → GossipTickMeasure

gossip-tick-is-measured : GossipTickMeasure → Bool
gossip-tick-is-measured gtm-unmeasured = false
gossip-tick-is-measured (gtm-measured _ _) = true

gossip-tick-observed-admissible : GossipTickMeasure → Maybe Bool
gossip-tick-observed-admissible gtm-unmeasured = nothing
gossip-tick-observed-admissible (gtm-measured v _) = just v

gossip-tick-dataset : GossipTickMeasure → Maybe String
gossip-tick-dataset gtm-unmeasured = nothing
gossip-tick-dataset (gtm-measured _ d) = just d

gossip-dataset-nonempty : String → Bool
gossip-dataset-nonempty "" = false
gossip-dataset-nonempty _ = true

data GossipExcitementComposePin : Set where
  gecp-import-select-excitement : GossipExcitementComposePin
  gecp-second-argmin-refused : GossipExcitementComposePin

record GossipTickCandidate : Set where
  field
    gossip-tick-id : ℕ
    gossip-candidate-measure : GossipTickMeasure
    gossip-tick-compose-pin : GossipExcitementComposePin
    gossip-tick-physics-green-claim : Bool

record GossipTickUcrsStamp : Set where
  field
    gossip-tick-ucrs-seq : ℕ
    gossip-tick-ucrs-wall-has-t : Bool

record GossipTickWitness : Set where
  field
    gossip-witness-ucrs : GossipTickUcrsStamp
    gossip-witness-measure : GossipTickMeasure
    gossip-witness-compose-pin : GossipExcitementComposePin

record GossipTickMorphism : Set where
  field
    gossip-morphism-candidate : GossipTickCandidate
    gossip-morphism-witness : GossipTickWitness
    gossip-morphism-excitement-selected : Bool

data GossipTickRefusal : Set where
  gtr-unmeasured-collapsed-to-false : GossipTickRefusal
  gtr-second-argmin-selector : GossipTickRefusal
  gtr-invented-physics-green : GossipTickRefusal
  gtr-gate-rejected : ℕ → GossipTickRefusal

data GossipTickVerdict : Set where
  gtv-gossip-admissible : GossipTickVerdict
  gtv-refuse-unmeasured-false-green : GossipTickVerdict
  gtv-refuse-second-argmin : GossipTickVerdict
  gtv-refuse-invented-green : GossipTickVerdict

------------------------------------------------------------------------
-- SECTION 3: §15.6 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record GossipTickAdmissibilityConjunct : Set where
  field
    gossip-conj-gate-ok : Bool
    gossip-conj-unmeasured-not-false-green : Bool
    gossip-conj-excitement-preserves : Bool

gossip-conjunct-admits : GossipTickAdmissibilityConjunct → Bool
gossip-conjunct-admits c =
  if_then_else_ (GossipTickAdmissibilityConjunct.gossip-conj-gate-ok c)
    (if_then_else_ (GossipTickAdmissibilityConjunct.gossip-conj-unmeasured-not-false-green c)
      (GossipTickAdmissibilityConjunct.gossip-conj-excitement-preserves c)
      false)
    false

refuse-unmeasured-gossip-tick-as-false-green :
  GossipTickMeasure → Maybe GossipTickRefusal
refuse-unmeasured-gossip-tick-as-false-green gtm-unmeasured =
  just gtr-unmeasured-collapsed-to-false
refuse-unmeasured-gossip-tick-as-false-green (gtm-measured _ _) = nothing

refuse-second-argmin-on-gossip-tick :
  GossipExcitementComposePin → Maybe GossipTickRefusal
refuse-second-argmin-on-gossip-tick gecp-second-argmin-refused =
  just gtr-second-argmin-selector
refuse-second-argmin-on-gossip-tick gecp-import-select-excitement = nothing

measured-gossip-tick :
  Bool → String → GossipTickMeasure ⊎ GossipTickRefusal
measured-gossip-tick observed dataset with gossip-dataset-nonempty dataset
... | false = inj₂ gtr-unmeasured-collapsed-to-false
... | true = inj₁ (gtm-measured observed dataset)

admit-gossip-tick : GossipTickCandidate → Maybe GossipTickRefusal
admit-gossip-tick c with GossipTickCandidate.gossip-tick-physics-green-claim c
... | true = just gtr-invented-physics-green
... | false with refuse-second-argmin-on-gossip-tick (GossipTickCandidate.gossip-tick-compose-pin c)
... | just r = just r
... | nothing with GossipTickCandidate.gossip-candidate-measure c
... | gtm-unmeasured = just gtr-unmeasured-collapsed-to-false
... | gtm-measured false _ = nothing
... | gtm-measured true dataset with gossip-dataset-nonempty dataset
... | false = just gtr-unmeasured-collapsed-to-false
... | true = nothing

evaluate-gossip-tick : GossipTickCandidate → GossipTickVerdict
evaluate-gossip-tick c with admit-gossip-tick c
... | nothing = gtv-gossip-admissible
... | just gtr-unmeasured-collapsed-to-false = gtv-refuse-unmeasured-false-green
... | just gtr-second-argmin-selector = gtv-refuse-second-argmin
... | just gtr-invented-physics-green = gtv-refuse-invented-green
... | just (gtr-gate-rejected _) = gtv-refuse-invented-green

witness-from-gossip-candidate :
  GossipTickCandidate → GossipTickUcrsStamp → GossipTickWitness
witness-from-gossip-candidate c ucrs = record
  { gossip-witness-ucrs = ucrs
  ; gossip-witness-measure = GossipTickCandidate.gossip-candidate-measure c
  ; gossip-witness-compose-pin = GossipTickCandidate.gossip-tick-compose-pin c
  }

apply-gossip-tick-morphism :
  GossipTickCandidate → GossipTickUcrsStamp → GossipTickAdmissibilityConjunct → Bool →
  GossipTickMorphism ⊎ GossipTickRefusal
apply-gossip-tick-morphism cand ucrs conj sel with gossip-conjunct-admits conj
... | false = inj₂ (gtr-gate-rejected (GossipTickUcrsStamp.gossip-tick-ucrs-seq ucrs))
... | true with admit-gossip-tick cand
... | just r = inj₂ r
... | nothing with sel
... | false = inj₂ gtr-second-argmin-selector
... | true = inj₁ record
    { gossip-morphism-candidate = cand
    ; gossip-morphism-witness = witness-from-gossip-candidate cand ucrs
    ; gossip-morphism-excitement-selected = sel
    }

------------------------------------------------------------------------
-- SECTION 4: Gossip tick composes excitement-select (no second argmin)
------------------------------------------------------------------------

record GossipTickCtx (src : ThermodynamicState) : Set where
  field
    gossip-tick-successors : List (history-candidate src)

gossip-tick-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  GossipExcitementComposePin →
  history-candidate src ⊎ excitement-residue
gossip-tick-excitement-select src cands gecp-import-select-excitement =
  excitement-select src cands
gossip-tick-excitement-select src cands gecp-second-argmin-refused =
  inj₂ exc-all-inadmissible

gossip-tick-select :
  (src : ThermodynamicState) (ctx : GossipTickCtx src) →
  history-candidate src ⊎ excitement-residue
gossip-tick-select src ctx =
  urge-recovery-select src (GossipTickCtx.gossip-tick-successors ctx)

gossip-tick-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : GossipTickCtx src) →
  gossip-tick-select src ctx ≡
  excitement-select src (GossipTickCtx.gossip-tick-successors ctx)
gossip-tick-select-eq-excitement-select src ctx = refl

gossip-tick-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : GossipTickCtx src) →
  gossip-tick-select src ctx ≡
  urge-recovery-select src (GossipTickCtx.gossip-tick-successors ctx)
gossip-tick-select-eq-urge-recovery-select src ctx = refl

gossip-tick-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : GossipTickCtx src) →
  gossip-tick-select src ctx ≡
  excitement-select src (GossipTickCtx.gossip-tick-successors ctx)
gossip-tick-no-local-argmin src ctx =
  gossip-tick-select-eq-excitement-select src ctx

gossip-tick-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  gossip-tick-excitement-select src cands gecp-import-select-excitement ≡
  excitement-select src cands
gossip-tick-excitement-select-eq-excitement-select src cands = refl

gossip-tick-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  gossip-tick-excitement-select src cands gecp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
gossip-tick-excitement-select-refuses-second-argmin src cands = refl

gossip-tick-select-empty :
  ∀ (src : ThermodynamicState) (ctx : GossipTickCtx src) →
  GossipTickCtx.gossip-tick-successors ctx ≡ List.[] →
  gossip-tick-select src ctx ≡ inj₂ exc-no-candidates
gossip-tick-select-empty src ctx Hnil rewrite Hnil = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 5: §15.6 H3 fixtures + witness theorems
------------------------------------------------------------------------

gossip-fixture-dataset : String
gossip-fixture-dataset = "fixture:h3:gossip-tick:admissible-001"

gossip-fixture-second-argmin-dataset : String
gossip-fixture-second-argmin-dataset = "fixture:h3:gossip-tick:second-argmin-002"

gossip-fixture-ucrs : GossipTickUcrsStamp
gossip-fixture-ucrs = record
  { gossip-tick-ucrs-seq = 7
  ; gossip-tick-ucrs-wall-has-t = true
  }

h3-admissible-measured-gossip-tick : GossipTickCandidate
h3-admissible-measured-gossip-tick = record
  { gossip-tick-id = 1
  ; gossip-candidate-measure = gtm-measured true gossip-fixture-dataset
  ; gossip-tick-compose-pin = gecp-import-select-excitement
  ; gossip-tick-physics-green-claim = false
  }

h3-unmeasured-false-green-fixture : GossipTickCandidate
h3-unmeasured-false-green-fixture = record
  { gossip-tick-id = 2
  ; gossip-candidate-measure = gtm-unmeasured
  ; gossip-tick-compose-pin = gecp-import-select-excitement
  ; gossip-tick-physics-green-claim = false
  }

h3-second-argmin-fixture : GossipTickCandidate
h3-second-argmin-fixture = record
  { gossip-tick-id = 3
  ; gossip-candidate-measure = gtm-measured false gossip-fixture-second-argmin-dataset
  ; gossip-tick-compose-pin = gecp-second-argmin-refused
  ; gossip-tick-physics-green-claim = false
  }

gossip-fixture-conjunct : GossipTickAdmissibilityConjunct
gossip-fixture-conjunct = record
  { gossip-conj-gate-ok = true
  ; gossip-conj-unmeasured-not-false-green = true
  ; gossip-conj-excitement-preserves = true
  }

refuse-unmeasured-gossip-tick-positive :
  refuse-unmeasured-gossip-tick-as-false-green gtm-unmeasured ≡
  just gtr-unmeasured-collapsed-to-false
refuse-unmeasured-gossip-tick-positive = refl

refuse-second-argmin-positive :
  refuse-second-argmin-on-gossip-tick gecp-second-argmin-refused ≡
  just gtr-second-argmin-selector
refuse-second-argmin-positive = refl

gossip-tick-unmeasured-not-measured :
  gossip-tick-is-measured gtm-unmeasured ≡ false
gossip-tick-unmeasured-not-measured = refl

gossip-tick-observed-none-when-unmeasured :
  gossip-tick-observed-admissible gtm-unmeasured ≡ nothing
gossip-tick-observed-none-when-unmeasured = refl

h3-admissible-measured-gossip-tick-admits :
  admit-gossip-tick h3-admissible-measured-gossip-tick ≡ nothing
h3-admissible-measured-gossip-tick-admits = refl

h3-admissible-measured-gossip-tick-evaluate-admit :
  evaluate-gossip-tick h3-admissible-measured-gossip-tick ≡ gtv-gossip-admissible
h3-admissible-measured-gossip-tick-evaluate-admit = refl

h3-unmeasured-false-green-refused :
  admit-gossip-tick h3-unmeasured-false-green-fixture ≡
  just gtr-unmeasured-collapsed-to-false
h3-unmeasured-false-green-refused = refl

h3-unmeasured-false-green-evaluate-refuse :
  evaluate-gossip-tick h3-unmeasured-false-green-fixture ≡
  gtv-refuse-unmeasured-false-green
h3-unmeasured-false-green-evaluate-refuse = refl

h3-second-argmin-refused :
  admit-gossip-tick h3-second-argmin-fixture ≡ just gtr-second-argmin-selector
h3-second-argmin-refused = refl

h3-second-argmin-evaluate-refuse :
  evaluate-gossip-tick h3-second-argmin-fixture ≡ gtv-refuse-second-argmin
h3-second-argmin-evaluate-refuse = refl

gossip-fixture-measured-gossip-tick-ok :
  measured-gossip-tick true gossip-fixture-dataset ≡
  inj₁ (gtm-measured true gossip-fixture-dataset)
gossip-fixture-measured-gossip-tick-ok = refl

gossip-fixture-empty-dataset-refused :
  measured-gossip-tick false "" ≡ inj₂ gtr-unmeasured-collapsed-to-false
gossip-fixture-empty-dataset-refused = refl

gossip-fixture-apply-morphism-ok :
  apply-gossip-tick-morphism
    h3-admissible-measured-gossip-tick gossip-fixture-ucrs
    gossip-fixture-conjunct true ≡
  inj₁ record
    { gossip-morphism-candidate = h3-admissible-measured-gossip-tick
    ; gossip-morphism-witness =
        witness-from-gossip-candidate
          h3-admissible-measured-gossip-tick gossip-fixture-ucrs
    ; gossip-morphism-excitement-selected = true
    }
gossip-fixture-apply-morphism-ok = refl

gossip-fixture-witness-preserves-measure :
  GossipTickWitness.gossip-witness-measure
    (witness-from-gossip-candidate
       h3-admissible-measured-gossip-tick gossip-fixture-ucrs) ≡
  gtm-measured true gossip-fixture-dataset
gossip-fixture-witness-preserves-measure = refl

gossip-fixture-conjunct-admits-true :
  gossip-conjunct-admits gossip-fixture-conjunct ≡ true
gossip-fixture-conjunct-admits-true = refl

------------------------------------------------------------------------
-- SECTION 6: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

gossip-tick-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
gossip-tick-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

gossip-tick-physics-green : Bool
gossip-tick-physics-green = false

gossip-tick-physics-green-false : gossip-tick-physics-green ≡ false
gossip-tick-physics-green-false = refl

gossip-tick-production-wired : Bool
gossip-tick-production-wired = false

gossip-tick-production-wired-false :
  gossip-tick-production-wired ≡ false
gossip-tick-production-wired-false = refl

gossip-tick-marker : ℕ
gossip-tick-marker = 1

gossip-tick-marker-eq : gossip-tick-marker ≡ 1
gossip-tick-marker-eq = refl

gossip-tick-module-witness : ⊤
gossip-tick-module-witness = tt

gossip-tick-catalog-witness :
  String
gossip-tick-catalog-witness =
  "URGE-FORMAL-MESO-AGDA-GOSSIP-TICK §15.6 H3 gossip tick as typed Unmeasured|Measured wrapper; UNKNOWN ≠ false-as-GREEN; compose excitement-select no second argmin sole postulate physicalSecondLaw not physics GREEN not production_wired"
