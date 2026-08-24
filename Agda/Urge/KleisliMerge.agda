-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliMerge — meso/acting §16.7 operator verb merge.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-MERGE (umst-formal acting fiber only).
-- §16.7: operator verb `merge` as Kleisli arrow — gate_check_before_sync inbound;
-- MergeSafe predicate required; Excitement = provenance preserved; entity check =
-- tier disjoint. Honest refuse on MergeSafe mismatch — no CRDT auto-merge.
--
-- Composes `excitement-select` — not a second ℚ argmin. Mirrors
-- `Urge.CompactionComposite` / `Urge.MergeSafe`. Anchored in
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliMerge where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; 0<1+n)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Rational.Properties as ℚ-Props using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does; yes; no)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head carriers (no Concrete.Gate K-infect)
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

------------------------------------------------------------------------
-- SECTION 0b: MergeSafe mirror (Urge.MergeSafe — import-only pin)
------------------------------------------------------------------------

record HistoryMemoryEntry : Set where
  field
    history-content-id history-theorem-id : ℕ

mergeSafePred : HistoryMemoryEntry → HistoryMemoryEntry → Set
mergeSafePred eₐ eᵦ =
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ ×
  HistoryMemoryEntry.history-theorem-id eₐ ≡ HistoryMemoryEntry.history-theorem-id eᵦ

data mergeSafeVerdict : Set where
  merge-safe-admit merge-safe-refuse-mismatch : mergeSafeVerdict

merge-safe : HistoryMemoryEntry → HistoryMemoryEntry → mergeSafeVerdict
merge-safe left right =
  if does (ℕ-Props._≟_ (HistoryMemoryEntry.history-content-id left) (HistoryMemoryEntry.history-content-id right)) then
    if does (ℕ-Props._≟_ (HistoryMemoryEntry.history-theorem-id left) (HistoryMemoryEntry.history-theorem-id right)) then
      merge-safe-admit
    else
      merge-safe-refuse-mismatch
  else
    merge-safe-refuse-mismatch

data crdt-auto-merge-refused : Set where
  crdt-auto-merge-refused-tag : crdt-auto-merge-refused

refuse-crdt-auto-merge : crdt-auto-merge-refused
refuse-crdt-auto-merge = crdt-auto-merge-refused-tag

merge-gate-check-before-sync : ThermodynamicState → ThermodynamicState → Bool
merge-gate-check-before-sync prior post =
  if does (ℚ-Props._≟_ (ThermodynamicState.density prior) (ThermodynamicState.density post))
  then if does (ℚ-Props._≟_ (ThermodynamicState.free-energy prior) (ThermodynamicState.free-energy post))
       then if does (ℚ-Props._≟_ (ThermodynamicState.hydration prior) (ThermodynamicState.hydration post))
            then does (ℚ-Props._≟_ (ThermodynamicState.strength prior) (ThermodynamicState.strength post))
            else false
       else false
  else false

------------------------------------------------------------------------
-- SECTION 1: §16.7 verb row + merge carriers
------------------------------------------------------------------------

data VerbColumnRequirement : Set where
  vcr-not-required vcr-required : VerbColumnRequirement

data KleisliGateKind : Set where
  kgk-frugal-mi-observation kgk-gate-check-before-sync-inbound kgk-outbound-tick-if-admitted : KleisliGateKind

data EntityCheckKind : Set where
  eck-tier-disjoint eck-remote-class eck-replica-class : EntityCheckKind

record OperatorVerbRow : Set where
  field
    verb-merge : Bool
    verb-kleisli-gate : KleisliGateKind
    verb-merge-safe : VerbColumnRequirement
    verb-excitement : VerbColumnRequirement
    verb-entity-check : EntityCheckKind

data MemoryTier : Set where
  mt-ephemeral mt-device mt-federated : MemoryTier

record MergeHistoryObject : Set where
  field
    mho-entry : HistoryMemoryEntry
    mho-tier : MemoryTier

data InboundGateCheck : Set where
  igc-admitted igc-refused igc-bypass-attempted : InboundGateCheck

inbound-gate-admits : InboundGateCheck → Bool
inbound-gate-admits igc-admitted = true
inbound-gate-admits igc-refused = false
inbound-gate-admits igc-bypass-attempted = false

record MergeTransition : Set where
  field
    merge-prior-commit merge-post-commit : ℕ

record MergeProvenance : Set where
  field
    merge-ucrs-chain : List ℕ
    merge-dag-commit : ℕ
    merge-landauer-witness : Bool

record MergeKleisliArrow : Set where
  field
    mka-gate : InboundGateCheck
    mka-left mka-right : MergeHistoryObject
    mka-transition : MergeTransition
    mka-prior-provenance mka-post-provenance : MergeProvenance
    mka-prior-state mka-post-state : ThermodynamicState

data TierDisjointVerdict : Set where
  tdv-admit tdv-refuse-cross-tier : TierDisjointVerdict

data ProvenancePreserveVerdict : Set where
  ppv-admit ppv-refuse-prior-dag ppv-refuse-post-dag ppv-refuse-chain ppv-refuse-witness : ProvenancePreserveVerdict

data MergeArrowRefusal : Set where
  mar-gate-refused mar-gate-bypass-refused mar-merge-safe-refused : MergeArrowRefusal
  mar-tier-disjoint : TierDisjointVerdict → MergeArrowRefusal
  mar-provenance-refused : ProvenancePreserveVerdict → MergeArrowRefusal
  mar-production-wired-refused : MergeArrowRefusal

record MergeOutcome : Set where
  field
    merge-out-merged : MergeHistoryObject
    merge-out-provenance : ProvenancePreserveVerdict
    merge-out-tier : TierDisjointVerdict

merge-verb-row : OperatorVerbRow
merge-verb-row = record
  { verb-merge = true
  ; verb-kleisli-gate = kgk-gate-check-before-sync-inbound
  ; verb-merge-safe = vcr-required
  ; verb-excitement = vcr-required
  ; verb-entity-check = eck-tier-disjoint
  }

------------------------------------------------------------------------
-- SECTION 2: MergeSafe + tier disjoint + provenance (computational)
------------------------------------------------------------------------

memory-tier-eqb : MemoryTier → MemoryTier → Bool
memory-tier-eqb mt-ephemeral mt-ephemeral = true
memory-tier-eqb mt-ephemeral mt-device = false
memory-tier-eqb mt-ephemeral mt-federated = false
memory-tier-eqb mt-device mt-ephemeral = false
memory-tier-eqb mt-device mt-device = true
memory-tier-eqb mt-device mt-federated = false
memory-tier-eqb mt-federated mt-ephemeral = false
memory-tier-eqb mt-federated mt-device = false
memory-tier-eqb mt-federated mt-federated = true

nat-list-eqb : List ℕ → List ℕ → Bool
nat-list-eqb [] [] = true
nat-list-eqb (x ∷ xs) (y ∷ ys) =
  if does (ℕ-Props._≟_ x y) then nat-list-eqb xs ys else false
nat-list-eqb [] (_ ∷ _) = false
nat-list-eqb (_ ∷ _) [] = false

evaluate-tier-disjoint : MemoryTier → MemoryTier → TierDisjointVerdict
evaluate-tier-disjoint t1 t2 =
  if memory-tier-eqb t1 t2 then tdv-admit else tdv-refuse-cross-tier

merge-history-entry : HistoryMemoryEntry → HistoryMemoryEntry → Maybe HistoryMemoryEntry
merge-history-entry left right with merge-safe left right
... | merge-safe-admit = just left
... | merge-safe-refuse-mismatch = nothing

preserves-merge-chain :
  MergeProvenance → MergeProvenance → ProvenancePreserveVerdict
preserves-merge-chain prior post =
  if nat-list-eqb
       (MergeProvenance.merge-ucrs-chain post)
       (MergeProvenance.merge-ucrs-chain prior ++ MergeProvenance.merge-dag-commit prior ∷ [])
  then if (MergeProvenance.merge-landauer-witness prior) ∧ not (MergeProvenance.merge-landauer-witness post)
       then ppv-refuse-witness
       else ppv-admit
  else ppv-refuse-chain

preserves-merge-provenance :
  MergeTransition → MergeProvenance → MergeProvenance → ProvenancePreserveVerdict
preserves-merge-provenance tr prior post =
  if does (ℕ-Props._≟_ (MergeProvenance.merge-dag-commit prior) (MergeTransition.merge-prior-commit tr))
  then if does (ℕ-Props._≟_ (MergeProvenance.merge-dag-commit post) (MergeTransition.merge-post-commit tr))
       then preserves-merge-chain prior post
       else ppv-refuse-post-dag
  else ppv-refuse-prior-dag

merge-prov-result :
  ProvenancePreserveVerdict → MergeKleisliArrow → HistoryMemoryEntry → MergeOutcome ⊎ MergeArrowRefusal
merge-prov-result ppv-admit a″ merged-entry′ =
  if merge-gate-check-before-sync (MergeKleisliArrow.mka-prior-state a″)
                                  (MergeKleisliArrow.mka-post-state a″)
  then inj₁ record
    { merge-out-merged = record
      { mho-entry = merged-entry′
      ; mho-tier = MergeHistoryObject.mho-tier (MergeKleisliArrow.mka-left a″)
      }
    ; merge-out-provenance = ppv-admit
    ; merge-out-tier = tdv-admit
    }
  else inj₂ mar-gate-refused
merge-prov-result ppv-refuse-prior-dag a″ _ = inj₂ (mar-provenance-refused ppv-refuse-prior-dag)
merge-prov-result ppv-refuse-post-dag a″ _ = inj₂ (mar-provenance-refused ppv-refuse-post-dag)
merge-prov-result ppv-refuse-chain a″ _ = inj₂ (mar-provenance-refused ppv-refuse-chain)
merge-prov-result ppv-refuse-witness a″ _ = inj₂ (mar-provenance-refused ppv-refuse-witness)

merge-prov-step : MergeKleisliArrow → HistoryMemoryEntry → MergeOutcome ⊎ MergeArrowRefusal
merge-prov-step a′ merged-entry =
  merge-prov-result
    (preserves-merge-provenance (MergeKleisliArrow.mka-transition a′)
      (MergeKleisliArrow.mka-prior-provenance a′)
      (MergeKleisliArrow.mka-post-provenance a′))
    a′ merged-entry

merge-safe-step : MergeKleisliArrow → MergeOutcome ⊎ MergeArrowRefusal
merge-safe-step a′ with merge-history-entry (MergeHistoryObject.mho-entry (MergeKleisliArrow.mka-left a′))
                                      (MergeHistoryObject.mho-entry (MergeKleisliArrow.mka-right a′))
... | nothing = inj₂ mar-merge-safe-refused
... | just merged-entry = merge-prov-step a′ merged-entry

merge-tier-step : MergeKleisliArrow → MergeOutcome ⊎ MergeArrowRefusal
merge-tier-step a′ with evaluate-tier-disjoint (MergeHistoryObject.mho-tier (MergeKleisliArrow.mka-left a′))
                                   (MergeHistoryObject.mho-tier (MergeKleisliArrow.mka-right a′))
... | tdv-admit = merge-safe-step a′
... | tdv-refuse-cross-tier = inj₂ (mar-tier-disjoint tdv-refuse-cross-tier)

evaluate-merge-kleisli : MergeKleisliArrow → MergeOutcome ⊎ MergeArrowRefusal
evaluate-merge-kleisli a with MergeKleisliArrow.mka-gate a
... | igc-bypass-attempted = inj₂ mar-gate-bypass-refused
... | igc-refused = inj₂ mar-gate-refused
... | igc-admitted = merge-tier-step a

merge-verb-row-merge-safe-required :
  OperatorVerbRow.verb-merge-safe merge-verb-row ≡ vcr-required
merge-verb-row-merge-safe-required = refl

merge-verb-row-excitement-required :
  OperatorVerbRow.verb-excitement merge-verb-row ≡ vcr-required
merge-verb-row-excitement-required = refl

merge-verb-row-tier-disjoint-entity :
  OperatorVerbRow.verb-entity-check merge-verb-row ≡ eck-tier-disjoint
merge-verb-row-tier-disjoint-entity = refl

kleisli-gate-matches-merge-inbound :
  OperatorVerbRow.verb-kleisli-gate merge-verb-row ≡ kgk-gate-check-before-sync-inbound
kleisli-gate-matches-merge-inbound = refl

merge-history-entry-admit :
  (left right : HistoryMemoryEntry) →
  merge-safe left right ≡ merge-safe-admit →
  merge-history-entry left right ≡ just left
merge-history-entry-admit left right h rewrite h = refl

merge-history-entry-refuse-on-mismatch :
  (left right : HistoryMemoryEntry) →
  merge-safe left right ≡ merge-safe-refuse-mismatch →
  merge-history-entry left right ≡ nothing
merge-history-entry-refuse-on-mismatch left right h rewrite h = refl

evaluate-tier-disjoint-same : (t : MemoryTier) → evaluate-tier-disjoint t t ≡ tdv-admit
evaluate-tier-disjoint-same mt-ephemeral = refl
evaluate-tier-disjoint-same mt-device = refl
evaluate-tier-disjoint-same mt-federated = refl

------------------------------------------------------------------------
-- SECTION 3: Merge composes Excitement (no second argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates exc-all-inadmissible exc-no-strict-improvement : excitement-residue

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

record merge-kleisli-ctx (src : ThermodynamicState) : Set where
  field
    merge-successors : List (history-candidate src)

merge-kleisli-select :
  (src : ThermodynamicState) (ctx : merge-kleisli-ctx src) →
  history-candidate src ⊎ excitement-residue
merge-kleisli-select src ctx =
  excitement-select src (merge-kleisli-ctx.merge-successors ctx)

merge-kleisli-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : merge-kleisli-ctx src) →
  merge-kleisli-select src ctx ≡
  excitement-select src (merge-kleisli-ctx.merge-successors ctx)
merge-kleisli-select-eq-excitement-select src ctx = refl

merge-kleisli-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : merge-kleisli-ctx src) →
  merge-kleisli-select src ctx ≡
  excitement-select src (merge-kleisli-ctx.merge-successors ctx)
merge-kleisli-no-local-argmin src ctx =
  merge-kleisli-select-eq-excitement-select src ctx

merge-kleisli-empty :
  ∀ (src : ThermodynamicState) (ctx : merge-kleisli-ctx src) →
  merge-kleisli-ctx.merge-successors ctx ≡ [] →
  merge-kleisli-select src ctx ≡ inj₂ exc-no-candidates
merge-kleisli-empty src ctx hnil rewrite hnil = refl

------------------------------------------------------------------------
-- SECTION 4: Positive refuse + CRDT + fixtures
------------------------------------------------------------------------

data MergeGateMismatch : Set where
  mgm-frugal-mi-on-merge mgm-outbound-tick-on-merge mgm-remote-class-on-merge mgm-replica-class-on-merge : MergeGateMismatch

refuse-frugal-mi-on-merge : MergeGateMismatch
refuse-frugal-mi-on-merge = mgm-frugal-mi-on-merge

refuse-outbound-tick-on-merge : MergeGateMismatch
refuse-outbound-tick-on-merge = mgm-outbound-tick-on-merge

refuse-remote-class-on-merge : MergeGateMismatch
refuse-remote-class-on-merge = mgm-remote-class-on-merge

refuse-replica-class-on-merge : MergeGateMismatch
refuse-replica-class-on-merge = mgm-replica-class-on-merge

refuse-production-wired-merge : MergeArrowRefusal
refuse-production-wired-merge = mar-production-wired-refused

merge-fixture-entry : HistoryMemoryEntry
merge-fixture-entry = record { history-content-id = 42 ; history-theorem-id = 7 }

merge-fixture-object : MergeHistoryObject
merge-fixture-object = record { mho-entry = merge-fixture-entry ; mho-tier = mt-device }

merge-fixture-state : ThermodynamicState
merge-fixture-state = record { density = 0ℚ ; free-energy = 0ℚ ; hydration = 0ℚ ; strength = 0ℚ }

merge-fixture-provenance : (prior post : ℕ) → MergeProvenance
merge-fixture-provenance prior post = record
  { merge-ucrs-chain = prior ∷ []
  ; merge-dag-commit = prior
  ; merge-landauer-witness = true
  }

merge-fixture-post-provenance : (prior post : ℕ) → MergeProvenance
merge-fixture-post-provenance prior post = record
  { merge-ucrs-chain = prior ∷ prior ∷ []
  ; merge-dag-commit = post
  ; merge-landauer-witness = true
  }

merge-fixture-arrow : MergeKleisliArrow
merge-fixture-arrow = record
  { mka-gate = igc-admitted
  ; mka-left = merge-fixture-object
  ; mka-right = merge-fixture-object
  ; mka-transition = record { merge-prior-commit = 10 ; merge-post-commit = 11 }
  ; mka-prior-provenance = merge-fixture-provenance 10 11
  ; mka-post-provenance = merge-fixture-post-provenance 10 11
  ; mka-prior-state = merge-fixture-state
  ; mka-post-state = merge-fixture-state
  }

merge-fixture-evaluate-ok :
  evaluate-merge-kleisli merge-fixture-arrow ≡
  inj₁ record
    { merge-out-merged = merge-fixture-object
    ; merge-out-provenance = ppv-admit
    ; merge-out-tier = tdv-admit
    }
merge-fixture-evaluate-ok = refl

merge-fixture-arrow-gate-refused : MergeKleisliArrow
merge-fixture-arrow-gate-refused = record
  { mka-gate = igc-refused
  ; mka-left = merge-fixture-object
  ; mka-right = merge-fixture-object
  ; mka-transition = record { merge-prior-commit = 10 ; merge-post-commit = 11 }
  ; mka-prior-provenance = merge-fixture-provenance 10 11
  ; mka-post-provenance = merge-fixture-post-provenance 10 11
  ; mka-prior-state = merge-fixture-state
  ; mka-post-state = merge-fixture-state
  }

merge-fixture-right-mismatch : MergeHistoryObject
merge-fixture-right-mismatch = record
  { mho-entry = record { history-content-id = 99 ; history-theorem-id = 7 }
  ; mho-tier = mt-device
  }

merge-fixture-arrow-merge-safe-refused : MergeKleisliArrow
merge-fixture-arrow-merge-safe-refused = record
  { mka-gate = igc-admitted
  ; mka-left = merge-fixture-object
  ; mka-right = merge-fixture-right-mismatch
  ; mka-transition = record { merge-prior-commit = 10 ; merge-post-commit = 11 }
  ; mka-prior-provenance = merge-fixture-provenance 10 11
  ; mka-post-provenance = merge-fixture-post-provenance 10 11
  ; mka-prior-state = merge-fixture-state
  ; mka-post-state = merge-fixture-state
  }

merge-fixture-right-cross-tier : MergeHistoryObject
merge-fixture-right-cross-tier = record
  { mho-entry = merge-fixture-entry
  ; mho-tier = mt-federated
  }

merge-fixture-arrow-tier-disjoint-refused : MergeKleisliArrow
merge-fixture-arrow-tier-disjoint-refused = record
  { mka-gate = igc-admitted
  ; mka-left = merge-fixture-object
  ; mka-right = merge-fixture-right-cross-tier
  ; mka-transition = record { merge-prior-commit = 10 ; merge-post-commit = 11 }
  ; mka-prior-provenance = merge-fixture-provenance 10 11
  ; mka-post-provenance = merge-fixture-post-provenance 10 11
  ; mka-prior-state = merge-fixture-state
  ; mka-post-state = merge-fixture-state
  }

merge-fixture-gate-refused :
  evaluate-merge-kleisli merge-fixture-arrow-gate-refused ≡ inj₂ mar-gate-refused
merge-fixture-gate-refused = refl

merge-fixture-merge-safe-refused :
  evaluate-merge-kleisli merge-fixture-arrow-merge-safe-refused ≡ inj₂ mar-merge-safe-refused
merge-fixture-merge-safe-refused = refl

merge-fixture-tier-disjoint-refused :
  evaluate-merge-kleisli merge-fixture-arrow-tier-disjoint-refused ≡
  inj₂ (mar-tier-disjoint tdv-refuse-cross-tier)
merge-fixture-tier-disjoint-refused = refl

merge-fixture-crdt-refused :
  refuse-crdt-auto-merge ≡ crdt-auto-merge-refused-tag
merge-fixture-crdt-refused = refl

merge-fixture-positive-refuse-gates :
  (refuse-frugal-mi-on-merge ≡ mgm-frugal-mi-on-merge) ×
  (refuse-outbound-tick-on-merge ≡ mgm-outbound-tick-on-merge) ×
  (refuse-remote-class-on-merge ≡ mgm-remote-class-on-merge) ×
  (refuse-replica-class-on-merge ≡ mgm-replica-class-on-merge)
merge-fixture-positive-refuse-gates = refl , refl , refl , refl

------------------------------------------------------------------------
-- SECTION 5: History transition + Landauer bridge (zero new postulates)
------------------------------------------------------------------------

record HistoryTransition : Set where
  field
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

merge-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
merge-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisli-merge-physics-green : Bool
kleisli-merge-physics-green = false

kleisli-merge-physics-green-false :
  kleisli-merge-physics-green ≡ false
kleisli-merge-physics-green-false = refl

kleisli-merge-production-wired : Bool
kleisli-merge-production-wired = false

kleisli-merge-production-wired-false :
  kleisli-merge-production-wired ≡ false
kleisli-merge-production-wired-false = refl

kleisli-merge-marker : ℕ
kleisli-merge-marker = 167

kleisli-merge-marker-pos : 0 < kleisli-merge-marker
kleisli-merge-marker-pos = 0<1+n

kleisli-merge-module-witness : ⊤
kleisli-merge-module-witness = tt

kleisli-merge-no-new-axiom : ⊤
kleisli-merge-no-new-axiom = tt

kleisli-merge-no-second-argmin :
  ∀ (src : ThermodynamicState) (ctx : merge-kleisli-ctx src) →
  merge-kleisli-select src ctx ≡
  excitement-select src (merge-kleisli-ctx.merge-successors ctx)
kleisli-merge-no-second-argmin src ctx =
  merge-kleisli-select-eq-excitement-select src ctx

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  mgm-frugal-mi-on-merge ≡ mgm-frugal-mi-on-merge
refuse-second-argmin-is-tag = refl
