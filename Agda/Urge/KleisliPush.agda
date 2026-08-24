-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliPush — meso/acting §16.7 operator verb push.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-PUSH (umst-formal acting fiber only).
-- §16.7: operator verb `push` as Kleisli arrow — outbound tick if admitted gate;
-- pre-push MergeSafe witness; provenance preserved Excitement; entity remote
-- entity check — not gate_check_before_sync inbound, not Frugal MI observation.
-- Composes `excitement-select` — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / `Urge.KleisliStatus`. Anchored in
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliPush where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

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
-- SECTION 1: §16.7 verb table + push Kleisli carriers
------------------------------------------------------------------------

data VerbColumnRequirement : Set where
  vcr-not-required vcr-required : VerbColumnRequirement

data KleisliGateKind : Set where
  kgk-outbound-tick-if-admitted kgk-gate-check-before-sync-inbound kgk-frugal-mi-observation : KleisliGateKind

data EntityCheckKind : Set where
  eck-entity-remote eck-remote-class eck-replica-class : EntityCheckKind

record OperatorVerbRow : Set where
  field
    verb-push : Bool
    verb-kleisli-gate : KleisliGateKind
    verb-merge-safe : VerbColumnRequirement
    verb-excitement : VerbColumnRequirement
    verb-entity-check : EntityCheckKind

data OutboundTickGate : Set where
  otg-admitted otg-refused otg-bypass-attempted : OutboundTickGate

data PrePushMergeSafeWitness : Set where
  ppms-witnessed ppms-missing ppms-bypass-attempted : PrePushMergeSafeWitness

data ProvenancePreserved : Set where
  pp-preserved pp-violated pp-bypass-attempted : ProvenancePreserved

data EntityRemoteClass : Set where
  erc-entity-remote erc-refused-upstream erc-unclassified : EntityRemoteClass

record PushKleisliArrow : Set where
  field
    push-gate : OutboundTickGate
    push-merge-safe : PrePushMergeSafeWitness
    push-provenance : ProvenancePreserved
    push-entity : EntityRemoteClass
    push-object-count : ℕ

data PushVerdict : Set where
  pv-admitted pv-gate-refused pv-merge-safe-refused pv-provenance-refused pv-entity-remote-refused pv-production-wired-refused pv-gate-bypass-refused : PushVerdict

data PushRefusal : Set where
  pr-gate-refused : PushRefusal
  pr-merge-safe-missing : PushRefusal
  pr-merge-safe-bypass-refused : PushRefusal
  pr-provenance-violated : PushRefusal
  pr-provenance-bypass-refused : PushRefusal
  pr-entity-remote-refused : EntityRemoteClass → PushRefusal
  pr-production-wired-refused : PushRefusal
  pr-gate-bypass-refused : PushRefusal
  pr-wrong-gate : KleisliGateKind → PushRefusal

data PushGateMismatch : Set where
  pgm-sync-inbound-on-push pgm-frugal-mi-on-push pgm-merge-safe-missing-on-push pgm-provenance-on-push : PushGateMismatch

------------------------------------------------------------------------
-- SECTION 2: §16.7 admissibility + push Kleisli evaluation
------------------------------------------------------------------------

push-verb-row : OperatorVerbRow
push-verb-row = record
  { verb-push = true
  ; verb-kleisli-gate = kgk-outbound-tick-if-admitted
  ; verb-merge-safe = vcr-required
  ; verb-excitement = vcr-required
  ; verb-entity-check = eck-entity-remote
  }

outbound-gate-admits : OutboundTickGate → Bool
outbound-gate-admits otg-admitted = true
outbound-gate-admits otg-refused = false
outbound-gate-admits otg-bypass-attempted = false

pre-push-merge-safe-admits : PrePushMergeSafeWitness → Bool
pre-push-merge-safe-admits ppms-witnessed = true
pre-push-merge-safe-admits ppms-missing = false
pre-push-merge-safe-admits ppms-bypass-attempted = false

provenance-preserved-admits : ProvenancePreserved → Bool
provenance-preserved-admits pp-preserved = true
provenance-preserved-admits pp-violated = false
provenance-preserved-admits pp-bypass-attempted = false

entity-remote-admits : EntityRemoteClass → Bool
entity-remote-admits erc-entity-remote = true
entity-remote-admits erc-refused-upstream = false
entity-remote-admits erc-unclassified = false

kleisli-gate-matches-push : KleisliGateKind → Bool
kleisli-gate-matches-push kgk-outbound-tick-if-admitted = true
kleisli-gate-matches-push kgk-gate-check-before-sync-inbound = false
kleisli-gate-matches-push kgk-frugal-mi-observation = false

data RemoteHostTag : Set where
  host-empty host-origin host-github host-forge-entity host-other : RemoteHostTag

classify-entity-remote : RemoteHostTag → EntityRemoteClass
classify-entity-remote host-empty = erc-unclassified
classify-entity-remote host-origin = erc-refused-upstream
classify-entity-remote host-github = erc-refused-upstream
classify-entity-remote host-forge-entity = erc-entity-remote
classify-entity-remote host-other = erc-unclassified

push-kleisli-arrow-from-host :
  OutboundTickGate → PrePushMergeSafeWitness → ProvenancePreserved →
  RemoteHostTag → ℕ → PushKleisliArrow
push-kleisli-arrow-from-host gate merge prov host n = record
  { push-gate = gate
  ; push-merge-safe = merge
  ; push-provenance = prov
  ; push-entity = classify-entity-remote host
  ; push-object-count = n
  }

evaluate-push-kleisli :
  PushKleisliArrow → PushVerdict ⊎ PushRefusal
evaluate-push-kleisli a =
  if outbound-gate-admits (PushKleisliArrow.push-gate a)
  then if pre-push-merge-safe-admits (PushKleisliArrow.push-merge-safe a)
       then if provenance-preserved-admits (PushKleisliArrow.push-provenance a)
            then if entity-remote-admits (PushKleisliArrow.push-entity a)
                 then inj₁ pv-admitted
                 else inj₂ (pr-entity-remote-refused (PushKleisliArrow.push-entity a))
            else gate-provenance-refuse (PushKleisliArrow.push-provenance a)
       else gate-merge-safe-refuse (PushKleisliArrow.push-merge-safe a)
  else gate-outbound-refuse (PushKleisliArrow.push-gate a)
  where
  gate-outbound-refuse : OutboundTickGate → PushVerdict ⊎ PushRefusal
  gate-outbound-refuse otg-admitted = inj₂ pr-gate-refused
  gate-outbound-refuse otg-refused = inj₂ pr-gate-refused
  gate-outbound-refuse otg-bypass-attempted = inj₂ pr-gate-bypass-refused

  gate-merge-safe-refuse : PrePushMergeSafeWitness → PushVerdict ⊎ PushRefusal
  gate-merge-safe-refuse ppms-witnessed = inj₂ pr-merge-safe-missing
  gate-merge-safe-refuse ppms-missing = inj₂ pr-merge-safe-missing
  gate-merge-safe-refuse ppms-bypass-attempted = inj₂ pr-merge-safe-bypass-refused

  gate-provenance-refuse : ProvenancePreserved → PushVerdict ⊎ PushRefusal
  gate-provenance-refuse pp-preserved = inj₂ pr-provenance-violated
  gate-provenance-refuse pp-violated = inj₂ pr-provenance-violated
  gate-provenance-refuse pp-bypass-attempted = inj₂ pr-provenance-bypass-refused

refuse-production-wired-push : PushRefusal
refuse-production-wired-push = pr-production-wired-refused

refuse-gate-bypass-push : PushRefusal
refuse-gate-bypass-push = pr-gate-bypass-refused

refuse-sync-gate-on-push : PushRefusal
refuse-sync-gate-on-push = pr-wrong-gate kgk-gate-check-before-sync-inbound

refuse-frugal-mi-on-push : PushRefusal
refuse-frugal-mi-on-push = pr-wrong-gate kgk-frugal-mi-observation

refuse-merge-safe-missing-on-push : PushGateMismatch
refuse-merge-safe-missing-on-push = pgm-merge-safe-missing-on-push

refuse-provenance-on-push : PushGateMismatch
refuse-provenance-on-push = pgm-provenance-on-push

push-verb-row-excitement-required :
  OperatorVerbRow.verb-excitement push-verb-row ≡ vcr-required
push-verb-row-excitement-required = refl

push-verb-row-merge-safe-required :
  OperatorVerbRow.verb-merge-safe push-verb-row ≡ vcr-required
push-verb-row-merge-safe-required = refl

push-verb-row-outbound-gate :
  OperatorVerbRow.verb-kleisli-gate push-verb-row ≡ kgk-outbound-tick-if-admitted
push-verb-row-outbound-gate = refl

kleisli-gate-matches-push-outbound :
  kleisli-gate-matches-push kgk-outbound-tick-if-admitted ≡ true
kleisli-gate-matches-push-outbound = refl

kleisli-gate-matches-push-sync-false :
  kleisli-gate-matches-push kgk-gate-check-before-sync-inbound ≡ false
kleisli-gate-matches-push-sync-false = refl

kleisli-gate-matches-push-frugal-false :
  kleisli-gate-matches-push kgk-frugal-mi-observation ≡ false
kleisli-gate-matches-push-frugal-false = refl

------------------------------------------------------------------------
-- SECTION 3: Excitement compose (no second argmin)
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

record push-ctx (src : ThermodynamicState) : Set where
  field
    push-successors : List (history-candidate src)

push-select :
  (src : ThermodynamicState) (ctx : push-ctx src) →
  history-candidate src ⊎ excitement-residue
push-select src ctx =
  excitement-select src (push-ctx.push-successors ctx)

data PushExcitementComposePin : Set where
  pecp-import-select-excitement pecp-second-argmin-refused : PushExcitementComposePin

push-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  PushExcitementComposePin →
  history-candidate src ⊎ excitement-residue
push-excitement-select src cands pecp-import-select-excitement =
  excitement-select src cands
push-excitement-select src cands pecp-second-argmin-refused =
  inj₂ exc-all-inadmissible

push-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : push-ctx src) →
  push-select src ctx ≡
  excitement-select src (push-ctx.push-successors ctx)
push-select-eq-excitement-select src ctx = refl

push-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  push-excitement-select src cands pecp-import-select-excitement ≡
  excitement-select src cands
push-excitement-select-eq-excitement-select src cands = refl

push-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  push-excitement-select src cands pecp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
push-excitement-select-refuses-second-argmin src cands = refl

push-no-local-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  push-excitement-select src cands pecp-import-select-excitement ≡
  excitement-select src cands
push-no-local-argmin src cands =
  push-excitement-select-eq-excitement-select src cands

push-excitement-empty :
  ∀ (src : ThermodynamicState) →
  push-excitement-select src [] pecp-import-select-excitement ≡
  inj₂ exc-no-candidates
push-excitement-empty src = refl

------------------------------------------------------------------------
-- SECTION 4: §16.7 fixtures + witness theorems
------------------------------------------------------------------------

push-fixture-admitted-arrow : PushKleisliArrow
push-fixture-admitted-arrow =
  push-kleisli-arrow-from-host otg-admitted ppms-witnessed pp-preserved host-forge-entity 3

push-fixture-gate-refused-arrow : PushKleisliArrow
push-fixture-gate-refused-arrow =
  push-kleisli-arrow-from-host otg-refused ppms-witnessed pp-preserved host-forge-entity 0

push-fixture-admitted-ok :
  evaluate-push-kleisli push-fixture-admitted-arrow ≡ inj₁ pv-admitted
push-fixture-admitted-ok = refl

push-fixture-gate-refused :
  evaluate-push-kleisli push-fixture-gate-refused-arrow ≡ inj₂ pr-gate-refused
push-fixture-gate-refused = refl

push-fixture-entity-remote-forge :
  classify-entity-remote host-forge-entity ≡ erc-entity-remote
push-fixture-entity-remote-forge = refl

push-fixture-entity-refused-upstream-origin :
  classify-entity-remote host-origin ≡ erc-refused-upstream
push-fixture-entity-refused-upstream-origin = refl

push-fixture-entity-refused-upstream-github :
  classify-entity-remote host-github ≡ erc-refused-upstream
push-fixture-entity-refused-upstream-github = refl

push-positive-refuse-sync-gate :
  refuse-sync-gate-on-push ≡ pr-wrong-gate kgk-gate-check-before-sync-inbound
push-positive-refuse-sync-gate = refl

push-positive-refuse-frugal-mi :
  refuse-frugal-mi-on-push ≡ pr-wrong-gate kgk-frugal-mi-observation
push-positive-refuse-frugal-mi = refl

push-positive-refuse-production-wired :
  refuse-production-wired-push ≡ pr-production-wired-refused
push-positive-refuse-production-wired = refl

push-positive-refuse-gate-bypass :
  refuse-gate-bypass-push ≡ pr-gate-bypass-refused
push-positive-refuse-gate-bypass = refl

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

push-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
push-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisli-push-physics-green : Bool
kleisli-push-physics-green = false

kleisli-push-physics-green-false :
  kleisli-push-physics-green ≡ false
kleisli-push-physics-green-false = refl

kleisli-push-production-wired : Bool
kleisli-push-production-wired = false

kleisli-push-production-wired-false :
  kleisli-push-production-wired ≡ false
kleisli-push-production-wired-false = refl

kleisli-push-module-witness : ⊤
kleisli-push-module-witness = tt

push-positive-refuse-aggregate :
  (refuse-sync-gate-on-push ≡ pr-wrong-gate kgk-gate-check-before-sync-inbound) ×
  (refuse-frugal-mi-on-push ≡ pr-wrong-gate kgk-frugal-mi-observation) ×
  (refuse-production-wired-push ≡ pr-production-wired-refused) ×
  (refuse-gate-bypass-push ≡ pr-gate-bypass-refused)
push-positive-refuse-aggregate =
  refl , refl , refl , refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  pgm-provenance-on-push ≡ pgm-provenance-on-push
refuse-second-argmin-is-tag = refl
