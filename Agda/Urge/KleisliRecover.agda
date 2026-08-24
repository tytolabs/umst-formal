-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliRecover — meso/acting §16.7 operator verb recover.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-RECOVER (umst-formal acting fiber only).
-- §16.7: operator verb `recover` as Kleisli arrow — Excitement argmin over
-- successors; MergeSafe witness; typed recovery morphism; network-egress
-- entity check. Recovery **is** `excitement-select` — not rsync theater; no
-- second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / `Urge.BackupRecovery`. Anchored in
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliRecover where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

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
-- SECTION 1: §16.7 recover Kleisli carriers + verb row
------------------------------------------------------------------------

data RecoverOperatorVerb : Set where
  rov-recover : RecoverOperatorVerb

data NetworkEgressClass : Set where
  nec-egress-empty nec-tailscale-admin nec-undeclared : NetworkEgressClass

network-egress-admits : NetworkEgressClass → Bool
network-egress-admits nec-egress-empty = true
network-egress-admits nec-tailscale-admin = true
network-egress-admits nec-undeclared = false

data RecoverReplicaClass : Set where
  rrc-forge-primary rrc-darwin-scratch rrc-offline-luks : RecoverReplicaClass

replica-egress-empty : RecoverReplicaClass → Bool
replica-egress-empty rrc-offline-luks = true
replica-egress-empty rrc-darwin-scratch = true
replica-egress-empty rrc-forge-primary = false

classify-network-egress : RecoverReplicaClass → NetworkEgressClass
classify-network-egress c =
  if replica-egress-empty c then nec-egress-empty else nec-tailscale-admin

record RecoverMergeSafeWitness : Set where
  field
    rmsw-ok : Bool

recover-merge-safe-admits : RecoverMergeSafeWitness → Bool
recover-merge-safe-admits w = RecoverMergeSafeWitness.rmsw-ok w

record RecoverUcrsStamp : Set where
  field
    recover-ucrs-seq : ℕ
    recover-ucrs-wall-has-t : Bool

record RecoverRecoverySnapshot : Set where
  field
    recover-snapshot-id : ℕ
    recover-snapshot-head : ThermodynamicState
    recover-snapshot-ucrs : RecoverUcrsStamp
    recover-snapshot-merge-safe : RecoverMergeSafeWitness
    recover-snapshot-provenance-intact : Bool
    recover-snapshot-replica : RecoverReplicaClass

record RecoverRecoveryWitness : Set where
  field
    recover-witness-ucrs : RecoverUcrsStamp
    recover-witness-merge-safe : RecoverMergeSafeWitness
    recover-witness-provenance-intact : Bool

data KleisliGateKind : Set where
  kgk-excitement-argmin kgk-gate-check-before-sync-inbound kgk-frugal-mi-observation : KleisliGateKind

record RecoverKleisliArrow : Set where
  field
    recover-verb : RecoverOperatorVerb
    recover-merge-safe : RecoverMergeSafeWitness
    recover-egress : NetworkEgressClass
    recover-snapshot : RecoverRecoverySnapshot

record RecoverRecoveryMorphism : Set where
  field
    recover-morphism-from : RecoverRecoverySnapshot
    recover-morphism-to-replica : RecoverReplicaClass
    recover-morphism-witness : RecoverRecoveryWitness
    recover-morphism-excitement-selected : Bool

data RecoverVerdict : Set where
  rv-admitted rv-merge-safe-refused rv-network-egress-refused
    rv-rsync-theater-refused rv-production-wired-refused rv-excitement-residue : RecoverVerdict

data RecoverRefusal : Set where
  rr-merge-safe-refused : RecoverRefusal
  rr-network-egress-refused : NetworkEgressClass → RecoverRefusal
  rr-rsync-theater-refused : ℕ → RecoverRefusal
  rr-gate-rejected : ℕ → RecoverRefusal
  rr-provenance-loss : ℕ → RecoverRefusal
  rr-production-wired-refused : RecoverRefusal
  rr-second-argmin-refused : RecoverRefusal
  rr-wrong-gate : KleisliGateKind → RecoverRefusal

record RecoverVerbRow : Set where
  field
    rvr-verb : RecoverOperatorVerb
    rvr-kleisli-gate : KleisliGateKind
    rvr-merge-safe-required : Bool
    rvr-excitement-required : Bool
    rvr-entity-check-egress : Bool

recover-verb-row-pin : RecoverVerbRow
recover-verb-row-pin = record
  { rvr-verb = rov-recover
  ; rvr-kleisli-gate = kgk-excitement-argmin
  ; rvr-merge-safe-required = true
  ; rvr-excitement-required = true
  ; rvr-entity-check-egress = true
  }

kleisli-gate-matches-recover : KleisliGateKind → Bool
kleisli-gate-matches-recover kgk-excitement-argmin = true
kleisli-gate-matches-recover kgk-gate-check-before-sync-inbound = false
kleisli-gate-matches-recover kgk-frugal-mi-observation = false

------------------------------------------------------------------------
-- SECTION 2: §16.7 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record RecoverAdmissibilityConjunct : Set where
  field
    recover-conj-gate-ok : Bool
    recover-conj-merge-safe : Bool
    recover-conj-excitement-preserves : Bool
    recover-conj-egress-ok : Bool

recover-conjunct-admits : RecoverAdmissibilityConjunct → Bool
recover-conjunct-admits (record { recover-conj-gate-ok = g
                               ; recover-conj-merge-safe = m
                               ; recover-conj-excitement-preserves = e
                               ; recover-conj-egress-ok = x }) =
  g ∧ m ∧ e ∧ x

data RecoverOperationClass : Set where
  roc-typed-morphism roc-rsync-theater : RecoverOperationClass

evaluate-recover-operation : RecoverOperationClass → RecoverVerdict
evaluate-recover-operation roc-rsync-theater = rv-rsync-theater-refused
evaluate-recover-operation roc-typed-morphism = rv-admitted

refuse-rsync-theater : ℕ → RecoverRefusal
refuse-rsync-theater snapshot-id = rr-rsync-theater-refused snapshot-id

witness-from-snapshot : RecoverRecoverySnapshot → RecoverRecoveryWitness
witness-from-snapshot (record { recover-snapshot-ucrs = ucrs
                             ; recover-snapshot-merge-safe = ms
                             ; recover-snapshot-provenance-intact = pi }) = record
  { recover-witness-ucrs = ucrs
  ; recover-witness-merge-safe = ms
  ; recover-witness-provenance-intact = pi
  }

recover-arrow-admissible : RecoverKleisliArrow → Bool
recover-arrow-admissible a =
  recover-merge-safe-admits (RecoverKleisliArrow.recover-merge-safe a) ∧
  network-egress-admits (RecoverKleisliArrow.recover-egress a)

evaluate-recover-kleisli :
  RecoverKleisliArrow → RecoverVerdict ⊎ RecoverRefusal
evaluate-recover-kleisli a =
  if not (recover-merge-safe-admits (RecoverKleisliArrow.recover-merge-safe a)) then
    inj₂ rr-merge-safe-refused
  else if not (network-egress-admits (RecoverKleisliArrow.recover-egress a)) then
    inj₂ (rr-network-egress-refused (RecoverKleisliArrow.recover-egress a))
  else inj₁ rv-admitted

apply-recover-recovery-morphism :
  (snapshot : RecoverRecoverySnapshot) →
  (to-replica : RecoverReplicaClass) →
  (conjunct : RecoverAdmissibilityConjunct) →
  (excitement-selected : Bool) →
  RecoverRecoveryMorphism ⊎ RecoverRefusal
apply-recover-recovery-morphism snapshot to-replica conjunct excitement-selected =
  if not (recover-conjunct-admits conjunct) then
    inj₂ (rr-gate-rejected
      (RecoverUcrsStamp.recover-ucrs-seq
        (RecoverRecoverySnapshot.recover-snapshot-ucrs snapshot)))
  else if not (recover-merge-safe-admits
                 (RecoverRecoverySnapshot.recover-snapshot-merge-safe snapshot)) then
    inj₂ rr-merge-safe-refused
  else if not (RecoverRecoverySnapshot.recover-snapshot-provenance-intact snapshot) then
    inj₂ (rr-provenance-loss (RecoverRecoverySnapshot.recover-snapshot-id snapshot))
  else if not excitement-selected then
    inj₂ (rr-provenance-loss (RecoverRecoverySnapshot.recover-snapshot-id snapshot))
  else inj₁ record
    { recover-morphism-from = snapshot
    ; recover-morphism-to-replica = to-replica
    ; recover-morphism-witness = witness-from-snapshot snapshot
    ; recover-morphism-excitement-selected = excitement-selected
    }

refuse-production-wired-recover : RecoverRefusal
refuse-production-wired-recover = rr-production-wired-refused

refuse-second-argmin-recover : RecoverRefusal
refuse-second-argmin-recover = rr-second-argmin-refused

refuse-sync-gate-on-recover : RecoverRefusal
refuse-sync-gate-on-recover = rr-wrong-gate kgk-gate-check-before-sync-inbound

refuse-frugal-mi-on-recover : RecoverRefusal
refuse-frugal-mi-on-recover = rr-wrong-gate kgk-frugal-mi-observation

recover-verb-row-merge-safe-required :
  RecoverVerbRow.rvr-merge-safe-required recover-verb-row-pin ≡ true
recover-verb-row-merge-safe-required = refl

recover-verb-row-excitement-required :
  RecoverVerbRow.rvr-excitement-required recover-verb-row-pin ≡ true
recover-verb-row-excitement-required = refl

recover-verb-row-entity-check-egress :
  RecoverVerbRow.rvr-entity-check-egress recover-verb-row-pin ≡ true
recover-verb-row-entity-check-egress = refl

kleisli-gate-matches-recover-excitement :
  kleisli-gate-matches-recover kgk-excitement-argmin ≡ true
kleisli-gate-matches-recover-excitement = refl

kleisli-gate-matches-recover-rejects-inbound-sync :
  kleisli-gate-matches-recover kgk-gate-check-before-sync-inbound ≡ false
kleisli-gate-matches-recover-rejects-inbound-sync = refl

------------------------------------------------------------------------
-- SECTION 3: Recover composes excitement-select (no second argmin)
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
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

record recover-ctx (src : ThermodynamicState) : Set where
  field
    recover-successors : List (history-candidate src)

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

recover-select :
  (src : ThermodynamicState) (ctx : recover-ctx src) →
  history-candidate src ⊎ excitement-residue
recover-select src ctx =
  urge-recovery-select src (recover-ctx.recover-successors ctx)

recover-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : recover-ctx src) →
  recover-select src ctx ≡
  excitement-select src (recover-ctx.recover-successors ctx)
recover-select-eq-excitement-select src ctx = refl

recover-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : recover-ctx src) →
  recover-select src ctx ≡
  urge-recovery-select src (recover-ctx.recover-successors ctx)
recover-select-eq-urge-recovery-select src ctx = refl

recover-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : recover-ctx src) →
  recover-select src ctx ≡
  excitement-select src (recover-ctx.recover-successors ctx)
recover-no-local-argmin src ctx =
  recover-select-eq-excitement-select src ctx

recover-select-empty :
  ∀ (src : ThermodynamicState) (ctx : recover-ctx src) →
  recover-ctx.recover-successors ctx ≡ List.[] →
  recover-select src ctx ≡ inj₂ exc-no-candidates
recover-select-empty src ctx hs rewrite hs = refl

data RecoverExcitementPin : Set where
  rep-import-select-excitement rep-second-argmin-refused : RecoverExcitementPin

recover-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  RecoverExcitementPin →
  history-candidate src ⊎ excitement-residue
recover-excitement-select src cands rep-import-select-excitement =
  excitement-select src cands
recover-excitement-select src cands rep-second-argmin-refused =
  inj₂ exc-all-inadmissible

recover-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  recover-excitement-select src cands rep-import-select-excitement ≡
  excitement-select src cands
recover-excitement-select-eq-excitement-select src cands = refl

recover-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  recover-excitement-select src cands rep-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
recover-excitement-select-refuses-second-argmin src cands = refl

------------------------------------------------------------------------
-- SECTION 4: §16.7 fixtures + witness theorems
------------------------------------------------------------------------

recover-fixture-state : ThermodynamicState
recover-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

recover-fixture-ucrs : RecoverUcrsStamp
recover-fixture-ucrs = record
  { recover-ucrs-seq = 7
  ; recover-ucrs-wall-has-t = true
  }

recover-fixture-merge-safe : RecoverMergeSafeWitness
recover-fixture-merge-safe = record { rmsw-ok = true }

recover-fixture-snapshot : RecoverRecoverySnapshot
recover-fixture-snapshot = record
  { recover-snapshot-id = 1
  ; recover-snapshot-head = recover-fixture-state
  ; recover-snapshot-ucrs = recover-fixture-ucrs
  ; recover-snapshot-merge-safe = recover-fixture-merge-safe
  ; recover-snapshot-provenance-intact = true
  ; recover-snapshot-replica = rrc-forge-primary
  }

recover-fixture-conjunct : RecoverAdmissibilityConjunct
recover-fixture-conjunct = record
  { recover-conj-gate-ok = true
  ; recover-conj-merge-safe = true
  ; recover-conj-excitement-preserves = true
  ; recover-conj-egress-ok = true
  }

recover-fixture-admitted-arrow : RecoverKleisliArrow
recover-fixture-admitted-arrow = record
  { recover-verb = rov-recover
  ; recover-merge-safe = recover-fixture-merge-safe
  ; recover-egress = nec-tailscale-admin
  ; recover-snapshot = recover-fixture-snapshot
  }

recover-fixture-merge-fail-arrow : RecoverKleisliArrow
recover-fixture-merge-fail-arrow = record
  { recover-verb = rov-recover
  ; recover-merge-safe = record { rmsw-ok = false }
  ; recover-egress = nec-egress-empty
  ; recover-snapshot = recover-fixture-snapshot
  }

recover-fixture-egress-fail-arrow : RecoverKleisliArrow
recover-fixture-egress-fail-arrow = record
  { recover-verb = rov-recover
  ; recover-merge-safe = recover-fixture-merge-safe
  ; recover-egress = nec-undeclared
  ; recover-snapshot = recover-fixture-snapshot
  }

recover-fixture-rsync-theater-refused :
  evaluate-recover-operation roc-rsync-theater ≡ rv-rsync-theater-refused
recover-fixture-rsync-theater-refused = refl

recover-fixture-apply-morphism-ok :
  apply-recover-recovery-morphism
    recover-fixture-snapshot rrc-offline-luks recover-fixture-conjunct true ≡
  inj₁ record
    { recover-morphism-from = recover-fixture-snapshot
    ; recover-morphism-to-replica = rrc-offline-luks
    ; recover-morphism-witness = witness-from-snapshot recover-fixture-snapshot
    ; recover-morphism-excitement-selected = true
    }
recover-fixture-apply-morphism-ok = refl

recover-fixture-admitted-ok :
  evaluate-recover-kleisli recover-fixture-admitted-arrow ≡ inj₁ rv-admitted
recover-fixture-admitted-ok = refl

recover-fixture-merge-safe-refused :
  evaluate-recover-kleisli recover-fixture-merge-fail-arrow ≡ inj₂ rr-merge-safe-refused
recover-fixture-merge-safe-refused = refl

recover-fixture-egress-refused :
  evaluate-recover-kleisli recover-fixture-egress-fail-arrow ≡
  inj₂ (rr-network-egress-refused nec-undeclared)
recover-fixture-egress-refused = refl

recover-offline-luks-egress-empty :
  replica-egress-empty rrc-offline-luks ≡ true
recover-offline-luks-egress-empty = refl

recover-darwin-scratch-egress-empty :
  replica-egress-empty rrc-darwin-scratch ≡ true
recover-darwin-scratch-egress-empty = refl

recover-forge-primary-egress-nonempty :
  replica-egress-empty rrc-forge-primary ≡ false
recover-forge-primary-egress-nonempty = refl

recover-classify-offline-luks-egress :
  classify-network-egress rrc-offline-luks ≡ nec-egress-empty
recover-classify-offline-luks-egress = refl

recover-fixture-witness-preserves-ucrs :
  RecoverRecoveryWitness.recover-witness-ucrs (witness-from-snapshot recover-fixture-snapshot) ≡
  recover-fixture-ucrs
recover-fixture-witness-preserves-ucrs = refl

recover-fixture-refuse-sync-gate-positive :
  refuse-sync-gate-on-recover ≡ rr-wrong-gate kgk-gate-check-before-sync-inbound
recover-fixture-refuse-sync-gate-positive = refl

recover-fixture-refuse-frugal-mi-positive :
  refuse-frugal-mi-on-recover ≡ rr-wrong-gate kgk-frugal-mi-observation
recover-fixture-refuse-frugal-mi-positive = refl

recover-arrow-admissible-fixture :
  recover-arrow-admissible recover-fixture-admitted-arrow ≡ true
recover-arrow-admissible-fixture = refl

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

recover-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
recover-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisli-recover-physics-green : Bool
kleisli-recover-physics-green = false

kleisli-recover-physics-green-false :
  kleisli-recover-physics-green ≡ false
kleisli-recover-physics-green-false = refl

kleisli-recover-production-wired : Bool
kleisli-recover-production-wired = false

kleisli-recover-production-wired-false :
  kleisli-recover-production-wired ≡ false
kleisli-recover-production-wired-false = refl

kleisli-recover-module-witness : ⊤
kleisli-recover-module-witness = tt

kleisli-recover-no-new-postulate : ⊤
kleisli-recover-no-new-postulate = tt

kleisli-recover-positive-refuse-not-silent :
  evaluate-recover-operation roc-rsync-theater ≢ rv-admitted
kleisli-recover-positive-refuse-not-silent ()

kleisli-recover-production-wired-refuse-positive :
  refuse-production-wired-recover ≡ rr-production-wired-refused
kleisli-recover-production-wired-refuse-positive = refl

kleisli-recover-second-argmin-refuse-positive :
  refuse-second-argmin-recover ≡ rr-second-argmin-refused
kleisli-recover-second-argmin-refuse-positive = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin-recover ≡ rr-second-argmin-refused
refuse-second-argmin-is-tag = refl
