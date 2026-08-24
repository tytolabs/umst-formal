-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.BackupRecovery — meso/acting §15.4 backup recovery.
--
-- URGE-FORMAL-MESO-AGDA-BACKUP-RECOVERY (umst-formal acting fiber only).
-- §15.4: backup is a typed recovery morphism — not rsync theater. Backup
-- **is** Excitement-selected admissible state transition. Compose
-- `backup-recovery-select` / `excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.BackupRecovery where

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
-- SECTION 1: Recovery snapshot + typed morphism carriers (§15.4)
------------------------------------------------------------------------

data backup-replica-class : Set where
  brc-forge-primary brc-darwin-scratch brc-offline-luks : backup-replica-class

replica-egress-empty : backup-replica-class → Bool
replica-egress-empty brc-offline-luks = true
replica-egress-empty brc-darwin-scratch = true
replica-egress-empty brc-forge-primary = false

record backup-ucrs-stamp : Set where
  field
    backup-ucrs-seq : ℕ
    backup-ucrs-wall-has-t : Bool

record backup-merge-safe-cert : Set where
  field
    backup-merge-safe : Bool

record backup-recovery-snapshot : Set where
  field
    backup-snapshot-id : ℕ
    backup-snapshot-head : ThermodynamicState
    backup-snapshot-ucrs : backup-ucrs-stamp
    backup-snapshot-merge-safe : backup-merge-safe-cert
    backup-snapshot-provenance-intact : Bool
    backup-snapshot-replica : backup-replica-class

record backup-recovery-witness : Set where
  field
    backup-witness-ucrs : backup-ucrs-stamp
    backup-witness-merge-safe : backup-merge-safe-cert
    backup-witness-provenance-intact : Bool

record backup-recovery-morphism : Set where
  field
    backup-morphism-from : backup-recovery-snapshot
    backup-morphism-to-replica : backup-replica-class
    backup-morphism-witness : backup-recovery-witness
    backup-morphism-excitement-selected : Bool

data backup-recovery-refusal : Set where
  brr-rsync-theater-refused : ℕ → backup-recovery-refusal
  brr-gate-rejected : ℕ → backup-recovery-refusal
  brr-merge-unsafe : ℕ → backup-recovery-refusal
  brr-provenance-loss : ℕ → backup-recovery-refusal
  brr-replica-class-mismatch : backup-recovery-refusal

data backup-recovery-verdict : Set where
  brv-morphism-ok brv-rsync-theater-refused brv-inadmissible : backup-recovery-verdict

------------------------------------------------------------------------
-- SECTION 2: §15.4 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record backup-admissibility-conjunct : Set where
  field
    backup-conj-gate-ok : Bool
    backup-conj-merge-safe : Bool
    backup-conj-excitement-preserves : Bool

backup-conjunct-admits : backup-admissibility-conjunct → Bool
backup-conjunct-admits (record { backup-conj-gate-ok = g
                               ; backup-conj-merge-safe = m
                               ; backup-conj-excitement-preserves = e }) =
  g ∧ m ∧ e

evaluate-backup-recovery-operation :
  (is-rsync-theater : Bool) → backup-recovery-verdict
evaluate-backup-recovery-operation true = brv-rsync-theater-refused
evaluate-backup-recovery-operation false = brv-morphism-ok

refuse-rsync-theater : ℕ → backup-recovery-refusal
refuse-rsync-theater snapshot-id = brr-rsync-theater-refused snapshot-id

witness-from-snapshot : backup-recovery-snapshot → backup-recovery-witness
witness-from-snapshot (record { backup-snapshot-ucrs = ucrs
                             ; backup-snapshot-merge-safe = ms
                             ; backup-snapshot-provenance-intact = pi }) = record
  { backup-witness-ucrs = ucrs
  ; backup-witness-merge-safe = ms
  ; backup-witness-provenance-intact = pi
  }

apply-backup-recovery-morphism :
  (snapshot : backup-recovery-snapshot) →
  (to-replica : backup-replica-class) →
  (conjunct : backup-admissibility-conjunct) →
  (excitement-selected : Bool) →
  backup-recovery-morphism ⊎ backup-recovery-refusal
apply-backup-recovery-morphism snapshot to-replica conjunct excitement-selected =
  if not (backup-conjunct-admits conjunct) then
    inj₂ (brr-gate-rejected
      (backup-ucrs-stamp.backup-ucrs-seq
        (backup-recovery-snapshot.backup-snapshot-ucrs snapshot)))
  else if not (backup-merge-safe-cert.backup-merge-safe
                 (backup-recovery-snapshot.backup-snapshot-merge-safe snapshot)) then
    inj₂ (brr-merge-unsafe (backup-recovery-snapshot.backup-snapshot-id snapshot))
  else if not (backup-recovery-snapshot.backup-snapshot-provenance-intact snapshot) then
    inj₂ (brr-provenance-loss (backup-recovery-snapshot.backup-snapshot-id snapshot))
  else if not excitement-selected then
    inj₂ (brr-provenance-loss (backup-recovery-snapshot.backup-snapshot-id snapshot))
  else inj₁ record
    { backup-morphism-from = snapshot
    ; backup-morphism-to-replica = to-replica
    ; backup-morphism-witness = witness-from-snapshot snapshot
    ; backup-morphism-excitement-selected = excitement-selected
    }

backup-recovery-rsync-theater-refused :
  ∀ (snapshot-id : ℕ) →
  evaluate-backup-recovery-operation true ≡ brv-rsync-theater-refused
backup-recovery-rsync-theater-refused snapshot-id = refl

backup-recovery-morphism-ok-when-not-rsync :
  evaluate-backup-recovery-operation false ≡ brv-morphism-ok
backup-recovery-morphism-ok-when-not-rsync = refl

refuse-rsync-theater-positive :
  ∀ (snapshot-id : ℕ) →
  refuse-rsync-theater snapshot-id ≡ brr-rsync-theater-refused snapshot-id
refuse-rsync-theater-positive snapshot-id = refl

------------------------------------------------------------------------
-- SECTION 3: Excitement hook — recovery **is** excitement-select
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

record backup-recovery-ctx (src : ThermodynamicState) : Set where
  field
    backup-recovery-successors : List (history-candidate src)

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

backup-recovery-select :
  (src : ThermodynamicState) → backup-recovery-ctx src →
  history-candidate src ⊎ excitement-residue
backup-recovery-select src ctx =
  urge-recovery-select src (backup-recovery-ctx.backup-recovery-successors ctx)

backup-recovery-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : backup-recovery-ctx src) →
  backup-recovery-select src ctx ≡
  excitement-select src (backup-recovery-ctx.backup-recovery-successors ctx)
backup-recovery-select-eq-excitement-select src ctx = refl

backup-recovery-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : backup-recovery-ctx src) →
  backup-recovery-select src ctx ≡
  urge-recovery-select src (backup-recovery-ctx.backup-recovery-successors ctx)
backup-recovery-select-eq-urge-recovery-select src ctx = refl

backup-recovery-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : backup-recovery-ctx src) →
  backup-recovery-select src ctx ≡
  excitement-select src (backup-recovery-ctx.backup-recovery-successors ctx)
backup-recovery-no-local-argmin src ctx =
  backup-recovery-select-eq-excitement-select src ctx

backup-recovery-empty :
  ∀ (src : ThermodynamicState) (ctx : backup-recovery-ctx src) →
  backup-recovery-ctx.backup-recovery-successors ctx ≡ List.[] →
  backup-recovery-select src ctx ≡ inj₂ exc-no-candidates
backup-recovery-empty src ctx refl = refl

urge-recovery-admissible :
  ∀ (src : ThermodynamicState) (successors : List (history-candidate src))
    (c : history-candidate src) →
  urge-recovery-select src successors ≡ inj₁ c →
  Admissible src (history-candidate.cand-tgt c)
urge-recovery-admissible src (h ∷ _) c eq with eq
... | refl = history-candidate.cand-admissible h

------------------------------------------------------------------------
-- SECTION 4: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

data BackupRecoveryRefusal : Set where
  rsync-theater second-argmin mi-unpaid : BackupRecoveryRefusal

refuse-rsync-theater-tag : BackupRecoveryRefusal
refuse-rsync-theater-tag = rsync-theater

refuse-second-argmin : BackupRecoveryRefusal
refuse-second-argmin = second-argmin

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

urge-backup-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-backup-select = excitement-select

------------------------------------------------------------------------
-- SECTION 5: §15.4 fixtures + witness theorems
------------------------------------------------------------------------

backup-fixture-state : ThermodynamicState
backup-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

backup-fixture-ucrs : backup-ucrs-stamp
backup-fixture-ucrs = record
  { backup-ucrs-seq = 7
  ; backup-ucrs-wall-has-t = true
  }

backup-fixture-merge-safe : backup-merge-safe-cert
backup-fixture-merge-safe = record { backup-merge-safe = true }

backup-fixture-snapshot : backup-recovery-snapshot
backup-fixture-snapshot = record
  { backup-snapshot-id = 1
  ; backup-snapshot-head = backup-fixture-state
  ; backup-snapshot-ucrs = backup-fixture-ucrs
  ; backup-snapshot-merge-safe = backup-fixture-merge-safe
  ; backup-snapshot-provenance-intact = true
  ; backup-snapshot-replica = brc-forge-primary
  }

backup-fixture-conjunct : backup-admissibility-conjunct
backup-fixture-conjunct = record
  { backup-conj-gate-ok = true
  ; backup-conj-merge-safe = true
  ; backup-conj-excitement-preserves = true
  }

backup-fixture-rsync-theater-refused :
  refuse-rsync-theater 1 ≡ brr-rsync-theater-refused 1
backup-fixture-rsync-theater-refused = refl

backup-fixture-apply-morphism-ok :
  apply-backup-recovery-morphism
    backup-fixture-snapshot brc-offline-luks backup-fixture-conjunct true ≡
  inj₁ record
    { backup-morphism-from = backup-fixture-snapshot
    ; backup-morphism-to-replica = brc-offline-luks
    ; backup-morphism-witness = witness-from-snapshot backup-fixture-snapshot
    ; backup-morphism-excitement-selected = true
    }
backup-fixture-apply-morphism-ok = refl

backup-offline-luks-egress-empty :
  replica-egress-empty brc-offline-luks ≡ true
backup-offline-luks-egress-empty = refl

backup-darwin-scratch-egress-empty :
  replica-egress-empty brc-darwin-scratch ≡ true
backup-darwin-scratch-egress-empty = refl

backup-forge-primary-egress-nonempty :
  replica-egress-empty brc-forge-primary ≡ false
backup-forge-primary-egress-nonempty = refl

backup-fixture-witness-preserves-ucrs :
  backup-recovery-witness.backup-witness-ucrs (witness-from-snapshot backup-fixture-snapshot) ≡
  backup-fixture-ucrs
backup-fixture-witness-preserves-ucrs = refl

backup-recovery-positive-refuse-not-silent :
  evaluate-backup-recovery-operation true ≢ brv-morphism-ok
backup-recovery-positive-refuse-not-silent ()

------------------------------------------------------------------------
-- SECTION 6: Typed history + Landauer bridge (zero new postulates)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head : ThermodynamicState

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

backup-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
backup-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

backup-recovery-physics-green : Bool
backup-recovery-physics-green = false

backup-recovery-physics-green-false :
  backup-recovery-physics-green ≡ false
backup-recovery-physics-green-false = refl

backup-recovery-production-wired : Bool
backup-recovery-production-wired = false

backup-recovery-production-wired-false :
  backup-recovery-production-wired ≡ false
backup-recovery-production-wired-false = refl

backup-recovery-module-witness : ⊤
backup-recovery-module-witness = tt

backup-recovery-no-new-axiom : ⊤
backup-recovery-no-new-axiom = tt

backup-recovery-marker : ℕ
backup-recovery-marker = 1

backup-recovery-marker-eq : backup-recovery-marker ≡ 1
backup-recovery-marker-eq = refl
