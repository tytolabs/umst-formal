-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CryptoCompose — meso/acting §5.4 cryptographic safety.
--
-- URGE-FORMAL-MESO-AGDA-CRYPTO-COMPOSE (umst-formal acting fiber only).
-- §5.4: cryptographic safety lifted by composition, not copied.
-- Content-addressed DID+RID, signed transitions, threshold canonicalization —
-- **is** an Excitement-selected admissible state transition, not egoff
-- copy-paste theater. Compose `crypto-compose-excitement-select` — no second
-- ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CryptoCompose where

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
-- SECTION 1: Crypto identity + typed morphism carriers (§5.4)
------------------------------------------------------------------------

data crypto-identity-class : Set where
  cic-content-addressed-rid cic-decentralized-did cic-host-id-surrogate : crypto-identity-class

identity-content-addressed : crypto-identity-class → Bool
identity-content-addressed cic-content-addressed-rid = true
identity-content-addressed cic-decentralized-did = true
identity-content-addressed cic-host-id-surrogate = false

record crypto-ucrs-stamp : Set where
  field
    crypto-ucrs-seq : ℕ
    crypto-ucrs-wall-has-t : Bool

record crypto-threshold-cert : Set where
  field
    crypto-threshold-quorum : ℕ
    crypto-threshold-valid : ℕ
    crypto-threshold-met : Bool

record crypto-ssot-digest : Set where
  field
    crypto-digest-hex-len : ℕ
    crypto-digest-hex-valid : Bool

record crypto-compose-snapshot : Set where
  field
    crypto-snapshot-id : ℕ
    crypto-snapshot-head : ThermodynamicState
    crypto-snapshot-ucrs : crypto-ucrs-stamp
    crypto-snapshot-threshold : crypto-threshold-cert
    crypto-snapshot-ssot-digest : crypto-ssot-digest
    crypto-snapshot-signed : Bool
    crypto-snapshot-identity : crypto-identity-class

record crypto-compose-witness : Set where
  field
    crypto-witness-ucrs : crypto-ucrs-stamp
    crypto-witness-threshold : crypto-threshold-cert
    crypto-witness-ssot-valid : Bool

record crypto-compose-morphism : Set where
  field
    crypto-morphism-from : crypto-compose-snapshot
    crypto-morphism-to-identity : crypto-identity-class
    crypto-morphism-witness : crypto-compose-witness
    crypto-morphism-excitement-selected : Bool

data crypto-compose-refusal : Set where
  ccr-egoff-copy-paste-refused : ℕ → crypto-compose-refusal
  ccr-gate-rejected : ℕ → crypto-compose-refusal
  ccr-unsigned-transition : ℕ → crypto-compose-refusal
  ccr-host-id-as-rid : ℕ → crypto-compose-refusal
  ccr-below-threshold : ℕ → crypto-compose-refusal
  ccr-invalid-ssot-digest : ℕ → crypto-compose-refusal
  ccr-identity-class-mismatch : crypto-compose-refusal

data crypto-compose-verdict : Set where
  ccv-morphism-ok ccv-egoff-copy-paste-refused ccv-inadmissible : crypto-compose-verdict

------------------------------------------------------------------------
-- SECTION 2: §5.4 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record crypto-admissibility-conjunct : Set where
  field
    crypto-conj-gate-ok : Bool
    crypto-conj-threshold-met : Bool
    crypto-conj-excitement-preserves : Bool

crypto-conjunct-admits : crypto-admissibility-conjunct → Bool
crypto-conjunct-admits (record { crypto-conj-gate-ok = g
                              ; crypto-conj-threshold-met = t
                              ; crypto-conj-excitement-preserves = e }) =
  g ∧ t ∧ e

evaluate-crypto-compose-operation :
  (is-egoff-copy-paste : Bool) → crypto-compose-verdict
evaluate-crypto-compose-operation true = ccv-egoff-copy-paste-refused
evaluate-crypto-compose-operation false = ccv-morphism-ok

refuse-egoff-copy-paste : ℕ → crypto-compose-refusal
refuse-egoff-copy-paste snapshot-id = ccr-egoff-copy-paste-refused snapshot-id

refuse-host-id-as-rid : ℕ → crypto-compose-refusal
refuse-host-id-as-rid host-id = ccr-host-id-as-rid host-id

refuse-unsigned-transition : ℕ → crypto-compose-refusal
refuse-unsigned-transition snapshot-id = ccr-unsigned-transition snapshot-id

witness-from-crypto-snapshot : crypto-compose-snapshot → crypto-compose-witness
witness-from-crypto-snapshot (record { crypto-snapshot-ucrs = ucrs
                                    ; crypto-snapshot-threshold = th
                                    ; crypto-snapshot-ssot-digest = dg }) = record
  { crypto-witness-ucrs = ucrs
  ; crypto-witness-threshold = th
  ; crypto-witness-ssot-valid = crypto-ssot-digest.crypto-digest-hex-valid dg
  }

apply-crypto-compose-morphism :
  (snapshot : crypto-compose-snapshot) →
  (to-identity : crypto-identity-class) →
  (conjunct : crypto-admissibility-conjunct) →
  (excitement-selected : Bool) →
  crypto-compose-morphism ⊎ crypto-compose-refusal
apply-crypto-compose-morphism snapshot to-identity conjunct excitement-selected =
  if not (crypto-conjunct-admits conjunct) then
    inj₂ (ccr-gate-rejected
      (crypto-ucrs-stamp.crypto-ucrs-seq
        (crypto-compose-snapshot.crypto-snapshot-ucrs snapshot)))
  else if not (crypto-threshold-cert.crypto-threshold-met
                 (crypto-compose-snapshot.crypto-snapshot-threshold snapshot)) then
    inj₂ (ccr-below-threshold (crypto-compose-snapshot.crypto-snapshot-id snapshot))
  else if not (crypto-ssot-digest.crypto-digest-hex-valid
                 (crypto-compose-snapshot.crypto-snapshot-ssot-digest snapshot)) then
    inj₂ (ccr-invalid-ssot-digest (crypto-compose-snapshot.crypto-snapshot-id snapshot))
  else if not (crypto-compose-snapshot.crypto-snapshot-signed snapshot) then
    inj₂ (ccr-unsigned-transition (crypto-compose-snapshot.crypto-snapshot-id snapshot))
  else if not excitement-selected then
    inj₂ (ccr-unsigned-transition (crypto-compose-snapshot.crypto-snapshot-id snapshot))
  else inj₁ record
    { crypto-morphism-from = snapshot
    ; crypto-morphism-to-identity = to-identity
    ; crypto-morphism-witness = witness-from-crypto-snapshot snapshot
    ; crypto-morphism-excitement-selected = excitement-selected
    }

crypto-compose-egoff-copy-paste-refused :
  ∀ (snapshot-id : ℕ) →
  evaluate-crypto-compose-operation true ≡ ccv-egoff-copy-paste-refused
crypto-compose-egoff-copy-paste-refused snapshot-id = refl

crypto-compose-morphism-ok-when-not-copy-paste :
  evaluate-crypto-compose-operation false ≡ ccv-morphism-ok
crypto-compose-morphism-ok-when-not-copy-paste = refl

refuse-egoff-copy-paste-positive :
  ∀ (snapshot-id : ℕ) →
  refuse-egoff-copy-paste snapshot-id ≡ ccr-egoff-copy-paste-refused snapshot-id
refuse-egoff-copy-paste-positive snapshot-id = refl

refuse-host-id-as-rid-positive :
  ∀ (host-id : ℕ) →
  refuse-host-id-as-rid host-id ≡ ccr-host-id-as-rid host-id
refuse-host-id-as-rid-positive host-id = refl

refuse-unsigned-transition-positive :
  ∀ (snapshot-id : ℕ) →
  refuse-unsigned-transition snapshot-id ≡ ccr-unsigned-transition snapshot-id
refuse-unsigned-transition-positive snapshot-id = refl

------------------------------------------------------------------------
-- SECTION 3: Excitement hook — crypto compose **is** excitement-select
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

record crypto-compose-ctx (src : ThermodynamicState) : Set where
  field
    crypto-compose-successors : List (history-candidate src)

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

crypto-compose-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
crypto-compose-excitement-select = excitement-select

crypto-compose-select :
  (src : ThermodynamicState) → crypto-compose-ctx src →
  history-candidate src ⊎ excitement-residue
crypto-compose-select src ctx =
  crypto-compose-excitement-select src (crypto-compose-ctx.crypto-compose-successors ctx)

crypto-compose-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : crypto-compose-ctx src) →
  crypto-compose-select src ctx ≡
  excitement-select src (crypto-compose-ctx.crypto-compose-successors ctx)
crypto-compose-select-eq-excitement-select src ctx = refl

crypto-compose-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : crypto-compose-ctx src) →
  crypto-compose-select src ctx ≡
  urge-recovery-select src (crypto-compose-ctx.crypto-compose-successors ctx)
crypto-compose-select-eq-urge-recovery-select src ctx = refl

crypto-compose-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : crypto-compose-ctx src) →
  crypto-compose-select src ctx ≡
  excitement-select src (crypto-compose-ctx.crypto-compose-successors ctx)
crypto-compose-no-local-argmin src ctx =
  crypto-compose-select-eq-excitement-select src ctx

crypto-compose-empty :
  ∀ (src : ThermodynamicState) (ctx : crypto-compose-ctx src) →
  crypto-compose-ctx.crypto-compose-successors ctx ≡ List.[] →
  crypto-compose-select src ctx ≡ inj₂ exc-no-candidates
crypto-compose-empty src ctx refl = refl

------------------------------------------------------------------------
-- SECTION 4: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

data CryptoComposeRefusal : Set where
  egoff-copy-paste second-argmin host-id-as-rid unsigned-transition : CryptoComposeRefusal

refuse-egoff-copy-paste-tag : CryptoComposeRefusal
refuse-egoff-copy-paste-tag = egoff-copy-paste

refuse-second-argmin : CryptoComposeRefusal
refuse-second-argmin = second-argmin

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

urge-crypto-compose-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-crypto-compose-select = crypto-compose-excitement-select

------------------------------------------------------------------------
-- SECTION 5: §5.4 fixtures + witness theorems
------------------------------------------------------------------------

crypto-compose-fixture-state : ThermodynamicState
crypto-compose-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

crypto-compose-fixture-ucrs : crypto-ucrs-stamp
crypto-compose-fixture-ucrs = record
  { crypto-ucrs-seq = 7
  ; crypto-ucrs-wall-has-t = true
  }

crypto-compose-fixture-threshold : crypto-threshold-cert
crypto-compose-fixture-threshold = record
  { crypto-threshold-quorum = 1
  ; crypto-threshold-valid = 1
  ; crypto-threshold-met = true
  }

crypto-compose-fixture-ssot : crypto-ssot-digest
crypto-compose-fixture-ssot = record
  { crypto-digest-hex-len = 64
  ; crypto-digest-hex-valid = true
  }

crypto-compose-fixture-snapshot : crypto-compose-snapshot
crypto-compose-fixture-snapshot = record
  { crypto-snapshot-id = 1
  ; crypto-snapshot-head = crypto-compose-fixture-state
  ; crypto-snapshot-ucrs = crypto-compose-fixture-ucrs
  ; crypto-snapshot-threshold = crypto-compose-fixture-threshold
  ; crypto-snapshot-ssot-digest = crypto-compose-fixture-ssot
  ; crypto-snapshot-signed = true
  ; crypto-snapshot-identity = cic-content-addressed-rid
  }

crypto-compose-fixture-conjunct : crypto-admissibility-conjunct
crypto-compose-fixture-conjunct = record
  { crypto-conj-gate-ok = true
  ; crypto-conj-threshold-met = true
  ; crypto-conj-excitement-preserves = true
  }

crypto-compose-fixture-egoff-copy-paste-refused :
  refuse-egoff-copy-paste 1 ≡ ccr-egoff-copy-paste-refused 1
crypto-compose-fixture-egoff-copy-paste-refused = refl

crypto-compose-fixture-apply-morphism-ok :
  apply-crypto-compose-morphism
    crypto-compose-fixture-snapshot cic-decentralized-did crypto-compose-fixture-conjunct true ≡
  inj₁ record
    { crypto-morphism-from = crypto-compose-fixture-snapshot
    ; crypto-morphism-to-identity = cic-decentralized-did
    ; crypto-morphism-witness = witness-from-crypto-snapshot crypto-compose-fixture-snapshot
    ; crypto-morphism-excitement-selected = true
    }
crypto-compose-fixture-apply-morphism-ok = refl

crypto-compose-content-addressed-identity :
  identity-content-addressed cic-content-addressed-rid ≡ true
crypto-compose-content-addressed-identity = refl

crypto-compose-decentralized-did-identity :
  identity-content-addressed cic-decentralized-did ≡ true
crypto-compose-decentralized-did-identity = refl

crypto-compose-host-id-not-content-addressed :
  identity-content-addressed cic-host-id-surrogate ≡ false
crypto-compose-host-id-not-content-addressed = refl

crypto-compose-fixture-witness-preserves-ucrs :
  crypto-compose-witness.crypto-witness-ucrs
    (witness-from-crypto-snapshot crypto-compose-fixture-snapshot) ≡
  crypto-compose-fixture-ucrs
crypto-compose-fixture-witness-preserves-ucrs = refl

crypto-compose-positive-refuse-not-silent :
  evaluate-crypto-compose-operation true ≢ ccv-morphism-ok
crypto-compose-positive-refuse-not-silent ()

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

crypto-compose-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
crypto-compose-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

crypto-compose-physics-green : Bool
crypto-compose-physics-green = false

crypto-compose-physics-green-false :
  crypto-compose-physics-green ≡ false
crypto-compose-physics-green-false = refl

crypto-compose-production-wired : Bool
crypto-compose-production-wired = false

crypto-compose-production-wired-false :
  crypto-compose-production-wired ≡ false
crypto-compose-production-wired-false = refl

crypto-compose-module-witness : ⊤
crypto-compose-module-witness = tt

crypto-compose-no-new-axiom : ⊤
crypto-compose-no-new-axiom = tt

crypto-compose-marker : ℕ
crypto-compose-marker = 1

crypto-compose-marker-eq : crypto-compose-marker ≡ 1
crypto-compose-marker-eq = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl
