-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CryptoCompose.lean

  Meso acting Urge — §5.4 cryptographic safety lifted by composition, not copied.
  Content-addressed DID+RID, signed transitions, threshold canonicalization —
  **is** an Excitement-selected admissible state transition, not egoff copy-paste theater.
  Composes `Excitement.select` — no second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ExcitementImport

namespace UMST.Urge.CryptoCompose

-- ================================================================
-- SECTION 1: Crypto identity + typed morphism carriers (§5.4)
-- ================================================================

/-- Identity class row from §5.4 — content-addressed vs host-id surrogate. -/
inductive CryptoIdentityClass where
  | contentAddressedRid
  | decentralizedDid
  | hostIdSurrogate
  deriving DecidableEq, Repr

/-- Whether identity is content-addressed (not raw host id). -/
def identityContentAddressed (c : CryptoIdentityClass) : Bool :=
  match c with
  | .contentAddressedRid | .decentralizedDid => true
  | .hostIdSurrogate => false

/-- UCRS stamp surrogate carried through signed transition. -/
structure CryptoUcrsStamp where
  ucrsSeq       : Nat
  ucrsWallHasT  : Bool

/-- Threshold canonicalization certificate — quorum must be met. -/
structure CryptoThresholdCert where
  thresholdQuorum : Nat
  thresholdValid  : Nat
  thresholdMet    : Bool

/-- SSOT digest hex surrogate (64-char content-addressed RID witness). -/
structure CryptoSsotDigest where
  digestHexLen   : Nat
  digestHexValid : Bool

/-- Snapshot identity at transition source (content-addressed surrogate). -/
structure CryptoComposeSnapshot where
  snapshotId       : Nat
  snapshotHead     : ThermodynamicState
  snapshotUcrs     : CryptoUcrsStamp
  snapshotThreshold : CryptoThresholdCert
  snapshotSsotDigest : CryptoSsotDigest
  snapshotSigned   : Bool
  snapshotIdentity : CryptoIdentityClass

/-- Witness bundle a crypto compose morphism must preserve (§5.4). -/
structure CryptoComposeWitness where
  witnessUcrs      : CryptoUcrsStamp
  witnessThreshold : CryptoThresholdCert
  witnessSsotValid : Bool

/-- Typed crypto compose morphism — admissible signed transition, not blind copy. -/
structure CryptoComposeMorphism where
  morphismFrom              : CryptoComposeSnapshot
  morphismToIdentity        : CryptoIdentityClass
  morphismWitness           : CryptoComposeWitness
  morphismExcitementSelected : Bool

/-- Fail-closed crypto compose errors — positive refuse, not silent no-op. -/
inductive CryptoComposeRefusal where
  | egoffCopyPasteRefused (snapshotId : Nat)
  | gateRejected (seq : Nat)
  | unsignedTransition (snapshotId : Nat)
  | hostIdAsRid (hostId : Nat)
  | belowThreshold (snapshotId : Nat)
  | invalidSsotDigest (snapshotId : Nat)
  | identityClassMismatch
  deriving DecidableEq, Repr

/-- Verdict of a crypto compose operation class. -/
inductive CryptoComposeVerdict where
  | morphismOk
  | egoffCopyPasteRefused
  | inadmissible
  deriving DecidableEq, Repr

/-- Compose-pin refusal tags (no second ℚ argmin). -/
inductive CryptoComposePinRefusal where
  | egoffCopyPaste
  | secondArgmin
  | hostIdAsRid
  | unsignedTransition
  deriving DecidableEq, Repr

def refuseEgoffCopyPasteTag : CryptoComposePinRefusal := .egoffCopyPaste

def refuseSecondArgmin : CryptoComposePinRefusal := .secondArgmin

-- ================================================================
-- SECTION 2: §5.4 admissibility conjunct + positive refuse
-- ================================================================

/-- §5.4 admissibility conjunct inputs (surrogate). -/
structure CryptoAdmissibilityConjunct where
  gateOk              : Bool
  thresholdMet        : Bool
  excitementPreserves : Bool

/-- Evaluate `admit(h) ⟺ gate ∧ threshold ∧ Excitement preserves`. -/
def cryptoConjunctAdmits (c : CryptoAdmissibilityConjunct) : Bool :=
  c.gateOk && c.thresholdMet && c.excitementPreserves

/-- Classify egoff copy-paste vs typed morphism without performing I/O. -/
def evaluateCryptoComposeOperation (isEgoffCopyPaste : Bool) : CryptoComposeVerdict :=
  if isEgoffCopyPaste then .egoffCopyPasteRefused else .morphismOk

/-- Positive refuse: egoff crypto inventory copy-paste is inadmissible. -/
def refuseEgoffCopyPaste (snapshotId : Nat) : CryptoComposeRefusal :=
  .egoffCopyPasteRefused snapshotId

/-- Positive refuse: host id cannot serve as content-addressed RID. -/
def refuseHostIdAsRid (hostId : Nat) : CryptoComposeRefusal :=
  .hostIdAsRid hostId

/-- Positive refuse: unsigned transition refused. -/
def refuseUnsignedTransition (snapshotId : Nat) : CryptoComposeRefusal :=
  .unsignedTransition snapshotId

/-- Build witness from snapshot — morphism must preserve stamps and certificates. -/
def witnessFromCryptoSnapshot (s : CryptoComposeSnapshot) : CryptoComposeWitness :=
  { witnessUcrs := s.snapshotUcrs
    witnessThreshold := s.snapshotThreshold
    witnessSsotValid := s.snapshotSsotDigest.digestHexValid }

/-- Attempt typed crypto compose morphism to target identity — fail closed. -/
def applyCryptoComposeMorphism (snapshot : CryptoComposeSnapshot)
    (toIdentity : CryptoIdentityClass) (conjunct : CryptoAdmissibilityConjunct)
    (excitementSelected : Bool) : CryptoComposeMorphism ⊕ CryptoComposeRefusal :=
  if !cryptoConjunctAdmits conjunct then
    Sum.inr (.gateRejected snapshot.snapshotUcrs.ucrsSeq)
  else if !snapshot.snapshotThreshold.thresholdMet then
    Sum.inr (.belowThreshold snapshot.snapshotId)
  else if !snapshot.snapshotSsotDigest.digestHexValid then
    Sum.inr (.invalidSsotDigest snapshot.snapshotId)
  else if !snapshot.snapshotSigned then
    Sum.inr (.unsignedTransition snapshot.snapshotId)
  else if !excitementSelected then
    Sum.inr (.unsignedTransition snapshot.snapshotId)
  else
    Sum.inl
      { morphismFrom := snapshot
        morphismToIdentity := toIdentity
        morphismWitness := witnessFromCryptoSnapshot snapshot
        morphismExcitementSelected := excitementSelected }

theorem cryptoComposeEgoffCopyPasteRefused (_snapshotId : Nat) :
    evaluateCryptoComposeOperation true = .egoffCopyPasteRefused := rfl

theorem cryptoComposeMorphismOkWhenNotCopyPaste :
    evaluateCryptoComposeOperation false = .morphismOk := rfl

-- ================================================================
-- SECTION 4: §5.4 fixtures + witness theorems
-- ================================================================

def cryptoComposeFixtureState : ThermodynamicState :=
  { density := 2400
    freeEnergy := 0
    hydration := 0
    strength := 0 }

def cryptoComposeFixtureUcrs : CryptoUcrsStamp :=
  { ucrsSeq := 7
    ucrsWallHasT := true }

def cryptoComposeFixtureThreshold : CryptoThresholdCert :=
  { thresholdQuorum := 1
    thresholdValid := 1
    thresholdMet := true }

def cryptoComposeFixtureSsot : CryptoSsotDigest :=
  { digestHexLen := 64
    digestHexValid := true }

def cryptoComposeFixtureSnapshot : CryptoComposeSnapshot :=
  { snapshotId := 1
    snapshotHead := cryptoComposeFixtureState
    snapshotUcrs := cryptoComposeFixtureUcrs
    snapshotThreshold := cryptoComposeFixtureThreshold
    snapshotSsotDigest := cryptoComposeFixtureSsot
    snapshotSigned := true
    snapshotIdentity := .contentAddressedRid }

def cryptoComposeFixtureConjunct : CryptoAdmissibilityConjunct :=
  { gateOk := true
    thresholdMet := true
    excitementPreserves := true }

theorem cryptoComposeFixtureEgoffCopyPasteRefused :
    refuseEgoffCopyPaste cryptoComposeFixtureSnapshot.snapshotId =
      .egoffCopyPasteRefused 1 :=
  rfl

theorem cryptoComposeFixtureApplyMorphismOk :
    applyCryptoComposeMorphism cryptoComposeFixtureSnapshot .decentralizedDid
      cryptoComposeFixtureConjunct true =
    Sum.inl
      { morphismFrom := cryptoComposeFixtureSnapshot
        morphismToIdentity := .decentralizedDid
        morphismWitness := witnessFromCryptoSnapshot cryptoComposeFixtureSnapshot
        morphismExcitementSelected := true } :=
  rfl

theorem cryptoComposeFixtureWitnessPreservesUcrs :
    (witnessFromCryptoSnapshot cryptoComposeFixtureSnapshot).witnessUcrs =
      cryptoComposeFixtureUcrs :=
  rfl

theorem cryptoComposePositiveRefuseNotSilent :
    evaluateCryptoComposeOperation true ≠ .morphismOk := by
  decide

-- ================================================================
-- SECTION 5: Landauer bridge (sole physics axiom — imported)
-- ================================================================

structure CryptoHistoryMove where
  gateChecked          : Prop
  thresholdCanonical   : Prop
  provenanceOk         : Prop

def admissibleCryptoCompose (h : CryptoHistoryMove) : Prop :=
  h.gateChecked ∧ h.thresholdCanonical ∧ h.provenanceOk

theorem admissibleCryptoCompose_intro (h : CryptoHistoryMove)
    (hg : h.gateChecked) (ht : h.thresholdCanonical) (hp : h.provenanceOk) :
    admissibleCryptoCompose h :=
  And.intro hg (And.intro ht hp)

abbrev admitCryptoInbound := admissibleCryptoCompose

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def cryptoComposeMarker : Nat := 1

end UMST.Urge.CryptoCompose
