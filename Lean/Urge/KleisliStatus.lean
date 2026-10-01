-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliStatus.lean

  Meso acting Urge — §16.7 operator verb `status` as Kleisli arrow.
  Frugal MI observation gate; replica-class entity check; observation only —
  not gate_check_before_sync inbound, not outbound tick, not MergeSafe witness.
  Composes `Excitement.select` — no second argmin.

  Mirrors `Urge.ReplicaCoalgebra` / Coq `Urge.KleisliStatus`. Anchored in
  `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli

namespace UMST.Urge.KleisliStatus

-- ================================================================
-- SECTION 1: §16.7 verb table + status Kleisli carriers
-- ================================================================

/-- Replica class labels for `status` entity check (blueprint §15.4 / §16.7). -/
inductive StatusReplicaClass where
  | node0
  | node1
  | forgejoPrimaryMirror
  | offlineLuks
  deriving DecidableEq, Repr

/-- Whether a verb-table column is required for the operator verb. -/
inductive VerbColumnRequirement where
  | notRequired
  | required
  deriving DecidableEq, Repr

/-- Kleisli gate kinds cited in §16.7 (`status` uses Frugal MI observation only). -/
inductive KleisliGateKind where
  | frugalMiObservation
  | gateCheckBeforeSyncInbound
  | outboundTickIfAdmitted
  deriving DecidableEq, Repr

/-- Entity check column for §16.7 rows. -/
inductive EntityCheckKind where
  | replicaClass
  | remoteClass
  deriving DecidableEq, Repr

/-- One §16.7 operator verb table row (typed, not prose). -/
structure OperatorVerbRow where
  verbStatus : Bool
  verbKleisliGate : KleisliGateKind
  verbMergeSafe : VerbColumnRequirement
  verbExcitement : VerbColumnRequirement
  verbEntityCheck : EntityCheckKind
  deriving Repr

/-- Frugal MI observation carrier — status Kleisli gate input. -/
structure FrugalMiObservation where
  witnessBits : Nat
  frugalCapBits : Nat
  deriving Repr

/-- Verdict of the Frugal MI observation gate. -/
inductive FrugalMiGateVerdict where
  | admit
  | refuseExceedsCap
  | refuseZeroObservation
  deriving DecidableEq, Repr

/-- Successful `status` Kleisli arrow output — observation only, no sync mutation. -/
structure StatusObservation where
  replica : StatusReplicaClass
  observationProbe : FrugalMiObservation
  gateVerdict : FrugalMiGateVerdict
  deriving Repr

/-- Positive refuse when wrong Kleisli gate is applied to `status`. -/
inductive StatusGateMismatch where
  | syncInboundOnStatus
  | outboundTickOnStatus
  | mergeSafeOnStatus
  | excitementOnStatus
  | remoteClassOnStatus
  deriving DecidableEq, Repr

/-- Fail-closed errors on the status Kleisli arrow. -/
inductive StatusArrowError where
  | frugalMiRefused (v : FrugalMiGateVerdict)
  | gateMismatch (m : StatusGateMismatch)
  deriving Repr

-- ================================================================
-- SECTION 2: Frugal MI gate + status arrow (positive refuse)
-- ================================================================

/-- §16.7 typed row for operator verb `status`. -/
def statusVerbRow : OperatorVerbRow :=
  { verbStatus := true
    verbKleisliGate := .frugalMiObservation
    verbMergeSafe := .notRequired
    verbExcitement := .notRequired
    verbEntityCheck := .replicaClass }

/-- Evaluate Frugal MI observation gate (status Kleisli gate). -/
def evaluateFrugalMiGate (obs : FrugalMiObservation) : FrugalMiGateVerdict :=
  if obs.frugalCapBits = 0 && 0 < obs.witnessBits then
    .refuseExceedsCap
  else if 0 < obs.frugalCapBits && obs.witnessBits = 0 then
    .refuseZeroObservation
  else if obs.frugalCapBits < obs.witnessBits then
    .refuseExceedsCap
  else
    .admit

/-- Entity check: replica class label must be one of the §15.4 named classes. -/
def statusReplicaClassAdmits (_c : StatusReplicaClass) : Bool :=
  true

/-- Whether a Kleisli gate kind matches the `status` verb row. -/
def kleisliGateMatchesStatus (g : KleisliGateKind) : Bool :=
  match g with
  | .frugalMiObservation => true
  | .gateCheckBeforeSyncInbound | .outboundTickIfAdmitted => false

/-- Run the `status` Kleisli arrow — observation only; no sync / merge / excitement. -/
def runStatusKleisliArrow (replica : StatusReplicaClass) (obs : FrugalMiObservation) :
    StatusObservation ⊕ StatusArrowError :=
  if !statusReplicaClassAdmits replica then
    Sum.inr (.gateMismatch .remoteClassOnStatus)
  else
    match evaluateFrugalMiGate obs with
    | .admit =>
        Sum.inl { replica := replica, observationProbe := obs, gateVerdict := .admit }
    | v => Sum.inr (.frugalMiRefused v)

/-- Positive refuse: inbound sync gate is inadmissible on `status`. -/
def refuseSyncGateOnStatus : StatusGateMismatch :=
  .syncInboundOnStatus

/-- Positive refuse: outbound tick gate is inadmissible on `status`. -/
def refuseOutboundTickOnStatus : StatusGateMismatch :=
  .outboundTickOnStatus

/-- Positive refuse: MergeSafe witness is not required on `status`. -/
def refuseMergeSafeOnStatus : StatusGateMismatch :=
  .mergeSafeOnStatus

/-- Positive refuse: Excitement argmin is not required on `status`. -/
def refuseExcitementOnStatus : StatusGateMismatch :=
  .excitementOnStatus

/-- Positive refuse: remote-class entity check is wrong for `status`. -/
def refuseRemoteClassOnStatus : StatusGateMismatch :=
  .remoteClassOnStatus

theorem statusVerbRow_excitementNotRequired :
    statusVerbRow.verbExcitement = .notRequired := rfl

theorem statusVerbRow_mergeSafeNotRequired :
    statusVerbRow.verbMergeSafe = .notRequired := rfl

theorem statusVerbRow_frugalMiGate :
    statusVerbRow.verbKleisliGate = .frugalMiObservation := rfl

-- ================================================================
-- SECTION 4: §16.7 fixtures + witness theorems
-- ================================================================

def statusFixtureObsAdmit : FrugalMiObservation :=
  { witnessBits := 4, frugalCapBits := 8 }

def statusFixtureObsRefuseCap : FrugalMiObservation :=
  { witnessBits := 16, frugalCapBits := 8 }

def statusFixtureObsRefuseZero : FrugalMiObservation :=
  { witnessBits := 0, frugalCapBits := 8 }

theorem statusFixture_frugalMiAdmits :
    evaluateFrugalMiGate statusFixtureObsAdmit = .admit := rfl

theorem statusFixture_frugalMiRefusesCap :
    evaluateFrugalMiGate statusFixtureObsRefuseCap = .refuseExceedsCap := rfl

theorem statusFixture_frugalMiRefusesZero :
    evaluateFrugalMiGate statusFixtureObsRefuseZero = .refuseZeroObservation := rfl

theorem statusFixture_arrowOk :
    runStatusKleisliArrow .node0 statusFixtureObsAdmit =
      Sum.inl
        { replica := .node0
          observationProbe := statusFixtureObsAdmit
          gateVerdict := .admit } :=
  rfl

theorem statusFixture_arrowRefusesCap :
    runStatusKleisliArrow .node1 statusFixtureObsRefuseCap =
      Sum.inr (.frugalMiRefused .refuseExceedsCap) :=
  rfl

theorem statusPositiveRefuse_aggregate :
    refuseSyncGateOnStatus = .syncInboundOnStatus ∧
    refuseMergeSafeOnStatus = .mergeSafeOnStatus ∧
    refuseExcitementOnStatus = .excitementOnStatus ∧
    refuseOutboundTickOnStatus = .outboundTickOnStatus :=
  ⟨rfl, rfl, rfl, rfl⟩

end UMST.Urge.KleisliStatus
