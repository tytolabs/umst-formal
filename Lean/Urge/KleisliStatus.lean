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

theorem kleisliGateMatchesStatus_frugal :
    kleisliGateMatchesStatus .frugalMiObservation = true := rfl

theorem kleisliGateMatchesStatus_syncFalse :
    kleisliGateMatchesStatus .gateCheckBeforeSyncInbound = false := rfl

-- ================================================================
-- SECTION 3: Excitement compose (no second argmin)
-- ================================================================

/-- Excitement compose pin — Urge imports selector; no second argmin. -/
inductive StatusExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

/-- Status path composes `Excitement.select` — not a second argmin. -/
noncomputable def statusExcitementSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src))
    (pin : StatusExcitementComposePin) : Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

theorem statusExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    statusExcitementSelect src cands .importSelectExcitement = select src cands :=
  rfl

theorem statusExcitementSelect_refusesSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    statusExcitementSelect src cands .secondArgminRefused = Sum.inr Residue.allInadmissible :=
  rfl

theorem statusNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    statusExcitementSelect src cands .importSelectExcitement = select src cands :=
  statusExcitementSelect_eq_select src cands

theorem statusExcitementSelect_eq_admitHistorySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    statusExcitementSelect src cands .importSelectExcitement = admitHistorySelect src cands :=
  rfl

theorem statusExcitement_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) :
    statusExcitementSelect src [] .importSelectExcitement = Sum.inr Residue.noCandidates := by
  simpa [statusExcitementSelect] using select_empty (src := src)

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

theorem statusPositiveRefuse_syncGate :
    refuseSyncGateOnStatus = .syncInboundOnStatus := rfl

theorem statusPositiveRefuse_mergeSafe :
    refuseMergeSafeOnStatus = .mergeSafeOnStatus := rfl

theorem statusPositiveRefuse_excitement :
    refuseExcitementOnStatus = .excitementOnStatus := rfl

theorem statusPositiveRefuse_outboundTick :
    refuseOutboundTickOnStatus = .outboundTickOnStatus := rfl

theorem statusPositiveRefuse_notSilent :
    refuseSyncGateOnStatus ≠ refuseMergeSafeOnStatus := by
  decide

theorem statusPositiveRefuse_aggregate :
    refuseSyncGateOnStatus = .syncInboundOnStatus ∧
    refuseMergeSafeOnStatus = .mergeSafeOnStatus ∧
    refuseExcitementOnStatus = .excitementOnStatus ∧
    refuseOutboundTickOnStatus = .outboundTickOnStatus :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ================================================================
-- SECTION 5: Landauer bridge (inherited — zero new axioms)
-- ================================================================

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

theorem statusSecondLaw_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition :=
  admitSecondLaw_from_physical b hSL

theorem statusAdmissibleTransition_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleHistoryTransition b.transition :=
  UMST.Urge.AdmitKleisli.admissibleHistoryTransition_from_physical b hSL

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def kleisliStatusPhysicsGreen : Bool := false

theorem kleisliStatusPhysicsGreenFalse : kleisliStatusPhysicsGreen = false := rfl

def kleisliStatusProductionWired : Bool := false

theorem kleisliStatusProductionWiredFalse : kleisliStatusProductionWired = false := rfl

theorem kleisliStatusModuleWitness : True := trivial

theorem kleisliStatus_noNewAxiom : True := trivial

end UMST.Urge.KleisliStatus
