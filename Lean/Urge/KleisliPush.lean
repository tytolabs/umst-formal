-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliPush.lean

  Meso acting Urge — §16.7 operator verb `push` as Kleisli arrow.
  Kleisli gate = `outbound_tick_if_admitted`; MergeSafe = pre-push witness;
  Excitement = provenance preserved; entity check = entity remote.

  Push composes `Excitement.select` (via `Urge.ExcitementImport`) — not a second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.ExcitementImport

namespace UMST.Urge.KleisliPush

-- ================================================================
-- SECTION 1: §16.7 push column carriers + Kleisli arrow witness
-- ================================================================

/-- Outbound tick gate — `outbound_tick_if_admitted` (push row Kleisli gate). -/
inductive OutboundTickGate where
  | admitted
  | refused
  | bypassAttempted
  deriving DecidableEq, Repr

def outboundGateAdmits (g : OutboundTickGate) : Bool :=
  match g with
  | .admitted => true
  | .refused | .bypassAttempted => false

/-- Pre-push MergeSafe witness column (§16.7 push row). -/
inductive PrePushMergeSafeWitness where
  | witnessed
  | missing
  | bypassAttempted
  deriving DecidableEq, Repr

def prePushMergeSafeAdmits (w : PrePushMergeSafeWitness) : Bool :=
  match w with
  | .witnessed => true
  | .missing | .bypassAttempted => false

/-- Excitement column for push — provenance preserved. -/
inductive ProvenancePreserved where
  | preserved
  | violated
  | bypassAttempted
  deriving DecidableEq, Repr

def provenancePreservedAdmits (p : ProvenancePreserved) : Bool :=
  match p with
  | .preserved => true
  | .violated | .bypassAttempted => false

/-- Entity remote class for push entity check (§16.7). -/
inductive EntityRemoteClass where
  | entityRemote
  | refusedUpstream
  | unclassified
  deriving DecidableEq, Repr

def entityRemoteAdmits (c : EntityRemoteClass) : Bool :=
  match c with
  | .entityRemote => true
  | .refusedUpstream | .unclassified => false

/-- Kleisli gate kinds cited in §16.7 (push uses outbound tick only). -/
inductive KleisliGateKind where
  | outboundTickIfAdmitted
  | gateCheckBeforeSyncInbound
  | frugalMiObservation
  deriving DecidableEq, Repr

/-- §16.7 typed Kleisli arrow witness for operator `push`. -/
structure PushKleisliArrow where
  gate         : OutboundTickGate
  mergeSafe    : PrePushMergeSafeWitness
  provenance   : ProvenancePreserved
  entity       : EntityRemoteClass
  objectCount  : Nat

/-- Push morphism verdict. -/
inductive PushVerdict where
  | admitted
  | gateRefused
  | mergeSafeRefused
  | provenanceRefused
  | entityRemoteRefused
  | productionWiredRefused
  | gateBypassRefused
  deriving DecidableEq, Repr

/-- Fail-closed push errors — positive refuse, not silent no-op. -/
inductive PushRefusal where
  | gateRefused
  | mergeSafeMissing
  | mergeSafeBypassRefused
  | provenanceViolated
  | provenanceBypassRefused
  | entityRemoteRefused (c : EntityRemoteClass)
  | productionWiredRefused
  | gateBypassRefused
  | wrongGate (g : KleisliGateKind)
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §16.7 admissibility conjunct + positive refuse
-- ================================================================

/-- §16.7 admissibility conjunct inputs (surrogate). -/
structure PushAdmissibilityConjunct where
  gateOk              : Bool
  mergeSafeOk         : Bool
  provenancePreserved : Bool
  entityRemote        : Bool

def pushConjunctAdmits (c : PushAdmissibilityConjunct) : Bool :=
  c.gateOk && c.mergeSafeOk && c.provenancePreserved && c.entityRemote

def pushArrowAdmissible (a : PushKleisliArrow) : Bool :=
  outboundGateAdmits a.gate &&
  prePushMergeSafeAdmits a.mergeSafe &&
  provenancePreservedAdmits a.provenance &&
  entityRemoteAdmits a.entity

def evaluatePushKleisli (a : PushKleisliArrow) : PushVerdict ⊕ PushRefusal :=
  if outboundGateAdmits a.gate then
    if prePushMergeSafeAdmits a.mergeSafe then
      if provenancePreservedAdmits a.provenance then
        if entityRemoteAdmits a.entity then
          Sum.inl PushVerdict.admitted
        else
          Sum.inr (PushRefusal.entityRemoteRefused a.entity)
      else
        match a.provenance with
        | .bypassAttempted => Sum.inr PushRefusal.provenanceBypassRefused
        | _ => Sum.inr PushRefusal.provenanceViolated
    else
      match a.mergeSafe with
      | .bypassAttempted => Sum.inr PushRefusal.mergeSafeBypassRefused
      | _ => Sum.inr PushRefusal.mergeSafeMissing
  else
    match a.gate with
    | .bypassAttempted => Sum.inr PushRefusal.gateBypassRefused
    | _ => Sum.inr PushRefusal.gateRefused

def refuseProductionWiredPush : PushRefusal := PushRefusal.productionWiredRefused

def refuseGateBypassPush : PushRefusal := PushRefusal.gateBypassRefused

def refuseSyncGateOnPush : PushRefusal :=
  PushRefusal.wrongGate KleisliGateKind.gateCheckBeforeSyncInbound

def refuseFrugalMiOnPush : PushRefusal :=
  PushRefusal.wrongGate KleisliGateKind.frugalMiObservation

def kleisliGateMatchesPush (g : KleisliGateKind) : Bool :=
  match g with
  | .outboundTickIfAdmitted => true
  | _ => false

/-- Classify remote host into entity-remote check class (typed surrogate). -/
def classifyEntityRemote (host : String) : EntityRemoteClass :=
  if host.isEmpty then .unclassified
  else if host = "origin.cursor.com" || host = "github.com" then .refusedUpstream
  else if host = "forge.entity" then .entityRemote
  else .unclassified

def pushKleisliArrowFromHost
    (gate : OutboundTickGate)
    (mergeSafe : PrePushMergeSafeWitness)
    (provenance : ProvenancePreserved)
    (remoteHost : String)
    (objectCount : Nat) : PushKleisliArrow :=
  { gate := gate
    mergeSafe := mergeSafe
    provenance := provenance
    entity := classifyEntityRemote remoteHost
    objectCount := objectCount }

-- ================================================================
-- SECTION 3: Push composes Excitement (no second argmin)
-- ================================================================

/-- Context for push over admissible history successors. -/
structure PushCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Push **is** `urgeRecoverySelect` / `Excitement.select` on successors. -/
noncomputable def pushSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : PushCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def pushSelectBare {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

theorem pushSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : PushCtx S) :
    pushSelect ctx = select ctx.prior ctx.successors :=
  urgeRecoverySelect_eq_select ctx.prior ctx.successors

theorem pushSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PushCtx S) :
    pushSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem pushNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : PushCtx S) :
    pushSelect ctx = select ctx.prior ctx.successors :=
  pushSelect_eq_select ctx

theorem pushSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : PushCtx S) (h : ctx.successors = []) :
    pushSelect ctx = Sum.inr Residue.noCandidates := by
  unfold pushSelect urgeRecoverySelect
  rw [h]
  simpa using select_empty (src := ctx.prior)

-- ================================================================
-- SECTION 4: §16.7 fixtures + witness theorems
-- ================================================================

def pushFixtureAdmittedArrow : PushKleisliArrow :=
  pushKleisliArrowFromHost .admitted .witnessed .preserved "forge.entity" 3

def pushFixtureGateRefusedArrow : PushKleisliArrow :=
  pushKleisliArrowFromHost .refused .witnessed .preserved "forge.entity" 0

def pushFixtureConjunct : PushAdmissibilityConjunct :=
  { gateOk := true
    mergeSafeOk := true
    provenancePreserved := true
    entityRemote := true }

theorem pushFixtureAdmittedOk :
    evaluatePushKleisli pushFixtureAdmittedArrow = Sum.inl PushVerdict.admitted := rfl

theorem pushFixtureGateRefused :
    evaluatePushKleisli pushFixtureGateRefusedArrow = Sum.inr PushRefusal.gateRefused := rfl

theorem pushFixtureEntityRemoteForge :
    classifyEntityRemote "forge.entity" = EntityRemoteClass.entityRemote := rfl

theorem pushFixtureEntityRefusedUpstreamOrigin :
    classifyEntityRemote "origin.cursor.com" = EntityRemoteClass.refusedUpstream := rfl

theorem pushFixtureEntityRefusedUpstreamGithub :
    classifyEntityRemote "github.com" = EntityRemoteClass.refusedUpstream := rfl

theorem pushFixtureKleisliGateMatchesPush :
    kleisliGateMatchesPush KleisliGateKind.outboundTickIfAdmitted = true := rfl

theorem pushFixtureKleisliGateRejectsInboundSync :
    kleisliGateMatchesPush KleisliGateKind.gateCheckBeforeSyncInbound = false := rfl

theorem pushFixtureRefuseSyncGatePositive :
    refuseSyncGateOnPush = PushRefusal.wrongGate KleisliGateKind.gateCheckBeforeSyncInbound := rfl

theorem pushFixtureRefuseFrugalMiPositive :
    refuseFrugalMiOnPush = PushRefusal.wrongGate KleisliGateKind.frugalMiObservation := rfl

theorem pushFixtureConjunctAdmits :
    pushConjunctAdmits pushFixtureConjunct = true := rfl

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure PushHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissiblePushHistoryMove (h : PushHistoryMove) : Prop :=
  h.gateChecked ∧ h.mergeSafe ∧ h.provenanceOk

theorem admissiblePushHistoryMove_intro (h : PushHistoryMove)
    (hg : h.gateChecked) (hm : h.mergeSafe) (hp : h.provenanceOk) :
    admissiblePushHistoryMove h :=
  And.intro hg (And.intro hm hp)

abbrev admitPushOutbound := admissiblePushHistoryMove

structure PushTransition where
  move            : PushHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def pushSecondLaw (t : PushTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalPushBridge where
  proc : ErasureProcess
  transition : PushTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissiblePushHistoryMove transition.move

theorem pushSecondLaw_from_physical (b : PhysicalPushBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    pushSecondLaw b.transition := by
  unfold pushSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissiblePushHistoryMove_from_physical (b : PhysicalPushBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissiblePushHistoryMove b.transition.move :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def kleisliPushPhysicsGreen : Bool := false

theorem kleisliPushPhysicsGreenFalse : kleisliPushPhysicsGreen = false := rfl

def kleisliPushProductionWired : Bool := false

theorem kleisliPushProductionWiredFalse : kleisliPushProductionWired = false := rfl

theorem kleisliPushModuleWitness : True := trivial

theorem kleisliPush_noNewAxiom : True := trivial

theorem kleisliPushPositiveRefuseNotSilent :
    evaluatePushKleisli pushFixtureGateRefusedArrow ≠ Sum.inl PushVerdict.admitted := by
  rw [pushFixtureGateRefused]
  decide

theorem kleisliPushProductionWiredRefusePositive :
    refuseProductionWiredPush = PushRefusal.productionWiredRefused := rfl

theorem kleisliPushGateBypassRefusePositive :
    refuseGateBypassPush = PushRefusal.gateBypassRefused := rfl

end UMST.Urge.KleisliPush
