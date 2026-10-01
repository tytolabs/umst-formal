-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliClone.lean

  Meso acting Urge — §16.7 operator verb `clone` as Kleisli arrow.
  Initial replica coalgebra admission — not sync inbound, not outbound tick,
  not Frugal MI observation, not MergeSafe witness, not Excitement argmin.
  Compose `Excitement.select` — no second argmin.

  Mirrors `Urge.ReplicaCoalgebra` / `Urge.ExcitementImport`.
  Anchored in `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ExcitementImport
import Urge.ReplicaCoalgebra

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ExcitementImport UMST.Urge.ReplicaCoalgebra

namespace UMST.Urge.KleisliClone

-- ================================================================
-- SECTION 1: §16.7 operator verb table carriers
-- ================================================================

inductive CloneOperatorVerb where
  | clone
  deriving DecidableEq, Repr

inductive CloneKleisliGateKind where
  | admitInitialReplicaCoalgebra
  | frugalMiObservation
  | gateCheckBeforeSyncInbound
  | outboundTickIfAdmitted
  | excitementArgmin
  deriving DecidableEq, Repr

inductive CloneVerbColumnReq where
  | notRequired
  | required
  deriving DecidableEq, Repr

inductive CloneEntityCheckKind where
  | entityLabel
  | replicaClass
  | remoteClass
  deriving DecidableEq, Repr

structure CloneVerbRow where
  verb         : CloneOperatorVerb
  kleisliGate  : CloneKleisliGateKind
  mergeSafe    : CloneVerbColumnReq
  excitement   : CloneVerbColumnReq
  entityCheck  : CloneEntityCheckKind

def cloneVerbRow : CloneVerbRow :=
  { verb := .clone
    kleisliGate := .admitInitialReplicaCoalgebra
    mergeSafe := .notRequired
    excitement := .notRequired
    entityCheck := .entityLabel }

def kleisliGateMatchesClone (g : CloneKleisliGateKind) : Bool :=
  match g with
  | .admitInitialReplicaCoalgebra => true
  | _ => false

-- ================================================================
-- SECTION 2: Entity labels + initial replica coalgebra gate
-- ================================================================

inductive CloneEntityLabel where
  | labs
  | compose
  deriving DecidableEq, Repr

inductive CloneReplicaClass where
  | node0
  | node1
  | forge
  | luks
  | darwinScratch
  deriving DecidableEq, Repr

def cloneReplicaClassTag (c : CloneReplicaClass) : String :=
  match c with
  | .node0 => "node-0"
  | .node1 => "node-1"
  | .forge => "forgejo-primary-mirror"
  | .luks => "offline-luks"
  | .darwinScratch => "darwin-scratch"

structure InitialReplicaCoalgebra where
  replicaClass       : CloneReplicaClass
  egressDeclared     : Bool
  authorityDeclared  : Bool

inductive InitialCoalgebraGateVerdict where
  | admit
  | refuseUndeclaredEgress
  | refuseUndeclaredAuthority
  deriving DecidableEq, Repr

def evaluateInitialCoalgebraGate (c : InitialReplicaCoalgebra) : InitialCoalgebraGateVerdict :=
  if c.egressDeclared then
    if c.authorityDeclared then .admit
    else .refuseUndeclaredAuthority
  else .refuseUndeclaredEgress

structure CloneRemoteHost where
  hostLabel : String

def composeUpstreamRefused (host : String) : Bool :=
  host == "github.com" || host == "origin.cursor.com"

def parseEntityLabel (label : String) : Option CloneEntityLabel :=
  if label == "labs" || label == "LABS" then some .labs
  else if label == "compose" || label == "COMPOSE" then some .compose
  else none

def entityLabelAdmitsClone (entity : CloneEntityLabel) (remote : CloneRemoteHost) : Bool :=
  match entity with
  | .labs => true
  | .compose => !composeUpstreamRefused remote.hostLabel

-- ================================================================
-- SECTION 3: Clone Kleisli arrow (initial admission only)
-- ================================================================

abbrev CloneArrow := AdmitArrow

inductive CloneGateMismatch where
  | frugalMiOnClone
  | syncInboundOnClone
  | outboundTickOnClone
  | mergeSafeWitnessOnClone
  | excitementArgminOnClone
  | replicaClassOnClone
  | remoteClassOnClone
  | secondArgminOnClone
  deriving DecidableEq, Repr

inductive CloneArrowError where
  | coalgebraRefused (v : InitialCoalgebraGateVerdict)
  | unknownEntityLabel
  | composeUpstreamRefused
  | gateMismatch (m : CloneGateMismatch)
  deriving Repr

structure CloneAdmission where
  entity  : CloneEntityLabel
  replica : CloneReplicaClass
  gate    : InitialCoalgebraGateVerdict

def runCloneKleisliArrow (entity : CloneEntityLabel) (coalgebra : InitialReplicaCoalgebra)
    (remote : CloneRemoteHost) : CloneAdmission ⊕ CloneArrowError :=
  if entityLabelAdmitsClone entity remote then
    match evaluateInitialCoalgebraGate coalgebra with
    | .admit =>
      Sum.inl { entity := entity, replica := coalgebra.replicaClass, gate := .admit }
    | v => Sum.inr (.coalgebraRefused v)
  else
    Sum.inr .composeUpstreamRefused

def runCloneKleisliArrowParsed (label : String) (coalgebra : InitialReplicaCoalgebra)
    (remote : CloneRemoteHost) : CloneAdmission ⊕ CloneArrowError :=
  match parseEntityLabel label with
  | some entity => runCloneKleisliArrow entity coalgebra remote
  | none => Sum.inr .unknownEntityLabel

def cloneKleisliIdentity : CloneArrow := admitIdentity

-- ================================================================
-- SECTION 4: Positive refuse (wrong gates / columns on `clone`)
-- ================================================================

def refuseFrugalMiOnClone : CloneGateMismatch := .frugalMiOnClone
def refuseSyncGateOnClone : CloneGateMismatch := .syncInboundOnClone
def refuseOutboundTickOnClone : CloneGateMismatch := .outboundTickOnClone
def refuseMergeSafeOnClone : CloneGateMismatch := .mergeSafeWitnessOnClone
def refuseExcitementArgminOnClone : CloneGateMismatch := .excitementArgminOnClone
def refuseReplicaClassOnClone : CloneGateMismatch := .replicaClassOnClone
def refuseRemoteClassOnClone : CloneGateMismatch := .remoteClassOnClone
theorem cloneVerbRowMergeSafeNotRequired :
    cloneVerbRow.mergeSafe = .notRequired := rfl

theorem cloneVerbRowExcitementNotRequired :
    cloneVerbRow.excitement = .notRequired := rfl

theorem cloneVerbRowEntityLabelCheck :
    cloneVerbRow.entityCheck = .entityLabel := rfl

-- ================================================================
-- SECTION 6: Fixtures + witness theorems
-- ================================================================

def cloneFixtureCoalgebraAdmit : InitialReplicaCoalgebra :=
  { replicaClass := .node0, egressDeclared := true, authorityDeclared := true }

def cloneFixtureCoalgebraRefuseEgress : InitialReplicaCoalgebra :=
  { replicaClass := .luks, egressDeclared := false, authorityDeclared := true }

def cloneFixtureRemoteForge : CloneRemoteHost := { hostLabel := "forge.entity" }
def cloneFixtureRemoteGithub : CloneRemoteHost := { hostLabel := "github.com" }

theorem cloneFixtureInitialCoalgebraAdmits :
    evaluateInitialCoalgebraGate cloneFixtureCoalgebraAdmit = .admit := rfl

theorem cloneFixtureInitialCoalgebraRefusesEgress :
    evaluateInitialCoalgebraGate cloneFixtureCoalgebraRefuseEgress = .refuseUndeclaredEgress := rfl

theorem cloneFixtureArrowAdmitsLabs :
    runCloneKleisliArrow .labs cloneFixtureCoalgebraAdmit cloneFixtureRemoteForge =
      Sum.inl { entity := .labs, replica := .node0, gate := .admit } :=
  rfl

theorem cloneFixtureComposeUpstreamRefused :
    composeUpstreamRefused "github.com" = true := by decide

theorem cloneFixtureComposeEntityRefusedOnGithub :
    runCloneKleisliArrow .compose cloneFixtureCoalgebraAdmit cloneFixtureRemoteGithub =
      Sum.inr .composeUpstreamRefused :=
  rfl

theorem cloneFixtureParseLabs : parseEntityLabel "labs" = some .labs := rfl

theorem cloneFixtureParseComposeCaseInsensitive :
    parseEntityLabel "COMPOSE" = some .compose := rfl

-- ================================================================
-- SECTION 8: Honesty flags + catalog witnesses
-- ================================================================

theorem kleisliClonePositiveRefuseNotSilent :
    kleisliGateMatchesClone .frugalMiObservation = false ∧
    kleisliGateMatchesClone .gateCheckBeforeSyncInbound = false :=
  ⟨rfl, rfl⟩

end UMST.Urge.KleisliClone
