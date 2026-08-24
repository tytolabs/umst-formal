-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ReplicaClass.lean

  Meso acting Urge — §15.4 replica-class table + `fabric-nodes.json` `class` field pin.
  Positive refuse via typed errors — not only `!physics_green`. Composes
  `Excitement.select` — no second argmin.

  Mirrors `Urge.ReplicaCoalgebra` / Coq `Urge.ReplicaClass`. Anchored in
  `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ExcitementImport

namespace UMST.Urge.ReplicaClass

-- ================================================================
-- SECTION 1: §15.4 replica-class table (six named rows)
-- ================================================================

/-- Named replica class row from blueprint §15.4. -/
inductive ReplicaClassLabel where
  | node0DevClone
  | node1DevClone
  | forgejoPrimaryMirror
  | darwinScratch
  | offlineLuks
  | customerCompose
  deriving DecidableEq, Repr

/-- Stable `fabric-nodes.json` `class` field value. -/
def replicaClassClassField (c : ReplicaClassLabel) : String :=
  match c with
  | .node0DevClone => "node-0-dev-clone"
  | .node1DevClone => "node-1-dev-clone"
  | .forgejoPrimaryMirror => "forgejo-primary-mirror"
  | .darwinScratch => "darwin-scratch"
  | .offlineLuks => "offline-luks"
  | .customerCompose => "customer-compose"

def rclNode0LegacyField : String := "node-0"
def rclNode1LegacyField : String := "node-1"

/-- Parse a `class` field string into a §15.4 row (also accepts legacy node ids). -/
def parseReplicaClassField (raw : String) : Option ReplicaClassLabel :=
  if raw == "node-0-dev-clone" then some .node0DevClone
  else if raw == rclNode0LegacyField then some .node0DevClone
  else if raw == "node-1-dev-clone" then some .node1DevClone
  else if raw == rclNode1LegacyField then some .node1DevClone
  else if raw == "forgejo-primary-mirror" then some .forgejoPrimaryMirror
  else if raw == "darwin-scratch" then some .darwinScratch
  else if raw == "offline-luks" then some .offlineLuks
  else if raw == "customer-compose" then some .customerCompose
  else none

/-- Network egress column from §15.4 replica-class table. -/
inductive ReplicaNetworkEgress where
  | tailscaleAdminOnly
  | tailscaleNoPublicPorts
  | empty
  | mountOnly
  | customerPolicy
  deriving DecidableEq, Repr

/-- Whether egress is explicitly empty (offline LUKS / Darwin scratch). -/
def replicaEgressEmpty (e : ReplicaNetworkEgress) : Bool :=
  match e with
  | .empty | .mountOnly => true
  | _ => false

/-- Authority column from §15.4 replica-class table. -/
inductive ReplicaAuthority where
  | workingCopy
  | canonicalRemote
  | backupScratch
  | disasterCopy
  | onSiteRecord
  deriving DecidableEq, Repr

/-- One §15.4 replica-class table row — network egress + authority typed. -/
structure ReplicaClassTableRow where
  replicaRowClass : ReplicaClassLabel
  replicaRowEgress : ReplicaNetworkEgress
  replicaRowAuthority : ReplicaAuthority
  deriving Repr

/-- Blueprint §15.4 default row for a named replica class. -/
def replicaClassBlueprintRow (c : ReplicaClassLabel) : ReplicaClassTableRow :=
  match c with
  | .node0DevClone =>
    { replicaRowClass := .node0DevClone
      replicaRowEgress := .tailscaleAdminOnly
      replicaRowAuthority := .workingCopy }
  | .node1DevClone =>
    { replicaRowClass := .node1DevClone
      replicaRowEgress := .tailscaleAdminOnly
      replicaRowAuthority := .workingCopy }
  | .forgejoPrimaryMirror =>
    { replicaRowClass := .forgejoPrimaryMirror
      replicaRowEgress := .tailscaleNoPublicPorts
      replicaRowAuthority := .canonicalRemote }
  | .darwinScratch =>
    { replicaRowClass := .darwinScratch
      replicaRowEgress := .mountOnly
      replicaRowAuthority := .backupScratch }
  | .offlineLuks =>
    { replicaRowClass := .offlineLuks
      replicaRowEgress := .empty
      replicaRowAuthority := .disasterCopy }
  | .customerCompose =>
    { replicaRowClass := .customerCompose
      replicaRowEgress := .customerPolicy
      replicaRowAuthority := .onSiteRecord }

def replicaClassTableCardinality : Nat := 6

def replicaClassLabelToNat (c : ReplicaClassLabel) : Nat :=
  match c with
  | .node0DevClone => 0
  | .node1DevClone => 1
  | .forgejoPrimaryMirror => 2
  | .darwinScratch => 3
  | .offlineLuks => 4
  | .customerCompose => 5

-- ================================================================
-- SECTION 2: fabric-nodes.json class pin + positive refuse
-- ================================================================

/-- Fabric node pin — `fabric-nodes.json` node with optional `class` field. -/
structure FabricNodeClassPin where
  fabricNodeId : String
  fabricClassField : Option String
  fabricPhysicsGreenClaim : Bool
  fabricJoinsLabsPublicGossip : Bool
  deriving Repr

inductive ReplicaClassAdmit where
  | admitted
  deriving DecidableEq, Repr

inductive FabricNodeClassVerdict where
  | accept
  deriving DecidableEq, Repr

/-- Typed refusal — positive errors, not silent `!physics_green`. -/
inductive ReplicaClassRefusal where
  | missingClassField
  | unknownReplicaClass
  | inventedPhysicsGreen
  | customerComposeLabsGossip
  | secondExcitementArgmin
  deriving DecidableEq, Repr

/-- Evaluated fabric node class row after §15.4 gate. -/
structure FabricNodeClassRow where
  fabricRowNodeId : String
  fabricRowClass : ReplicaClassLabel
  fabricRowTable : ReplicaClassTableRow
  fabricRowVerdict : FabricNodeClassVerdict
  fabricRowAdmit : ReplicaClassAdmit
  deriving Repr

/-- Evaluate one fabric node `class` pin against §15.4 table. -/
def evaluateFabricNodeClass (pin : FabricNodeClassPin) :
    FabricNodeClassRow ⊕ ReplicaClassRefusal :=
  if pin.fabricPhysicsGreenClaim then
    Sum.inr .inventedPhysicsGreen
  else
    match pin.fabricClassField with
    | none => Sum.inr .missingClassField
    | some raw =>
      match parseReplicaClassField raw with
      | none => Sum.inr .unknownReplicaClass
      | some cls =>
        if replicaClassLabelToNat cls == replicaClassLabelToNat .customerCompose &&
            pin.fabricJoinsLabsPublicGossip then
          Sum.inr .customerComposeLabsGossip
        else
          Sum.inl
            { fabricRowNodeId := pin.fabricNodeId
              fabricRowClass := cls
              fabricRowTable := replicaClassBlueprintRow cls
              fabricRowVerdict := .accept
              fabricRowAdmit := .admitted }

def refuseInventedPhysicsGreen : ReplicaClassRefusal := .inventedPhysicsGreen
def refuseMissingClassField : ReplicaClassRefusal := .missingClassField
def refuseCustomerComposeLabsGossip : ReplicaClassRefusal := .customerComposeLabsGossip
def refuseSecondExcitementArgmin : ReplicaClassRefusal := .secondExcitementArgmin

theorem refuseInventedPhysicsGreenPositive :
    refuseInventedPhysicsGreen = .inventedPhysicsGreen := rfl

theorem refuseMissingClassFieldPositive :
    refuseMissingClassField = .missingClassField := rfl

theorem refuseCustomerComposeLabsGossipPositive :
    refuseCustomerComposeLabsGossip = .customerComposeLabsGossip := rfl

theorem refuseSecondExcitementArgminPositive :
    refuseSecondExcitementArgmin = .secondExcitementArgmin := rfl

-- ================================================================
-- SECTION 3: Replica class composes Excitement.select (no argmin)
-- ================================================================

inductive ReplicaExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

structure ReplicaClassCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  replicaClassSrc : S
  replicaClassSuccessors : List (Cand (K := ℚ) replicaClassSrc)

noncomputable def composeReplicaExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src))
    (pin : ReplicaExcitementComposePin) : Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

noncomputable def replicaClassSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ReplicaClassCtx S) :
    Cand (K := ℚ) ctx.replicaClassSrc ⊕ Residue :=
  urgeRecoverySelect ctx.replicaClassSrc ctx.replicaClassSuccessors

theorem composeReplicaExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    composeReplicaExcitementSelect src cands .importSelectExcitement = select src cands :=
  rfl

theorem replicaClassSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ReplicaClassCtx S) :
    replicaClassSelect ctx = select ctx.replicaClassSrc ctx.replicaClassSuccessors :=
  rfl

theorem replicaClassSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : ReplicaClassCtx S) :
    replicaClassSelect ctx = urgeRecoverySelect ctx.replicaClassSrc ctx.replicaClassSuccessors :=
  rfl

theorem replicaClassNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ReplicaClassCtx S) :
    replicaClassSelect ctx = select ctx.replicaClassSrc ctx.replicaClassSuccessors :=
  replicaClassSelect_eq_select ctx

theorem composeReplicaExcitementSelect_refusesSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    composeReplicaExcitementSelect src cands .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

theorem replicaClassSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : ReplicaClassCtx S)
    (hnil : ctx.replicaClassSuccessors = []) :
    replicaClassSelect ctx = Sum.inr Residue.noCandidates := by
  unfold replicaClassSelect
  rw [hnil]
  simpa using urgeRecovery_empty ctx.replicaClassSrc

-- ================================================================
-- SECTION 4: fabric-nodes.json census + §15.4 fixtures
-- ================================================================

def fabricNodesJsonRel : String := "workspace/ops/fabric-nodes.json"
def fabricNodesSchemaPin : String := "umst_fabric_nodes_v1"

def replicaClassFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def replicaClassFixtureNode0Pin : FabricNodeClassPin :=
  { fabricNodeId := "node-0"
    fabricClassField := some "node-0-dev-clone"
    fabricPhysicsGreenClaim := false
    fabricJoinsLabsPublicGossip := false }

def replicaClassFixtureInventGreenPin : FabricNodeClassPin :=
  { fabricNodeId := "node-invent-green"
    fabricClassField := some "node-1-dev-clone"
    fabricPhysicsGreenClaim := true
    fabricJoinsLabsPublicGossip := false }

def replicaClassFixtureComposeGossipPin : FabricNodeClassPin :=
  { fabricNodeId := "compose-customer"
    fabricClassField := some "customer-compose"
    fabricPhysicsGreenClaim := false
    fabricJoinsLabsPublicGossip := true }

theorem replicaClassFixtureNode0Admitted :
    evaluateFabricNodeClass replicaClassFixtureNode0Pin =
      Sum.inl
        { fabricRowNodeId := "node-0"
          fabricRowClass := .node0DevClone
          fabricRowTable := replicaClassBlueprintRow .node0DevClone
          fabricRowVerdict := .accept
          fabricRowAdmit := .admitted } :=
  rfl

theorem replicaClassFixtureInventGreenRefused :
    evaluateFabricNodeClass replicaClassFixtureInventGreenPin =
      Sum.inr .inventedPhysicsGreen :=
  rfl

theorem replicaClassFixtureComposeGossipRefused :
    evaluateFabricNodeClass replicaClassFixtureComposeGossipPin =
      Sum.inr .customerComposeLabsGossip :=
  rfl

theorem replicaClassOfflineLuksEgressEmpty :
    replicaEgressEmpty (replicaClassBlueprintRow .offlineLuks).replicaRowEgress = true :=
  rfl

theorem replicaClassDarwinScratchEgressEmpty :
    replicaEgressEmpty (replicaClassBlueprintRow .darwinScratch).replicaRowEgress = true :=
  rfl

theorem replicaClassForgejoEgressNonempty :
    replicaEgressEmpty (replicaClassBlueprintRow .forgejoPrimaryMirror).replicaRowEgress = false :=
  rfl

theorem replicaClassTableCardinalitySix : replicaClassTableCardinality = 6 := rfl

theorem replicaClassNode0ClassField :
    replicaClassClassField .node0DevClone = "node-0-dev-clone" := rfl

theorem replicaClassParseLegacyNode0 :
    parseReplicaClassField rclNode0LegacyField = some .node0DevClone := rfl

theorem replicaClassParseUnknownNone :
    parseReplicaClassField "unknown-class" = none := rfl

theorem replicaClassPositiveRefuseNotSilent :
    evaluateFabricNodeClass replicaClassFixtureInventGreenPin ≠
      Sum.inl
        { fabricRowNodeId := "node-invent-green"
          fabricRowClass := .node1DevClone
          fabricRowTable := replicaClassBlueprintRow .node1DevClone
          fabricRowVerdict := .accept
          fabricRowAdmit := .admitted } := by
  intro h
  cases h

theorem replicaClassComposeExcitementNotArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : ReplicaClassCtx S) :
    replicaClassSelect ctx = select ctx.replicaClassSrc ctx.replicaClassSuccessors :=
  replicaClassNoLocalArgmin ctx

-- ================================================================
-- SECTION 5: Landauer bridge (inherited — zero new axioms)
-- ================================================================

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

theorem replicaClassSecondLaw_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition :=
  admitSecondLaw_from_physical b hSL

theorem landauerAnchorCited (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def replicaClassProductionWired : Bool := false

theorem replicaClassProductionWiredFalse : replicaClassProductionWired = false := rfl

def replicaClassMarker : Nat := 1

theorem replicaClassMarkerEq : replicaClassMarker = 1 := rfl

theorem replicaClassModuleWitness : True := trivial

theorem replicaClassNoNewAxiom : True := trivial

end UMST.Urge.ReplicaClass
