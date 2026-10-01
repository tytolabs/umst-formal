-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/FabricNodes.lean

  Meso acting Urge — §15 fabric-nodes replica-class pin.
  Declared fabric nodes (`fabric-nodes.json`) pin to §15.4 replica-class table rows —
  software schema, not Forgejo installer. Compose `fabric-excitement-select` — no second
  ℚ argmin.

  Mirrors `Urge.ReplicaCoalgebra` typed recovery morphism discipline.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.FabricNodes

-- ================================================================
-- SECTION 1: §15.4 replica-class + fabric-node pin carriers
-- ================================================================

inductive FabricReplicaClass where
  | node0DevClone
  | node1DevClone
  | forgejoPrimaryMirror
  | darwinScratch
  | offlineLuks
  | customerCompose
  deriving DecidableEq, Repr

inductive FabricAuthority where
  | workingCopy
  | canonicalRemote
  | scratchPlane
  | disasterCopy
  | customerOnSite
  deriving DecidableEq, Repr

def fabricReplicaEgressEmpty (c : FabricReplicaClass) : Bool :=
  match c with
  | .darwinScratch | .offlineLuks => true
  | _ => false

def fabricReplicaFromNodeId (id : Nat) : Option FabricReplicaClass :=
  match id with
  | 0 => some .node0DevClone
  | 1 => some .node1DevClone
  | _ => none

def fabricAuthorityOf (c : FabricReplicaClass) : FabricAuthority :=
  match c with
  | .node0DevClone | .node1DevClone => .workingCopy
  | .forgejoPrimaryMirror => .canonicalRemote
  | .darwinScratch => .scratchPlane
  | .offlineLuks => .disasterCopy
  | .customerCompose => .customerOnSite

def fabricNodesSchemaPin : String := "umst_fabric_nodes_v1"

def fabricNodesJsonRel : String := "workspace/ops/fabric-nodes.json"

def fabricNodesSchemaValid (schemaOk : Bool) : Bool := schemaOk

structure FabricUcrsStamp where
  seq         : Nat
  wallHasT    : Bool

structure FabricMergeSafeCert where
  mergeSafe : Bool

structure FabricNodePin where
  stepId                  : Nat
  nodeId                  : Nat
  schemaOk                : Bool
  byzantineMesh           : Bool
  claimsForgejoRunning    : Bool
  ucrs                    : FabricUcrsStamp
  mergeSafe               : FabricMergeSafeCert
  provenanceIntact        : Bool

-- ================================================================
-- SECTION 2: Witness bundle (§15 morphism must preserve stamps)
-- ================================================================

structure FabricNodeWitness where
  ucrs                : FabricUcrsStamp
  mergeSafe           : FabricMergeSafeCert
  provenanceIntact    : Bool

def witnessFromFabricPin (pin : FabricNodePin) : FabricNodeWitness :=
  { ucrs := pin.ucrs
    mergeSafe := pin.mergeSafe
    provenanceIntact := pin.provenanceIntact }

structure FabricNodeMorphism where
  fromPin               : FabricNodePin
  toReplica             : FabricReplicaClass
  witness               : FabricNodeWitness
  excitementSelected    : Bool

-- ================================================================
-- SECTION 3: MergeSafe certificate — pin must not violate tier disjointness
-- ================================================================

def fabricMergeSafeAdmits (cert : FabricMergeSafeCert) : Bool :=
  cert.mergeSafe

-- ================================================================
-- SECTION 4: Admissibility conjunct + fabric-node operation class
-- ================================================================

structure FabricAdmissibilityConjunct where
  gateOk                  : Bool
  mergeSafe               : Bool
  excitementPreserves     : Bool

def fabricConjunctAdmits (c : FabricAdmissibilityConjunct) : Bool :=
  c.gateOk && c.mergeSafe && c.excitementPreserves

inductive FabricNodesVerdict where
  | pinOk
  | byzantineMeshRefused
  | forgejoInstallRefused
  | inadmissible
  deriving DecidableEq, Repr

def evaluateFabricNodesOperation (byzantineMesh claimsForgejoRunning : Bool) : FabricNodesVerdict :=
  if byzantineMesh then .byzantineMeshRefused
  else if claimsForgejoRunning then .forgejoInstallRefused
  else .pinOk

-- ================================================================
-- SECTION 5: Typed refusal (positive refuse — not only !physics_green)
-- ================================================================

inductive FabricNodesRefusal where
  | byzantineMeshClaim
  | forgejoInstallClaim
  | unknownFabricNodeId (id : Nat)
  | schemaMismatch
  | secondArgmin
  | productionWired
  | gateRejected (seq : Nat)
  | mergeUnsafe (stepId : Nat)
  | provenanceLoss (stepId : Nat)
  | replicaClassMismatch
  deriving Repr

def refuseByzantineMeshClaim : FabricNodesRefusal := .byzantineMeshClaim

def refuseForgejoInstallClaim : FabricNodesRefusal := .forgejoInstallClaim

def admitFabricNodePin (pin : FabricNodePin) : Unit ⊕ FabricNodesRefusal :=
  if pin.byzantineMesh then Sum.inr .byzantineMeshClaim
  else if pin.claimsForgejoRunning then Sum.inr .forgejoInstallClaim
  else if !fabricNodesSchemaValid pin.schemaOk then Sum.inr .schemaMismatch
  else match fabricReplicaFromNodeId pin.nodeId with
    | none => Sum.inr (.unknownFabricNodeId pin.nodeId)
    | some _ => Sum.inl ()

def applyFabricNodeMorphism (pin : FabricNodePin) (toReplica : FabricReplicaClass)
    (conjunct : FabricAdmissibilityConjunct) (excitementSelected : Bool) :
    FabricNodeMorphism ⊕ FabricNodesRefusal :=
  match admitFabricNodePin pin with
  | Sum.inr r => Sum.inr r
  | Sum.inl _ =>
    if !fabricConjunctAdmits conjunct then
      Sum.inr (.gateRejected pin.ucrs.seq)
    else if !fabricMergeSafeAdmits pin.mergeSafe then
      Sum.inr (.mergeUnsafe pin.stepId)
    else if !pin.provenanceIntact then
      Sum.inr (.provenanceLoss pin.stepId)
    else if !excitementSelected then
      Sum.inr (.provenanceLoss pin.stepId)
    else
      Sum.inl
        { fromPin := pin
          toReplica := toReplica
          witness := witnessFromFabricPin pin
          excitementSelected := excitementSelected }

theorem fabricNodesByzantineMeshRefused :
    evaluateFabricNodesOperation true false = .byzantineMeshRefused := rfl

theorem fabricNodesForgejoInstallRefused :
    evaluateFabricNodesOperation false true = .forgejoInstallRefused := rfl

theorem fabricNodesPinOkWhenHonest :
    evaluateFabricNodesOperation false false = .pinOk := rfl

theorem fabricNodesPositiveRefuseNotSilent :
    evaluateFabricNodesOperation true false ≠ .pinOk := by decide

theorem fabricNodesForgejoRefuseNotSilent :
    evaluateFabricNodesOperation false true ≠ .pinOk := by decide

-- ================================================================
-- SECTION 6: Excitement compose pin (no second ℚ argmin)
-- ================================================================

noncomputable def urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

-- ================================================================
-- SECTION 7: §15 fixtures + Landauer bridge (ReplicaCoalgebra-style)
-- ================================================================

def fabricFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def fabricFixtureUcrs : FabricUcrsStamp :=
  { seq := 7, wallHasT := true }

def fabricFixtureMergeSafe : FabricMergeSafeCert :=
  { mergeSafe := true }

def fabricFixtureNode0Pin : FabricNodePin :=
  { stepId := 1
    nodeId := 0
    schemaOk := true
    byzantineMesh := false
    claimsForgejoRunning := false
    ucrs := fabricFixtureUcrs
    mergeSafe := fabricFixtureMergeSafe
    provenanceIntact := true }

def fabricFixtureConjunct : FabricAdmissibilityConjunct :=
  { gateOk := true, mergeSafe := true, excitementPreserves := true }

theorem fabricFixtureAdmitNode0Ok :
    admitFabricNodePin fabricFixtureNode0Pin = Sum.inl () := rfl

theorem fabricFixtureApplyMorphismOk :
    applyFabricNodeMorphism fabricFixtureNode0Pin .node0DevClone fabricFixtureConjunct true =
      Sum.inl
        { fromPin := fabricFixtureNode0Pin
          toReplica := .node0DevClone
          witness := witnessFromFabricPin fabricFixtureNode0Pin
          excitementSelected := true } :=
  rfl

theorem fabricNode0MapsToDevClone :
    fabricReplicaFromNodeId 0 = some .node0DevClone := rfl

theorem fabricNode1MapsToDevClone :
    fabricReplicaFromNodeId 1 = some .node1DevClone := rfl

theorem fabricUnknownNodeIdRefused :
    fabricReplicaFromNodeId 99 = none := rfl

theorem fabricFixtureWitnessPreservesUcrs :
    (witnessFromFabricPin fabricFixtureNode0Pin).ucrs = fabricFixtureUcrs := rfl

def fabricFixtureByzantinePin : FabricNodePin :=
  { stepId := 1
    nodeId := 0
    schemaOk := true
    byzantineMesh := true
    claimsForgejoRunning := false
    ucrs := fabricFixtureUcrs
    mergeSafe := fabricFixtureMergeSafe
    provenanceIntact := true }

def fabricFixtureForgejoPin : FabricNodePin :=
  { stepId := 1
    nodeId := 0
    schemaOk := true
    byzantineMesh := false
    claimsForgejoRunning := true
    ucrs := fabricFixtureUcrs
    mergeSafe := fabricFixtureMergeSafe
    provenanceIntact := true }

theorem fabricFixtureByzantineRefused :
    admitFabricNodePin fabricFixtureByzantinePin = Sum.inr .byzantineMeshClaim := rfl

theorem fabricFixtureForgejoRefused :
    admitFabricNodePin fabricFixtureForgejoPin = Sum.inr .forgejoInstallClaim := rfl

structure FabricHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissibleFabricHistoryMove (h : FabricHistoryMove) : Prop :=
  h.gateChecked ∧ h.mergeSafe ∧ h.provenanceOk

theorem admissibleFabricHistoryMove_intro (h : FabricHistoryMove)
    (hg : h.gateChecked) (hm : h.mergeSafe) (hp : h.provenanceOk) :
    admissibleFabricHistoryMove h :=
  And.intro hg (And.intro hm hp)

abbrev admitFabricInbound := admissibleFabricHistoryMove

def fabricNodesMarker : Nat := 1

end UMST.Urge.FabricNodes
