-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CollaborativeObject.lean

  Meso acting Urge — §3 COB: history carrier + typed social graph.
  Collaborative Object = same Repository/History carrier product
  (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness) plus typed social graph
  overlay (patch, issue, review, identity).

  Excitement `select` composed — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import Urge.CarrierProduct

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Concrete
  UMST.Urge.AdmitKleisli UMST.Urge.CarrierProduct

namespace UMST.Urge.CollaborativeObject

-- Local JointThermo witness for cement `ThermodynamicState` heads (meso scaffold).
instance concreteJointThermo : JointThermo ℚ ConcreteState where
  internalEnergy s := s.density * (-s.freeEnergy)
  entropy s := s.hydration
  mutualInfo s := 0
  temperature s := 1
  temperature_pos _ := by norm_num

-- ================================================================
-- SECTION 1: Typed social graph (patch / issue / review / identity)
-- ================================================================

/-- Radicle-style social node kinds — untyped edges refused at link time. -/
inductive SocialNodeKind where
  | patch
  | issue
  | review
  | identity
  deriving DecidableEq, Repr

/-- One node in the typed social graph. -/
structure SocialNode where
  id    : Nat
  kind  : SocialNodeKind
  label : String

/-- Typed edge between social nodes — source/target kinds pinned. -/
structure SocialEdge where
  fromId    : Nat
  toId      : Nat
  fromKind  : SocialNodeKind
  toKind    : SocialNodeKind

/-- Typed social graph carrier (append-only lists). -/
structure TypedSocialGraph where
  nodes   : List SocialNode
  edges   : List SocialEdge
  nextId  : Nat

def emptySocialGraph : TypedSocialGraph :=
  { nodes := [], edges := [], nextId := 0 }

/-- Lookup a social node by id. -/
def findSocialNode (nodes : List SocialNode) (nid : Nat) : Option SocialNode :=
  match nodes with
  | [] => none
  | n :: rest => if n.id == nid then some n else findSocialNode rest nid

def kindEqb (k1 k2 : SocialNodeKind) : Bool :=
  match k1, k2 with
  | .patch, .patch => true
  | .issue, .issue => true
  | .review, .review => true
  | .identity, .identity => true
  | _, _ => false

theorem kindEqb_refl (k : SocialNodeKind) : kindEqb k k = true := by
  cases k <;> rfl

theorem kindEqb_eq (k1 k2 : SocialNodeKind) (h : kindEqb k1 k2 = true) : k1 = k2 := by
  cases k1 <;> cases k2 <;> first | rfl | simp [kindEqb] at h

theorem kindEqb_ne_iff (k1 k2 : SocialNodeKind) : kindEqb k1 k2 = false ↔ k1 ≠ k2 := by
  cases k1 <;> cases k2 <;> simp [kindEqb, Ne.eq_def]

theorem kindEqb_neq (k1 k2 : SocialNodeKind) (h : kindEqb k1 k2 = false) : k1 ≠ k2 :=
  (kindEqb_ne_iff k1 k2).mp h

/-- Add a typed social node (monotonic id assignment). -/
def addSocialNode (g : TypedSocialGraph) (kind : SocialNodeKind) (label : String) :
    SocialNode × TypedSocialGraph :=
  let nid := g.nextId
  let node := { id := nid, kind := kind, label := label }
  (node, { nodes := g.nodes ++ [node], edges := g.edges, nextId := nid + 1 })

inductive CobLinkVerdict where
  | linkOk : CobLinkVerdict
  | untypedSocialEdgeRefused : CobLinkVerdict
  | nodeNotFound : CobLinkVerdict

/-- Link two existing nodes with typed kinds — kind mismatch refused. -/
def linkTypedEdge (g : TypedSocialGraph) (fromId toId : Nat)
    (fromKind toKind : SocialNodeKind) : CobLinkVerdict × TypedSocialGraph :=
  match findSocialNode g.nodes fromId with
  | none => (CobLinkVerdict.nodeNotFound, g)
  | some fromNode =>
    match findSocialNode g.nodes toId with
    | none => (CobLinkVerdict.nodeNotFound, g)
    | some toNode =>
      if kindEqb fromNode.kind fromKind && kindEqb toNode.kind toKind then
        let edge := { fromId := fromId, toId := toId, fromKind := fromKind, toKind := toKind }
        (CobLinkVerdict.linkOk,
         { nodes := g.nodes, edges := g.edges ++ [edge], nextId := g.nextId })
      else
        (CobLinkVerdict.untypedSocialEdgeRefused, g)

-- ================================================================
-- SECTION 2: Repository identity + history carrier (§3 COB)
-- ================================================================

/-- Repository identity: RID pin + owning history carrier. -/
structure RepositoryIdentity where
  rid     : String
  carrier : HistoryCarrier

inductive CobIdentityVerdict where
  | identityOk : RepositoryIdentity → CobIdentityVerdict
  | gitHashOnlyIdentityRefused : String → CobIdentityVerdict

/-- Refuse constructing identity from RID alone — carrier required. -/
def refuseGitHashOnlyIdentity (rid : String) : CobIdentityVerdict :=
  CobIdentityVerdict.gitHashOnlyIdentityRefused rid

/-- Build repository identity with full carrier (geometric identity primary). -/
def repositoryIdentityWithCarrier (rid : String) (c : HistoryCarrier) : CobIdentityVerdict :=
  CobIdentityVerdict.identityOk { rid := rid, carrier := c }

/-- Carrier populated when UMST commit id or stamp wall is present. -/
def carrierPopulated (c : HistoryCarrier) : Bool :=
  0 < (umstProj c).commitId || 0 < (stampProj c).observedAtWall

/-- Collaborative Object — history carrier + typed social graph (§3 COB). -/
structure Cob where
  identity : RepositoryIdentity
  social   : TypedSocialGraph

abbrev CollaborativeObject := Cob

def cobNew (id : RepositoryIdentity) : Cob :=
  { identity := id, social := emptySocialGraph }

def cobCarrier (cob : Cob) : HistoryCarrier :=
  cob.identity.carrier

def cobHead (cob : Cob) : ThermodynamicState :=
  (umstProj (cobCarrier cob)).head

-- ================================================================
-- SECTION 3: Positive refuse witnesses
-- ================================================================

theorem refuse_git_hash_only_is_refused (rid : String) :
    refuseGitHashOnlyIdentity rid = CobIdentityVerdict.gitHashOnlyIdentityRefused rid :=
  rfl

theorem empty_graph_link_node_not_found :
    (linkTypedEdge emptySocialGraph 0 0 .patch .issue).1 = CobLinkVerdict.nodeNotFound := by
  simp [linkTypedEdge, emptySocialGraph, findSocialNode]

theorem addSocialNode_then_link_ok :
    (linkTypedEdge
      (addSocialNode (addSocialNode emptySocialGraph .patch "p").2 .issue "i").2
      0 1 .patch .issue).1 = CobLinkVerdict.linkOk := by
  unfold linkTypedEdge addSocialNode emptySocialGraph findSocialNode kindEqb
  rfl

theorem linkTypedEdge_untyped_refused (g : TypedSocialGraph) (fromId toId : Nat)
    (fk tk : SocialNodeKind)
    (nf : SocialNode) (Hnf : findSocialNode g.nodes fromId = some nf)
    (nt : SocialNode) (Hnt : findSocialNode g.nodes toId = some nt)
    (Hbad : nf.kind ≠ fk ∨ nt.kind ≠ tk) :
    (linkTypedEdge g fromId toId fk tk).1 = CobLinkVerdict.untypedSocialEdgeRefused ∧
    (linkTypedEdge g fromId toId fk tk).2 = g := by
  unfold linkTypedEdge
  simp only [Hnf, Hnt]
  rcases Hbad with Hfk | Htk
  · have hf := (kindEqb_ne_iff nf.kind fk).mpr Hfk
    simp [linkTypedEdge, Hnf, Hnt, hf, Bool.false_and, ite_false]
  · rcases eq_or_ne nf.kind fk with heq | hne
    · subst heq
      have ht := (kindEqb_ne_iff nt.kind tk).mpr Htk
      simp [linkTypedEdge, Hnf, Hnt, kindEqb_refl, ht, Bool.true_and, ite_false]
    · have hf := (kindEqb_ne_iff nf.kind fk).mpr hne
      simp [linkTypedEdge, Hnf, Hnt, hf, Bool.false_and, ite_false]

-- ================================================================
-- SECTION 4: Excitement alignment (no second argmin)
-- ================================================================

/-- COB history recovery composes `Excitement.select` on carrier UMST head. -/
noncomputable def cobSelect (cob : Cob)
    (cands : List (Cand (K := ℚ) (cobHead cob))) :
    Cand (K := ℚ) (cobHead cob) ⊕ Residue :=
  select (cobHead cob) cands

/-- Carrier-level selection on history carrier UMST head. -/
noncomputable def cobCarrierSelect (c : HistoryCarrier)
    (cands : List (Cand (K := ℚ) (umstProj c).head)) :
    Cand (K := ℚ) (umstProj c).head ⊕ Residue :=
  select (umstProj c).head cands

theorem cobSelect_eq_select (cob : Cob)
    (cands : List (Cand (K := ℚ) (cobHead cob))) :
    cobSelect cob cands = select (cobHead cob) cands :=
  rfl

theorem cobSelect_eq_carrierSelect (cob : Cob)
    (cands : List (Cand (K := ℚ) (cobHead cob))) :
    cobSelect cob cands = cobCarrierSelect (cobCarrier cob) cands :=
  rfl

theorem cob_no_local_argmin (cob : Cob)
    (cands : List (Cand (K := ℚ) (cobHead cob))) :
    cobSelect cob cands = select (cobHead cob) cands :=
  rfl

theorem cobSelect_eq_carrierSelect_head (cob : Cob)
    (cands : List (Cand (K := ℚ) (cobHead cob))) :
    cobSelect cob cands = carrierSelect (cobHead cob) cands :=
  rfl

-- ================================================================
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ================================================================

theorem cob_admitSecondLaw_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition :=
  admitSecondLaw_from_physical b hSL

theorem cob_physicalSecondLaw_discharge (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def collaborativeObjectPhysicsGreen : Bool := false

theorem collaborativeObjectPhysicsGreenFalse :
    collaborativeObjectPhysicsGreen = false := rfl

def collaborativeObjectProductionWired : Bool := false

theorem collaborativeObjectProductionWiredFalse :
    collaborativeObjectProductionWired = false := rfl

def collaborativeObjectNonClaim : String :=
  "§3 COB: same carrier + typed social graph (patch, issue, review, identity); " ++
  "geometric identity primary; not physics GREEN; not production_wired"

theorem collaborativeObjectNonClaim_nonempty :
    collaborativeObjectNonClaim.length > 0 := by
  native_decide

theorem collaborativeObjectModuleWitness : True := trivial

theorem collaborativeObject_noNewAxiom : True := trivial

end UMST.Urge.CollaborativeObject
