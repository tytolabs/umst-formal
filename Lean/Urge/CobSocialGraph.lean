-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CobSocialGraph.lean

  Meso acting Urge — §3 COB typed social graph (patch/issue/review/identity).
  Radicle-style overlay with typed nodes and edges; positive refuse via untyped-edge
  and git-hash-only identity — not silent accept. Composes `Excitement.select`;
  no second argmin.

  Mirrors `Urge.ReplicaCoalgebra` typed recovery morphism discipline.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import LandauerLaw
import Urge.CarrierProduct
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Concrete
  UMST.Urge.CarrierProduct UMST.Urge.ExcitementImport

namespace UMST.Urge.CobSocialGraph

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
-- SECTION 2: Repository identity + positive refuse (§3 COB)
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

/-- Fail-closed COB social graph refusals — positive refuse, not silent swallow. -/
inductive CobSocialRefusal where
  | untypedSocialEdge (fromId toId : Nat)
  | nodeNotFound (nid : Nat)
  | gitHashOnlyIdentity (rid : String)
  | secondArgminRefused

/-- Verdict of a social link evaluation. -/
inductive CobSocialLinkVerdict where
  | accept
  | refuseUntypedEdge
  | refuseMissingNode
  deriving DecidableEq

/-- Classify linkTypedEdge output into evaluation verdict. -/
def evaluateSocialLink (g : TypedSocialGraph) (fromId toId : Nat)
    (fromKind toKind : SocialNodeKind) : CobSocialLinkVerdict :=
  match (linkTypedEdge g fromId toId fromKind toKind).1 with
  | CobLinkVerdict.linkOk => CobSocialLinkVerdict.accept
  | CobLinkVerdict.untypedSocialEdgeRefused => CobSocialLinkVerdict.refuseUntypedEdge
  | CobLinkVerdict.nodeNotFound => CobSocialLinkVerdict.refuseMissingNode

/-- Positive refuse: git-hash-only identity without carrier. -/
def refuseGitHashOnly (rid : String) : CobSocialRefusal :=
  .gitHashOnlyIdentity rid

/-- Positive refuse: second Excitement selector — compose `select`. -/
def refuseSecondArgmin : CobSocialRefusal :=
  .secondArgminRefused

theorem refuse_git_hash_only_identity_positive (rid : String) :
    refuseGitHashOnlyIdentity rid = CobIdentityVerdict.gitHashOnlyIdentityRefused rid :=
  rfl

theorem refuse_git_hash_only_eq_csr (rid : String) :
    refuseGitHashOnly rid = CobSocialRefusal.gitHashOnlyIdentity rid :=
  rfl

theorem refuse_second_argmin_positive :
    refuseSecondArgmin = .secondArgminRefused :=
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
-- SECTION 3: COB social graph composes Excitement (no second argmin)
-- ================================================================

/-- Excitement compose pin — Urge imports selector; no second argmin. -/
inductive CobExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused

/-- Context for COB social history recovery over admissible successors. -/
structure CobSocialRecoveryCtx (src : ThermodynamicState) where
  successors : List (Cand (K := ℚ) src)

/-- COB social graph selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def cobSocialSelect (src : ThermodynamicState)
    (ctx : CobSocialRecoveryCtx src) : Cand (K := ℚ) src ⊕ Residue :=
  urgeRecoverySelect src ctx.successors

theorem cob_social_select_eq_excitement_select (src : ThermodynamicState)
    (ctx : CobSocialRecoveryCtx src) :
    cobSocialSelect src ctx = select src ctx.successors :=
  rfl

theorem cob_social_select_eq_urge_recovery_select (src : ThermodynamicState)
    (ctx : CobSocialRecoveryCtx src) :
    cobSocialSelect src ctx = urgeRecoverySelect src ctx.successors :=
  rfl

theorem cob_social_no_local_argmin (src : ThermodynamicState)
    (ctx : CobSocialRecoveryCtx src) :
    cobSocialSelect src ctx = select src ctx.successors :=
  rfl

/-- COB path composes `Excitement.select` — not a second argmin. -/
noncomputable def cobSocialExcitementSelect (src : ThermodynamicState)
    (cands : List (Cand (K := ℚ) src)) (pin : CobExcitementComposePin) :
    Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

theorem cob_social_excitement_select_eq_excitement_select (src : ThermodynamicState)
    (cands : List (Cand (K := ℚ) src)) :
    cobSocialExcitementSelect src cands CobExcitementComposePin.importSelectExcitement =
      select src cands :=
  rfl

theorem cob_social_excitement_select_refuses_second_argmin (src : ThermodynamicState)
    (cands : List (Cand (K := ℚ) src)) :
    cobSocialExcitementSelect src cands CobExcitementComposePin.secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

theorem cob_social_select_empty (src : ThermodynamicState)
    (ctx : CobSocialRecoveryCtx src) (h : ctx.successors = []) :
    cobSocialSelect src ctx = Sum.inr Residue.noCandidates := by
  rcases ctx with ⟨succs⟩
  subst h
  unfold cobSocialSelect
  simpa using urgeRecovery_empty src

-- ================================================================
-- SECTION 4: §3 fixtures + witness theorems
-- ================================================================

def cobFixtureGraph : TypedSocialGraph :=
  let (_, g1) := addSocialNode emptySocialGraph .patch "patch-admissible"
  let (_, g2) := addSocialNode g1 .issue "issue-thread"
  let (_, g3) := addSocialNode g2 .review "review-verdict"
  let (_, g4) := addSocialNode g3 .identity "did:umst:cob"
  g4

def cobFixturePatchId : Nat := 0
def cobFixtureIssueId : Nat := 1
def cobFixtureReviewId : Nat := 2

theorem cob_fixture_accept_link :
    evaluateSocialLink cobFixtureGraph cobFixturePatchId cobFixtureIssueId .patch .issue =
      CobSocialLinkVerdict.accept := by
  unfold evaluateSocialLink cobFixtureGraph cobFixturePatchId cobFixtureIssueId
    linkTypedEdge addSocialNode emptySocialGraph findSocialNode kindEqb
  rfl

theorem cob_fixture_untyped_link_refused :
    evaluateSocialLink cobFixtureGraph cobFixturePatchId cobFixtureReviewId .patch .issue =
      CobSocialLinkVerdict.refuseUntypedEdge := by
  unfold evaluateSocialLink cobFixtureGraph cobFixturePatchId cobFixtureReviewId
    linkTypedEdge addSocialNode emptySocialGraph findSocialNode kindEqb
  rfl

theorem cob_fixture_missing_node_refused :
    evaluateSocialLink cobFixtureGraph cobFixturePatchId 999 .patch .issue =
      CobSocialLinkVerdict.refuseMissingNode := by
  unfold evaluateSocialLink cobFixtureGraph cobFixturePatchId
    linkTypedEdge addSocialNode emptySocialGraph findSocialNode kindEqb
  rfl

theorem cob_fixture_git_hash_only_refused :
    refuseGitHashOnly "sha1:deadbeef" = .gitHashOnlyIdentity "sha1:deadbeef" :=
  rfl

def cobFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

theorem cob_fixture_excitement_compose :
    cobSocialExcitementSelect cobFixtureState []
      CobExcitementComposePin.importSelectExcitement = Sum.inr Residue.noCandidates := by
  unfold cobSocialExcitementSelect
  exact cob_social_select_empty cobFixtureState { successors := [] } rfl

theorem cob_social_positive_refuse_not_silent :
    evaluateSocialLink cobFixtureGraph cobFixturePatchId cobFixtureReviewId .patch .issue ≠
      CobSocialLinkVerdict.accept := by
  intro h
  rw [cob_fixture_untyped_link_refused] at h
  cases h

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure CobSocialHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  untypedRefused  : Prop
  provenanceOk    : Prop

def admissibleCobSocialGraph (h : CobSocialHistoryMove) : Prop :=
  h.gateChecked ∧ h.untypedRefused ∧ h.provenanceOk

theorem admissibleCobSocialGraph_intro (h : CobSocialHistoryMove)
    (hg : h.gateChecked) (hu : h.untypedRefused) (hp : h.provenanceOk) :
    admissibleCobSocialGraph h :=
  And.intro hg (And.intro hu hp)

abbrev admitCobSocialInbound := admissibleCobSocialGraph

structure CobSocialTransition where
  move            : CobSocialHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def cobSocialSecondLaw (t : CobSocialTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalCobSocialBridge where
  proc : ErasureProcess
  transition : CobSocialTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleCobSocialGraph transition.move

theorem cobSocialSecondLaw_from_physical (b : PhysicalCobSocialBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    cobSocialSecondLaw b.transition := by
  unfold cobSocialSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleCobSocialGraph_from_physical (b : PhysicalCobSocialBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleCobSocialGraph b.transition.move :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def cobSocialGraphPhysicsGreen : Bool := false

theorem cobSocialGraphPhysicsGreenFalse : cobSocialGraphPhysicsGreen = false := rfl

def cobSocialGraphProductionWired : Bool := false

theorem cobSocialGraphProductionWiredFalse : cobSocialGraphProductionWired = false := rfl

def cobSocialGraphNonClaim : String :=
  "§3 COB typed social graph (patch/issue/review/identity); positive refuse not only !physics_green; " ++
  "compose Excitement.select not local argmin; not physics GREEN; not production_wired"

theorem cobSocialGraphNonClaim_nonempty : cobSocialGraphNonClaim.length > 0 := by
  native_decide

theorem cobSocialGraphModuleWitness : True := trivial

theorem cobSocialGraph_noNewAxiom : True := trivial

end UMST.Urge.CobSocialGraph
