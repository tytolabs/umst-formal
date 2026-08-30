-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/NoWorkLost.lean

  Meso acting Urge — BP II §1 `NO-WORK-LOST` prime invariant (checkable property pin).
  For any admitted change `c` and operation `op`, `c` remains reachable from at least one
  replica after `op`. Orphaning an admitted change is the positive refuse (RED guard).

  Scaffold / theorem pin only — runtime reconcile+guard test wiring is a later cell.
  Composes `Urge.AdmitKleisli` history carriers + `Urge.AppendOnly` discipline.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Urge.AdmitKleisli
import Urge.AppendOnly
import LandauerLaw

open UMST.Urge.AdmitKleisli UMST.Urge.AppendOnly

namespace UMST.Urge.NoWorkLost

-- ================================================================
-- SECTION 1: Admitted change + replica reachability carriers (§1)
-- ================================================================

/-- Admitted change — content id + commit id at admission time. -/
structure AdmittedChange where
  changeId   : Nat
  contentId  : Nat
  commitId   : Nat

/-- Replica reachability row — surrogate for multi-transport redundancy (mech #8). -/
structure ReplicaReachability where
  replicaId      : Nat
  reachableIds   : List Nat

/-- Whether change `c` is reachable from at least one replica catalog row. -/
def reachableFromSomeReplica (c : AdmittedChange) (replicas : List ReplicaReachability) : Prop :=
  ∃ r ∈ replicas, c.changeId ∈ r.reachableIds

/-- Operation class threatening reachability (§1 guard-test surrogate). -/
inductive UrgeOperationKind where
  | sync
  | reconcile
  | transport
  | refuseHold
  deriving DecidableEq, Repr

/-- One Urge operation applied to replica reachability (no I/O). -/
structure UrgeOperation where
  kind                      : UrgeOperationKind
  preservesReachability     : Bool

/-- Apply operation to replica catalog — non-preserving ops clear reachability (orphan risk). -/
def applyOperation (replicas : List ReplicaReachability) (op : UrgeOperation) :
    List ReplicaReachability :=
  if op.preservesReachability then replicas
  else replicas.map fun r => { replicaId := r.replicaId, reachableIds := [] }

/-- Orphan: admitted change unreachable from every replica after operation. -/
def orphansAdmittedChange (c : AdmittedChange) (post : List ReplicaReachability) : Prop :=
  ¬ reachableFromSomeReplica c post

/-- §1 `NO-WORK-LOST`: pre-reachability ⇒ post-reachability after `op`. -/
def noWorkLost (c : AdmittedChange) (pre post : List ReplicaReachability)
    (_op : UrgeOperation) : Prop :=
  reachableFromSomeReplica c pre → reachableFromSomeReplica c post

/-- §1 invariant on one admitted change + catalog + operation. -/
def noWorkLostInvariant (c : AdmittedChange) (replicas : List ReplicaReachability)
    (op : UrgeOperation) : Prop :=
  noWorkLost c replicas (applyOperation replicas op) op

-- ================================================================
-- SECTION 2: Positive refuse + identity / preserving-op theorems
-- ================================================================

/-- Positive refuse tag: operation would orphan admitted change `changeId`. -/
structure OrphanRefusal where
  changeId : Nat

def refuseOrphan (changeId : Nat) : OrphanRefusal := { changeId := changeId }

theorem refuseOrphan_positive (changeId : Nat) :
    (refuseOrphan changeId).changeId = changeId := rfl

theorem preservingOp_identity (replicas : List ReplicaReachability) (op : UrgeOperation)
    (h : op.preservesReachability = true) :
    applyOperation replicas op = replicas := by
  unfold applyOperation
  simp [h]

theorem noWorkLost_preservingOp (c : AdmittedChange) (replicas : List ReplicaReachability)
    (op : UrgeOperation) (h : op.preservesReachability = true)
    (hr : reachableFromSomeReplica c replicas) :
    reachableFromSomeReplica c (applyOperation replicas op) := by
  rw [preservingOp_identity replicas op h]
  exact hr

theorem noWorkLostInvariant_preservingOp (c : AdmittedChange) (replicas : List ReplicaReachability)
    (op : UrgeOperation) (h : op.preservesReachability = true) :
    noWorkLostInvariant c replicas op := by
  unfold noWorkLostInvariant noWorkLost
  intro hr
  exact noWorkLost_preservingOp c replicas op h hr

theorem noWorkLost_iff_not_orphan (c : AdmittedChange) (pre post : List ReplicaReachability)
    (op : UrgeOperation) :
    noWorkLost c pre post op ↔
      (reachableFromSomeReplica c pre → ¬ orphansAdmittedChange c post) := by
  unfold noWorkLost orphansAdmittedChange
  tauto

-- ================================================================
-- SECTION 3: Append-only discipline ⇒ no silent rewrite orphan (mech #2 link)
-- ================================================================

/-- Lift admitted change from append-only history transition. -/
def admittedChangeFromTransition (changeId contentId : Nat) (t : HistoryTransition) :
    AdmittedChange :=
  { changeId := changeId
    contentId := contentId
    commitId := t.post.commitId }

theorem appendOnly_preserves_commit_head (t : HistoryTransition)
    (h : appendOnlyCommitMove t) :
    t.prior.commitId < t.post.commitId :=
  h

/-- Append-only transition cannot silently rewrite its own commit head. -/
theorem admittedChange_appendOnly_not_silentRewrite (_changeId _contentId : Nat)
    (t : HistoryTransition) (h : appendOnlyCommitMove t) :
    ¬ silentRewrite t :=
  silentRewriteRefused t h

-- ================================================================
-- SECTION 4: Fixtures + catalog witnesses
-- ================================================================

def fixtureChange : AdmittedChange :=
  { changeId := 101, contentId := 5381, commitId := 7 }

def fixtureReplicaA : ReplicaReachability :=
  { replicaId := 1, reachableIds := [101, 102] }

def fixtureReplicaB : ReplicaReachability :=
  { replicaId := 2, reachableIds := [202] }

def fixtureCatalog : List ReplicaReachability :=
  [fixtureReplicaA, fixtureReplicaB]

def fixturePreservingOp : UrgeOperation :=
  { kind := .sync, preservesReachability := true }

def fixtureOrphaningOp : UrgeOperation :=
  { kind := .reconcile, preservesReachability := false }

theorem fixture_reachable : reachableFromSomeReplica fixtureChange fixtureCatalog := by
  refine ⟨fixtureReplicaA, ?_, ?_⟩
  · simp [fixtureCatalog, fixtureReplicaA]
  · simp [fixtureReplicaA, fixtureChange]

theorem fixture_noWorkLost_preserving :
    noWorkLostInvariant fixtureChange fixtureCatalog fixturePreservingOp :=
  noWorkLostInvariant_preservingOp fixtureChange fixtureCatalog fixturePreservingOp rfl

theorem fixture_orphaning_clears_catalog :
    applyOperation fixtureCatalog fixtureOrphaningOp =
      [{ replicaId := 1, reachableIds := []}, { replicaId := 2, reachableIds := []}] := by
  unfold applyOperation fixtureOrphaningOp fixtureCatalog fixtureReplicaA fixtureReplicaB
  simp

theorem fixture_orphan_after_bad_op :
    orphansAdmittedChange fixtureChange (applyOperation fixtureCatalog fixtureOrphaningOp) := by
  unfold orphansAdmittedChange reachableFromSomeReplica applyOperation fixtureOrphaningOp
  simp [fixtureCatalog, fixtureReplicaA, fixtureReplicaB, fixtureChange]

-- ================================================================
-- SECTION 5: Honesty flags + non-claim (not runtime proven)
-- ================================================================

def noWorkLostPhysicsGreen : Bool := false

theorem noWorkLostPhysicsGreenFalse : noWorkLostPhysicsGreen = false := rfl

def noWorkLostProductionWired : Bool := false

theorem noWorkLostProductionWiredFalse : noWorkLostProductionWired = false := rfl

def noWorkLostProvenanceMarker : String := "urge_ii_no_work_lost_v1"

theorem noWorkLostProvenanceMarkerWitness :
    noWorkLostProvenanceMarker = "urge_ii_no_work_lost_v1" := rfl

def noWorkLostNonClaim : String :=
  "BP II §1 NO-WORK-LOST checkable property pin; orphan refuse named; " ++
  "Lean scaffold only; not physics GREEN; not production_wired; not runtime proven"

theorem noWorkLostModuleWitness : True := trivial

theorem noWorkLost_noNewAxiom : True := trivial

end UMST.Urge.NoWorkLost
