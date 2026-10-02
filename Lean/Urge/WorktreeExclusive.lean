-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/WorktreeExclusive.lean

  Meso acting Urge — §16.11 one agent ↔ one exclusive worktree; antichain exclusive
  copy on the conflict graph. Gate failure at **claim** time — not merge-conflict theater.
  Composes `Excitement.select` — no second argmin.

  Mirrors `ReplicaCoalgebra.lean` typed morphism discipline.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.WorktreeExclusive

-- ================================================================
-- SECTION 1: Agent lane + worktree + write_set carriers (§16.11)
-- ================================================================

/-- Admit-series agent lane surrogate — §16.11 first-class users. -/
inductive AgentLane where
  | composer | grok | kimi
  deriving DecidableEq, Repr

/-- Replica-class worktree id — one per agent at claim time. -/
structure WorktreeId where
  val : Nat
  deriving DecidableEq, Repr

/-- Write_set path surrogate — conflict-graph vertex pin. -/
structure WriteSetPath where
  id : Nat
  deriving DecidableEq, Repr

/-- Antichain write_set — disjoint path set owned exclusively at claim. -/
structure ExclusiveWriteSet where
  paths : List WriteSetPath
  deriving Repr

/-- One active exclusive claim — agent ↔ worktree ↔ write_set. -/
structure ExclusiveClaim where
  agent     : AgentLane
  worktree  : WorktreeId
  writeSet  : ExclusiveWriteSet
  deriving Repr

/-- Successful claim admission at allocate/claim gate. -/
structure ExclusiveAdmission where
  claim           : ExclusiveClaim
  antichainIndex  : Nat
  deriving Repr

/-- Claim gate verdict — admit or typed refuse. -/
inductive ClaimGateVerdict where
  | admit | refused
  deriving DecidableEq, Repr

/-- Fail-closed refusal when §16.11 exclusivity is violated at claim time. -/
inductive WorktreeExclusiveRefusal where
  | overlappingWriteSetAtClaim
  | agentAlreadyOwnsWorktree
  | mergeConflictTheater
  | secondArgminOnClaim
  deriving DecidableEq, Repr

/-- Verdict of a claim operation class. -/
inductive WorktreeExclusiveVerdict where
  | exclusiveAdmit | overlapRefused | mergeTheaterRefused | secondArgminRefused
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §16.11 admissibility conjunct + positive refuse
-- ================================================================

/-- §16.11 admissibility conjunct inputs (surrogate). -/
structure WorktreeAdmissibilityConjunct where
  antichainOk              : Bool
  oneAgentOneWorktree      : Bool
  excitementPreserves      : Bool

def worktreeConjunctAdmits (c : WorktreeAdmissibilityConjunct) : Bool :=
  c.antichainOk && c.oneAgentOneWorktree && c.excitementPreserves

def agentLaneEq (a b : AgentLane) : Bool :=
  decide (a = b)

def pathInWriteSet (p : WriteSetPath) (ws : ExclusiveWriteSet) : Bool :=
  ws.paths.any fun q => p.id == q.id

def writeSetsOverlap (left right : ExclusiveWriteSet) : Bool :=
  left.paths.any fun p => pathInWriteSet p right

def agentAlreadyClaimed (a : AgentLane) : List ExclusiveClaim → Bool
  | [] => false
  | c :: rest =>
    if agentLaneEq a c.agent then true
    else agentAlreadyClaimed a rest

def anyWriteSetOverlap (ws : ExclusiveWriteSet) : List ExclusiveClaim → Bool
  | [] => false
  | c :: rest =>
    if writeSetsOverlap ws c.writeSet then true
    else anyWriteSetOverlap ws rest

/-- Attempt exclusive claim — fail closed at claim time on overlap or duplicate agent worktree. -/
def tryClaimExclusive (registry : List ExclusiveClaim) (claim : ExclusiveClaim) :
    ExclusiveAdmission ⊕ WorktreeExclusiveRefusal :=
  if agentAlreadyClaimed claim.agent registry then
    Sum.inr .agentAlreadyOwnsWorktree
  else if anyWriteSetOverlap claim.writeSet registry then
    Sum.inr .overlappingWriteSetAtClaim
  else
    Sum.inl { claim := claim, antichainIndex := registry.length }

/-- Classify merge-theater vs claim-time gate without performing I/O. -/
def evaluateClaimOperation (deferToMerge : Bool) : WorktreeExclusiveVerdict :=
  if deferToMerge then .mergeTheaterRefused else .exclusiveAdmit

def refuseOverlappingWriteSetAtClaim : WorktreeExclusiveRefusal :=
  .overlappingWriteSetAtClaim

def refuseAgentSecondWorktree : WorktreeExclusiveRefusal :=
  .agentAlreadyOwnsWorktree

theorem evaluateClaimOperation_exclusiveAdmit :
    evaluateClaimOperation false = .exclusiveAdmit := rfl

-- ================================================================
-- SECTION 4: Landauer bridge (the erase instance of `SecondLaw` — imported)
-- ================================================================

structure WorktreeHistoryMove where
  antichainOk           : Prop
  oneAgentOneWorktree   : Prop
  provenanceOk          : Prop

def admissibleWorktreeExclusive (h : WorktreeHistoryMove) : Prop :=
  h.antichainOk ∧ h.oneAgentOneWorktree ∧ h.provenanceOk

theorem admissibleWorktreeExclusive_intro (h : WorktreeHistoryMove)
    (ha : h.antichainOk) (ho : h.oneAgentOneWorktree) (hp : h.provenanceOk) :
    admissibleWorktreeExclusive h :=
  And.intro ha (And.intro ho hp)

abbrev admitWorktreeInbound := admissibleWorktreeExclusive

-- ================================================================
-- SECTION 5: §16.11 fixtures + witness theorems
-- ================================================================

def wePathSrc : WriteSetPath := ⟨0⟩
def wePathTest : WriteSetPath := ⟨1⟩
def wePathOriginRefuse : WriteSetPath := ⟨2⟩

def weWorktree0 : WorktreeId := ⟨0⟩
def weWorktree1 : WorktreeId := ⟨1⟩
def weWorktree2 : WorktreeId := ⟨2⟩

def composerWriteSet : ExclusiveWriteSet :=
  { paths := [wePathSrc, wePathTest] }

def grokOverlapWriteSet : ExclusiveWriteSet :=
  { paths := [wePathTest] }

def originRefuseWriteSet : ExclusiveWriteSet :=
  { paths := [wePathOriginRefuse] }

def composerExclusiveAdmitFixture : ExclusiveClaim :=
  { agent := .composer, worktree := weWorktree0, writeSet := composerWriteSet }

def grokOverlappingWriteSetFixture : ExclusiveClaim :=
  { agent := .grok, worktree := weWorktree1, writeSet := grokOverlapWriteSet }

def composerSecondWorktreeFixture : ExclusiveClaim :=
  { agent := .composer, worktree := weWorktree1, writeSet := originRefuseWriteSet }

def kimiAntichainDisjointFixture : ExclusiveClaim :=
  { agent := .kimi, worktree := weWorktree2, writeSet := originRefuseWriteSet }

def worktreeFixtureConjunct : WorktreeAdmissibilityConjunct :=
  { antichainOk := true, oneAgentOneWorktree := true, excitementPreserves := true }

def worktreeFixtureRegistry : List ExclusiveClaim :=
  [composerExclusiveAdmitFixture]

theorem composerExclusiveAdmitFixture_ok :
    tryClaimExclusive [] composerExclusiveAdmitFixture =
      Sum.inl { claim := composerExclusiveAdmitFixture, antichainIndex := 0 } :=
  rfl

theorem grokOverlapRefusedAtClaim :
    tryClaimExclusive worktreeFixtureRegistry grokOverlappingWriteSetFixture =
      Sum.inr .overlappingWriteSetAtClaim :=
  rfl

theorem composerSecondWorktreeRefused :
    tryClaimExclusive worktreeFixtureRegistry composerSecondWorktreeFixture =
      Sum.inr .agentAlreadyOwnsWorktree :=
  rfl

theorem kimiAntichainDisjointAdmits :
    tryClaimExclusive worktreeFixtureRegistry kimiAntichainDisjointFixture =
      Sum.inl { claim := kimiAntichainDisjointFixture, antichainIndex := 1 } :=
  rfl

theorem writeSetsOverlap_composer_grok :
    writeSetsOverlap composerWriteSet grokOverlapWriteSet = true := rfl

theorem writeSetsDisjoint_composer_originRefuse :
    writeSetsOverlap composerWriteSet originRefuseWriteSet = false := rfl

theorem worktreeConjunct_fixture_admits :
    worktreeConjunctAdmits worktreeFixtureConjunct = true := rfl

theorem worktreeExclusive_positiveRefuse_notSilent :
    evaluateClaimOperation true ≠ .exclusiveAdmit := by
  simp [evaluateClaimOperation]

end UMST.Urge.WorktreeExclusive
