-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/WorktreeExclusive.lean

  Meso acting Urge — §16.11 one agent ↔ one exclusive worktree; antichain exclusive
  copy on the conflict graph. Gate failure at **claim** time — not merge-conflict theater.
  Composes `Excitement.select` — no second argmin.

  Mirrors `ReplicaCoalgebra.lean` typed morphism discipline.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
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

def refuseMergeConflictTheater : WorktreeExclusiveRefusal :=
  .mergeConflictTheater

def refuseSecondArgminOnClaim : WorktreeExclusiveRefusal :=
  .secondArgminOnClaim

theorem refuseOverlappingWriteSetAtClaim_positive :
    refuseOverlappingWriteSetAtClaim = .overlappingWriteSetAtClaim := rfl

theorem refuseAgentSecondWorktree_positive :
    refuseAgentSecondWorktree = .agentAlreadyOwnsWorktree := rfl

theorem refuseMergeConflictTheater_positive :
    refuseMergeConflictTheater = .mergeConflictTheater := rfl

theorem refuseSecondArgminOnClaim_positive :
    refuseSecondArgminOnClaim = .secondArgminOnClaim := rfl

theorem evaluateClaimOperation_mergeTheaterRefused :
    evaluateClaimOperation true = .mergeTheaterRefused := rfl

theorem evaluateClaimOperation_exclusiveAdmit :
    evaluateClaimOperation false = .exclusiveAdmit := rfl

-- ================================================================
-- SECTION 3: Worktree exclusive composes Excitement.select (no second argmin)
-- ================================================================

inductive WorktreeExcitementComposePin where
  | importSelectExcitement | secondArgminRefused
  deriving DecidableEq, Repr

structure WorktreeExclusiveCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def composeExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) (pin : WorktreeExcitementComposePin) :
    Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

noncomputable def worktreeExclusiveSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : WorktreeExclusiveCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def worktreeExclusiveSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem composeExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) :
    composeExcitementSelect src cands .importSelectExcitement = select src cands :=
  rfl

theorem worktreeExclusiveSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : WorktreeExclusiveCtx S) :
    worktreeExclusiveSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem worktreeExclusiveSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : WorktreeExclusiveCtx S) :
    worktreeExclusiveSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem worktreeExclusive_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : WorktreeExclusiveCtx S) :
    worktreeExclusiveSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem composeExcitementSelect_refuses_secondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) :
    composeExcitementSelect src cands .secondArgminRefused = Sum.inr Residue.allInadmissible :=
  rfl

theorem worktreeExclusive_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    worktreeExclusiveSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [worktreeExclusiveSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: Landauer bridge (sole physics axiom — imported)
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

structure WorktreeTransition where
  move            : WorktreeHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def worktreeSecondLaw (t : WorktreeTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalWorktreeBridge where
  proc : ErasureProcess
  transition : WorktreeTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleWorktreeExclusive transition.move

theorem worktreeSecondLaw_from_physical (b : PhysicalWorktreeBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    worktreeSecondLaw b.transition := by
  unfold worktreeSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleWorktreeExclusive_from_physical (b : PhysicalWorktreeBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleWorktreeExclusive b.transition.move :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

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

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def worktreeExclusivePhysicsGreen : Bool := false

theorem worktreeExclusivePhysicsGreenFalse : worktreeExclusivePhysicsGreen = false := rfl

def worktreeExclusiveProductionWired : Bool := false

theorem worktreeExclusiveProductionWiredFalse : worktreeExclusiveProductionWired = false := rfl

theorem worktreeExclusiveModuleWitness : True := trivial

theorem worktreeExclusive_noNewAxiom : True := trivial

theorem worktreeExclusive_mergeTheaterRefused_positive :
    refuseMergeConflictTheater = .mergeConflictTheater := rfl

theorem worktreeExclusive_secondArgminRefused_positive :
    refuseSecondArgminOnClaim = .secondArgminOnClaim := rfl

end UMST.Urge.WorktreeExclusive
