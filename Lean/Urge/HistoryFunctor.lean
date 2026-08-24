-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/HistoryFunctor.lean

  Meso acting Urge — Admissible HistoryFunctor (§5.1).
  identity: history_functor
  Git-style content-addressed bytes → typed gate-checked history with
  second-law preservation (Prop — not a Lean axiom).

  Mirrors umst-meta `evaluate_transition` provenance gate; thermodynamic
  head moves reuse `UMST.Urge.AdmitKleisli` carriers.
  Adds **zero** Lean `axiom` declarations.
-/

import Urge.AdmitKleisli

open Real UMST UMST.Core UMST.LandauerLaw UMST.Urge.AdmitKleisli

namespace UMST.Urge.HistoryFunctor

abbrev RawCommitBytes := ByteArray

structure RawGitCommit where
  commitHash : Nat
  payload    : RawCommitBytes

structure RepoStateSlice where
  provenanceIntact  : Bool
  physicsGreenClaim : Bool
  witnessPresent    : Bool

structure RepoTransitionStep where
  before            : RepoStateSlice
  after             : RepoStateSlice
  provenanceStamp   : Option String
  dropsProvenance   : Bool
  inventsGreen      : Bool

inductive TransitionVerdict where
  | Accept
  | Reject
  deriving DecidableEq

structure TypedHistory where
  snapshot          : HistorySnapshot
  provenanceIntact  : Bool

structure AdmissibleHistoryFunctor where
  decode : RawGitCommit → Option TypedHistory
  preserveCommitId : ∀ c h, decode c = some h → c.commitHash = h.snapshot.commitId

def history_functor_identity : String := "history_functor"

def preservationProp (t : HistoryTransition) : Prop :=
  admitSecondLaw t ∧ Admissible t.prior.head t.post.head

theorem preservationProp_of_admissible (t : HistoryTransition)
    (h : admissibleHistoryTransition t) : preservationProp t :=
  And.intro h t.gateAdmissible

def provenancedOkStep : RepoTransitionStep := {
  before := { provenanceIntact := true, physicsGreenClaim := false, witnessPresent := false }
  after := { provenanceIntact := true, physicsGreenClaim := false, witnessPresent := false }
  provenanceStamp := some "ucrs:t"
  dropsProvenance := false
  inventsGreen := false
}

def evaluateTransition (step : RepoTransitionStep) : TransitionVerdict :=
  if step.inventsGreen || (step.after.physicsGreenClaim && !step.after.witnessPresent) then
    TransitionVerdict.Reject
  else if step.dropsProvenance || (step.before.provenanceIntact && !step.after.provenanceIntact) then
    TransitionVerdict.Reject
  else
    match step.provenanceStamp with
    | none => TransitionVerdict.Reject
    | some stamp =>
      if stamp.trim.isEmpty then TransitionVerdict.Reject
      else if step.after.provenanceIntact && !step.after.physicsGreenClaim then
        TransitionVerdict.Accept
      else TransitionVerdict.Reject

theorem evaluateTransition_rejects_invents_green (step : RepoTransitionStep)
    (h : step.inventsGreen = true) :
    evaluateTransition step = TransitionVerdict.Reject := by
  simp [evaluateTransition, h]

theorem evaluateTransition_rejects_physics_green_without_witness (step : RepoTransitionStep)
    (hg : step.after.physicsGreenClaim = true) (hw : step.after.witnessPresent = false)
    (hi : step.inventsGreen = false) :
    evaluateTransition step = TransitionVerdict.Reject := by
  simp [evaluateTransition, hg, hw, hi]

theorem evaluateTransition_rejects_drops_provenance (step : RepoTransitionStep)
    (hd : step.dropsProvenance = true) (hi : step.inventsGreen = false)
    (hn : step.after.physicsGreenClaim = false) :
    evaluateTransition step = TransitionVerdict.Reject := by
  simp [evaluateTransition, hd, hi, hn]

theorem provenancedOkStep_evaluates_accept :
    evaluateTransition provenancedOkStep = TransitionVerdict.Accept := by
  native_decide

def fixtureState : ThermodynamicState :=
  { density := 2400, freeEnergy := 0, hydration := 0, strength := 0 }

def fixtureCommitHash : Nat := 42

def fixturePayload : RawCommitBytes := ByteArray.empty

def fixtureRawCommit : RawGitCommit :=
  { commitHash := fixtureCommitHash, payload := fixturePayload }

def fixtureTypedHistory : TypedHistory :=
  { snapshot := { commitId := fixtureCommitHash, head := fixtureState }
  , provenanceIntact := true }

def catalogDecode (c : RawGitCommit) : Option TypedHistory :=
  if c.commitHash = fixtureCommitHash then some fixtureTypedHistory else none

theorem catalogDecode_fixture :
    catalogDecode fixtureRawCommit = some fixtureTypedHistory := by
  simp [catalogDecode, fixtureRawCommit, fixtureCommitHash, fixtureTypedHistory]

theorem catalogDecode_preserveCommitId (c : RawGitCommit) (h : TypedHistory)
    (hd : catalogDecode c = some h) : c.commitHash = h.snapshot.commitId := by
  unfold catalogDecode at hd
  by_cases hc : c.commitHash = fixtureCommitHash
  · simp only [hc, fixtureTypedHistory, fixtureCommitHash, if_true] at hd
    rw [← Option.some.inj hd]
    exact hc
  · simp only [hc, if_false] at hd
    cases hd

def catalogHistoryFunctor : AdmissibleHistoryFunctor where
  decode := catalogDecode
  preserveCommitId := catalogDecode_preserveCommitId

theorem catalog_decode_fixture :
    catalogHistoryFunctor.decode fixtureRawCommit = some fixtureTypedHistory :=
  catalogDecode_fixture

theorem preservationProp_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    preservationProp b.transition :=
  And.intro (admitSecondLaw_from_physical b hSL) b.transition.gateAdmissible

theorem admissible_preserves_second_law (t : HistoryTransition)
    (h : admissibleHistoryTransition t) : admitSecondLaw t := h

theorem historyFunctor_noNewAxiom (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    preservationProp b.transition :=
  preservationProp_from_physical b hSL

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def historyFunctorProductionWired : Bool := false

theorem historyFunctorProductionWiredFalse : historyFunctorProductionWired = false := rfl

theorem historyFunctorModuleWitness : True := trivial

end UMST.Urge.HistoryFunctor
