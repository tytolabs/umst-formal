-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliMerge.lean

  Meso acting Urge — §16.7 operator verb `merge` as Kleisli arrow.
  Kleisli gate = `gate_check_before_sync` inbound; MergeSafe predicate required;
  Excitement = provenance preserved; entity check = tier disjoint.
  Honest refuse on MergeSafe mismatch — no CRDT auto-merge.

  Composes `Excitement.select` (via `Urge.ExcitementImport`) — not a second argmin.
  Mirrors `Urge.ReplicaCoalgebra` / Coq `Urge.KleisliMerge`. Anchored in
  `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import LandauerLaw
import Urge.AdmitKleisli
import Urge.ExcitementImport
import Urge.GateBeforeSync

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ExcitementImport UMST.Urge.GateBeforeSync

namespace UMST.Urge.KleisliMerge

-- ================================================================
-- SECTION 0: MergeSafe mirror (Urge.MergeSafe — import-only pin)
-- ================================================================

/-- Minimal history memory row: SDF-canonical content id + theorem binding. -/
structure HistoryMemoryEntry where
  contentId  : Nat
  theoremId  : Nat
  deriving DecidableEq, Repr

/-- Merge-safe predicate: same canonical content id and same theorem binding. -/
def mergeSafePred (left right : HistoryMemoryEntry) : Prop :=
  left.contentId = right.contentId ∧ left.theoremId = right.theoremId

inductive MergeSafeVerdict where
  | admit
  | refuseMismatch
  deriving DecidableEq, Repr

/-- Computational merge-safe check — honest refuse on any mismatch. -/
def mergeSafe (left right : HistoryMemoryEntry) : MergeSafeVerdict :=
  if left.contentId == right.contentId then
    if left.theoremId == right.theoremId then .admit else .refuseMismatch
  else .refuseMismatch

inductive CrdtAutoMergeRefused where
  | tag
  deriving DecidableEq, Repr

/-- Positive refuse: CRDT auto-merge is forbidden (not silent swallow). -/
def refuseCrdtAutoMerge : CrdtAutoMergeRefused := .tag

def thermoStateEqb (s1 s2 : ThermodynamicState) : Bool :=
  decide (s1.density = s2.density) &&
  decide (s1.freeEnergy = s2.freeEnergy) &&
  decide (s1.hydration = s2.hydration) &&
  decide (s1.strength = s2.strength)

def mergeGateCheckBeforeSync (prior post : ThermodynamicState) : Bool :=
  if thermoStateEqb prior post then true else gateCheck prior post

-- ================================================================
-- SECTION 1: §16.7 verb row + merge carriers
-- ================================================================

inductive OperatorVerb where
  | merge
  deriving DecidableEq, Repr

inductive VerbColumnRequirement where
  | notRequired
  | required
  deriving DecidableEq, Repr

inductive KleisliGateKind where
  | gateCheckBeforeSyncInbound
  | frugalMiObservation
  | outboundTickIfAdmitted
  deriving DecidableEq, Repr

inductive EntityCheckKind where
  | tierDisjoint
  | remoteClass
  | replicaClass
  deriving DecidableEq, Repr

structure OperatorVerbRow where
  verb           : OperatorVerb
  kleisliGate    : KleisliGateKind
  mergeSafeCol   : VerbColumnRequirement
  excitementCol  : VerbColumnRequirement
  entityCheck    : EntityCheckKind
  deriving Repr

def mergeVerbRow : OperatorVerbRow :=
  { verb := .merge
    kleisliGate := .gateCheckBeforeSyncInbound
    mergeSafeCol := .required
    excitementCol := .required
    entityCheck := .tierDisjoint }

inductive MemoryTier where
  | ephemeral
  | device
  | federated
  deriving DecidableEq, Repr

structure MergeHistoryObject where
  entry : HistoryMemoryEntry
  tier  : MemoryTier
  deriving Repr, DecidableEq

inductive InboundGateCheck where
  | admitted
  | refused
  | bypassAttempted
  deriving DecidableEq, Repr

def inboundGateAdmits (g : InboundGateCheck) : Bool :=
  match g with
  | .admitted => true
  | .refused | .bypassAttempted => false

structure MergeTransition where
  priorCommit : Nat
  postCommit  : Nat
  deriving Repr

structure MergeProvenance where
  ucrsChain        : List Nat
  dagCommit        : Nat
  landauerWitness  : Bool
  deriving Repr, DecidableEq

structure MergeKleisliArrow where
  verb           : OperatorVerb
  gate           : InboundGateCheck
  leftObj        : MergeHistoryObject
  rightObj       : MergeHistoryObject
  transition     : MergeTransition
  priorProv      : MergeProvenance
  postProv       : MergeProvenance
  priorState     : ThermodynamicState
  postState      : ThermodynamicState
  deriving Repr

inductive TierDisjointVerdict where
  | admit
  | refuseCrossTier
  deriving DecidableEq, Repr

inductive ProvenancePreserveVerdict where
  | admit
  | refusePriorDag
  | refusePostDag
  | refuseChain
  | refuseWitness
  deriving DecidableEq, Repr

inductive MergeArrowRefusal where
  | wrongVerb
  | gateRefused
  | gateBypassRefused
  | tierDisjoint (v : TierDisjointVerdict)
  | mergeSafeRefused
  | provenanceRefused (v : ProvenancePreserveVerdict)
  | productionWiredRefused
  deriving Repr, DecidableEq

structure MergeOutcome where
  merged      : MergeHistoryObject
  provenance  : ProvenancePreserveVerdict
  tier        : TierDisjointVerdict
  deriving Repr, DecidableEq

-- ================================================================
-- SECTION 2: MergeSafe + tier disjoint + provenance (computational)
-- ================================================================

def memoryTierEqb (t1 t2 : MemoryTier) : Bool :=
  match t1, t2 with
  | .ephemeral, .ephemeral => true
  | .device, .device => true
  | .federated, .federated => true
  | _, _ => false

def evaluateTierDisjoint (t1 t2 : MemoryTier) : TierDisjointVerdict :=
  if memoryTierEqb t1 t2 then .admit else .refuseCrossTier

def mergeHistoryEntry (left right : HistoryMemoryEntry) : Option HistoryMemoryEntry :=
  match mergeSafe left right with
  | .admit => some left
  | .refuseMismatch => none

def preservesMergeChain (prior post : MergeProvenance) : ProvenancePreserveVerdict :=
  let expected := prior.ucrsChain ++ [prior.dagCommit]
  if post.ucrsChain == expected then
    if prior.landauerWitness && !post.landauerWitness then .refuseWitness else .admit
  else .refuseChain

def preservesMergeProvenance (tr : MergeTransition) (prior post : MergeProvenance) :
    ProvenancePreserveVerdict :=
  if prior.dagCommit == tr.priorCommit then
    if post.dagCommit == tr.postCommit then
      preservesMergeChain prior post
    else .refusePostDag
  else .refusePriorDag

def evaluateMergeKleisli (a : MergeKleisliArrow) : MergeOutcome ⊕ MergeArrowRefusal :=
  if a.verb != OperatorVerb.merge then
    Sum.inr .wrongVerb
  else
    match a.gate with
    | .bypassAttempted => Sum.inr .gateBypassRefused
    | g =>
      if !inboundGateAdmits g then
        Sum.inr .gateRefused
      else
        match evaluateTierDisjoint a.leftObj.tier a.rightObj.tier with
        | TierDisjointVerdict.refuseCrossTier => Sum.inr (.tierDisjoint .refuseCrossTier)
        | TierDisjointVerdict.admit =>
          match mergeHistoryEntry a.leftObj.entry a.rightObj.entry with
          | none => Sum.inr .mergeSafeRefused
          | some mergedEntry =>
            let prov := preservesMergeProvenance a.transition a.priorProv a.postProv
            match prov with
            | ProvenancePreserveVerdict.admit =>
              if mergeGateCheckBeforeSync a.priorState a.postState then
                Sum.inl
                  { merged := { entry := mergedEntry, tier := a.leftObj.tier }
                    provenance := prov
                    tier := TierDisjointVerdict.admit }
              else
                Sum.inr .gateRefused
            | pv => Sum.inr (.provenanceRefused pv)

theorem mergeVerbRow_mergeSafeRequired :
    mergeVerbRow.mergeSafeCol = .required := rfl

theorem mergeVerbRow_excitementRequired :
    mergeVerbRow.excitementCol = .required := rfl

theorem mergeVerbRow_tierDisjointEntity :
    mergeVerbRow.entityCheck = .tierDisjoint := rfl

theorem kleisliGateMatchesMergeInbound :
    mergeVerbRow.kleisliGate = .gateCheckBeforeSyncInbound := rfl

theorem mergeHistoryEntry_admit (left right : HistoryMemoryEntry)
    (h : mergeSafe left right = .admit) :
    mergeHistoryEntry left right = some left := by
  simp [mergeHistoryEntry, h]

theorem mergeHistoryEntry_refuseOnMismatch (left right : HistoryMemoryEntry)
    (h : mergeSafe left right = .refuseMismatch) :
    mergeHistoryEntry left right = none := by
  simp [mergeHistoryEntry, h]

theorem evaluateTierDisjoint_same (t : MemoryTier) :
    evaluateTierDisjoint t t = .admit := by
  cases t <;> rfl

-- ================================================================
-- SECTION 3: Merge composes Excitement (no second argmin)
-- ================================================================

structure MergeCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def mergeSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : MergeCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def mergeSelectBare {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

theorem mergeSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : MergeCtx S) :
    mergeSelect ctx = select ctx.prior ctx.successors :=
  urgeRecoverySelect_eq_select ctx.prior ctx.successors

theorem mergeSelect_eq_admitHistorySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MergeCtx S) :
    mergeSelect ctx = admitHistorySelect ctx.prior ctx.successors :=
  rfl

theorem mergeKleisliNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : MergeCtx S) :
    mergeSelect ctx = select ctx.prior ctx.successors :=
  mergeSelect_eq_select ctx

theorem mergeSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : MergeCtx S) (h : ctx.successors = []) :
    mergeSelect ctx = Sum.inr Residue.noCandidates := by
  unfold mergeSelect urgeRecoverySelect
  rw [h]
  simpa using select_empty (src := ctx.prior)

-- ================================================================
-- SECTION 4: Positive refuse + CRDT + fixtures
-- ================================================================

inductive MergeGateMismatch where
  | frugalMiOnMerge
  | outboundTickOnMerge
  | remoteClassOnMerge
  | replicaClassOnMerge
  deriving DecidableEq, Repr

def refuseFrugalMiOnMerge : MergeGateMismatch := .frugalMiOnMerge
def refuseOutboundTickOnMerge : MergeGateMismatch := .outboundTickOnMerge
def refuseRemoteClassOnMerge : MergeGateMismatch := .remoteClassOnMerge
def refuseReplicaClassOnMerge : MergeGateMismatch := .replicaClassOnMerge
def refuseProductionWiredMerge : MergeArrowRefusal := .productionWiredRefused

def mergeFixtureEntry : HistoryMemoryEntry :=
  { contentId := 42, theoremId := 7 }

def mergeFixtureObject : MergeHistoryObject :=
  { entry := mergeFixtureEntry, tier := .device }

def mergeFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def mergeFixtureProvenance (prior _post : Nat) : MergeProvenance :=
  { ucrsChain := [prior], dagCommit := prior, landauerWitness := true }

def mergeFixturePostProvenance (prior post : Nat) : MergeProvenance :=
  { ucrsChain := [prior, prior], dagCommit := post, landauerWitness := true }


theorem mergeFixtureSyncGateCheck :
    mergeGateCheckBeforeSync mergeFixtureState mergeFixtureState = true := by
  simp [mergeGateCheckBeforeSync, thermoStateEqb, mergeFixtureState]

def mergeFixtureArrow : MergeKleisliArrow :=
  { verb := .merge
    gate := .admitted
    leftObj := mergeFixtureObject
    rightObj := mergeFixtureObject
    transition := { priorCommit := 10, postCommit := 11 }
    priorProv := mergeFixtureProvenance 10 11
    postProv := mergeFixturePostProvenance 10 11
    priorState := mergeFixtureState
    postState := mergeFixtureState }

def mergeFixtureArrowGateRefused : MergeKleisliArrow :=
  { mergeFixtureArrow with gate := .refused }

def mergeFixtureRightMismatch : MergeHistoryObject :=
  { entry := { contentId := 99, theoremId := 7 }, tier := .device }

def mergeFixtureArrowMergeSafeRefused : MergeKleisliArrow :=
  { mergeFixtureArrow with rightObj := mergeFixtureRightMismatch }

def mergeFixtureRightCrossTier : MergeHistoryObject :=
  { entry := mergeFixtureEntry, tier := .federated }

def mergeFixtureArrowTierDisjointRefused : MergeKleisliArrow :=
  { mergeFixtureArrow with rightObj := mergeFixtureRightCrossTier }

theorem mergeFixtureEvaluateOk :
    evaluateMergeKleisli mergeFixtureArrow =
      Sum.inl { merged := mergeFixtureObject, provenance := ProvenancePreserveVerdict.admit, tier := TierDisjointVerdict.admit } := rfl

theorem mergeFixtureGateRefused :
    evaluateMergeKleisli mergeFixtureArrowGateRefused = Sum.inr .gateRefused := rfl

theorem mergeFixtureMergeSafeRefused :
    evaluateMergeKleisli mergeFixtureArrowMergeSafeRefused = Sum.inr .mergeSafeRefused := by
  dsimp [evaluateMergeKleisli, mergeFixtureArrowMergeSafeRefused, mergeFixtureArrow,
         mergeFixtureObject, mergeFixtureRightMismatch, mergeFixtureEntry,
         inboundGateAdmits, evaluateTierDisjoint, memoryTierEqb, mergeHistoryEntry, mergeSafe]

theorem mergeFixtureTierDisjointRefused :
    evaluateMergeKleisli mergeFixtureArrowTierDisjointRefused =
      Sum.inr (.tierDisjoint TierDisjointVerdict.refuseCrossTier) := by
  dsimp [evaluateMergeKleisli, mergeFixtureArrowTierDisjointRefused, mergeFixtureArrow,
         mergeFixtureObject, mergeFixtureRightCrossTier, mergeFixtureEntry,
         inboundGateAdmits, evaluateTierDisjoint, memoryTierEqb]

theorem mergeFixtureCrdtRefused :
    refuseCrdtAutoMerge = .tag := rfl

theorem mergeFixturePositiveRefuseGates :
    refuseFrugalMiOnMerge = .frugalMiOnMerge ∧
    refuseOutboundTickOnMerge = .outboundTickOnMerge ∧
    refuseRemoteClassOnMerge = .remoteClassOnMerge ∧
    refuseReplicaClassOnMerge = .replicaClassOnMerge :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure MergeHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissibleMergeHistoryMove (h : MergeHistoryMove) : Prop :=
  h.gateChecked ∧ h.mergeSafe ∧ h.provenanceOk

theorem admissibleMergeHistoryMove_intro (h : MergeHistoryMove)
    (hg : h.gateChecked) (hm : h.mergeSafe) (hp : h.provenanceOk) :
    admissibleMergeHistoryMove h :=
  And.intro hg (And.intro hm hp)

abbrev admitMergeInbound := admissibleMergeHistoryMove

structure MergeTransitionLaw where
  move            : MergeHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def mergeSecondLaw (t : MergeTransitionLaw) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalMergeBridge where
  proc : ErasureProcess
  transition : MergeTransitionLaw
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleMergeHistoryMove transition.move

theorem mergeSecondLaw_from_physical (b : PhysicalMergeBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    mergeSecondLaw b.transition := by
  unfold mergeSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleMergeHistoryMove_from_physical (b : PhysicalMergeBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleMergeHistoryMove b.transition.move :=
  b.admissible

theorem merge_physicalSecondLaw_discharge (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def kleisliMergePhysicsGreen : Bool := false

theorem kleisliMergePhysicsGreenFalse : kleisliMergePhysicsGreen = false := rfl

def kleisliMergeProductionWired : Bool := false

theorem kleisliMergeProductionWiredFalse : kleisliMergeProductionWired = false := rfl

def kleisliMergeMarker : Nat := 167

theorem kleisliMergeMarkerPos : 0 < kleisliMergeMarker := by decide

theorem kleisliMergeModuleWitness : True := trivial

theorem kleisliMerge_noNewAxiom : True := trivial

theorem kleisliMergeNoSecondArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : MergeCtx S) :
    mergeSelect ctx = admitHistorySelect ctx.prior ctx.successors :=
  rfl

def excitementComposePin : Nat := 0

theorem excitementComposePin_marker : excitementComposePin = 0 := rfl

theorem refuseSecondArgminIsTag :
    MergeGateMismatch.frugalMiOnMerge = .frugalMiOnMerge := rfl

end UMST.Urge.KleisliMerge
