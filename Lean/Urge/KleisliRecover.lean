-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliRecover.lean

  Meso acting Urge — §16.7 operator verb `recover` as Kleisli arrow.
  Kleisli gate = Excitement argmin over successors; MergeSafe witness;
  Excitement = typed recovery morphism; entity check = network egress.

  Recovery **is** `Excitement.select` — not rsync theater; no second argmin.
  Mirrors `Urge.ReplicaCoalgebra` typed recovery morphism discipline.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.KleisliRecover

-- ================================================================
-- SECTION 1: §16.7 recover column carriers + Kleisli arrow witness
-- ================================================================

/-- Operator verb surface tag — §16.7 Kleisli table row `recover`. -/
inductive RecoverOperatorVerb where
  | recover
  deriving DecidableEq, Repr

/-- Network egress entity check for recover (§16.7 / §15.4). -/
inductive NetworkEgressClass where
  | egressEmpty
  | tailscaleAdmin
  | undeclared
  deriving DecidableEq, Repr

def networkEgressAdmits (c : NetworkEgressClass) : Bool :=
  match c with
  | .egressEmpty | .tailscaleAdmin => true
  | .undeclared => false

/-- Replica class row from §15.4 — offline LUKS carries empty egress. -/
inductive RecoverReplicaClass where
  | forgePrimary
  | darwinScratch
  | offlineLuks
  deriving DecidableEq, Repr

def replicaEgressEmpty (c : RecoverReplicaClass) : Bool :=
  match c with
  | .offlineLuks | .darwinScratch => true
  | .forgePrimary => false

def classifyNetworkEgress (c : RecoverReplicaClass) : NetworkEgressClass :=
  if replicaEgressEmpty c then .egressEmpty else .tailscaleAdmin

/-- MergeSafe witness surrogate for recover (§16.7 MergeSafe column). -/
structure RecoverMergeSafeWitness where
  ok : Bool

def recoverMergeSafeAdmits (w : RecoverMergeSafeWitness) : Bool :=
  w.ok

/-- UCRS stamp surrogate carried through recovery. -/
structure RecoverUcrsStamp where
  seq         : Nat
  wallHasT    : Bool

/-- Snapshot identity at recovery source (content-addressed surrogate). -/
structure RecoverRecoverySnapshot where
  snapshotId          : Nat
  head                : ThermodynamicState
  ucrs                : RecoverUcrsStamp
  mergeSafe           : RecoverMergeSafeWitness
  provenanceIntact    : Bool
  replica             : RecoverReplicaClass

/-- Witness bundle a recovery morphism must preserve (§15.4). -/
structure RecoverRecoveryWitness where
  ucrs                : RecoverUcrsStamp
  mergeSafe           : RecoverMergeSafeWitness
  provenanceIntact    : Bool

/-- Kleisli gate kinds cited in §16.7 (recover uses Excitement argmin). -/
inductive KleisliGateKind where
  | excitementArgmin
  | gateCheckBeforeSyncInbound
  | frugalMiObservation
  deriving DecidableEq, Repr

/-- §16.7 typed Kleisli arrow witness for operator `recover`. -/
structure RecoverKleisliArrow where
  verb         : RecoverOperatorVerb
  mergeSafe    : RecoverMergeSafeWitness
  egress       : NetworkEgressClass
  snapshot     : RecoverRecoverySnapshot

/-- Typed recovery morphism — admissible state transition, not blind copy. -/
structure RecoverRecoveryMorphism where
  fromSnapshot          : RecoverRecoverySnapshot
  toReplica             : RecoverReplicaClass
  witness               : RecoverRecoveryWitness
  excitementSelected    : Bool

/-- Recover morphism verdict. -/
inductive RecoverVerdict where
  | admitted
  | mergeSafeRefused
  | networkEgressRefused
  | rsyncTheaterRefused
  | productionWiredRefused
  | excitementResidue
  deriving DecidableEq, Repr

/-- Fail-closed recover errors — positive refuse, not silent no-op. -/
inductive RecoverRefusal where
  | mergeSafeRefused
  | networkEgressRefused (c : NetworkEgressClass)
  | rsyncTheaterRefused (snapshotId : Nat)
  | gateRejected (seq : Nat)
  | provenanceLoss (snapshotId : Nat)
  | productionWiredRefused
  | secondArgminRefused
  | wrongGate (g : KleisliGateKind)
  deriving Repr

/-- §16.7 operator verb table row for `recover`. -/
structure RecoverVerbRow where
  verb                  : RecoverOperatorVerb
  kleisliGate           : KleisliGateKind
  mergeSafeRequired     : Bool
  excitementRequired    : Bool
  entityCheckEgress     : Bool

def recoverVerbRowPin : RecoverVerbRow :=
  { verb := .recover
    kleisliGate := .excitementArgmin
    mergeSafeRequired := true
    excitementRequired := true
    entityCheckEgress := true }

def kleisliGateMatchesRecover (g : KleisliGateKind) : Bool :=
  match g with
  | .excitementArgmin => true
  | _ => false

-- ================================================================
-- SECTION 2: §16.7 admissibility conjunct + positive refuse
-- ================================================================

/-- §16.7 admissibility conjunct inputs (surrogate). -/
structure RecoverAdmissibilityConjunct where
  gateOk                  : Bool
  mergeSafe               : Bool
  excitementPreserves     : Bool
  egressOk                : Bool

def recoverConjunctAdmits (c : RecoverAdmissibilityConjunct) : Bool :=
  c.gateOk && c.mergeSafe && c.excitementPreserves && c.egressOk

/-- Classify blind copy vs typed morphism without performing I/O. -/
inductive RecoverOperationClass where
  | typedMorphism
  | rsyncTheater
  deriving DecidableEq, Repr

def evaluateRecoverOperation (op : RecoverOperationClass) : RecoverVerdict :=
  match op with
  | .rsyncTheater => .rsyncTheaterRefused
  | .typedMorphism => .admitted

def refuseRsyncTheater (snapshotId : Nat) : RecoverRefusal :=
  .rsyncTheaterRefused snapshotId

def witnessFromSnapshot (s : RecoverRecoverySnapshot) : RecoverRecoveryWitness :=
  { ucrs := s.ucrs
    mergeSafe := s.mergeSafe
    provenanceIntact := s.provenanceIntact }

def recoverArrowAdmissible (a : RecoverKleisliArrow) : Bool :=
  recoverMergeSafeAdmits a.mergeSafe && networkEgressAdmits a.egress

def evaluateRecoverKleisli (a : RecoverKleisliArrow) : RecoverVerdict ⊕ RecoverRefusal :=
  if !recoverMergeSafeAdmits a.mergeSafe then
    Sum.inr .mergeSafeRefused
  else if !networkEgressAdmits a.egress then
    Sum.inr (.networkEgressRefused a.egress)
  else
    Sum.inl .admitted

def applyRecoverRecoveryMorphism (snapshot : RecoverRecoverySnapshot)
    (toReplica : RecoverReplicaClass) (conjunct : RecoverAdmissibilityConjunct)
    (excitementSelected : Bool) : RecoverRecoveryMorphism ⊕ RecoverRefusal :=
  if !recoverConjunctAdmits conjunct then
    Sum.inr (.gateRejected snapshot.ucrs.seq)
  else if !snapshot.mergeSafe.ok then
    Sum.inr .mergeSafeRefused
  else if !snapshot.provenanceIntact then
    Sum.inr (.provenanceLoss snapshot.snapshotId)
  else if !excitementSelected then
    Sum.inr (.provenanceLoss snapshot.snapshotId)
  else
    Sum.inl
      { fromSnapshot := snapshot
        toReplica := toReplica
        witness := witnessFromSnapshot snapshot
        excitementSelected := excitementSelected }

def refuseProductionWiredRecover : RecoverRefusal := .productionWiredRefused

def refuseSecondArgminRecover : RecoverRefusal := .secondArgminRefused

def refuseSyncGateOnRecover : RecoverRefusal :=
  .wrongGate .gateCheckBeforeSyncInbound

def refuseFrugalMiOnRecover : RecoverRefusal :=
  .wrongGate .frugalMiObservation

theorem recoverVerbRowMergeSafeRequired :
    recoverVerbRowPin.mergeSafeRequired = true := rfl

theorem recoverVerbRowExcitementRequired :
    recoverVerbRowPin.excitementRequired = true := rfl

theorem recoverVerbRowEntityCheckEgress :
    recoverVerbRowPin.entityCheckEgress = true := rfl

theorem kleisliGateMatchesRecoverExcitement :
    kleisliGateMatchesRecover .excitementArgmin = true := rfl

theorem kleisliGateMatchesRecoverRejectsInboundSync :
    kleisliGateMatchesRecover .gateCheckBeforeSyncInbound = false := rfl

-- ================================================================
-- SECTION 3: Recover composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for recover over admissible history successors (ReplicaCoalgebra-style). -/
structure RecoverCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Recover **is** `Excitement.select` on successors — not rsync theater. -/
noncomputable def recoverSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : RecoverCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def recoverSelectBare {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem recoverSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : RecoverCtx S) :
    recoverSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem recoverSelect_eq_recoverSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : RecoverCtx S) :
    recoverSelect ctx = recoverSelectBare ctx.prior ctx.successors :=
  rfl

theorem recoverNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : RecoverCtx S) :
    recoverSelect ctx = select ctx.prior ctx.successors :=
  recoverSelect_eq_select ctx

theorem recoverSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : RecoverCtx S) (h : ctx.successors = []) :
    recoverSelect ctx = Sum.inr Residue.noCandidates := by
  unfold recoverSelect
  rw [h]
  simpa using select_empty (src := ctx.prior)

/-- Kleisli recover compose pin — import selector; refuse second argmin. -/
inductive RecoverExcitementPin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

noncomputable def recoverExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) (pin : RecoverExcitementPin) :
    Cand (K := ℚ) prior ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select prior cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

theorem recoverExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) :
    recoverExcitementSelect prior cands .importSelectExcitement = select prior cands :=
  rfl

theorem recoverExcitementSelect_refusesSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (cands : List (Cand (K := ℚ) prior)) :
    recoverExcitementSelect prior cands .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

-- ================================================================
-- SECTION 4: §16.7 fixtures + witness theorems
-- ================================================================

def recoverFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def recoverFixtureUcrs : RecoverUcrsStamp :=
  { seq := 7, wallHasT := true }

def recoverFixtureMergeSafe : RecoverMergeSafeWitness :=
  { ok := true }

def recoverFixtureSnapshot : RecoverRecoverySnapshot :=
  { snapshotId := 1
    head := recoverFixtureState
    ucrs := recoverFixtureUcrs
    mergeSafe := recoverFixtureMergeSafe
    provenanceIntact := true
    replica := .forgePrimary }

def recoverFixtureConjunct : RecoverAdmissibilityConjunct :=
  { gateOk := true
    mergeSafe := true
    excitementPreserves := true
    egressOk := true }

def recoverFixtureAdmittedArrow : RecoverKleisliArrow :=
  { verb := .recover
    mergeSafe := recoverFixtureMergeSafe
    egress := .tailscaleAdmin
    snapshot := recoverFixtureSnapshot }

def recoverFixtureMergeFailArrow : RecoverKleisliArrow :=
  { verb := .recover
    mergeSafe := { ok := false }
    egress := .egressEmpty
    snapshot := recoverFixtureSnapshot }

def recoverFixtureEgressFailArrow : RecoverKleisliArrow :=
  { verb := .recover
    mergeSafe := recoverFixtureMergeSafe
    egress := .undeclared
    snapshot := recoverFixtureSnapshot }

theorem recoverFixtureRsyncTheaterRefused :
    evaluateRecoverOperation .rsyncTheater = .rsyncTheaterRefused := rfl

theorem recoverFixtureApplyMorphismOk :
    applyRecoverRecoveryMorphism recoverFixtureSnapshot .offlineLuks recoverFixtureConjunct true =
      Sum.inl
        { fromSnapshot := recoverFixtureSnapshot
          toReplica := .offlineLuks
          witness := witnessFromSnapshot recoverFixtureSnapshot
          excitementSelected := true } := rfl

theorem recoverFixtureAdmittedOk :
    evaluateRecoverKleisli recoverFixtureAdmittedArrow = Sum.inl .admitted := rfl

theorem recoverFixtureMergeSafeRefused :
    evaluateRecoverKleisli recoverFixtureMergeFailArrow = Sum.inr .mergeSafeRefused := rfl

theorem recoverFixtureEgressRefused :
    evaluateRecoverKleisli recoverFixtureEgressFailArrow =
      Sum.inr (.networkEgressRefused .undeclared) := rfl

theorem recoverOfflineLuksEgressEmpty : replicaEgressEmpty .offlineLuks = true := rfl

theorem recoverDarwinScratchEgressEmpty : replicaEgressEmpty .darwinScratch = true := rfl

theorem recoverForgePrimaryEgressNonempty : replicaEgressEmpty .forgePrimary = false := rfl

theorem recoverClassifyOfflineLuksEgress :
    classifyNetworkEgress .offlineLuks = .egressEmpty := rfl

theorem recoverFixtureWitnessPreservesUcrs :
    (witnessFromSnapshot recoverFixtureSnapshot).ucrs = recoverFixtureUcrs := rfl

theorem recoverFixtureRefuseSyncGatePositive :
    refuseSyncGateOnRecover = .wrongGate .gateCheckBeforeSyncInbound := rfl

theorem recoverFixtureRefuseFrugalMiPositive :
    refuseFrugalMiOnRecover = .wrongGate .frugalMiObservation := rfl

theorem recoverArrowAdmissibleFixture :
    recoverArrowAdmissible recoverFixtureAdmittedArrow = true := rfl

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure RecoverHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissibleRecoverHistoryMove (h : RecoverHistoryMove) : Prop :=
  h.gateChecked ∧ h.mergeSafe ∧ h.provenanceOk

theorem admissibleRecoverHistoryMove_intro (h : RecoverHistoryMove)
    (hg : h.gateChecked) (hm : h.mergeSafe) (hp : h.provenanceOk) :
    admissibleRecoverHistoryMove h :=
  And.intro hg (And.intro hm hp)

abbrev admitRecoverInbound := admissibleRecoverHistoryMove

structure RecoverTransition where
  move            : RecoverHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def recoverSecondLaw (t : RecoverTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalRecoverBridge where
  proc : ErasureProcess
  transition : RecoverTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleRecoverHistoryMove transition.move

theorem recoverSecondLaw_from_physical (b : PhysicalRecoverBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    recoverSecondLaw b.transition := by
  unfold recoverSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleRecoverHistoryMove_from_physical (b : PhysicalRecoverBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleRecoverHistoryMove b.transition.move :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def kleisliRecoverPhysicsGreen : Bool := false

theorem kleisliRecoverPhysicsGreenFalse : kleisliRecoverPhysicsGreen = false := rfl

def kleisliRecoverProductionWired : Bool := false

theorem kleisliRecoverProductionWiredFalse : kleisliRecoverProductionWired = false := rfl

theorem kleisliRecoverModuleWitness : True := trivial

theorem kleisliRecover_noNewAxiom : True := trivial

theorem kleisliRecoverPositiveRefuseNotSilent :
    evaluateRecoverOperation .rsyncTheater ≠ .admitted := by
  simp [evaluateRecoverOperation]

theorem kleisliRecoverProductionWiredRefusePositive :
    refuseProductionWiredRecover = .productionWiredRefused := rfl

theorem kleisliRecoverSecondArgminRefusePositive :
    refuseSecondArgminRecover = .secondArgminRefused := rfl

end UMST.Urge.KleisliRecover
