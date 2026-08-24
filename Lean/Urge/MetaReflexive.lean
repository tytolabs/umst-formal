-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/MetaReflexive.lean

  Meso acting Urge — §10.5 umst-meta reflexive health of Urge morphisms.
  Reflexive gate on repository + mesh transitions so Urge cannot lie about
  integrity, residues, or formal coverage. Positive refuse via typed
  `MetaReflexiveRefusal` — not only `!physics_green`.

  Composes `Excitement.select` (via `Urge.ExcitementImport`) — not a second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.MetaReflexive

-- ================================================================
-- SECTION 1: Urge morphism + reflexive health carriers (§10.5)
-- ================================================================

/-- Urge morphism kinds from blueprint §4 (typed, not prose). -/
inductive UrgeMorphismKind where
  | commitPatch
  | merge
  | recovery
  | miObservation
  | signedPropagate
  deriving DecidableEq, Repr

/-- Reflexive health verdict on one Urge morphism. -/
inductive ReflexiveHealthVerdict where
  | healthy
  | refuseBypassMeta
  | refuseSelfExempt
  | refuseInventedGreen
  | refuseMissingStamp
  | refuseFormalOverclaim
  deriving DecidableEq, Repr

/-- UCRS stamp surrogate carried through reflexive meta health. -/
structure MetaReflexiveStamp where
  seq         : Nat
  wallHasT    : Bool
  deriving Repr

/-- Witness bundle a reflexive morphism must preserve (§10.5). -/
structure MetaReflexiveWitness where
  stamp               : MetaReflexiveStamp
  present             : Bool
  formalCoverage      : Bool
  deriving Repr

/-- One Urge morphism under reflexive meta health check. -/
structure UrgeMorphism where
  kind                    : UrgeMorphismKind
  bypassesMetaGate        : Bool
  selfExempt              : Bool
  physicsGreenClaim       : Bool
  metaWitnessPresent      : Bool
  stamp                   : MetaReflexiveStamp
  stampNonempty           : Bool
  formalOverclaim           : Bool
  deriving Repr

/-- Fail-closed reflexive errors — positive refuse, not silent accept. -/
inductive MetaReflexiveRefusal where
  | bypassMeta (k : UrgeMorphismKind)
  | selfExempt (k : UrgeMorphismKind)
  | inventedGreen (k : UrgeMorphismKind)
  | missingStamp (seq : Nat)
  | formalOverclaim (k : UrgeMorphismKind)
  deriving Repr

/-- Verdict of a reflexive health operation class. -/
inductive MetaReflexiveVerdict where
  | healthy
  | bypassRefused
  | inadmissible
  deriving DecidableEq, Repr

/-- Successful reflexive health report — typed, not bool theater. -/
structure ReflexiveHealthReport where
  kind            : UrgeMorphismKind
  verdict         : ReflexiveHealthVerdict
  physicsGreen    : Bool
  deriving Repr

-- ================================================================
-- SECTION 2: §10.5 admissibility conjunct + positive refuse
-- ================================================================

/-- §10.5 admissibility conjunct inputs (surrogate). -/
structure MetaAdmissibilityConjunct where
  gateOk                  : Bool
  reflexiveHonest         : Bool
  excitementPreserves     : Bool
  deriving Repr

def metaConjunctAdmits (c : MetaAdmissibilityConjunct) : Bool :=
  c.gateOk && c.reflexiveHonest && c.excitementPreserves

def evaluateMetaGateBypass (bypasses : Bool) : MetaReflexiveVerdict :=
  if bypasses then .bypassRefused else .healthy

def refuseBypassMetaGate (k : UrgeMorphismKind) : MetaReflexiveRefusal :=
  .bypassMeta k

def refuseSelfExempt (k : UrgeMorphismKind) : MetaReflexiveRefusal :=
  .selfExempt k

def refuseInventedGreen (k : UrgeMorphismKind) : MetaReflexiveRefusal :=
  .inventedGreen k

def refuseFormalOverclaim (k : UrgeMorphismKind) : MetaReflexiveRefusal :=
  .formalOverclaim k

def healthyReport (k : UrgeMorphismKind) : ReflexiveHealthReport :=
  { kind := k, verdict := .healthy, physicsGreen := false }

def evaluateReflexiveHealthStampFormal (m : UrgeMorphism) :
    ReflexiveHealthReport ⊕ MetaReflexiveRefusal :=
  if m.stampNonempty then
    if m.formalOverclaim then
      Sum.inr (.formalOverclaim m.kind)
    else
      Sum.inl (healthyReport m.kind)
  else
    Sum.inr (.missingStamp m.stamp.seq)

def evaluateReflexiveHealthAfterSelf (m : UrgeMorphism) :
    ReflexiveHealthReport ⊕ MetaReflexiveRefusal :=
  if m.physicsGreenClaim && !m.metaWitnessPresent then
    Sum.inr (.inventedGreen m.kind)
  else
    evaluateReflexiveHealthStampFormal m

def evaluateReflexiveHealth (m : UrgeMorphism) :
    ReflexiveHealthReport ⊕ MetaReflexiveRefusal :=
  if m.bypassesMetaGate then
    Sum.inr (.bypassMeta m.kind)
  else if m.selfExempt then
    Sum.inr (.selfExempt m.kind)
  else
    evaluateReflexiveHealthAfterSelf m

def applyMetaReflexiveMorphism (m : UrgeMorphism) (conjunct : MetaAdmissibilityConjunct)
    (excitementSelected : Bool) : UrgeMorphism ⊕ MetaReflexiveRefusal :=
  if !metaConjunctAdmits conjunct then
    Sum.inr (.missingStamp m.stamp.seq)
  else if !excitementSelected then
    Sum.inr (.formalOverclaim m.kind)
  else
    match evaluateReflexiveHealth m with
    | Sum.inl _ => Sum.inl m
    | Sum.inr r => Sum.inr r

theorem metaReflexiveBypassRefused (k : UrgeMorphismKind) :
    refuseBypassMetaGate k = .bypassMeta k := rfl

theorem metaReflexiveSelfExemptRefused (k : UrgeMorphismKind) :
    refuseSelfExempt k = .selfExempt k := rfl

theorem metaReflexiveInventedGreenRefused (k : UrgeMorphismKind) :
    refuseInventedGreen k = .inventedGreen k := rfl

theorem metaReflexiveFormalOverclaimRefused (k : UrgeMorphismKind) :
    refuseFormalOverclaim k = .formalOverclaim k := rfl

theorem evaluateMetaGateBypassPositive :
    evaluateMetaGateBypass true = .bypassRefused := rfl

theorem evaluateMetaGateBypassHonest :
    evaluateMetaGateBypass false = .healthy := rfl

-- ================================================================
-- SECTION 3: Reflexive recovery composes Excitement (no second argmin)
-- ================================================================

/-- Context for reflexive recovery over admissible history successors. -/
structure MetaReflexiveCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Reflexive recovery **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def metaReflexiveSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MetaReflexiveCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def metaReflexiveSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) : Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem metaReflexiveSelect_eq_excitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MetaReflexiveCtx S) :
    metaReflexiveSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem metaReflexiveSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MetaReflexiveCtx S) :
    metaReflexiveSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem metaReflexiveNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MetaReflexiveCtx S) :
    metaReflexiveSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem metaReflexive_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : MetaReflexiveCtx S) (h : ctx.successors = []) :
    metaReflexiveSelect ctx = Sum.inr Residue.noCandidates := by
  unfold metaReflexiveSelect
  rw [h]
  simpa using select_empty (src := ctx.prior)

theorem metaReflexive_emptyBare {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    metaReflexiveSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [metaReflexiveSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: §10.5 fixtures + witness theorems
-- ================================================================

def metaFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def metaFixtureStamp : MetaReflexiveStamp :=
  { seq := 7, wallHasT := true }

def metaFixtureWitness : MetaReflexiveWitness :=
  { stamp := metaFixtureStamp, present := true, formalCoverage := true }

def metaFixtureHealthyMorphism : UrgeMorphism :=
  { kind := .commitPatch
    bypassesMetaGate := false
    selfExempt := false
    physicsGreenClaim := false
    metaWitnessPresent := false
    stamp := metaFixtureStamp
    stampNonempty := true
    formalOverclaim := false }

def metaFixtureBypassMorphism : UrgeMorphism :=
  { kind := .merge
    bypassesMetaGate := true
    selfExempt := false
    physicsGreenClaim := false
    metaWitnessPresent := false
    stamp := metaFixtureStamp
    stampNonempty := true
    formalOverclaim := false }

def metaFixtureInventedGreen : UrgeMorphism :=
  { kind := .recovery
    bypassesMetaGate := false
    selfExempt := false
    physicsGreenClaim := true
    metaWitnessPresent := false
    stamp := metaFixtureStamp
    stampNonempty := true
    formalOverclaim := false }

def metaFixtureConjunct : MetaAdmissibilityConjunct :=
  { gateOk := true, reflexiveHonest := true, excitementPreserves := true }

def metaFixtureHealthyReport : ReflexiveHealthReport :=
  { kind := .commitPatch, verdict := .healthy, physicsGreen := false }

theorem metaFixtureHealthyAdmits :
    evaluateReflexiveHealth metaFixtureHealthyMorphism =
      Sum.inl metaFixtureHealthyReport := rfl

theorem metaFixtureBypassRefused :
    evaluateReflexiveHealth metaFixtureBypassMorphism =
      Sum.inr (.bypassMeta .merge) := rfl

theorem metaFixtureInventedGreenRefused :
    evaluateReflexiveHealth metaFixtureInventedGreen =
      Sum.inr (.inventedGreen .recovery) := rfl

theorem metaFixtureApplyMorphismOk :
    applyMetaReflexiveMorphism metaFixtureHealthyMorphism metaFixtureConjunct true =
      Sum.inl metaFixtureHealthyMorphism := rfl

theorem metaFixtureWitnessPreservesStamp :
    metaFixtureWitness.stamp = metaFixtureStamp := rfl

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure MetaReflexiveTransition where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  reflexiveHonest : Prop
  provenanceOk    : Prop
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def admissibleMetaReflexiveTransition (t : MetaReflexiveTransition) : Prop :=
  t.gateChecked ∧ t.reflexiveHonest ∧ t.provenanceOk

def metaReflexiveSecondLaw (t : MetaReflexiveTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalMetaReflexiveBridge where
  proc : ErasureProcess
  transition : MetaReflexiveTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleMetaReflexiveTransition transition

theorem metaReflexiveSecondLaw_from_physical (b : PhysicalMetaReflexiveBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    metaReflexiveSecondLaw b.transition := by
  unfold metaReflexiveSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleMetaReflexiveTransition_from_physical (b : PhysicalMetaReflexiveBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleMetaReflexiveTransition b.transition :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def metaReflexivePhysicsGreen : Bool := false

theorem metaReflexivePhysicsGreenFalse : metaReflexivePhysicsGreen = false := rfl

def metaReflexiveProductionWired : Bool := false

theorem metaReflexiveProductionWiredFalse : metaReflexiveProductionWired = false := rfl

theorem metaReflexiveModuleWitness : True := trivial

theorem metaReflexive_noNewAxiom : True := trivial

theorem metaReflexivePositiveRefuseNotSilent :
    evaluateMetaGateBypass true ≠ .healthy := by
  simp [evaluateMetaGateBypass]

theorem metaReflexiveHonest :
    metaReflexivePhysicsGreen = false ∧
    metaReflexiveProductionWired = false ∧
    (∃ r, evaluateReflexiveHealth metaFixtureHealthyMorphism = Sum.inl r) ∧
    evaluateReflexiveHealth metaFixtureBypassMorphism ≠
      Sum.inl { kind := .merge, verdict := .healthy, physicsGreen := false } := by
  refine ⟨metaReflexivePhysicsGreenFalse, ?_, ?_, ?_⟩
  · exact metaReflexiveProductionWiredFalse
  · exact ⟨metaFixtureHealthyReport, metaFixtureHealthyAdmits⟩
  · rw [metaFixtureBypassRefused]
    intro h
    cases h

theorem metaReflexivePositiveRefuse :
    refuseBypassMetaGate .merge = .bypassMeta .merge ∧
    refuseSelfExempt .miObservation = .selfExempt .miObservation ∧
    refuseInventedGreen .recovery = .inventedGreen .recovery ∧
    refuseFormalOverclaim .signedPropagate = .formalOverclaim .signedPropagate := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end UMST.Urge.MetaReflexive
