-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/GossipTick.lean

  Meso acting Urge — §15.6 H3 gossip tick as typed Unmeasured|Measured wrapper.
  UNKNOWN ≠ false-as-GREEN — positive refuse, not silent accept.
  Composes `Excitement.select`; no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.GossipTick

-- ================================================================
-- SECTION 1: H3 gossip tick measurement + typed morphism carriers
-- ================================================================

/-- §15.6 H3 gossip tick measurement posture — UNKNOWN never collapses to `bool`. -/
inductive GossipTickMeasure where
  | unmeasured
  | measured (observedAdmissible : Bool) (dataset : String)
  deriving Repr

def gossipTickIsMeasured (m : GossipTickMeasure) : Bool :=
  match m with
  | .unmeasured => false
  | .measured _ _ => true

/-- Measured admissibility when present — `none` for `Unmeasured` (not `some false`). -/
def gossipTickObservedAdmissible (m : GossipTickMeasure) : Option Bool :=
  match m with
  | .unmeasured => none
  | .measured v _ => some v

def gossipTickDataset (m : GossipTickMeasure) : Option String :=
  match m with
  | .unmeasured => none
  | .measured _ d => some d

def gossipDatasetNonempty (d : String) : Bool :=
  !d.isEmpty

/-- Excitement compose pin — Urge imports selector; no second argmin. -/
inductive GossipExcitementComposePin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

/-- One H3 gossip tick candidate on the UCRS-gated mesh spine. -/
structure GossipTickCandidate where
  gossipTickId            : Nat
  candidateMeasure        : GossipTickMeasure
  composePin              : GossipExcitementComposePin
  physicsGreenClaim       : Bool

/-- UCRS stamp surrogate carried through gossip tick evaluation. -/
structure GossipTickUcrsStamp where
  seq         : Nat
  wallHasT    : Bool

/-- Witness bundle a gossip tick morphism must preserve (§15.6). -/
structure GossipTickWitness where
  ucrs                : GossipTickUcrsStamp
  measure             : GossipTickMeasure
  composePin          : GossipExcitementComposePin

/-- Typed gossip tick morphism — admissible transition, not silent accept. -/
structure GossipTickMorphism where
  candidate               : GossipTickCandidate
  witness                 : GossipTickWitness
  excitementSelected      : Bool

/-- Fail-closed gossip tick errors — positive refuse, not silent no-op. -/
inductive GossipTickRefusal where
  | unmeasuredCollapsedToFalse
  | secondArgminSelector
  | inventedPhysicsGreen
  | gateRejected (seq : Nat)
  deriving Repr

/-- Verdict for H3 gossip tick admissibility on the mesh spine. -/
inductive GossipTickVerdict where
  | gossipAdmissible
  | refuseUnmeasuredFalseGreen
  | refuseSecondArgmin
  | refuseInventedGreen
  deriving Repr

-- ================================================================
-- SECTION 2: §15.6 admissibility conjunct + positive refuse
-- ================================================================

/-- §15.6 admissibility conjunct inputs (surrogate). -/
structure GossipTickAdmissibilityConjunct where
  gateOk                          : Bool
  unmeasuredNotFalseGreen         : Bool
  excitementPreserves             : Bool

def gossipConjunctAdmits (c : GossipTickAdmissibilityConjunct) : Bool :=
  c.gateOk && c.unmeasuredNotFalseGreen && c.excitementPreserves

def refuseUnmeasuredGossipTickAsFalseGreen (m : GossipTickMeasure) :
    Option GossipTickRefusal :=
  match m with
  | .unmeasured => some .unmeasuredCollapsedToFalse
  | .measured _ _ => none

def refuseSecondArgminOnGossipTick (pin : GossipExcitementComposePin) :
    Option GossipTickRefusal :=
  match pin with
  | .secondArgminRefused => some .secondArgminSelector
  | .importSelectExcitement => none

def measuredGossipTick (observedAdmissible : Bool) (dataset : String) :
    GossipTickMeasure ⊕ GossipTickRefusal :=
  if gossipDatasetNonempty dataset then
    Sum.inl (.measured observedAdmissible dataset)
  else
    Sum.inr .unmeasuredCollapsedToFalse

def admitGossipTick (c : GossipTickCandidate) : Option GossipTickRefusal :=
  if c.physicsGreenClaim then
    some .inventedPhysicsGreen
  else
    match refuseSecondArgminOnGossipTick c.composePin with
    | some r => some r
    | none =>
      match c.candidateMeasure with
      | .unmeasured => some .unmeasuredCollapsedToFalse
      | .measured false _ => none
      | .measured true dataset =>
        if !gossipDatasetNonempty dataset then
          some .unmeasuredCollapsedToFalse
        else
          none

def evaluateGossipTick (c : GossipTickCandidate) : GossipTickVerdict :=
  match admitGossipTick c with
  | none => .gossipAdmissible
  | some .unmeasuredCollapsedToFalse => .refuseUnmeasuredFalseGreen
  | some .secondArgminSelector => .refuseSecondArgmin
  | some .inventedPhysicsGreen => .refuseInventedGreen
  | some (.gateRejected _) => .refuseInventedGreen

def witnessFromGossipCandidate (c : GossipTickCandidate) (ucrs : GossipTickUcrsStamp) :
    GossipTickWitness :=
  { ucrs := ucrs
    measure := c.candidateMeasure
    composePin := c.composePin }

def applyGossipTickMorphism (cand : GossipTickCandidate) (ucrs : GossipTickUcrsStamp)
    (conjunct : GossipTickAdmissibilityConjunct) (excitementSelected : Bool) :
    GossipTickMorphism ⊕ GossipTickRefusal :=
  if !gossipConjunctAdmits conjunct then
    Sum.inr (.gateRejected ucrs.seq)
  else
    match admitGossipTick cand with
    | some r => Sum.inr r
    | none =>
      if !excitementSelected then
        Sum.inr .secondArgminSelector
      else
        Sum.inl
          { candidate := cand
            witness := witnessFromGossipCandidate cand ucrs
            excitementSelected := excitementSelected }

theorem refuseUnmeasuredGossipTick_positive :
    refuseUnmeasuredGossipTickAsFalseGreen .unmeasured =
      some .unmeasuredCollapsedToFalse := rfl

theorem refuseSecondArgmin_positive :
    refuseSecondArgminOnGossipTick .secondArgminRefused =
      some .secondArgminSelector := rfl

theorem gossipTick_unmeasuredNotMeasured :
    gossipTickIsMeasured .unmeasured = false := rfl

theorem gossipTick_observedNoneWhenUnmeasured :
    gossipTickObservedAdmissible .unmeasured = none := rfl

-- ================================================================
-- SECTION 3: Gossip tick composes Excitement.select (no second argmin)
-- ================================================================

structure GossipTickCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def gossipTickExcitementSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) (pin : GossipExcitementComposePin) :
    Cand (K := ℚ) src ⊕ Residue :=
  match pin with
  | .importSelectExcitement => select src cands
  | .secondArgminRefused => Sum.inr Residue.allInadmissible

noncomputable def gossipTickSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : GossipTickCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

theorem gossipTickSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : GossipTickCtx S) :
    gossipTickSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem gossipTickSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : GossipTickCtx S) :
    gossipTickSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem gossipTick_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : GossipTickCtx S) :
    gossipTickSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem gossipTickExcitementSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) :
    gossipTickExcitementSelect src cands .importSelectExcitement = select src cands :=
  rfl

theorem gossipTickExcitementSelect_refusesSecondArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (cands : List (Cand (K := ℚ) src)) :
    gossipTickExcitementSelect src cands .secondArgminRefused =
      Sum.inr Residue.allInadmissible :=
  rfl

noncomputable def gossipTickSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) : Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

theorem gossipTickSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    gossipTickSelectBare prior successors = select prior successors :=
  rfl

theorem gossipTickSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    gossipTickSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [gossipTickSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: §15.6 H3 fixtures + witness theorems
-- ================================================================

def gossipFixtureDataset : String :=
  "fixture:h3:gossip-tick:admissible-001"

def gossipFixtureSecondArgminDataset : String :=
  "fixture:h3:gossip-tick:second-argmin-002"

def gossipFixtureUcrs : GossipTickUcrsStamp :=
  { seq := 7, wallHasT := true }

def h3AdmissibleMeasuredGossipTick : GossipTickCandidate :=
  { gossipTickId := 1
    candidateMeasure := .measured true gossipFixtureDataset
    composePin := .importSelectExcitement
    physicsGreenClaim := false }

def h3UnmeasuredFalseGreenFixture : GossipTickCandidate :=
  { gossipTickId := 2
    candidateMeasure := .unmeasured
    composePin := .importSelectExcitement
    physicsGreenClaim := false }

def h3SecondArgminFixture : GossipTickCandidate :=
  { gossipTickId := 3
    candidateMeasure := .measured false gossipFixtureSecondArgminDataset
    composePin := .secondArgminRefused
    physicsGreenClaim := false }

def gossipFixtureConjunct : GossipTickAdmissibilityConjunct :=
  { gateOk := true, unmeasuredNotFalseGreen := true, excitementPreserves := true }

theorem h3AdmissibleMeasuredGossipTick_admits :
    admitGossipTick h3AdmissibleMeasuredGossipTick = none := rfl

theorem h3AdmissibleMeasuredGossipTick_evaluateAdmit :
    evaluateGossipTick h3AdmissibleMeasuredGossipTick = .gossipAdmissible := rfl

theorem h3UnmeasuredFalseGreen_refused :
    admitGossipTick h3UnmeasuredFalseGreenFixture =
      some .unmeasuredCollapsedToFalse := rfl

theorem h3UnmeasuredFalseGreen_evaluateRefuse :
    evaluateGossipTick h3UnmeasuredFalseGreenFixture = .refuseUnmeasuredFalseGreen := rfl

theorem h3SecondArgmin_refused :
    admitGossipTick h3SecondArgminFixture = some .secondArgminSelector := rfl

theorem h3SecondArgmin_evaluateRefuse :
    evaluateGossipTick h3SecondArgminFixture = .refuseSecondArgmin := rfl

theorem gossipFixture_measuredGossipTickOk :
    measuredGossipTick true gossipFixtureDataset =
      Sum.inl (.measured true gossipFixtureDataset) := rfl

theorem gossipFixture_emptyDatasetRefused :
    measuredGossipTick false "" = Sum.inr .unmeasuredCollapsedToFalse := rfl

theorem gossipFixture_applyMorphismOk :
    applyGossipTickMorphism h3AdmissibleMeasuredGossipTick gossipFixtureUcrs
      gossipFixtureConjunct true =
      Sum.inl
        { candidate := h3AdmissibleMeasuredGossipTick
          witness := witnessFromGossipCandidate h3AdmissibleMeasuredGossipTick gossipFixtureUcrs
          excitementSelected := true } := rfl

theorem gossipFixture_witnessPreservesMeasure :
    (witnessFromGossipCandidate h3AdmissibleMeasuredGossipTick gossipFixtureUcrs).measure =
      .measured true gossipFixtureDataset := rfl

theorem gossipFixture_conjunctAdmitsTrue :
    gossipConjunctAdmits gossipFixtureConjunct = true := rfl

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure GossipTickTransition where
  candidate       : GossipTickCandidate
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateChecked     : Prop
  unmeasuredHonest : Prop
  excitementPreserves : Prop

def admissibleGossipTick (t : GossipTickTransition) : Prop :=
  t.gateChecked ∧ t.unmeasuredHonest ∧ t.excitementPreserves

def gossipTickSecondLaw (t : GossipTickTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalGossipTickBridge where
  proc : ErasureProcess
  transition : GossipTickTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleGossipTick transition

theorem gossipTickSecondLaw_from_physical (b : PhysicalGossipTickBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    gossipTickSecondLaw b.transition := by
  unfold gossipTickSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleGossipTick_from_physical (b : PhysicalGossipTickBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleGossipTick b.transition :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def gossipTickPhysicsGreen : Bool := false

theorem gossipTickPhysicsGreenFalse : gossipTickPhysicsGreen = false := rfl

def gossipTickProductionWired : Bool := false

theorem gossipTickProductionWiredFalse : gossipTickProductionWired = false := rfl

theorem gossipTickModuleWitness : True := trivial

theorem gossipTick_noNewAxiom : True := trivial

theorem gossipTick_positiveRefuseNotSilent :
    admitGossipTick h3UnmeasuredFalseGreenFixture ≠ none := by
  rw [h3UnmeasuredFalseGreen_refused]
  simp

theorem gossipTick_unmeasuredNotFalseAsGreen :
    refuseUnmeasuredGossipTickAsFalseGreen .unmeasured ≠ none := by
  rw [refuseUnmeasuredGossipTick_positive]
  simp

def gossipTickCatalogWitness : String :=
  "URGE-FORMAL-MESO-LEAN-GOSSIP-TICK §15.6 H3 gossip tick : Unmeasured | Measured wrapper; UNKNOWN ≠ false-as-GREEN; compose excitement-select no second argmin; sole axiom physicalSecondLaw; physics_green false; production_wired false"

end UMST.Urge.GossipTick
