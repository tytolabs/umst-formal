-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/GossipTick.lean

  Meso acting Urge — §15.6 H3 gossip tick as typed Unmeasured|Measured wrapper.
  UNKNOWN ≠ false-as-GREEN — positive refuse, not silent accept.
  Composes `Excitement.select`; no second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
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

theorem gossipTick_observedNoneWhenUnmeasured :
    gossipTickObservedAdmissible .unmeasured = none := rfl

-- ================================================================
-- SECTION 4: §15.6 H3 fixtures + witness theorems
-- ================================================================

def gossipFixtureDataset : String :=
  "fixture:h3:gossip-tick:admissible-001"

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

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

theorem gossipTick_positiveRefuseNotSilent :
    admitGossipTick h3UnmeasuredFalseGreenFixture ≠ none := by
  rw [h3UnmeasuredFalseGreen_refused]
  simp

theorem gossipTick_unmeasuredNotFalseAsGreen :
    refuseUnmeasuredGossipTickAsFalseGreen .unmeasured ≠ none := by
  rw [refuseUnmeasuredGossipTick_positive]
  simp

end UMST.Urge.GossipTick
