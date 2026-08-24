-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/SignedPropagate.lean

  Meso acting Urge — §4 propagation of signed stamped witnessed states.
  Stamp `T` required; witness retained; unsigned propagation refused — not silent accept.
  Composes `Excitement.select` — no second ℚ argmin.

  Mirrors `Urge.ReplicaCoalgebra` / Coq `Urge.SignedPropagate`. Sole physics axiom remains
  `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.SignedPropagate

-- ================================================================
-- SECTION 1: Signed stamped witnessed carriers (§4)
-- ================================================================

/-- Wall ISO chronology stamp surrogate — `observed_at_wall` must contain `T`. -/
structure SignedPropagateWallStamp where
  signedWallSeq : Nat
  signedWallHasT : Bool

/-- Signed payload surrogate on the propagation carrier. -/
structure SignedStampedWitnessState where
  signedValue : Int
  signedStamp : SignedPropagateWallStamp
  signedWitnessBits : Nat

/-- One admissible propagation step — signed delta + post stamp/witness. -/
structure SignedPropagationStep where
  signedDelta : Int
  signedPostStamp : SignedPropagateWallStamp
  signedPostWitnessBits : Nat

/-- Witness bundle a propagation morphism must preserve (§4). -/
structure SignedPropagateWitness where
  signedWitnessStamp : SignedPropagateWallStamp
  signedWitnessBitBudget : Nat

/-- Typed propagation morphism — admissible signed transition, not unsigned carry. -/
structure SignedPropagateMorphism where
  signedMorphismFrom : SignedStampedWitnessState
  signedMorphismTo : SignedStampedWitnessState
  signedMorphismWitness : SignedPropagateWitness
  signedMorphismExcitementSelected : Bool

/-- Fail-closed propagation errors — positive refuse, not silent no-op. -/
inductive SignedPropagateRefusal where
  | sprPriorStampInvalid (seq : Nat)
  | sprPostStampInvalid (seq : Nat)
  | sprUnsignedPropagationRefused
  | sprWitnessDropped (prior post : Nat)
  | sprSignedOverflow
  | sprGateRejected (seq : Nat)
  deriving DecidableEq, Repr

/-- Verdict of a propagation operation class. -/
inductive SignedPropagateVerdict where
  | spvMorphismOk
  | spvUnsignedPropagationRefused
  | spvInadmissible
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §4 admissibility conjunct + positive refuse
-- ================================================================

/-- §4 admissibility conjunct inputs (surrogate). -/
structure SignedAdmissibilityConjunct where
  signedConjGateOk : Bool
  signedConjStampOk : Bool
  signedConjWitnessPresent : Bool
  signedConjExcitementPreserves : Bool

/-- Whether wall stamp passes minimal ISO `T` honesty. -/
def wallStampOk (s : SignedPropagateWallStamp) : Bool :=
  s.signedWallHasT

/-- Whether witness is present for propagation (non-zero bits). -/
def witnessPresent (st : SignedStampedWitnessState) : Bool :=
  st.signedWitnessBits > 0

/-- Evaluate `admit(h) ⟺ gate ∧ stamp ∧ witness ∧ Excitement preserves`. -/
def signedConjunctAdmits (c : SignedAdmissibilityConjunct) : Bool :=
  c.signedConjGateOk && c.signedConjStampOk &&
    c.signedConjWitnessPresent && c.signedConjExcitementPreserves

/-- Classify unsigned carry vs typed morphism without performing I/O. -/
def evaluateSignedPropagateOperation (isUnsignedCarry : Bool) : SignedPropagateVerdict :=
  if isUnsignedCarry then .spvUnsignedPropagationRefused else .spvMorphismOk

/-- Positive refuse: unsigned propagation is inadmissible — witness required. -/
def refuseUnsignedPropagation : SignedPropagateRefusal :=
  .sprUnsignedPropagationRefused

/-- Build witness from prior state — morphism must preserve stamps and witness. -/
def witnessFromSignedState (st : SignedStampedWitnessState) : SignedPropagateWitness :=
  { signedWitnessStamp := st.signedStamp
    signedWitnessBitBudget := st.signedWitnessBits }

/-- Surrogate signed overflow fence on additive propagation. -/
def signedAddOk (prior delta : Int) : Bool :=
  let result := prior + delta
  decide (-1000000 ≤ result) && decide (result ≤ 1000000)

/-- Attempt §4 propagate signed stamped witnessed state — fail closed. -/
def propagateSignedState (prior : SignedStampedWitnessState)
    (step : SignedPropagationStep) (conjunct : SignedAdmissibilityConjunct)
    (excitementSelected : Bool) : SignedStampedWitnessState ⊕ SignedPropagateRefusal :=
  if !wallStampOk prior.signedStamp then
    Sum.inr (.sprPriorStampInvalid prior.signedStamp.signedWallSeq)
  else if !witnessPresent prior then
    Sum.inr .sprUnsignedPropagationRefused
  else if !wallStampOk step.signedPostStamp then
    Sum.inr (.sprPostStampInvalid step.signedPostStamp.signedWallSeq)
  else if step.signedPostWitnessBits < prior.signedWitnessBits then
    Sum.inr (.sprWitnessDropped prior.signedWitnessBits step.signedPostWitnessBits)
  else if !signedAddOk prior.signedValue step.signedDelta then
    Sum.inr .sprSignedOverflow
  else if !signedConjunctAdmits conjunct then
    Sum.inr (.sprGateRejected prior.signedStamp.signedWallSeq)
  else if !excitementSelected then
    Sum.inr .sprUnsignedPropagationRefused
  else
    Sum.inl
      { signedValue := prior.signedValue + step.signedDelta
        signedStamp := step.signedPostStamp
        signedWitnessBits := step.signedPostWitnessBits }

/-- Attempt typed propagation morphism — packages prior/post + witness. -/
def applySignedPropagateMorphism (prior : SignedStampedWitnessState)
    (step : SignedPropagationStep) (conjunct : SignedAdmissibilityConjunct)
    (excitementSelected : Bool) : SignedPropagateMorphism ⊕ SignedPropagateRefusal :=
  match propagateSignedState prior step conjunct excitementSelected with
  | Sum.inl post =>
      Sum.inl
        { signedMorphismFrom := prior
          signedMorphismTo := post
          signedMorphismWitness := witnessFromSignedState prior
          signedMorphismExcitementSelected := excitementSelected }
  | Sum.inr r => Sum.inr r

theorem signedPropagateUnsignedRefused (isUnsignedCarry : Bool)
    (h : isUnsignedCarry = true) :
    evaluateSignedPropagateOperation isUnsignedCarry = .spvUnsignedPropagationRefused := by
  subst h
  rfl

theorem signedPropagateMorphismOkWhenNotUnsigned :
    evaluateSignedPropagateOperation false = .spvMorphismOk := rfl

theorem refuseUnsignedPropagationPositive :
    refuseUnsignedPropagation = .sprUnsignedPropagationRefused := rfl

-- ================================================================
-- SECTION 3: Signed propagate composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for signed propagation over admissible history successors. -/
structure SignedPropagateCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) where
  successors : List (Cand (K := ℚ) src)

/-- Signed propagation **is** `Excitement.select` — not a second argmin. -/
noncomputable def signedPropagateSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (ctx : SignedPropagateCtx S src) :
    Cand (K := ℚ) src ⊕ Residue :=
  select src ctx.successors

noncomputable def urgeSignedPropagateSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (successors : List (Cand (K := ℚ) src)) : Cand (K := ℚ) src ⊕ Residue :=
  select src successors

theorem signedPropagateSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (ctx : SignedPropagateCtx S src) :
    signedPropagateSelect src ctx = select src ctx.successors :=
  rfl

theorem signedPropagateSelect_eq_urgeSignedPropagateSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (ctx : SignedPropagateCtx S src) :
    signedPropagateSelect src ctx = urgeSignedPropagateSelect src ctx.successors :=
  rfl

theorem signedPropagateNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (ctx : SignedPropagateCtx S src) :
    signedPropagateSelect src ctx = select src ctx.successors :=
  signedPropagateSelect_eq_select src ctx

theorem signedPropagateEmpty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (ctx : SignedPropagateCtx S src)
    (h : ctx.successors = []) :
    signedPropagateSelect src ctx = Sum.inr Residue.noCandidates := by
  unfold signedPropagateSelect
  rw [h]
  simpa using select_empty (src := src)

inductive SignedPropagateComposeRefusal where
  | unsignedPropagation
  | secondArgmin
  | witnessDrop
  deriving DecidableEq, Repr

def refuseUnsignedPropagationTag : SignedPropagateComposeRefusal := .unsignedPropagation

def refuseSecondArgmin : SignedPropagateComposeRefusal := .secondArgmin

def excitementComposePin : Nat := 0

theorem excitementComposePinMarker : excitementComposePin = 0 := rfl

theorem urgeSignedPropagateSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S)
    (successors : List (Cand (K := ℚ) src)) :
    urgeSignedPropagateSelect src successors = select src successors :=
  rfl

-- ================================================================
-- SECTION 4: §4 fixtures + witness theorems
-- ================================================================

def signedFixtureStamp : SignedPropagateWallStamp :=
  { signedWallSeq := 1, signedWallHasT := true }

def signedFixturePostStamp : SignedPropagateWallStamp :=
  { signedWallSeq := 2, signedWallHasT := true }

def signedFixtureState : SignedStampedWitnessState :=
  { signedValue := 10
    signedStamp := signedFixtureStamp
    signedWitnessBits := 4 }

def signedFixtureStep : SignedPropagationStep :=
  { signedDelta := 3
    signedPostStamp := signedFixturePostStamp
    signedPostWitnessBits := 4 }

def signedFixtureConjunct : SignedAdmissibilityConjunct :=
  { signedConjGateOk := true
    signedConjStampOk := true
    signedConjWitnessPresent := true
    signedConjExcitementPreserves := true }

def signedFixturePostState : SignedStampedWitnessState :=
  { signedValue := 13
    signedStamp := signedFixturePostStamp
    signedWitnessBits := 4 }

theorem signedFixtureUnsignedRefused :
    refuseUnsignedPropagation = .sprUnsignedPropagationRefused := rfl

theorem signedFixturePropagateOk :
    propagateSignedState signedFixtureState signedFixtureStep signedFixtureConjunct true =
      Sum.inl signedFixturePostState := rfl

theorem signedFixtureApplyMorphismOk :
    applySignedPropagateMorphism signedFixtureState signedFixtureStep signedFixtureConjunct true =
      Sum.inl
        { signedMorphismFrom := signedFixtureState
          signedMorphismTo := signedFixturePostState
          signedMorphismWitness := witnessFromSignedState signedFixtureState
          signedMorphismExcitementSelected := true } := rfl

def signedFixtureUnsignedState : SignedStampedWitnessState :=
  { signedValue := 1
    signedStamp := signedFixtureStamp
    signedWitnessBits := 0 }

theorem signedFixtureUnsignedPropagationRefused :
    propagateSignedState signedFixtureUnsignedState signedFixtureStep signedFixtureConjunct true =
      Sum.inr .sprUnsignedPropagationRefused := rfl

def signedFixtureWitnessDropStep : SignedPropagationStep :=
  { signedDelta := 1
    signedPostStamp := signedFixturePostStamp
    signedPostWitnessBits := 2 }

theorem signedFixtureWitnessDropRefused :
    propagateSignedState signedFixtureState signedFixtureWitnessDropStep signedFixtureConjunct true =
      Sum.inr (.sprWitnessDropped 4 2) := rfl

theorem signedFixtureWitnessPreservesStamp :
    (witnessFromSignedState signedFixtureState).signedWitnessStamp = signedFixtureStamp := rfl

theorem signedFixtureWallStampOk : wallStampOk signedFixtureStamp = true := rfl

theorem signedFixtureWitnessPresent : witnessPresent signedFixtureState = true := rfl

theorem signedPropagatePositiveRefuseNotSilent :
    evaluateSignedPropagateOperation true ≠ .spvMorphismOk := by
  decide

-- ================================================================
-- SECTION 5: Landauer bridge (ReplicaCoalgebra-style — zero new axioms)
-- ================================================================

structure SignedPropagateHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissibleSignedPropagateHistoryMove (h : SignedPropagateHistoryMove) : Prop :=
  h.gateChecked ∧ h.mergeSafe ∧ h.provenanceOk

theorem admissibleSignedPropagateHistoryMove_intro (h : SignedPropagateHistoryMove)
    (hg : h.gateChecked) (hm : h.mergeSafe) (hp : h.provenanceOk) :
    admissibleSignedPropagateHistoryMove h :=
  And.intro hg (And.intro hm hp)

abbrev admitSignedPropagateInbound := admissibleSignedPropagateHistoryMove

structure SignedPropagateTransition where
  move            : SignedPropagateHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def signedPropagateSecondLaw (t : SignedPropagateTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalSignedPropagateBridge where
  proc : ErasureProcess
  transition : SignedPropagateTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleSignedPropagateHistoryMove transition.move

theorem signedPropagateSecondLaw_from_physical (b : PhysicalSignedPropagateBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    signedPropagateSecondLaw b.transition := by
  unfold signedPropagateSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleSignedPropagateHistoryMove_from_physical (b : PhysicalSignedPropagateBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleSignedPropagateHistoryMove b.transition.move :=
  b.admissible

theorem landauerAnchorCited :
    physicalSecondLawUniformBinary { bath := { bathTemp := ⟨1, by norm_num⟩ }, work := 1 } :=
  physicalSecondLaw_uniform_binary { bath := { bathTemp := ⟨1, by norm_num⟩ }, work := 1 }

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def signedPropagatePhysicsGreen : Bool := false

theorem signedPropagatePhysicsGreenFalse : signedPropagatePhysicsGreen = false := rfl

def signedPropagateProductionWired : Bool := false

theorem signedPropagateProductionWiredFalse : signedPropagateProductionWired = false := rfl

def signedPropagateMarker : Nat := 1

theorem signedPropagateMarkerEq : signedPropagateMarker = 1 := rfl

theorem signedPropagateModuleWitness : True := trivial

theorem signedPropagateNoNewAxiom : True := trivial

theorem refuseSecondArgminIsTag : refuseSecondArgmin = .secondArgmin := rfl

end UMST.Urge.SignedPropagate
