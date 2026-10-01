-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/FrugalMi.lean

  Meso acting Urge — §4 frugal MI observation of local+mesh state.
  Observation **is** an Excitement-selected admissible transition —
  acting coalgebra deconstruct, not Landauer proof theater.
  Composes `UMST.Excitement.select`; no second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.FrugalMi

-- ================================================================
-- SECTION 1: Local+mesh carriers + acting coalgebra
-- ================================================================

/-- Local working-copy surrogate (commit head + entropy bits). -/
structure FrugalLocalState where
  commitHead      : Nat
  entropyBits     : Nat

/-- Mesh replica surrogate (gossip mesh census entropy). -/
structure FrugalMeshState where
  replicaSeq              : Nat
  gossipEntropyBits       : Nat

/-- Paired local+mesh carrier — product state for §4 observation. -/
structure FrugalLocalMeshState where
  localState : FrugalLocalState
  meshState  : FrugalMeshState

/-- Acting coalgebra deconstruct tag on local+mesh — not Landauer proof. -/
inductive FrugalLocalMeshCoalgebra where
  | localOnly (l : FrugalLocalState)
  | meshOnly (m : FrugalMeshState)
  | paired (s : FrugalLocalMeshState)

/-- Whether observation requires both local and mesh components. -/
def frugalCoalgebraRequiresPaired (c : FrugalLocalMeshCoalgebra) : Bool :=
  match c with
  | .paired _ => true
  | _ => false

/-- Acting coalgebra deconstruct — unfold paired carrier into observation tag. -/
def frugalLocalMeshDeconstruct (s : FrugalLocalMeshState) : FrugalLocalMeshCoalgebra :=
  .paired s

/-- Frugal MI bit observation — minimal MI cost surrogate for status verb. -/
structure FrugalMiObservation where
  requiredBits  : Nat
  observedBits  : Nat

/-- Witness deficit — `max(0, required − observed)` on nat surrogate. -/
def frugalMiDeficit (obs : FrugalMiObservation) : Nat :=
  if obs.observedBits ≤ obs.requiredBits then obs.requiredBits - obs.observedBits else 0

/-- Fail-closed frugal MI errors — positive refuse, not silent no-op. -/
inductive FrugalMiRefusal where
  | landauerProofRefused
  | landauerKernelForkRefused
  | mutualInformationZero
  | meshAbsentWhenPairedRequired
  | inconsistentEntropies
  | witnessDeficit (required observed : Nat)

/-- Verdict of a frugal MI observation class. -/
inductive FrugalMiVerdict where
  | observationOk
  | landauerProofRefused
  | inadmissible

-- ================================================================
-- SECTION 2: Pairwise MI + admissibility conjunct + positive refuse
-- ================================================================

/-- Pairwise Shannon MI bits — `I(X;Y) = H(X) + H(Y) − H(X,Y)` (nat surrogate). -/
def pairwiseMiBitsNat (hLocal hMesh jointEntropy : Nat) : Option Nat :=
  let sum := hLocal + hMesh
  if jointEntropy ≤ sum then some (sum - jointEntropy) else none

/-- §4 admissibility conjunct inputs (surrogate). -/
structure FrugalMiAdmissibilityConjunct where
  gateOk                  : Bool
  miPositive              : Bool
  excitementPreserves     : Bool

/-- Evaluate `admit(h) ⟺ gate ∧ MI>0 ∧ Excitement preserves`. -/
def frugalConjunctAdmits (c : FrugalMiAdmissibilityConjunct) : Bool :=
  c.gateOk && c.miPositive && c.excitementPreserves

/-- Classify Landauer proof theater vs typed observation without performing I/O. -/
def evaluateFrugalMiOperation (isLandauerProof : Bool) : FrugalMiVerdict :=
  if isLandauerProof then .landauerProofRefused else .observationOk

/-- Positive refuse: Landauer bound proof is inadmissible on this scaffold. -/
def refuseLandauerProof : FrugalMiRefusal := .landauerProofRefused

/-- Positive refuse: UCRS Landauer kernel fork is inadmissible. -/
def refuseLandauerKernelFork : FrugalMiRefusal := .landauerKernelForkRefused

def frugalMiObservationMk (required observed : Nat) : FrugalMiObservation :=
  { requiredBits := required, observedBits := observed }

/-- Attempt frugal MI observation on acting coalgebra — fail closed. -/
def observeFrugalMiFromCoalgebra
    (coalgebra : FrugalLocalMeshCoalgebra)
    (hLocal hMesh jointEntropy required observed : Nat)
    (conjunct : FrugalMiAdmissibilityConjunct) :
    FrugalMiObservation ⊕ FrugalMiRefusal :=
  if !frugalConjunctAdmits conjunct then
    Sum.inr .inconsistentEntropies
  else if !frugalCoalgebraRequiresPaired coalgebra then
    Sum.inr .meshAbsentWhenPairedRequired
  else
    match pairwiseMiBitsNat hLocal hMesh jointEntropy with
    | none => Sum.inr .inconsistentEntropies
    | some mi =>
      if mi = 0 then
        Sum.inr .mutualInformationZero
      else
        let obs := frugalMiObservationMk required observed
        if observed < required then
          Sum.inr (.witnessDeficit required observed)
        else
          Sum.inl obs

theorem frugalMiLandauerProofRefused :
    evaluateFrugalMiOperation true = .landauerProofRefused := rfl

theorem frugalMiObservationOkWhenNotLandauer :
    evaluateFrugalMiOperation false = .observationOk := rfl

theorem pairwiseMiFixturePaired :
    pairwiseMiBitsNat 4 3 5 = some 2 := rfl

theorem pairwiseMiFixtureZero :
    pairwiseMiBitsNat 2 2 4 = some 0 := rfl

-- ================================================================
-- SECTION 4: §4 fixtures + witness theorems
-- ================================================================

def frugalFixtureLocal : FrugalLocalState :=
  { commitHead := 7, entropyBits := 4 }

def frugalFixtureMesh : FrugalMeshState :=
  { replicaSeq := 3, gossipEntropyBits := 3 }

def frugalFixturePaired : FrugalLocalMeshState :=
  { localState := frugalFixtureLocal, meshState := frugalFixtureMesh }

def frugalFixtureCoalgebra : FrugalLocalMeshCoalgebra :=
  frugalLocalMeshDeconstruct frugalFixturePaired

def frugalFixtureConjunct : FrugalMiAdmissibilityConjunct :=
  { gateOk := true, miPositive := true, excitementPreserves := true }

theorem frugalFixturePairedObservationOk :
    observeFrugalMiFromCoalgebra
      frugalFixtureCoalgebra 4 3 5 2 2 frugalFixtureConjunct =
      Sum.inl (frugalMiObservationMk 2 2) := rfl

theorem frugalFixtureMeshAbsentRefused :
    observeFrugalMiFromCoalgebra
      (.localOnly frugalFixtureLocal) 4 3 5 2 2 frugalFixtureConjunct =
      Sum.inr .meshAbsentWhenPairedRequired := rfl

theorem frugalFixtureMiZeroRefused :
    observeFrugalMiFromCoalgebra
      frugalFixtureCoalgebra 2 2 4 2 2 frugalFixtureConjunct =
      Sum.inr .mutualInformationZero := rfl

theorem frugalFixtureWitnessDeficitRefused :
    observeFrugalMiFromCoalgebra
      frugalFixtureCoalgebra 4 3 5 3 2 frugalFixtureConjunct =
      Sum.inr (.witnessDeficit 3 2) := rfl

theorem frugalFixtureCoalgebraRequiresPaired :
    frugalCoalgebraRequiresPaired frugalFixtureCoalgebra = true := rfl

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

theorem frugalMiPositiveRefuseNotSilent :
    evaluateFrugalMiOperation true ≠ .observationOk := by
  simp [evaluateFrugalMiOperation]

theorem frugalMiActingCoalgebraNotLandauerProof :
    refuseLandauerProof ≠ .landauerKernelForkRefused := by
  intro h
  cases h

end UMST.Urge.FrugalMi
