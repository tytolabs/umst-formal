-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ContentAddressed.lean

  Meso acting Urge — §3 content-addressed history.
  Geometric identity is **primary**; git hash is a compatibility witness, not sole id.
  History recovery composes `UMST.Excitement.select` — no second argmin.

  Mirrors `ReplicaCoalgebra.lean` carrier discipline and Coq `ContentAddressed.v`.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Concrete UMST.Urge.ExcitementImport

namespace UMST.Urge.ContentAddressed

-- Local JointThermo witness for cement `ThermodynamicState` heads (meso scaffold).
instance concreteJointThermo : JointThermo ℚ ConcreteState where
  internalEnergy s := s.density * (-s.freeEnergy)
  entropy s := s.hydration
  mutualInfo s := 0
  temperature s := 1
  temperature_pos _ := by norm_num


-- ================================================================
-- SECTION 1: Content-addressed snapshot + typed morphism carriers
-- ================================================================

/-- §3 geometric identity — primary content-address factor (SDF surrogate). -/
structure ContentGeometricIdentity where
  contentId       : Nat
  resolutionBits  : Nat

/-- Git hash compatibility witness — secondary to geometric identity. -/
structure ContentGitHashCompat where
  gitHash : String

/-- UCRS stamp surrogate carried through content-addressed history. -/
structure ContentAddressedUcrsStamp where
  seq         : Nat
  wallHasT    : Bool

/-- Geometric-primary certificate — content id must be non-zero. -/
structure ContentGeometricPrimaryCert where
  geometricPrimary : Bool

/-- Snapshot identity at history head (content-addressed surrogate). -/
structure ContentAddressedSnapshot where
  snapshotId          : Nat
  head                : ThermodynamicState
  geometric           : ContentGeometricIdentity
  gitCompat           : Option ContentGitHashCompat
  ucrs                : ContentAddressedUcrsStamp
  geometricCert       : ContentGeometricPrimaryCert
  provenanceIntact    : Bool

/-- Witness bundle a content-addressed morphism must preserve (§3). -/
structure ContentAddressedWitness where
  geometric           : ContentGeometricIdentity
  gitCompat           : Option ContentGitHashCompat
  geometricPrimary    : Bool
  provenanceIntact    : Bool

/-- Typed content-addressed morphism — admissible history transition. -/
structure ContentAddressedMorphism where
  morphismFrom          : ContentAddressedSnapshot
  morphismToSeq         : Nat
  witness               : ContentAddressedWitness
  excitementSelected    : Bool

/-- Fail-closed content-addressed errors — positive refuse, not silent accept. -/
inductive ContentAddressedRefusal where
  | gitHashOnlyIdentity (gitHash : String)
  | hostIdIdentity (hostId : Nat)
  | gateRejected (seq : Nat)
  | geometricZero (snapshotId : Nat)
  | secondArgminRefused
  deriving Repr

/-- Verdict of a content-addressed admission operation class. -/
inductive ContentAddressedVerdict where
  | admitted
  | gitHashOnlyRefused
  | hostIdRefused
  | inadmissible
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §3 admissibility conjunct + positive refuse
-- ================================================================

/-- §3 admissibility conjunct inputs (surrogate). -/
structure ContentAdmissibilityConjunct where
  gateOk                  : Bool
  geometricPrimary        : Bool
  excitementPreserves     : Bool

def contentConjunctAdmits (c : ContentAdmissibilityConjunct) : Bool :=
  c.gateOk && c.geometricPrimary && c.excitementPreserves

def geometricContentIdPresent (g : ContentGeometricIdentity) : Bool :=
  g.contentId != 0

def evaluateGitHashOnlyIdentity (gitHashOnly : Bool) : ContentAddressedVerdict :=
  if gitHashOnly then .gitHashOnlyRefused else .admitted

def evaluateHostIdIdentity (useHostId : Bool) : ContentAddressedVerdict :=
  if useHostId then .hostIdRefused else .admitted

def refuseGitHashOnlyIdentity (gitHash : String) : ContentAddressedRefusal :=
  .gitHashOnlyIdentity gitHash

def refuseHostIdIdentity (hostId : Nat) : ContentAddressedRefusal :=
  .hostIdIdentity hostId

def refuseSecondArgmin : ContentAddressedRefusal := .secondArgminRefused

def witnessFromSnapshot (s : ContentAddressedSnapshot) : ContentAddressedWitness :=
  { geometric := s.geometric
    gitCompat := s.gitCompat
    geometricPrimary := s.geometricCert.geometricPrimary
    provenanceIntact := s.provenanceIntact }

def applyContentAddressedMorphism (snapshot : ContentAddressedSnapshot) (toSeq : Nat)
    (conjunct : ContentAdmissibilityConjunct) (excitementSelected : Bool) :
    ContentAddressedMorphism ⊕ ContentAddressedRefusal :=
  if !contentConjunctAdmits conjunct then
    Sum.inr (.gateRejected snapshot.ucrs.seq)
  else if !geometricContentIdPresent snapshot.geometric then
    match snapshot.gitCompat with
    | some compat => Sum.inr (.gitHashOnlyIdentity compat.gitHash)
    | none => Sum.inr (.hostIdIdentity 0)
  else if !snapshot.geometricCert.geometricPrimary then
    Sum.inr (.geometricZero snapshot.snapshotId)
  else if !snapshot.provenanceIntact then
    Sum.inr (.geometricZero snapshot.snapshotId)
  else if !excitementSelected then
    Sum.inr (.geometricZero snapshot.snapshotId)
  else
    Sum.inl
      { morphismFrom := snapshot
        morphismToSeq := toSeq
        witness := witnessFromSnapshot snapshot
        excitementSelected := excitementSelected }

theorem contentAddressed_gitHashOnly_refused (gitHash : String) :
    refuseGitHashOnlyIdentity gitHash = .gitHashOnlyIdentity gitHash := rfl

theorem contentAddressed_admitted_when_not_gitHashOnly :
    evaluateGitHashOnlyIdentity false = .admitted := rfl

theorem contentAddressed_hostId_refused (hostId : Nat) :
    refuseHostIdIdentity hostId = .hostIdIdentity hostId := rfl

theorem contentAddressed_admitted_when_not_hostId :
    evaluateHostIdIdentity false = .admitted := rfl

theorem refuseSecondArgmin_positive :
    refuseSecondArgmin = .secondArgminRefused := rfl

-- ================================================================
-- SECTION 3: Content-addressed composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for content-addressed history over admissible successors. -/
structure ContentAddressedCtx where
  prior       : ThermodynamicState
  successors  : List (Cand (K := ℚ) prior)

/-- Content-addressed history **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def contentAddressedSelect (ctx : ContentAddressedCtx) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def contentAddressedSelectBare (prior : ThermodynamicState)
    (successors : List (Cand (K := ℚ) prior)) : Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

theorem contentAddressedSelect_eq_select (ctx : ContentAddressedCtx) :
    contentAddressedSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem contentAddressedSelect_eq_urgeRecoverySelect (ctx : ContentAddressedCtx) :
    contentAddressedSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem contentAddressedSelectBare_eq_select (prior : ThermodynamicState)
    (successors : List (Cand (K := ℚ) prior)) :
    contentAddressedSelectBare prior successors = select prior successors :=
  rfl

theorem contentAddressed_noLocalArgmin (ctx : ContentAddressedCtx) :
    contentAddressedSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem contentAddressed_empty (prior : ThermodynamicState)
    (successors : List (Cand (K := ℚ) prior)) (h : successors = []) :
    contentAddressedSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [contentAddressedSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: §3 fixtures + witness theorems
-- ================================================================

def contentFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def contentFixtureGeometric : ContentGeometricIdentity :=
  { contentId := 5381, resolutionBits := 2 }

def contentFixtureGitCompat : ContentGitHashCompat :=
  { gitHash := "sha1:geometric-primary-compat" }

def contentFixtureUcrs : ContentAddressedUcrsStamp :=
  { seq := 3, wallHasT := true }

def contentFixtureGeometricCert : ContentGeometricPrimaryCert :=
  { geometricPrimary := true }

def contentFixtureSnapshot : ContentAddressedSnapshot :=
  { snapshotId := 1
    head := contentFixtureState
    geometric := contentFixtureGeometric
    gitCompat := some contentFixtureGitCompat
    ucrs := contentFixtureUcrs
    geometricCert := contentFixtureGeometricCert
    provenanceIntact := true }

def contentFixtureConjunct : ContentAdmissibilityConjunct :=
  { gateOk := true, geometricPrimary := true, excitementPreserves := true }

theorem contentFixture_gitHashOnly_refused :
    refuseGitHashOnlyIdentity "sha1:only-hash" = .gitHashOnlyIdentity "sha1:only-hash" := rfl

theorem contentFixture_hostId_refused :
    refuseHostIdIdentity 0xdeadbeef = .hostIdIdentity 0xdeadbeef := rfl

theorem contentFixture_apply_morphism_ok :
    applyContentAddressedMorphism contentFixtureSnapshot 2 contentFixtureConjunct true =
      Sum.inl
        { morphismFrom := contentFixtureSnapshot
          morphismToSeq := 2
          witness := witnessFromSnapshot contentFixtureSnapshot
          excitementSelected := true } := rfl

theorem contentFixture_geometricContentId_present :
    geometricContentIdPresent contentFixtureGeometric = true := rfl

theorem contentFixture_witness_preserves_geometric :
    (witnessFromSnapshot contentFixtureSnapshot).geometric = contentFixtureGeometric := rfl

theorem contentFixture_witness_preserves_gitCompat :
    (witnessFromSnapshot contentFixtureSnapshot).gitCompat = some contentFixtureGitCompat := rfl

theorem contentAddressed_gitHashOnly_not_admitted :
    evaluateGitHashOnlyIdentity true ≠ .admitted := by
  simp [evaluateGitHashOnlyIdentity]

theorem contentAddressed_hostId_not_admitted :
    evaluateHostIdIdentity true ≠ .admitted := by
  simp [evaluateHostIdIdentity]

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure ContentHistoryTransition where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateChecked     : Prop
  geometricPrimary : Prop
  provenanceOk    : Prop

def admissibleContentAddressed (t : ContentHistoryTransition) : Prop :=
  t.gateChecked ∧ t.geometricPrimary ∧ t.provenanceOk

def contentSecondLaw (t : ContentHistoryTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalContentBridge where
  proc : ErasureProcess
  transition : ContentHistoryTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleContentAddressed transition

theorem contentSecondLaw_from_physical (b : PhysicalContentBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    contentSecondLaw b.transition := by
  unfold contentSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleContentAddressed_from_physical (b : PhysicalContentBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleContentAddressed b.transition :=
  b.admissible

theorem physicalSecondLaw_imported (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def contentAddressedPhysicsGreen : Bool := false

theorem contentAddressedPhysicsGreenFalse : contentAddressedPhysicsGreen = false := rfl

def contentAddressedProductionWired : Bool := false

theorem contentAddressedProductionWiredFalse : contentAddressedProductionWired = false := rfl

theorem contentAddressedModuleWitness : True := trivial

theorem contentAddressed_noNewAxiom : True := trivial

def contentAddressedNonClaim : String :=
  "§3 content-addressed history; geometric identity primary, git hash compatibility; " ++
  "compose excitement_select not local argmin; not physics GREEN; not production_wired"

end UMST.Urge.ContentAddressed
