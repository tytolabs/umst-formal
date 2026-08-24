-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/HilbertPersist.lean

  Meso acting Urge — §12.7 persist Hilbert (acting) distinct from occupancy Hilbert (knowing).
  Acting fiber only — refuse fuse with knowing occupancy Hilbert (not implemented here).
  Composes `UMST.Excitement.select`; no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.HilbertPersist

-- ================================================================
-- SECTION 1: Acting persist Hilbert carriers (§12.7 acting fiber)
-- ================================================================

/-- Acting meso role tag — persist Hilbert indexes Device-tier sled keys. -/
inductive HilbertPersistRole where
  | persistActing
  deriving DecidableEq, Repr

/-- Knowing occupancy Hilbert is **not** on this acting fiber — cite only for refuse. -/
inductive OccupancyKnowingHilbertRefused where
  | fusePersistIntoOccupancy
  | fuseOccupancyIntoPersist
  | knowingFiberNotOnActingMeso
  deriving DecidableEq, Repr

/-- UCRS stamp surrogate carried through persist Hilbert morphism. -/
structure PersistHilbertUcrsStamp where
  seq         : Nat
  wallHasT    : Bool

/-- MergeSafe certificate surrogate — persist must not violate tier disjointness. -/
structure PersistHilbertMergeSafeCert where
  mergeSafe : Bool

/-- Persist Hilbert index — typed acting meso sled key layout (§12.7 acting). -/
structure PersistHilbertIndex where
  raw         : Nat
  bits        : Nat

/-- Snapshot identity at persist source (content-addressed surrogate). -/
structure PersistHilbertSnapshot where
  snapshotId          : Nat
  head                : ThermodynamicState
  ucrs                : PersistHilbertUcrsStamp
  mergeSafeCert       : PersistHilbertMergeSafeCert
  provenanceIntact    : Bool
  index               : PersistHilbertIndex

/-- Witness bundle a persist Hilbert morphism must preserve (§12.7). -/
structure PersistHilbertWitness where
  ucrs                : PersistHilbertUcrsStamp
  mergeSafeCert       : PersistHilbertMergeSafeCert
  provenanceIntact    : Bool
  index               : PersistHilbertIndex

/-- Typed persist Hilbert morphism — admissible acting transition, not fuse. -/
structure PersistHilbertMorphism where
  morphismFrom        : PersistHilbertSnapshot
  witness             : PersistHilbertWitness
  excitementSelected  : Bool

/-- Fail-closed persist Hilbert errors — positive refuse, not silent no-op. -/
inductive PersistHilbertRefusal where
  | fuseOccupancyRefused
  | gateRejected (seq : Nat)
  | mergeUnsafe (snapshotId : Nat)
  | provenanceLoss (snapshotId : Nat)
  | knowingFiberFuseRefused
  deriving Repr

/-- Verdict of a persist Hilbert operation class. -/
inductive PersistHilbertVerdict where
  | morphismOk
  | fuseOccupancyRefused
  | inadmissible
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 2: §12.7 admissibility conjunct + fuse refuse
-- ================================================================

/-- §12.7 admissibility conjunct inputs (surrogate). -/
structure PersistAdmissibilityConjunct where
  gateOk                  : Bool
  mergeSafe               : Bool
  excitementPreserves     : Bool

def persistConjunctAdmits (c : PersistAdmissibilityConjunct) : Bool :=
  c.gateOk && c.mergeSafe && c.excitementPreserves

/-- Classify fuse attempt vs typed morphism without performing I/O. -/
def evaluatePersistHilbertOperation (attemptsFuse : Bool) : PersistHilbertVerdict :=
  if attemptsFuse then .fuseOccupancyRefused else .morphismOk

theorem persistHilbert_fuse_occupancy_refused :
    evaluatePersistHilbertOperation true = .fuseOccupancyRefused := rfl

theorem persistHilbert_morphism_ok_when_not_fuse :
    evaluatePersistHilbertOperation false = .morphismOk := rfl

def refuseHilbertFuseOccupancy : OccupancyKnowingHilbertRefused :=
  .fusePersistIntoOccupancy

theorem refuseHilbertFuseOccupancy_positive :
    refuseHilbertFuseOccupancy = .fusePersistIntoOccupancy := rfl

def refuseKnowingFiberFuse : OccupancyKnowingHilbertRefused :=
  .knowingFiberNotOnActingMeso

theorem refuseKnowingFiberFuse_positive :
    refuseKnowingFiberFuse = .knowingFiberNotOnActingMeso := rfl

def witnessFromPersistSnapshot (s : PersistHilbertSnapshot) : PersistHilbertWitness :=
  { ucrs := s.ucrs
    mergeSafeCert := s.mergeSafeCert
    provenanceIntact := s.provenanceIntact
    index := s.index }

/-- Attempt typed persist Hilbert morphism — fail closed on inadmissibility. -/
def applyPersistHilbertMorphism (snapshot : PersistHilbertSnapshot)
    (conjunct : PersistAdmissibilityConjunct) (excitementSelected : Bool)
    (attemptsFuse : Bool) : PersistHilbertMorphism ⊕ PersistHilbertRefusal :=
  if attemptsFuse then
    Sum.inr .fuseOccupancyRefused
  else if !persistConjunctAdmits conjunct then
    Sum.inr (.gateRejected snapshot.ucrs.seq)
  else if !snapshot.mergeSafeCert.mergeSafe then
    Sum.inr (.mergeUnsafe snapshot.snapshotId)
  else if !snapshot.provenanceIntact then
    Sum.inr (.provenanceLoss snapshot.snapshotId)
  else if !excitementSelected then
    Sum.inr .knowingFiberFuseRefused
  else
    Sum.inl
      { morphismFrom := snapshot
        witness := witnessFromPersistSnapshot snapshot
        excitementSelected := excitementSelected }

-- ================================================================
-- SECTION 3: Persist Hilbert composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for persist Hilbert over admissible history successors. -/
structure PersistHilbertCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Persist Hilbert selection **is** `Excitement.select` — not a second argmin. -/
noncomputable def persistHilbertSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistHilbertCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def persistHilbertSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) : Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem persistHilbertSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistHilbertCtx S) :
    persistHilbertSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem persistHilbertSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    persistHilbertSelectBare prior successors = select prior successors :=
  rfl

theorem persistHilbertSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistHilbertCtx S) :
    persistHilbertSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem persistHilbert_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistHilbertCtx S) :
    persistHilbertSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem persistHilbert_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    persistHilbertSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [persistHilbertSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: §12.7 persist index surrogate + fixtures
-- ================================================================

def defaultPersistHilbertBits : Nat := 4

def persistHilbertSide (bits : Nat) : Nat :=
  Nat.shiftLeft 1 bits

def persistHilbertMask (bits : Nat) : Nat :=
  persistHilbertSide bits - 1

/-- Map `(ucrs_seq, grid_hash)` to 2D coords for persist acting path. -/
def persistHilbertCoords (ucrs grid : Nat) (bits : Nat) : Nat × Nat :=
  let mask := persistHilbertMask bits
  let x := ucrs % (mask + 1)
  let y := (Nat.xor grid (grid / 65536)) % (mask + 1)
  (x, y)

/-- Surrogate curve index — acting meso sled key layout (not occupancy). -/
def persistCurveIndex (x y bits : Nat) : Nat :=
  let side := persistHilbertSide bits
  (x % side) + (y % side) * side

def computePersistHilbertIndex (ucrs grid bits : Nat) : PersistHilbertIndex :=
  let (x, y) := persistHilbertCoords ucrs grid bits
  { raw := persistCurveIndex x y bits, bits := bits }

def persistFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def persistFixtureUcrs : PersistHilbertUcrsStamp :=
  { seq := 7, wallHasT := true }

def persistFixtureMergeSafe : PersistHilbertMergeSafeCert :=
  { mergeSafe := true }

def persistFixtureIndex : PersistHilbertIndex :=
  computePersistHilbertIndex 7 0xABCD defaultPersistHilbertBits

def persistFixtureSnapshot : PersistHilbertSnapshot :=
  { snapshotId := 1
    head := persistFixtureState
    ucrs := persistFixtureUcrs
    mergeSafeCert := persistFixtureMergeSafe
    provenanceIntact := true
    index := persistFixtureIndex }

def persistFixtureConjunct : PersistAdmissibilityConjunct :=
  { gateOk := true, mergeSafe := true, excitementPreserves := true }

theorem persistFixture_fuse_occupancy_refused :
    refuseHilbertFuseOccupancy = .fusePersistIntoOccupancy := rfl

theorem persistFixture_apply_morphism_ok :
    applyPersistHilbertMorphism persistFixtureSnapshot persistFixtureConjunct true false =
      Sum.inl
        { morphismFrom := persistFixtureSnapshot
          witness := witnessFromPersistSnapshot persistFixtureSnapshot
          excitementSelected := true } := rfl

theorem persistFixture_apply_fuse_refused :
    applyPersistHilbertMorphism persistFixtureSnapshot persistFixtureConjunct true true =
      Sum.inr .fuseOccupancyRefused := rfl

theorem persistFixture_witness_preserves_ucrs :
    (witnessFromPersistSnapshot persistFixtureSnapshot).ucrs = persistFixtureUcrs := rfl

theorem persistFixture_witness_preserves_index :
    (witnessFromPersistSnapshot persistFixtureSnapshot).index = persistFixtureIndex := rfl

theorem persistFixture_index_bits :
    persistFixtureIndex.bits = defaultPersistHilbertBits := rfl

-- ================================================================
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

structure PersistHilbertTransition where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissiblePersistHilbertTransition (t : PersistHilbertTransition) : Prop :=
  t.gateChecked ∧ t.mergeSafe ∧ t.provenanceOk

def persistHilbertSecondLaw (t : PersistHilbertTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalPersistHilbertBridge where
  proc : ErasureProcess
  transition : PersistHilbertTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissiblePersistHilbertTransition transition

theorem persistHilbertSecondLaw_from_physical (b : PhysicalPersistHilbertBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    persistHilbertSecondLaw b.transition := by
  unfold persistHilbertSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissiblePersistHilbertTransition_from_physical (b : PhysicalPersistHilbertBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissiblePersistHilbertTransition b.transition :=
  b.admissible

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def hilbertPersistPhysicsGreen : Bool := false

theorem hilbertPersistPhysicsGreenFalse : hilbertPersistPhysicsGreen = false := rfl

def hilbertPersistProductionWired : Bool := false

theorem hilbertPersistProductionWiredFalse : hilbertPersistProductionWired = false := rfl

theorem hilbertPersistModuleWitness : True := trivial

theorem hilbertPersist_noNewAxiom : True := trivial

theorem hilbertPersist_positive_refuse_not_silent :
    evaluatePersistHilbertOperation true ≠ .morphismOk := by
  decide

theorem hilbertPersist_acting_role_witness :
    HilbertPersistRole.persistActing = HilbertPersistRole.persistActing := rfl

end UMST.Urge.HilbertPersist
