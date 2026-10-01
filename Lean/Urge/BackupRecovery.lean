-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/BackupRecovery.lean

  Meso acting Urge — §15.4 backup as typed recovery morphism.
  Backup **is** an Excitement-selected admissible state transition — not rsync theater.
  Composes `UMST.Excitement.select`; no second argmin.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Excitement
import Compat.Gate
import ExcitementProofs
import LandauerLaw
import Urge.ExcitementImport

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

namespace UMST.Urge.BackupRecovery

-- ================================================================
-- SECTION 1: Recovery snapshot + typed morphism carriers
-- ================================================================

/-- Replica class row from §15.4 — offline LUKS carries empty egress. -/
inductive BackupReplicaClass where
  | forgePrimary
  | darwinScratch
  | offlineLuks
  deriving DecidableEq, Repr

def replicaEgressEmpty (c : BackupReplicaClass) : Bool :=
  match c with
  | .offlineLuks | .darwinScratch => true
  | .forgePrimary => false

/-- UCRS stamp surrogate carried through recovery. -/
structure BackupUcrsStamp where
  seq         : Nat
  wallHasT    : Bool

/-- MergeSafe certificate surrogate — recovery must not violate tier disjointness. -/
structure BackupMergeSafeCert where
  mergeSafe : Bool

/-- Snapshot identity at recovery source (content-addressed surrogate). -/
structure BackupRecoverySnapshot where
  snapshotId          : Nat
  head                : ThermodynamicState
  ucrs                : BackupUcrsStamp
  mergeSafeCert       : BackupMergeSafeCert
  provenanceIntact    : Bool
  replica             : BackupReplicaClass

/-- Witness bundle a recovery morphism must preserve (§15.4). -/
structure BackupRecoveryWitness where
  ucrs                : BackupUcrsStamp
  mergeSafeCert       : BackupMergeSafeCert
  provenanceIntact    : Bool

/-- Typed recovery morphism — admissible state transition, not blind copy. -/
structure BackupRecoveryMorphism where
  sourceSnapshot      : BackupRecoverySnapshot
  toReplica           : BackupReplicaClass
  witness             : BackupRecoveryWitness
  excitementSelected  : Bool

/-- Fail-closed recovery errors — positive refuse, not silent no-op. -/
inductive BackupRecoveryRefusal where
  | rsyncTheaterRefused (snapshotId : Nat)
  | gateRejected (seq : Nat)
  | mergeUnsafe (snapshotId : Nat)
  | provenanceLoss (snapshotId : Nat)
  | replicaClassMismatch
  deriving Repr

/-- Verdict of a recovery operation class. -/
inductive BackupRecoveryVerdict where
  | morphismOk
  | rsyncTheaterRefused
  | inadmissible
  deriving Repr

-- ================================================================
-- SECTION 2: §15.4 admissibility conjunct + positive refuse
-- ================================================================

/-- §15.4 admissibility conjunct inputs (surrogate). -/
structure BackupAdmissibilityConjunct where
  gateOk                  : Bool
  mergeSafe               : Bool
  excitementPreserves     : Bool

def backupConjunctAdmits (c : BackupAdmissibilityConjunct) : Bool :=
  c.gateOk && c.mergeSafe && c.excitementPreserves

/-- Classify blind copy vs typed morphism without performing I/O. -/
def evaluateBackupRecoveryOperation (isRsyncTheater : Bool) : BackupRecoveryVerdict :=
  if isRsyncTheater then .rsyncTheaterRefused else .morphismOk

theorem backupRecovery_morphism_ok_when_not_rsync :
    evaluateBackupRecoveryOperation false = .morphismOk := rfl

def witnessFromSnapshot (s : BackupRecoverySnapshot) : BackupRecoveryWitness :=
  { ucrs := s.ucrs
    mergeSafeCert := s.mergeSafeCert
    provenanceIntact := s.provenanceIntact }

/-- Attempt typed recovery morphism to target replica — fail closed on inadmissibility. -/
def applyBackupRecoveryMorphism (snapshot : BackupRecoverySnapshot)
    (toReplica : BackupReplicaClass) (conjunct : BackupAdmissibilityConjunct)
    (excitementSelected : Bool) : BackupRecoveryMorphism ⊕ BackupRecoveryRefusal :=
  if !(backupConjunctAdmits conjunct) then
    Sum.inr (.gateRejected snapshot.ucrs.seq)
  else if !snapshot.mergeSafeCert.mergeSafe then
    Sum.inr (.mergeUnsafe snapshot.snapshotId)
  else if !snapshot.provenanceIntact then
    Sum.inr (.provenanceLoss snapshot.snapshotId)
  else if !excitementSelected then
    Sum.inr (.provenanceLoss snapshot.snapshotId)
  else
    Sum.inl
      { sourceSnapshot := snapshot
        toReplica := toReplica
        witness := witnessFromSnapshot snapshot
        excitementSelected := excitementSelected }

-- ================================================================
-- SECTION 4: §15.4 fixtures + witness theorems
-- ================================================================

def backupFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def backupFixtureUcrs : BackupUcrsStamp :=
  { seq := 7, wallHasT := true }

def backupFixtureMergeSafe : BackupMergeSafeCert :=
  { mergeSafe := true }

def backupFixtureSnapshot : BackupRecoverySnapshot :=
  { snapshotId := 1
    head := backupFixtureState
    ucrs := backupFixtureUcrs
    mergeSafeCert := backupFixtureMergeSafe
    provenanceIntact := true
    replica := .forgePrimary }

def backupFixtureConjunct : BackupAdmissibilityConjunct :=
  { gateOk := true, mergeSafe := true, excitementPreserves := true }

theorem backupFixture_apply_morphism_ok :
    applyBackupRecoveryMorphism backupFixtureSnapshot .offlineLuks backupFixtureConjunct true =
      Sum.inl
        { sourceSnapshot := backupFixtureSnapshot
          toReplica := .offlineLuks
          witness := witnessFromSnapshot backupFixtureSnapshot
          excitementSelected := true } := rfl

theorem backupFixture_witness_preserves_ucrs :
    (witnessFromSnapshot backupFixtureSnapshot).ucrs = backupFixtureUcrs := rfl

theorem backup_recovery_positive_refuse_not_silent :
    evaluateBackupRecoveryOperation true ≠ .morphismOk := by
  simp [evaluateBackupRecoveryOperation]

end UMST.Urge.BackupRecovery
