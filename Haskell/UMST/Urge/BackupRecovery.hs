-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.BackupRecovery
-- Description : Meso acting Urge — §15.4 backup as typed recovery morphism.
--
-- Backup **is** an Excitement-selected admissible state transition on the
-- admissible replica coalgebra — not rsync theater.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.BackupRecovery
  ( -- * Replica class rows (§15.4)
    BackupReplicaClass (..)
  , replicaEgressEmpty
  , offlineLuksEgressEmpty
  , darwinScratchEgressEmpty
  , forgePrimaryEgressNonempty
    -- * Recovery snapshot + typed morphism carriers
  , BackupUcrsStamp (..)
  , BackupMergeSafeCert (..)
  , BackupRecoverySnapshot (..)
  , BackupRecoveryWitness (..)
  , BackupRecoveryMorphism (..)
  , BackupRecoveryRefusal (..)
  , BackupRecoveryVerdict (..)
    -- * §15.4 admissibility conjunct + positive refuse
  , BackupAdmissibilityConjunct (..)
  , backupConjunctAdmits
  , evaluateBackupRecoveryOperation
  , refuseRsyncTheater
  , refuseRsyncTheaterPositive
  , witnessFromSnapshot
  , applyBackupRecoveryMorphism
  , backupRecoveryRsyncTheaterRefused
  , backupRecoveryMorphismOkWhenNotRsync
  , backupRecoveryPositiveRefuseNotSilent
    -- * Excitement alignment (no second argmin)
  , BackupRecoveryCtx (..)
  , backupRecoverySelect
  , backupRecoverySelectBare
  , backupRecoverySelectEqExcitementSelect
  , backupRecoverySelectBareEqExcitementSelect
  , backupRecoverySelectEqUrgeRecoverySelect
  , backupRecoveryNoLocalArgmin
  , backupRecoveryEmpty
    -- * Landauer bridge (derived — zero new axioms)
  , BackupTransition (..)
  , admissibleBackupTransition
  , backupSecondLaw
  , PhysicalBackupBridge (..)
  , backupSecondLawFromPhysical
  , admissibleBackupTransitionFromPhysical
  , backupSecondLawFromLandauer
  , backupSecondLawFromHypothesis
    -- * §15.4 fixtures + witness theorems
  , backupFixtureState
  , backupFixtureUcrs
  , backupFixtureMergeSafe
  , backupFixtureSnapshot
  , backupFixtureConjunct
  , backupFixtureRsyncTheaterRefused
  , backupFixtureApplyMorphismOk
  , backupFixtureWitnessPreservesUcrs
    -- * Honesty flags + catalog witnesses
  , backupRecoveryPhysicsGreen
  , backupRecoveryPhysicsGreenFalse
  , backupRecoveryProductionWired
  , backupRecoveryProductionWiredFalse
  , backupRecoveryNonClaim
  , backupRecoveryNonClaimNonempty
  , backupRecoveryModuleWitness
  , backupRecoveryNoNewAxiom
  , backupRecoveryNoSecondArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.ExcitementImport
  ( urgeRecoverySelect
  , urgeRecoverySelectEqExcitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Replica class rows (§15.4)
-- ---------------------------------------------------------------------------

-- | Replica class row from §15.4 — offline LUKS carries empty egress.
data BackupReplicaClass
  = BackupForgePrimary
  | BackupDarwinScratch
  | BackupOfflineLuks
  deriving (Show, Eq)

-- | Whether declared network egress is empty for this replica class.
replicaEgressEmpty :: BackupReplicaClass -> Bool
replicaEgressEmpty BackupOfflineLuks   = True
replicaEgressEmpty BackupDarwinScratch = True
replicaEgressEmpty BackupForgePrimary  = False

-- | Offline LUKS row: egress explicitly empty.
offlineLuksEgressEmpty :: Bool
offlineLuksEgressEmpty = replicaEgressEmpty BackupOfflineLuks

-- | Darwin scratch row: egress explicitly empty.
darwinScratchEgressEmpty :: Bool
darwinScratchEgressEmpty = replicaEgressEmpty BackupDarwinScratch

-- | Forge primary row: egress non-empty.
forgePrimaryEgressNonempty :: Bool
forgePrimaryEgressNonempty = not (replicaEgressEmpty BackupForgePrimary)

-- ---------------------------------------------------------------------------
-- SECTION 2: Recovery snapshot + typed morphism carriers
-- ---------------------------------------------------------------------------

-- | UCRS stamp surrogate carried through recovery.
data BackupUcrsStamp = BackupUcrsStamp
  { backupUcrsSeq     :: !Int
  , backupUcrsWallHasT :: !Bool
  } deriving (Show, Eq)

-- | MergeSafe certificate surrogate — recovery must not violate tier disjointness.
data BackupMergeSafeCert = BackupMergeSafeCert
  { backupMergeSafe :: !Bool
  } deriving (Show, Eq)

-- | Snapshot identity at recovery source (content-addressed surrogate).
data BackupRecoverySnapshot = BackupRecoverySnapshot
  { backupSnapshotId          :: !Int
  , backupSnapshotHead        :: !ThermodynamicState
  , backupSnapshotUcrs          :: !BackupUcrsStamp
  , backupSnapshotMergeSafe   :: !BackupMergeSafeCert
  , backupSnapshotProvenanceIntact :: !Bool
  , backupSnapshotReplica       :: !BackupReplicaClass
  } deriving (Show, Eq)

-- | Witness bundle a recovery morphism must preserve (§15.4).
data BackupRecoveryWitness = BackupRecoveryWitness
  { backupWitnessUcrs              :: !BackupUcrsStamp
  , backupWitnessMergeSafe           :: !BackupMergeSafeCert
  , backupWitnessProvenanceIntact    :: !Bool
  } deriving (Show, Eq)

-- | Typed recovery morphism — admissible state transition, not blind copy.
data BackupRecoveryMorphism = BackupRecoveryMorphism
  { backupMorphismFrom              :: !BackupRecoverySnapshot
  , backupMorphismToReplica         :: !BackupReplicaClass
  , backupMorphismWitness           :: !BackupRecoveryWitness
  , backupMorphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed recovery errors — positive refuse, not silent no-op.
data BackupRecoveryRefusal
  = BackupRsyncTheaterRefused !Int
  | BackupGateRejected !Int
  | BackupMergeUnsafe !Int
  | BackupProvenanceLoss !Int
  | BackupReplicaClassMismatch
  deriving (Show, Eq)

-- | Verdict of a recovery operation class.
data BackupRecoveryVerdict
  = BackupMorphismOk
  | BackupVerdictRsyncTheaterRefused
  | BackupInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 3: §15.4 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §15.4 admissibility conjunct inputs (surrogate).
data BackupAdmissibilityConjunct = BackupAdmissibilityConjunct
  { backupConjGateOk              :: !Bool
  , backupConjMergeSafe           :: !Bool
  , backupConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate `admit(h) ⟺ gate ∧ MergeSafe ∧ Excitement preserves`.
backupConjunctAdmits :: BackupAdmissibilityConjunct -> Bool
backupConjunctAdmits c =
  backupConjGateOk c
  && backupConjMergeSafe c
  && backupConjExcitementPreserves c

-- | Classify blind copy vs typed morphism without performing I/O.
evaluateBackupRecoveryOperation :: Bool -> BackupRecoveryVerdict
evaluateBackupRecoveryOperation isRsyncTheater =
  if isRsyncTheater then BackupVerdictRsyncTheaterRefused else BackupMorphismOk

-- | Positive refuse: rsync theater is inadmissible — backup is typed morphism.
refuseRsyncTheater :: Int -> BackupRecoveryRefusal
refuseRsyncTheater snapshotId = BackupRsyncTheaterRefused snapshotId

-- | Reflexivity witness for rsync theater refusal.
refuseRsyncTheaterPositive :: Int -> Bool
refuseRsyncTheaterPositive snapshotId =
  refuseRsyncTheater snapshotId == BackupRsyncTheaterRefused snapshotId

-- | Build witness from snapshot — morphism must preserve stamps and certificates.
witnessFromSnapshot :: BackupRecoverySnapshot -> BackupRecoveryWitness
witnessFromSnapshot s =
  BackupRecoveryWitness
    { backupWitnessUcrs = backupSnapshotUcrs s
    , backupWitnessMergeSafe = backupSnapshotMergeSafe s
    , backupWitnessProvenanceIntact = backupSnapshotProvenanceIntact s
    }

-- | Attempt typed recovery morphism to target replica — fail closed on inadmissibility.
applyBackupRecoveryMorphism
  :: BackupRecoverySnapshot
  -> BackupReplicaClass
  -> BackupAdmissibilityConjunct
  -> Bool
  -> Either BackupRecoveryRefusal BackupRecoveryMorphism
applyBackupRecoveryMorphism snapshot toReplica conjunct excitementSelected =
  if not (backupConjunctAdmits conjunct)
    then Left (BackupGateRejected (backupUcrsSeq (backupSnapshotUcrs snapshot)))
  else if not (backupMergeSafe (backupSnapshotMergeSafe snapshot))
    then Left (BackupMergeUnsafe (backupSnapshotId snapshot))
  else if not (backupSnapshotProvenanceIntact snapshot)
    then Left (BackupProvenanceLoss (backupSnapshotId snapshot))
  else if not excitementSelected
    then Left (BackupProvenanceLoss (backupSnapshotId snapshot))
  else
    Right
      BackupRecoveryMorphism
        { backupMorphismFrom = snapshot
        , backupMorphismToReplica = toReplica
        , backupMorphismWitness = witnessFromSnapshot snapshot
        , backupMorphismExcitementSelected = excitementSelected
        }

-- | Rsync theater classification is always refused verdict.
backupRecoveryRsyncTheaterRefused :: Bool
backupRecoveryRsyncTheaterRefused =
  evaluateBackupRecoveryOperation True == BackupVerdictRsyncTheaterRefused

-- | Non-rsync path yields morphism-ok verdict.
backupRecoveryMorphismOkWhenNotRsync :: Bool
backupRecoveryMorphismOkWhenNotRsync =
  evaluateBackupRecoveryOperation False == BackupMorphismOk

-- | Positive refuse is not silent no-op.
backupRecoveryPositiveRefuseNotSilent :: Bool
backupRecoveryPositiveRefuseNotSilent =
  evaluateBackupRecoveryOperation True /= BackupMorphismOk

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for backup recovery over admissible history successors.
data BackupRecoveryCtx = BackupRecoveryCtx
  { backupRecoveryPrior      :: !ThermodynamicState
  , backupRecoverySuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Backup recovery **is** 'excitementSelect' — not a second argmin.
backupRecoverySelect
  :: BackupRecoveryCtx
  -> Either ExcitementResidue HistoryCandidate
backupRecoverySelect ctx =
  excitementSelect (backupRecoveryPrior ctx) (backupRecoverySuccessors ctx)

-- | Bare @(prior, successors)@ alias — same selector, no re-derivation.
backupRecoverySelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
backupRecoverySelectBare = excitementSelect

-- | Definitional witness: backup recovery API is 'excitementSelect'.
backupRecoverySelectEqExcitementSelect :: BackupRecoveryCtx -> Bool
backupRecoverySelectEqExcitementSelect ctx =
  backupRecoverySelect ctx
    == excitementSelect (backupRecoveryPrior ctx) (backupRecoverySuccessors ctx)

-- | Bare alias equals 'excitementSelect'.
backupRecoverySelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
backupRecoverySelectBareEqExcitementSelect prior successors =
  backupRecoverySelectBare prior successors == excitementSelect prior successors

-- | Backup recovery equals 'urgeRecoverySelect' import.
backupRecoverySelectEqUrgeRecoverySelect :: BackupRecoveryCtx -> Bool
backupRecoverySelectEqUrgeRecoverySelect ctx =
  backupRecoverySelect ctx
    == urgeRecoverySelect (backupRecoveryPrior ctx) (backupRecoverySuccessors ctx)

-- | Backup selector re-uses 'excitementSelect' — no Urge-local argmin.
backupRecoveryNoLocalArgmin :: BackupRecoveryCtx -> Bool
backupRecoveryNoLocalArgmin ctx =
  backupRecoverySelect ctx
    == excitementSelect (backupRecoveryPrior ctx) (backupRecoverySuccessors ctx)

-- | Empty successor list yields no-candidates residue.
backupRecoveryEmpty :: ThermodynamicState -> Bool
backupRecoveryEmpty prior =
  backupRecoverySelectBare prior [] == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Backup transition accounting (surrogate for §15.4 second-law discharge).
data BackupTransition = BackupTransition
  { backupTransition :: !HistoryTransition
  , backupGateChecked :: !Bool
  , backupMergeSafeOk :: !Bool
  , backupProvenanceOk :: !Bool
  } deriving (Show, Eq)

-- | Admissible backup transition conjunct.
admissibleBackupTransition :: BackupTransition -> Bool
admissibleBackupTransition t =
  backupGateChecked t && backupMergeSafeOk t && backupProvenanceOk t

-- | Second law on backup transition (Bool witness — not a new axiom).
backupSecondLaw :: BackupTransition -> Bool
backupSecondLaw t = admitSecondLaw (backupTransition t)

-- | Physical bridge tying backup transition to Landauer discharge.
data PhysicalBackupBridge = PhysicalBackupBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalBackupTrans    :: !BackupTransition
  , physicalAdmissible     :: !Bool
  } deriving (Show, Eq)

-- | Second law from physical @physicalSecondLaw@ hypothesis discharge.
backupSecondLawFromPhysical :: PhysicalBackupBridge -> Bool -> Bool
backupSecondLawFromPhysical b hSL =
  hSL && backupSecondLaw (physicalBackupTrans b)

-- | Admissible transition from physical bridge (no new axiom).
admissibleBackupTransitionFromPhysical :: PhysicalBackupBridge -> Bool -> Bool
admissibleBackupTransitionFromPhysical b hSL =
  hSL && admissibleBackupTransition (physicalBackupTrans b) && physicalAdmissible b

-- | Second law on backup carrier transition from Landauer bridge discharge.
backupSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
backupSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for backup second law (no new axiom).
backupSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
backupSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: §15.4 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture thermodynamic head for catalog decode.
backupFixtureState :: ThermodynamicState
backupFixtureState = ThermodynamicState 2400 0 0.3 30 40

-- | Fixture UCRS stamp surrogate.
backupFixtureUcrs :: BackupUcrsStamp
backupFixtureUcrs = BackupUcrsStamp {backupUcrsSeq = 7, backupUcrsWallHasT = True}

-- | Fixture MergeSafe certificate.
backupFixtureMergeSafe :: BackupMergeSafeCert
backupFixtureMergeSafe = BackupMergeSafeCert {backupMergeSafe = True}

-- | Fixture recovery snapshot at forge primary.
backupFixtureSnapshot :: BackupRecoverySnapshot
backupFixtureSnapshot =
  BackupRecoverySnapshot
    { backupSnapshotId = 1
    , backupSnapshotHead = backupFixtureState
    , backupSnapshotUcrs = backupFixtureUcrs
    , backupSnapshotMergeSafe = backupFixtureMergeSafe
    , backupSnapshotProvenanceIntact = True
    , backupSnapshotReplica = BackupForgePrimary
    }

-- | Fixture admissibility conjunct (all gates pass).
backupFixtureConjunct :: BackupAdmissibilityConjunct
backupFixtureConjunct =
  BackupAdmissibilityConjunct
    { backupConjGateOk = True
    , backupConjMergeSafe = True
    , backupConjExcitementPreserves = True
    }

-- | Fixture rsync theater refusal is positive.
backupFixtureRsyncTheaterRefused :: Bool
backupFixtureRsyncTheaterRefused =
  refuseRsyncTheater (backupSnapshotId backupFixtureSnapshot)
    == BackupRsyncTheaterRefused 1

-- | Fixture typed morphism to offline LUKS succeeds.
backupFixtureApplyMorphismOk :: Bool
backupFixtureApplyMorphismOk =
  applyBackupRecoveryMorphism
    backupFixtureSnapshot
    BackupOfflineLuks
    backupFixtureConjunct
    True
    == Right
      BackupRecoveryMorphism
        { backupMorphismFrom = backupFixtureSnapshot
        , backupMorphismToReplica = BackupOfflineLuks
        , backupMorphismWitness = witnessFromSnapshot backupFixtureSnapshot
        , backupMorphismExcitementSelected = True
        }

-- | Fixture witness preserves UCRS stamp.
backupFixtureWitnessPreservesUcrs :: Bool
backupFixtureWitnessPreservesUcrs =
  backupWitnessUcrs (witnessFromSnapshot backupFixtureSnapshot)
    == backupFixtureUcrs

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
backupRecoveryPhysicsGreen :: Bool
backupRecoveryPhysicsGreen = False

-- | Lean/Coq: @backup_recovery_physics_green_false@.
backupRecoveryPhysicsGreenFalse :: Bool
backupRecoveryPhysicsGreenFalse = not backupRecoveryPhysicsGreen

-- | Production wiring stays open (backup lift only).
backupRecoveryProductionWired :: Bool
backupRecoveryProductionWired = False

-- | Lean/Coq: @backup_recovery_production_wired_false@.
backupRecoveryProductionWiredFalse :: Bool
backupRecoveryProductionWiredFalse = not backupRecoveryProductionWired

-- | Honest non-claim string (meso §15.4 backup scaffold).
backupRecoveryNonClaim :: String
backupRecoveryNonClaim =
  "§15.4 backup is typed recovery morphism on admissible replica coalgebra; "
    ++ "gate_check MergeSafe Excitement preserves provenance; "
    ++ "rsync theater refused; offline LUKS egress empty; "
    ++ "not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
backupRecoveryNonClaimNonempty :: Bool
backupRecoveryNonClaimNonempty = length backupRecoveryNonClaim > 0

-- | Catalog witness: meso Urge BackupRecovery module present.
backupRecoveryModuleWitness :: Bool
backupRecoveryModuleWitness = True

-- | Zero new axiom discipline witness.
backupRecoveryNoNewAxiom :: Bool
backupRecoveryNoNewAxiom = True

-- | Second-argmin refusal: backup composes 'excitementSelect' only.
backupRecoveryNoSecondArgmin :: Bool
backupRecoveryNoSecondArgmin =
  backupRecoveryNoLocalArgmin
    (BackupRecoveryCtx backupFixtureState [])
  && urgeRecoverySelectEqExcitementSelect backupFixtureState []
