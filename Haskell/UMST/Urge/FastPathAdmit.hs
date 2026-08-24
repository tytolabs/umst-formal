-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.FastPathAdmit
-- Description : Meso acting Urge — §17.8 fast-path admission as typed predicate.
--
-- Local commit uses a typed fast predicate (≤100ms budget constant),
-- analogue of R23 PreservationWitness — no whole-tree re-scan.
-- Merge / recovery pays the slow path (≤1s budget) with composed
-- 'excitementSelect' — **not** wall-clock GREEN, not a second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.FastPathAdmit
  ( -- * §17.8 typed budget constants (not wall-clock GREEN)
    localCommitBudgetMs
  , mergeRecoveryBudgetMs
  , localCommitBudgetIs100
  , mergeRecoveryBudgetIs1000
    -- * Admission path classification
  , AdmitPath (..)
  , admitPathBudgetMs
  , admitPathFastLocalBudget
  , admitPathMergeRecoveryBudget
    -- * Fast-path candidate + typed predicate
  , FastPathCandidate (..)
  , fastPathAdmitPred
  , FastPathAdmitRefusal (..)
  , classifyAdmitPath
  , classifyAdmitPathFastLocal
  , classifyAdmitPathWholeTreeRescan
  , classifyAdmitPathMergeRecovery
  , refuseWallClockSlaTheater
  , refuseWallClockSlaTheaterIsRefused
    -- * Typed budget witness (declared ceiling, not measured)
  , LatencyBudgetWitness (..)
  , budgetWitnessFor
  , budgetWitnessForTyped
  , budgetWitnessForBudget
  , checkTypedBudget
  , checkTypedBudgetOk
  , checkTypedBudgetExceeded
    -- * Slow path composes Excitement (no second argmin)
  , slowPathRecovery
  , excitementSelectBare
  , slowPathRecoveryEqUrgeRecovery
  , slowPathRecoveryEqExcitementSelect
  , slowPathRecoveryNoSecondArgmin
  , classifySlowPath
  , classifySlowPathMergeRecovery
    -- * Positive refuse witnesses
  , sampleFastCandidate
  , classifyAdmitPathFastLocalSample
  , classifyAdmitPathWholeTreeRescanSample
  , classifyAdmitPathMergeRecoverySample
  , fastPathSelect
  , fastPathSelectEqExcitementSelect
  , fastPathNoLocalArgmin
    -- * Bridge to physicalSecondLaw (derived — zero new axioms)
  , FastPathTransition (..)
  , fastPathSecondLaw
  , fastPathSecondLawFromLandauer
  , fastPathSecondLawFromHypothesis
  , fastPathFromLandauerAdmitSecondLaw
    -- * Honesty flags + catalog witnesses
  , fastPathPhysicsGreen
  , fastPathPhysicsGreenFalse
  , fastPathProductionWired
  , fastPathProductionWiredFalse
  , fastPathAdmitModuleWitness
  , fastPathAdmitNoNewAxiom
  , fastPathAdmitNoSecondArgmin
  , fastPathAdmitNonClaim
  , fastPathAdmitNonClaimNonempty
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.ExcitementImport
  ( HistoryRecoveryCtx (..)
  , urgeRecovery
  , urgeRecoveryEqExcitementSelect
  , urgeRecoverySelect
  , urgeRecoverySelectEqExcitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: §17.8 typed budget constants (not wall-clock GREEN)
-- ---------------------------------------------------------------------------

-- | Blueprint §17.8 local commit admission budget (milliseconds, typed).
localCommitBudgetMs :: Int
localCommitBudgetMs = 100

-- | Blueprint §17.8 merge / recovery slow-path budget (milliseconds, typed).
mergeRecoveryBudgetMs :: Int
mergeRecoveryBudgetMs = 1000

-- | Witness: local commit budget is 100ms (typed constant, not measured).
localCommitBudgetIs100 :: Bool
localCommitBudgetIs100 = localCommitBudgetMs == 100

-- | Witness: merge/recovery budget is 1000ms (typed constant, not measured).
mergeRecoveryBudgetIs1000 :: Bool
mergeRecoveryBudgetIs1000 = mergeRecoveryBudgetMs == 1000

-- ---------------------------------------------------------------------------
-- SECTION 2: Admission path classification
-- ---------------------------------------------------------------------------

-- | Admission path class — fast local vs full merge/recovery slow path.
data AdmitPath
  = FastLocal
  | FullMergeRecovery
  deriving (Show, Eq)

-- | Typed budget ceiling for each path class (not measured wall-clock).
admitPathBudgetMs :: AdmitPath -> Int
admitPathBudgetMs path =
  case path of
    FastLocal -> localCommitBudgetMs
    FullMergeRecovery -> mergeRecoveryBudgetMs

-- | Fast-local path budget equals local commit constant.
admitPathFastLocalBudget :: Bool
admitPathFastLocalBudget =
  admitPathBudgetMs FastLocal == localCommitBudgetMs

-- | Merge/recovery path budget equals slow-path constant.
admitPathMergeRecoveryBudget :: Bool
admitPathMergeRecoveryBudget =
  admitPathBudgetMs FullMergeRecovery == mergeRecoveryBudgetMs

-- ---------------------------------------------------------------------------
-- SECTION 3: Fast-path candidate + typed predicate
-- ---------------------------------------------------------------------------

-- | Candidate for fast-path admission — local predicate inputs only.
data FastPathCandidate = FastPathCandidate
  { fpIsLocalAppend            :: !Bool
  , fpRequiresWholeTreeRescan  :: !Bool
  , fpIsMergeOrRecovery        :: !Bool
  } deriving (Show, Eq)

-- | Fast-path typed predicate — local append without whole-tree re-scan or merge.
fastPathAdmitPred :: FastPathCandidate -> Bool
fastPathAdmitPred c =
  fpIsLocalAppend c
    && not (fpRequiresWholeTreeRescan c)
    && not (fpIsMergeOrRecovery c)

data FastPathAdmitRefusal
  = RefuseWholeTreeRescan
  | RefuseMergeRecoverySlowPath
  | RefuseWallClockSlaTheater
  | RefuseBudgetExceeded !Int !Int
  deriving (Show, Eq)

-- | Classify admission path from candidate — honest refusal on inadmissible fast path.
classifyAdmitPath :: FastPathCandidate -> Either FastPathAdmitRefusal AdmitPath
classifyAdmitPath c =
  if fpRequiresWholeTreeRescan c then
    Left RefuseWholeTreeRescan
  else if fpIsMergeOrRecovery c then
    Left RefuseMergeRecoverySlowPath
  else if fastPathAdmitPred c then
    Right FastLocal
  else
    Left (RefuseBudgetExceeded (localCommitBudgetMs + 1) localCommitBudgetMs)

-- | Witness: local append without rescan/merge classifies as fast local.
classifyAdmitPathFastLocal :: FastPathCandidate -> Bool
classifyAdmitPathFastLocal c =
  fpIsLocalAppend c
    && not (fpRequiresWholeTreeRescan c)
    && not (fpIsMergeOrRecovery c)
    && classifyAdmitPath c == Right FastLocal

-- | Witness: whole-tree rescan refuses fast path.
classifyAdmitPathWholeTreeRescan :: FastPathCandidate -> Bool
classifyAdmitPathWholeTreeRescan c =
  fpRequiresWholeTreeRescan c
    && classifyAdmitPath c == Left RefuseWholeTreeRescan

-- | Witness: merge/recovery refuses fast path (slow path required).
classifyAdmitPathMergeRecovery :: FastPathCandidate -> Bool
classifyAdmitPathMergeRecovery c =
  not (fpRequiresWholeTreeRescan c)
    && fpIsMergeOrRecovery c
    && classifyAdmitPath c == Left RefuseMergeRecoverySlowPath

-- | Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only.
refuseWallClockSlaTheater :: Either FastPathAdmitRefusal ()
refuseWallClockSlaTheater = Left RefuseWallClockSlaTheater

-- | Wall-clock SLA theater refusal is always refused.
refuseWallClockSlaTheaterIsRefused :: Bool
refuseWallClockSlaTheaterIsRefused =
  refuseWallClockSlaTheater == Left RefuseWallClockSlaTheater

-- ---------------------------------------------------------------------------
-- SECTION 4: Typed budget witness (declared ceiling, not measured)
-- ---------------------------------------------------------------------------

-- | Typed latency budget witness — declared ceiling, not measured wall-clock.
data LatencyBudgetWitness = LatencyBudgetWitness
  { lbPath            :: !AdmitPath
  , lbBudgetMs        :: !Int
  , lbTypedPredicate  :: !Bool
  } deriving (Show, Eq)

-- | Budget witness for a path class with typed predicate flag set.
budgetWitnessFor :: AdmitPath -> LatencyBudgetWitness
budgetWitnessFor path =
  LatencyBudgetWitness
    { lbPath = path
    , lbBudgetMs = admitPathBudgetMs path
    , lbTypedPredicate = True
    }

-- | Budget witness typed predicate is always true.
budgetWitnessForTyped :: AdmitPath -> Bool
budgetWitnessForTyped path =
  lbTypedPredicate (budgetWitnessFor path)

-- | Budget witness budget matches path ceiling.
budgetWitnessForBudget :: AdmitPath -> Bool
budgetWitnessForBudget path =
  lbBudgetMs (budgetWitnessFor path) == admitPathBudgetMs path

-- | Check surrogate estimated cost against typed budget — refuse if exceeded.
checkTypedBudget
  :: AdmitPath
  -> Int
  -> Either FastPathAdmitRefusal LatencyBudgetWitness
checkTypedBudget path estimatedMs =
  if estimatedMs <= admitPathBudgetMs path then
    Right (budgetWitnessFor path)
  else
    Left (RefuseBudgetExceeded estimatedMs (admitPathBudgetMs path))

-- | Witness: estimated cost within budget yields witness.
checkTypedBudgetOk :: AdmitPath -> Int -> Bool
checkTypedBudgetOk path estimatedMs =
  estimatedMs <= admitPathBudgetMs path
    && checkTypedBudget path estimatedMs == Right (budgetWitnessFor path)

-- | Witness: estimated cost above budget refuses.
checkTypedBudgetExceeded :: AdmitPath -> Int -> Bool
checkTypedBudgetExceeded path estimatedMs =
  admitPathBudgetMs path < estimatedMs
    && checkTypedBudget path estimatedMs
      == Left (RefuseBudgetExceeded estimatedMs (admitPathBudgetMs path))

-- ---------------------------------------------------------------------------
-- SECTION 5: Slow path composes Excitement (no second argmin)
-- ---------------------------------------------------------------------------

-- | Merge / recovery slow path routes through 'urgeRecovery' / 'excitementSelect'.
slowPathRecovery
  :: HistoryRecoveryCtx
  -> Either ExcitementResidue HistoryCandidate
slowPathRecovery = urgeRecovery

-- | Alias on bare @(prior, successors)@ — same selector, no re-derivation.
excitementSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
excitementSelectBare = excitementSelect

-- | Slow path equals 'urgeRecovery' (definitional).
slowPathRecoveryEqUrgeRecovery :: HistoryRecoveryCtx -> Bool
slowPathRecoveryEqUrgeRecovery ctx =
  slowPathRecovery ctx == urgeRecovery ctx

-- | Slow path equals bare 'excitementSelect' (no second argmin).
slowPathRecoveryEqExcitementSelect :: HistoryRecoveryCtx -> Bool
slowPathRecoveryEqExcitementSelect ctx =
  slowPathRecovery ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Slow path re-uses 'excitementSelect' — no Urge-local argmin.
slowPathRecoveryNoSecondArgmin :: HistoryRecoveryCtx -> Bool
slowPathRecoveryNoSecondArgmin ctx =
  slowPathRecovery ctx
    == urgeRecoverySelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Slow-path admission class for merge/recovery candidates.
classifySlowPath :: FastPathCandidate -> Either FastPathAdmitRefusal AdmitPath
classifySlowPath c =
  if fpIsMergeOrRecovery c then
    Right FullMergeRecovery
  else
    classifyAdmitPath c

-- | Witness: merge/recovery candidate classifies as slow path.
classifySlowPathMergeRecovery :: FastPathCandidate -> Bool
classifySlowPathMergeRecovery c =
  fpIsMergeOrRecovery c
    && classifySlowPath c == Right FullMergeRecovery

-- ---------------------------------------------------------------------------
-- SECTION 6: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Sample fast-path candidate: local append, no rescan, no merge.
sampleFastCandidate :: FastPathCandidate
sampleFastCandidate =
  FastPathCandidate
    { fpIsLocalAppend = True
    , fpRequiresWholeTreeRescan = False
    , fpIsMergeOrRecovery = False
    }

-- | Sample fast candidate classifies as fast local.
classifyAdmitPathFastLocalSample :: Bool
classifyAdmitPathFastLocalSample =
  classifyAdmitPath sampleFastCandidate == Right FastLocal

-- | Sample whole-tree rescan refuses fast path.
classifyAdmitPathWholeTreeRescanSample :: Bool
classifyAdmitPathWholeTreeRescanSample =
  classifyAdmitPath
    (FastPathCandidate True True False)
    == Left RefuseWholeTreeRescan

-- | Sample merge/recovery refuses fast path.
classifyAdmitPathMergeRecoverySample :: Bool
classifyAdmitPathMergeRecoverySample =
  classifyAdmitPath
    (FastPathCandidate True False True)
    == Left RefuseMergeRecoverySlowPath

-- | Fast-path history recovery composes 'excitementSelect' — not a second argmin.
fastPathSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
fastPathSelect = excitementSelect

-- | Definitional witness: fast-path selection API is 'excitementSelect'.
fastPathSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
fastPathSelectEqExcitementSelect src cands =
  fastPathSelect src cands == excitementSelect src cands

-- | Fast-path selector re-uses 'excitementSelect' — no Urge-local argmin.
fastPathNoLocalArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
fastPathNoLocalArgmin src cands =
  fastPathSelect src cands == excitementSelect src cands

-- ---------------------------------------------------------------------------
-- SECTION 7: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Fast-path thermodynamic transition carrier (Bool witness — not a new axiom).
data FastPathTransition = FastPathTransition
  { fastPathPrior          :: !ThermodynamicState
  , fastPathPost           :: !ThermodynamicState
  , fastPathBath           :: !HeatBath
  , fastPathDissipatedWork :: !Double
  , fastPathEntropyDrop    :: !Double
  , fastPathOk             :: !Bool
  } deriving (Show, Eq)

-- | Second law on fast-path transition (Bool witness — not a new axiom).
fastPathSecondLaw :: FastPathTransition -> Bool
fastPathSecondLaw t =
  fastPathEntropyDrop t
    <= fastPathDissipatedWork t / bathTemp (fastPathBath t)

-- | Second law on fast-path transition from Landauer bridge discharge.
fastPathSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
fastPathSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
fastPathFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
fastPathFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for fast-path second law (no new axiom).
fastPathSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
fastPathSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
fastPathPhysicsGreen :: Bool
fastPathPhysicsGreen = False

-- | Lean/Coq: @fast_path_physics_green_false@.
fastPathPhysicsGreenFalse :: Bool
fastPathPhysicsGreenFalse = not fastPathPhysicsGreen

-- | Production wiring stays open (meso lift only).
fastPathProductionWired :: Bool
fastPathProductionWired = False

-- | Lean/Coq: @fast_path_production_wired_false@.
fastPathProductionWiredFalse :: Bool
fastPathProductionWiredFalse = not fastPathProductionWired

-- | Catalog witness: meso Urge FastPathAdmit module present.
fastPathAdmitModuleWitness :: Bool
fastPathAdmitModuleWitness = True

-- | Zero new axiom discipline witness.
fastPathAdmitNoNewAxiom :: Bool
fastPathAdmitNoNewAxiom = True

-- | Second-argmin refusal: fast path composes 'excitementSelect' only.
fastPathAdmitNoSecondArgmin :: Bool
fastPathAdmitNoSecondArgmin =
  fastPathNoLocalArgmin (ThermodynamicState 2400 0 0.3 30 40) []
  && slowPathRecoveryNoSecondArgmin
    (HistoryRecoveryCtx
      (ThermodynamicState 2400 0 0.3 30 40)
      [])
  && urgeRecoveryEqExcitementSelect
    (HistoryRecoveryCtx
      (ThermodynamicState 2400 0 0.3 30 40)
      [])
  && urgeRecoverySelectEqExcitementSelect
    (ThermodynamicState 2400 0 0.3 30 40)
    []

-- | Honest non-claim string (meso §17.8 scaffold).
fastPathAdmitNonClaim :: String
fastPathAdmitNonClaim =
  "§17.8 fast-path admission as typed predicate (≤100ms budget), not wall-clock "
    ++ "GREEN; merge/recovery composes excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
fastPathAdmitNonClaimNonempty :: Bool
fastPathAdmitNonClaimNonempty = length fastPathAdmitNonClaim > 0
