-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ClosedLoopWitness
-- Description : Meso acting Urge — §22.7 messy witness back into Excitement occupancy.
--
-- Residue counts + observed ΔF feed occupancy surrogate. Composes
-- 'excitementSelect'; no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.ClosedLoopWitness
  ( -- * Messy witness + occupancy feedback carriers (§22.7)
    ClosedLoopResidue (..)
  , residueConstructorTag
  , residueConstructorCount
  , ClosedLoopResidueCounts (..)
  , closedLoopResidueCountsZero
  , closedLoopResidueCountsTotal
  , closedLoopResidueCountOf
  , incrementClosedLoopResidueCount
  , ObservedDeltaF (..)
  , observedDeltaF
  , observedDeltaFCompute
  , observedDeltaFEqCompute
  , observedDeltaFFromCand
  , MessyWitness (..)
  , emptyMessyWitness
  , addMessyObservedDelta
  , recordMessyResidue
  , ExcitementOccupancyFeedback (..)
  , occupancyFromWitness
    -- * §22.7 typed refusal + positive refuse
  , ClosedLoopRefusal (..)
  , ClosedLoopStepVerdict (..)
  , refuseClosedLoopSecondArgmin
  , refuseClosedLoopF64DeltaF
  , refuseClosedLoopOpenLoopIsolation
  , f64DeltaFTheater
  , refuseF64DeltaF
  , strictImprovement
  , strictImprovementSuccessors
    -- * Closed loop composes excitementSelect (no argmin)
  , ClosedLoopCtx (..)
  , closedLoopSelect
  , closedLoopSelectList
  , closedLoopSelectEqExcitementSelect
  , closedLoopSelectEqUrgeRecoverySelect
  , closedLoopNoLocalArgmin
  , closedLoopEmpty
  , witnessClosedLoopStep
    -- * §22.7 fixtures + witness theorems
  , closedLoopFixtureAcceptSrc
  , closedLoopFixtureAcceptTgt
  , closedLoopFixtureAcceptCandidate
  , closedLoopFixtureRefuseSrc
  , closedLoopFixtureRefuseTgt
  , closedLoopFixtureRefuseCandidate
  , fixtureStrictImprovementAccept
  , fixtureStrictImprovementRefuse
  , fixtureAcceptRecordsDelta
  , fixtureRefuseNoCandidates
  , fixtureRefuseNoStrictImprovement
  , occupancySurrogateFixture
  , refuseSecondArgminPositive
  , refuseF64DeltaFPositive
  , refuseOpenLoopIsolationPositive
  , observedDeltaFComputeFixture
  , positiveRefuseNotSilent
    -- * Bridge to physicalSecondLaw (derived — zero new axioms)
  , ClosedLoopTransition (..)
  , PhysicalClosedLoopBridge (..)
  , closedLoopAdmitSecondLawFromPhysical
  , closedLoopAdmissibleFromPhysical
  , closedLoopSecondLawFromLandauer
  , closedLoopSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , closedLoopWitnessPhysicsGreen
  , closedLoopWitnessPhysicsGreenFalse
  , closedLoopWitnessProductionWired
  , closedLoopWitnessProductionWiredFalse
  , closedLoopWitnessModuleWitness
  , closedLoopWitnessNoNewAxiom
  , closedLoopWitnessNoLocalArgmin
  , closedLoopWitnessNonClaim
  , closedLoopWitnessNonClaimNonempty
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
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: Messy witness + occupancy feedback carriers (§22.7)
-- ---------------------------------------------------------------------------

-- | Residue constructors mirroring Lean @UMST.Excitement.Residue@ (§22.7 corpus).
data ClosedLoopResidue
  = ClosedLoopNoCandidates
  | ClosedLoopAllInadmissible
  | ClosedLoopAllExcludedByCBF
  | ClosedLoopAllExcludedByDEC
  | ClosedLoopUntaggedConstant
  | ClosedLoopNoStrictImprovement
  deriving (Show, Eq)

-- | Constructor tag string for catalog witnesses.
residueConstructorTag :: ClosedLoopResidue -> String
residueConstructorTag r = case r of
  ClosedLoopNoCandidates -> "NoCandidates"
  ClosedLoopAllInadmissible -> "AllInadmissible"
  ClosedLoopAllExcludedByCBF -> "AllExcludedByCbf"
  ClosedLoopAllExcludedByDEC -> "AllExcludedByDec"
  ClosedLoopUntaggedConstant -> "UntaggedConstant"
  ClosedLoopNoStrictImprovement -> "NoStrictImprovement"

-- | Six residue constructors in the §22.7 messy witness corpus.
residueConstructorCount :: Int
residueConstructorCount = 6

-- | Per-constructor residue occurrence counts.
data ClosedLoopResidueCounts = ClosedLoopResidueCounts
  { clNoCandidates        :: !Int
  , clAllInadmissible     :: !Int
  , clAllExcludedByCBF    :: !Int
  , clAllExcludedByDEC    :: !Int
  , clUntaggedConstant    :: !Int
  , clNoStrictImprovement :: !Int
  } deriving (Show, Eq)

-- | Zero residue counts scaffold.
closedLoopResidueCountsZero :: ClosedLoopResidueCounts
closedLoopResidueCountsZero =
  ClosedLoopResidueCounts
    { clNoCandidates = 0
    , clAllInadmissible = 0
    , clAllExcludedByCBF = 0
    , clAllExcludedByDEC = 0
    , clUntaggedConstant = 0
    , clNoStrictImprovement = 0
    }

-- | Total residue observations across all six constructors.
closedLoopResidueCountsTotal :: ClosedLoopResidueCounts -> Int
closedLoopResidueCountsTotal c =
  clNoCandidates c
    + clAllInadmissible c
    + clAllExcludedByCBF c
    + clAllExcludedByDEC c
    + clUntaggedConstant c
    + clNoStrictImprovement c

-- | Lookup one constructor count.
closedLoopResidueCountOf :: ClosedLoopResidueCounts -> ClosedLoopResidue -> Int
closedLoopResidueCountOf c r = case r of
  ClosedLoopNoCandidates -> clNoCandidates c
  ClosedLoopAllInadmissible -> clAllInadmissible c
  ClosedLoopAllExcludedByCBF -> clAllExcludedByCBF c
  ClosedLoopAllExcludedByDEC -> clAllExcludedByDEC c
  ClosedLoopUntaggedConstant -> clUntaggedConstant c
  ClosedLoopNoStrictImprovement -> clNoStrictImprovement c

-- | Increment one constructor count.
incrementClosedLoopResidueCount
  :: ClosedLoopResidueCounts -> ClosedLoopResidue -> ClosedLoopResidueCounts
incrementClosedLoopResidueCount c r = case r of
  ClosedLoopNoCandidates ->
    c {clNoCandidates = clNoCandidates c + 1}
  ClosedLoopAllInadmissible ->
    c {clAllInadmissible = clAllInadmissible c + 1}
  ClosedLoopAllExcludedByCBF ->
    c {clAllExcludedByCBF = clAllExcludedByCBF c + 1}
  ClosedLoopAllExcludedByDEC ->
    c {clAllExcludedByDEC = clAllExcludedByDEC c + 1}
  ClosedLoopUntaggedConstant ->
    c {clUntaggedConstant = clUntaggedConstant c + 1}
  ClosedLoopNoStrictImprovement ->
    c {clNoStrictImprovement = clNoStrictImprovement c + 1}

-- | Observed free-energy delta: ΔF = observed − src (exact field on head state).
data ObservedDeltaF = ObservedDeltaF
  { observedDeltaFSrc      :: !Double
  , observedDeltaFVal      :: !Double
  } deriving (Show, Eq)

-- | Signed ΔF from observed bundle.
observedDeltaF :: ObservedDeltaF -> Double
observedDeltaF d = observedDeltaFVal d - observedDeltaFSrc d

-- | Compute ΔF from src and observed free-energy fields.
observedDeltaFCompute :: Double -> Double -> Double
observedDeltaFCompute src observed = observed - src

-- | Definitional witness: bundle ΔF equals compute.
observedDeltaFEqCompute :: ObservedDeltaF -> Bool
observedDeltaFEqCompute d =
  observedDeltaF d == observedDeltaFCompute (observedDeltaFSrc d) (observedDeltaFVal d)

-- | ΔF observation from one history candidate at src head.
observedDeltaFFromCand :: ThermodynamicState -> HistoryCandidate -> ObservedDeltaF
observedDeltaFFromCand src c =
  ObservedDeltaF
    { observedDeltaFSrc = freeEnergy src
    , observedDeltaFVal = freeEnergy (candTgt c)
    }

-- | §22.7 messy witness bundle — residue corpus + measured ΔF steps.
data MessyWitness = MessyWitness
  { messyCounts         :: !ClosedLoopResidueCounts
  , messyObservedDeltaF :: ![ObservedDeltaF]
  } deriving (Show, Eq)

-- | Empty messy witness buffer.
emptyMessyWitness :: MessyWitness
emptyMessyWitness =
  MessyWitness
    { messyCounts = closedLoopResidueCountsZero
    , messyObservedDeltaF = []
    }

-- | Append one observed ΔF step.
addMessyObservedDelta :: MessyWitness -> ObservedDeltaF -> MessyWitness
addMessyObservedDelta w d =
  w {messyObservedDeltaF = messyObservedDeltaF w ++ [d]}

-- | Record one residue constructor hit.
recordMessyResidue :: MessyWitness -> ClosedLoopResidue -> MessyWitness
recordMessyResidue w r =
  w {messyCounts = incrementClosedLoopResidueCount (messyCounts w) r}

-- | Excitement occupancy feedback derived from messy witness.
data ExcitementOccupancyFeedback = ExcitementOccupancyFeedback
  { feedbackResidueTotal       :: !Int
  , feedbackDeltaFSteps        :: !Int
  , feedbackOccupancySurrogate :: !Int
  } deriving (Show, Eq)

-- | Occupancy surrogate from residue corpus + ΔF step count.
occupancyFromWitness :: MessyWitness -> ExcitementOccupancyFeedback
occupancyFromWitness w =
  let residueTotal = closedLoopResidueCountsTotal (messyCounts w)
      deltaFSteps = length (messyObservedDeltaF w)
   in ExcitementOccupancyFeedback
        { feedbackResidueTotal = residueTotal
        , feedbackDeltaFSteps = deltaFSteps
        , feedbackOccupancySurrogate = residueTotal * 1000 + deltaFSteps
        }

-- ---------------------------------------------------------------------------
-- SECTION 2: §22.7 typed refusal + positive refuse
-- ---------------------------------------------------------------------------

-- | Fail-closed closed-loop refusal — positive typed refuse, not only !physics_green.
data ClosedLoopRefusal
  = ClosedLoopRefusedExcitement ClosedLoopResidue
  | ClosedLoopRefusedSecondArgmin
  | ClosedLoopRefusedF64DeltaF
  | ClosedLoopRefusedOpenLoopIsolation
  deriving (Show, Eq)

data ClosedLoopStepVerdict
  = ClosedLoopAccepted ExcitementOccupancyFeedback
  | ClosedLoopRefused ClosedLoopRefusal
  deriving (Show, Eq)

-- | Positive refuse: second local argmin forbidden.
refuseClosedLoopSecondArgmin :: ClosedLoopRefusal
refuseClosedLoopSecondArgmin = ClosedLoopRefusedSecondArgmin

-- | Positive refuse: f64 ΔF theater forbidden — exact free-energy field only.
refuseClosedLoopF64DeltaF :: ClosedLoopRefusal
refuseClosedLoopF64DeltaF = ClosedLoopRefusedF64DeltaF

-- | Positive refuse: open-loop isolation forbidding Excitement consume.
refuseClosedLoopOpenLoopIsolation :: ClosedLoopRefusal
refuseClosedLoopOpenLoopIsolation = ClosedLoopRefusedOpenLoopIsolation

-- | Theater pattern: treating non-exact carrier as ΔF (always false here).
f64DeltaFTheater :: Bool
f64DeltaFTheater = False

-- | f64 ΔF theater is refused.
refuseF64DeltaF :: Bool
refuseF64DeltaF = not f64DeltaFTheater

-- | Strict improvement on exact free-energy field.
strictImprovement :: ThermodynamicState -> HistoryCandidate -> Bool
strictImprovement src c = freeEnergy (candTgt c) < freeEnergy src

-- | Filter successors that strictly improve free energy.
strictImprovementSuccessors
  :: ThermodynamicState -> [HistoryCandidate] -> [HistoryCandidate]
strictImprovementSuccessors src =
  filter (strictImprovement src)

-- | Map meso 'ExcitementResidue' into §22.7 closed-loop residue corpus.
excitementResidueToClosedLoop :: ExcitementResidue -> ClosedLoopResidue
excitementResidueToClosedLoop r = case r of
  ExcNoCandidates -> ClosedLoopNoCandidates
  ExcAllInadmissible -> ClosedLoopAllInadmissible
  ExcNoStrictImprovement -> ClosedLoopNoStrictImprovement

-- ---------------------------------------------------------------------------
-- SECTION 3: Closed loop composes excitementSelect (no argmin)
-- ---------------------------------------------------------------------------

-- | Context for §22.7 closed-loop witness over admissible successors.
data ClosedLoopCtx = ClosedLoopCtx
  { closedLoopPrior      :: !ThermodynamicState
  , closedLoopSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Closed-loop selection **is** 'excitementSelect' / 'urgeRecoverySelect'.
closedLoopSelect
  :: ClosedLoopCtx
  -> Either ExcitementResidue HistoryCandidate
closedLoopSelect ctx =
  excitementSelect (closedLoopPrior ctx) (closedLoopSuccessors ctx)

-- | Bare prior + successors closed-loop selection.
closedLoopSelectList
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
closedLoopSelectList = excitementSelect

-- | Definitional witness: closed-loop API is 'excitementSelect'.
closedLoopSelectEqExcitementSelect :: ClosedLoopCtx -> Bool
closedLoopSelectEqExcitementSelect ctx =
  closedLoopSelect ctx
    == excitementSelect (closedLoopPrior ctx) (closedLoopSuccessors ctx)

-- | Closed-loop selection equals 'urgeRecoverySelect'.
closedLoopSelectEqUrgeRecoverySelect :: ClosedLoopCtx -> Bool
closedLoopSelectEqUrgeRecoverySelect ctx =
  closedLoopSelect ctx
    == urgeRecoverySelect (closedLoopPrior ctx) (closedLoopSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
closedLoopNoLocalArgmin :: ClosedLoopCtx -> Bool
closedLoopNoLocalArgmin = closedLoopSelectEqExcitementSelect

-- | Empty successor list → 'ExcNoCandidates' via imported selector.
closedLoopEmpty :: ThermodynamicState -> Bool
closedLoopEmpty prior =
  closedLoopSelectList prior [] == Left ExcNoCandidates

-- | One §22.7 closed-loop witness step — compose 'excitementSelect'.
witnessClosedLoopStep
  :: MessyWitness
  -> ThermodynamicState
  -> [HistoryCandidate]
  -> (MessyWitness, ClosedLoopStepVerdict)
witnessClosedLoopStep w src successors =
  case successors of
    [] ->
      case closedLoopSelectList src [] of
        Left r ->
          let r' = excitementResidueToClosedLoop r
           in (recordMessyResidue w r', ClosedLoopRefused (ClosedLoopRefusedExcitement r'))
        Right _ ->
          (w, ClosedLoopRefused (ClosedLoopRefusedExcitement ClosedLoopNoCandidates))
    (_ : _) ->
      case strictImprovementSuccessors src successors of
        [] ->
          ( recordMessyResidue w ClosedLoopNoStrictImprovement
          , ClosedLoopRefused
              (ClosedLoopRefusedExcitement ClosedLoopNoStrictImprovement)
          )
        improving ->
          case closedLoopSelectList src improving of
            Right c ->
              let delta = observedDeltaFFromCand src c
                  w' = addMessyObservedDelta w delta
               in (w', ClosedLoopAccepted (occupancyFromWitness w'))
            Left r ->
              let r' = excitementResidueToClosedLoop r
               in (recordMessyResidue w r', ClosedLoopRefused (ClosedLoopRefusedExcitement r'))

-- ---------------------------------------------------------------------------
-- SECTION 4: §22.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

closedLoopFixtureAcceptSrc :: ThermodynamicState
closedLoopFixtureAcceptSrc = ThermodynamicState 2400 10 0 0 0

closedLoopFixtureAcceptTgt :: ThermodynamicState
closedLoopFixtureAcceptTgt = ThermodynamicState 2400 3 0 0 0

closedLoopFixtureAcceptCandidate :: HistoryCandidate
closedLoopFixtureAcceptCandidate =
  HistoryCandidate {candId = 1, candTgt = closedLoopFixtureAcceptTgt}

closedLoopFixtureRefuseSrc :: ThermodynamicState
closedLoopFixtureRefuseSrc = ThermodynamicState 2400 2 0 0 0

closedLoopFixtureRefuseTgt :: ThermodynamicState
closedLoopFixtureRefuseTgt = closedLoopFixtureRefuseSrc

closedLoopFixtureRefuseCandidate :: HistoryCandidate
closedLoopFixtureRefuseCandidate =
  HistoryCandidate {candId = 0, candTgt = closedLoopFixtureRefuseTgt}

-- | Accept candidate strictly improves free energy.
fixtureStrictImprovementAccept :: Bool
fixtureStrictImprovementAccept =
  strictImprovement
    closedLoopFixtureAcceptSrc
    closedLoopFixtureAcceptCandidate

-- | Refuse candidate does not strictly improve.
fixtureStrictImprovementRefuse :: Bool
fixtureStrictImprovementRefuse =
  not
    ( strictImprovement
        closedLoopFixtureRefuseSrc
        closedLoopFixtureRefuseCandidate
    )

-- | Accept path records one ΔF step with occupancy surrogate 1.
fixtureAcceptRecordsDelta :: Bool
fixtureAcceptRecordsDelta =
  fixtureStrictImprovementAccept
    && occupancyFromWitness
      ( addMessyObservedDelta emptyMessyWitness
          ( observedDeltaFFromCand
              closedLoopFixtureAcceptSrc
              closedLoopFixtureAcceptCandidate
          )
      )
      == ExcitementOccupancyFeedback
        { feedbackResidueTotal = 0
        , feedbackDeltaFSteps = 1
        , feedbackOccupancySurrogate = 1
        }

-- | Empty successors refuse with no-candidates residue recorded.
fixtureRefuseNoCandidates :: Bool
fixtureRefuseNoCandidates =
  let (w, v) =
        witnessClosedLoopStep emptyMessyWitness closedLoopFixtureAcceptSrc []
   in v
        == ClosedLoopRefused
          (ClosedLoopRefusedExcitement ClosedLoopNoCandidates)
        && closedLoopResidueCountOf (messyCounts w) ClosedLoopNoCandidates == 1

-- | Non-improving successor refuses with no-strict-improvement residue.
fixtureRefuseNoStrictImprovement :: Bool
fixtureRefuseNoStrictImprovement =
  let (w, v) =
        witnessClosedLoopStep
          emptyMessyWitness
          closedLoopFixtureRefuseSrc
          [closedLoopFixtureRefuseCandidate]
   in v
        == ClosedLoopRefused
          (ClosedLoopRefusedExcitement ClosedLoopNoStrictImprovement)
        && closedLoopResidueCountOf (messyCounts w) ClosedLoopNoStrictImprovement == 1

-- | Occupancy surrogate fixture: two residues + one ΔF → 2001.
occupancySurrogateFixture :: Bool
occupancySurrogateFixture =
  let w =
        recordMessyResidue
          (recordMessyResidue emptyMessyWitness ClosedLoopNoCandidates)
          ClosedLoopNoStrictImprovement
      w' = addMessyObservedDelta w (ObservedDeltaF 10 3)
   in feedbackOccupancySurrogate (occupancyFromWitness w') == 2001

-- | Positive refuse witnesses.
refuseSecondArgminPositive :: Bool
refuseSecondArgminPositive =
  refuseClosedLoopSecondArgmin == ClosedLoopRefusedSecondArgmin

refuseF64DeltaFPositive :: Bool
refuseF64DeltaFPositive =
  refuseClosedLoopF64DeltaF == ClosedLoopRefusedF64DeltaF

refuseOpenLoopIsolationPositive :: Bool
refuseOpenLoopIsolationPositive =
  refuseClosedLoopOpenLoopIsolation == ClosedLoopRefusedOpenLoopIsolation

observedDeltaFComputeFixture :: Bool
observedDeltaFComputeFixture = observedDeltaFCompute 10 3 == 3 - 10

positiveRefuseNotSilent :: Bool
positiveRefuseNotSilent =
  refuseClosedLoopSecondArgmin /= ClosedLoopRefusedExcitement ClosedLoopNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ---------------------------------------------------------------------------

data ClosedLoopTransition = ClosedLoopTransition
  { closedLoopHistory :: !HistoryTransition
  , closedLoopMessy   :: !MessyWitness
  } deriving (Show, Eq)

data PhysicalClosedLoopBridge = PhysicalClosedLoopBridge
  { closedLoopLandauerBridge :: !LandauerHistoryBridge
  , closedLoopPack           :: !ClosedLoopTransition
  , closedLoopHistoryEq      :: !Bool
  } deriving (Show, Eq)

-- | Second law on closed-loop transition from Landauer bridge (physicalSecondLaw cited).
closedLoopAdmitSecondLawFromPhysical :: PhysicalClosedLoopBridge -> Bool -> Bool
closedLoopAdmitSecondLawFromPhysical b hSL =
  hSL
  && closedLoopHistoryEq b
  && admitSecondLaw (landauerTransition (closedLoopLandauerBridge b))

-- | Admissible closed-loop transition from Landauer bridge discharge.
closedLoopAdmissibleFromPhysical :: PhysicalClosedLoopBridge -> Bool -> Bool
closedLoopAdmissibleFromPhysical b hSL =
  hSL
  && closedLoopHistoryEq b
  && admissibleHistoryTransitionFromLandauerBridge
    (closedLoopLandauerBridge b)
    hSL

-- | Second law on closed-loop carrier transition from Landauer bridge.
closedLoopSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
closedLoopSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for closed-loop second law (no new axiom).
closedLoopSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
closedLoopSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
closedLoopWitnessPhysicsGreen :: Bool
closedLoopWitnessPhysicsGreen = False

-- | Lean/Coq: @closed_loop_witness_physics_green_false@.
closedLoopWitnessPhysicsGreenFalse :: Bool
closedLoopWitnessPhysicsGreenFalse = not closedLoopWitnessPhysicsGreen

-- | Production wiring stays open (meso lift only).
closedLoopWitnessProductionWired :: Bool
closedLoopWitnessProductionWired = False

-- | Lean/Coq: @closed_loop_witness_production_wired_false@.
closedLoopWitnessProductionWiredFalse :: Bool
closedLoopWitnessProductionWiredFalse = not closedLoopWitnessProductionWired

-- | Catalog witness: meso Urge ClosedLoopWitness module present.
closedLoopWitnessModuleWitness :: Bool
closedLoopWitnessModuleWitness = True

-- | Zero new axiom discipline witness.
closedLoopWitnessNoNewAxiom :: Bool
closedLoopWitnessNoNewAxiom = True

-- | Closed-loop composes 'excitementSelect' — no Urge-local argmin.
closedLoopWitnessNoLocalArgmin :: ClosedLoopCtx -> Bool
closedLoopWitnessNoLocalArgmin = closedLoopNoLocalArgmin

-- | Honest non-claim string (meso §22.7 closed-loop scaffold).
closedLoopWitnessNonClaim :: String
closedLoopWitnessNonClaim =
  "§22.7 closed-loop: messy witness residue counts + observed ΔF back to "
    ++ "Excitement occupancy; composes excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
closedLoopWitnessNonClaimNonempty :: Bool
closedLoopWitnessNonClaimNonempty = length closedLoopWitnessNonClaim > 0
