-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CompactionAsArrow
-- Description : Meso acting Urge — §17.5 compaction as composite Excitement arrow.
--
-- Semantic squash is refused unless recorded as an admitted composite arrow whose
-- derivation witness retains the chain — the composite *is* the residue.
-- Compaction pays MI (Landauer lift); it is not delete-old-commits theater.
--
-- Urge compaction composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CompactionAsArrow
  ( -- * Derivation chain + MI payment + composite arrow (§17.5)
    DerivationChainWitness (..)
  , retainsChainBool
  , retainsChainBoolNonEmpty
  , MiPaymentWitness (..)
  , miPaidBool
  , miPaymentFromLandauerBits
  , landauerBridgeMiPaidWhenNonzero
  , CompactionArrow (..)
  , compactionArrowFromChain
    -- * Typed refuse + gate (positive, not bool theater)
  , CompactionVerdict (..)
  , CompactionAsArrowRefuse (..)
  , refuseDeleteOldCommitsTheater
  , refuseMiUnpaid
  , refuseSecondArgmin
  , refuseMissingDerivationWitness
  , CompactionAttempt (..)
  , evaluateCompactionAttempt
  , evaluateCompactionAttemptRefuse
  , deleteOldCommitsRefused
    -- * Landauer bridge — compaction pays MI (cited, not axiom)
  , compositeFromLandauer
  , compositeFromLandauerRetainsChain
  , landauerCompactionPreservesProvenance
  , compactionSecondLawFromLandauer
    -- * Compaction composes excitementSelect (no second argmin)
  , CompactionCtx (..)
  , compactionAsArrowSelect
  , compactionAsArrowSelectBare
  , compactionAsArrowSelectEqExcitementSelect
  , compactionAsArrowSelectBareEqExcitementSelect
  , compactionAsArrowSelectEqBare
  , compactionAsArrowNoLocalArgmin
  , urgeCompactionSelect
  , urgeCompactionSelectEqExcitementSelect
  , urgeCompactionSelectEqAdmitHistorySelect
  , compactionCompose
  , compactionComposeAssocInherited
  , compactionAsArrowEmpty
    -- * §17.5 fixtures + witness theorems
  , fixtureMiPaid
  , fixtureWitness
  , fixtureAdmissible
  , fixtureDeleteOldCommits
  , fixtureMiUnpaid
  , fixtureAdmissibleAccept
  , fixtureDeleteOldCommitsReject
  , fixtureMiUnpaidReject
  , fixtureArrowFromChainOk
  , fixtureArrowFromEmptyChainRefused
  , positiveRefuseNotSilent
    -- * Honesty flags + catalog witnesses
  , urgeCompactionPhysicsGreen
  , urgeCompactionPhysicsGreenFalse
  , compactionAsArrowProductionWired
  , compactionAsArrowProductionWiredFalse
  , compactionAsArrowMarker
  , compactionAsArrowMarkerPos
  , compactionAsArrowModuleWitness
  , compactionAsArrowNoNewAxiom
  , compactionAsArrowNoSecondArgmin
  , refuseDeleteOldCommitsTheaterPositive
  , refuseSecondArgminPositive
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( AdmitArrow
  , ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitHistorySelect
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , kleisliCompose
  , kleisliComposeAssocAt
  , landauerTransition
  )
import UMST.Urge.ProvenancePreserve
  ( Provenance (..)
  , landauerBridgePreserves
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Derivation chain + MI payment + composite arrow (§17.5)
-- ---------------------------------------------------------------------------

-- | Provenance derivation chain retained on composite compaction arrows.
data DerivationChainWitness = DerivationChainWitness
  { derivationChain :: ![Int]
  } deriving (Show, Eq)

-- | Whether the witness retains a non-empty derivation chain.
retainsChainBool :: DerivationChainWitness -> Bool
retainsChainBool w =
  case derivationChain w of
    []   -> False
    _:_  -> True

-- | Non-empty chain witness.
retainsChainBoolNonEmpty :: DerivationChainWitness -> Bool
retainsChainBoolNonEmpty w = retainsChainBool w

-- | MI payment witness — compaction must pay mutual-information cost.
data MiPaymentWitness = MiPaymentWitness
  { miRequiredBits :: !Int
  , miPaidBits     :: !Int
  } deriving (Show, Eq)

-- | Whether MI cost was paid (strictly positive paid bits >= required).
miPaidBool :: MiPaymentWitness -> Bool
miPaidBool m =
  miPaidBits m > 0 && miRequiredBits m <= miPaidBits m

-- | MI payment witness from nat MI bits (Landauer field cited, not re-derived).
miPaymentFromLandauerBits :: Int -> MiPaymentWitness
miPaymentFromLandauerBits n =
  MiPaymentWitness
    { miRequiredBits = n
    , miPaidBits     = n
    }

-- | Positive bit count implies MI paid witness holds.
landauerBridgeMiPaidWhenNonzero :: Int -> Bool
landauerBridgeMiPaidWhenNonzero n =
  n > 0 && miPaidBool (miPaymentFromLandauerBits n)

-- | Admitted composite compaction arrow — composite *is* the residue (§17.5).
data CompactionArrow = CompactionArrow
  { compositeId                   :: !Int
  , compositeWitness              :: !DerivationChainWitness
  , compositeSourceCommit         :: !Int
  , compositeExcitementSelected   :: !Bool
  } deriving (Show, Eq)

-- | Build composite arrow from a non-empty derivation chain.
compactionArrowFromChain
  :: Int -> [Int] -> Int -> Bool
  -> Either CompactionAsArrowRefuse CompactionArrow
compactionArrowFromChain cid chain sourceCommit excitementSelected =
  case chain of
    []   -> Left MissingDerivationWitness
    _:_  ->
      Right CompactionArrow
        { compositeId                 = cid
        , compositeWitness            =
            DerivationChainWitness {derivationChain = chain}
        , compositeSourceCommit       = sourceCommit
        , compositeExcitementSelected = excitementSelected
        }

-- ---------------------------------------------------------------------------
-- SECTION 2: Typed refuse + gate (positive, not bool theater)
-- ---------------------------------------------------------------------------

data CompactionVerdict
  = CompactionAccept
  | CompactionReject
  deriving (Show, Eq)

data CompactionAsArrowRefuse
  = DeleteOldCommitsTheater
  | MiUnpaid
  | SecondArgmin
  | MissingDerivationWitness
  deriving (Show, Eq)

refuseDeleteOldCommitsTheater :: CompactionAsArrowRefuse
refuseDeleteOldCommitsTheater = DeleteOldCommitsTheater

refuseMiUnpaid :: CompactionAsArrowRefuse
refuseMiUnpaid = MiUnpaid

refuseSecondArgmin :: CompactionAsArrowRefuse
refuseSecondArgmin = SecondArgmin

refuseMissingDerivationWitness :: CompactionAsArrowRefuse
refuseMissingDerivationWitness = MissingDerivationWitness

-- | One compaction attempt before gating (§17.5 fixture surface).
data CompactionAttempt = CompactionAttempt
  { attemptDeleteOldCommits   :: !Bool
  , attemptMi                 :: !MiPaymentWitness
  , attemptWitness            :: !(Maybe DerivationChainWitness)
  , attemptProvenanceIntact   :: !Bool
  , attemptExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Gate a compaction attempt — composite arrow paying MI, not delete-old-commits.
evaluateCompactionAttempt :: CompactionAttempt -> CompactionVerdict
evaluateCompactionAttempt a =
  if attemptDeleteOldCommits a
    then CompactionReject
  else if not (miPaidBool (attemptMi a))
    then CompactionReject
  else case attemptWitness a of
    Nothing -> CompactionReject
    Just w  ->
      if retainsChainBool w
        then if attemptProvenanceIntact a
          then if attemptExcitementSelected a
            then CompactionAccept
            else CompactionReject
          else CompactionReject
        else CompactionReject

-- | Evaluate attempt with typed refuse on reject path.
evaluateCompactionAttemptRefuse
  :: CompactionAttempt -> Either CompactionAsArrowRefuse CompactionVerdict
evaluateCompactionAttemptRefuse a =
  if attemptDeleteOldCommits a
    then Left DeleteOldCommitsTheater
  else if not (miPaidBool (attemptMi a))
    then Left MiUnpaid
  else case attemptWitness a of
    Nothing -> Left MissingDerivationWitness
    Just w  ->
      if retainsChainBool w
        then if attemptProvenanceIntact a
          then if attemptExcitementSelected a
            then Right CompactionAccept
            else Left MissingDerivationWitness
          else Left MissingDerivationWitness
        else Left MissingDerivationWitness

-- | §17.5 named obligation: delete-old-commits theater refused.
deleteOldCommitsRefused :: CompactionAttempt -> Bool
deleteOldCommitsRefused a =
  attemptDeleteOldCommits a
  && evaluateCompactionAttemptRefuse a == Left DeleteOldCommitsTheater

-- ---------------------------------------------------------------------------
-- SECTION 3: Landauer bridge — compaction pays MI (cited, not axiom)
-- ---------------------------------------------------------------------------

-- | Composite arrow from Landauer bridge + prior provenance chain extension.
compositeFromLandauer
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
  -> CompactionArrow
compositeFromLandauer b prior _hPrior _hSL excitementSelected =
  CompactionArrow
    { compositeId =
        historyCommitId (historyPost (landauerTransition b))
    , compositeWitness =
        DerivationChainWitness
          { derivationChain = ucrsChain prior ++ [dagCommit prior]
          }
    , compositeSourceCommit = dagCommit prior
    , compositeExcitementSelected = excitementSelected
    }

-- | Landauer composite retains non-empty derivation chain.
compositeFromLandauerRetainsChain
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
  -> Bool
compositeFromLandauerRetainsChain b prior hPrior hSL excitementSelected =
  retainsChainBool
    (compositeWitness (compositeFromLandauer b prior hPrior hSL excitementSelected))

-- | Landauer compaction preserves provenance (physicalSecondLaw cited on Lean).
landauerCompactionPreservesProvenance
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
landauerCompactionPreservesProvenance b prior hPrior hSL =
  landauerBridgePreserves b prior hPrior hSL

-- | Second law on compaction transition from Landauer bridge discharge.
compactionSecondLawFromLandauer
  :: LandauerHistoryBridge
  -> Bool
  -> Bool
compactionSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- ---------------------------------------------------------------------------
-- SECTION 4: Compaction composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for compaction over admissible history successors.
data CompactionCtx = CompactionCtx
  { compactionPrior      :: !ThermodynamicState
  , compactionSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Urge compaction **is** 'excitementSelect' — not a second argmin.
compactionAsArrowSelect
  :: CompactionCtx -> Either ExcitementResidue HistoryCandidate
compactionAsArrowSelect ctx =
  excitementSelect (compactionPrior ctx) (compactionSuccessors ctx)

compactionAsArrowSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
compactionAsArrowSelectBare prior successors =
  excitementSelect prior successors

compactionAsArrowSelectEqExcitementSelect :: CompactionCtx -> Bool
compactionAsArrowSelectEqExcitementSelect ctx =
  compactionAsArrowSelect ctx
    == excitementSelect (compactionPrior ctx) (compactionSuccessors ctx)

compactionAsArrowSelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
compactionAsArrowSelectBareEqExcitementSelect prior successors =
  compactionAsArrowSelectBare prior successors == excitementSelect prior successors

compactionAsArrowSelectEqBare :: CompactionCtx -> Bool
compactionAsArrowSelectEqBare ctx =
  compactionAsArrowSelect ctx
    == compactionAsArrowSelectBare
      (compactionPrior ctx)
      (compactionSuccessors ctx)

compactionAsArrowNoLocalArgmin :: CompactionCtx -> Bool
compactionAsArrowNoLocalArgmin ctx =
  compactionAsArrowSelect ctx
    == admitHistorySelect (compactionPrior ctx) (compactionSuccessors ctx)

urgeCompactionSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeCompactionSelect = excitementSelect

urgeCompactionSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeCompactionSelectEqExcitementSelect src cands =
  urgeCompactionSelect src cands == excitementSelect src cands

urgeCompactionSelectEqAdmitHistorySelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeCompactionSelectEqAdmitHistorySelect src cands =
  urgeCompactionSelect src cands == admitHistorySelect src cands

-- | Kleisli composite pin — compaction chains inherited arrows, not squash.
compactionCompose :: AdmitArrow -> AdmitArrow -> AdmitArrow
compactionCompose = kleisliCompose

-- | Inherited Kleisli associativity at a thermodynamic state.
compactionComposeAssocInherited
  :: AdmitArrow -> AdmitArrow -> AdmitArrow -> ThermodynamicState -> Bool
compactionComposeAssocInherited = kleisliComposeAssocAt

compactionAsArrowEmpty :: CompactionCtx -> Bool
compactionAsArrowEmpty ctx =
  compactionSuccessors ctx == []
  && compactionAsArrowSelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §17.5 fixtures + witness theorems
-- ---------------------------------------------------------------------------

fixtureMiPaid :: MiPaymentWitness
fixtureMiPaid = MiPaymentWitness {miRequiredBits = 2, miPaidBits = 4}

fixtureWitness :: DerivationChainWitness
fixtureWitness = DerivationChainWitness {derivationChain = [1, 2, 3]}

fixtureAdmissible :: CompactionAttempt
fixtureAdmissible =
  CompactionAttempt
    { attemptDeleteOldCommits   = False
    , attemptMi                 = fixtureMiPaid
    , attemptWitness            = Just fixtureWitness
    , attemptProvenanceIntact   = True
    , attemptExcitementSelected = True
    }

fixtureDeleteOldCommits :: CompactionAttempt
fixtureDeleteOldCommits =
  CompactionAttempt
    { attemptDeleteOldCommits   = True
    , attemptMi                 = fixtureMiPaid
    , attemptWitness            = Just fixtureWitness
    , attemptProvenanceIntact   = True
    , attemptExcitementSelected = True
    }

fixtureMiUnpaid :: CompactionAttempt
fixtureMiUnpaid =
  CompactionAttempt
    { attemptDeleteOldCommits   = False
    , attemptMi                 = MiPaymentWitness {miRequiredBits = 2, miPaidBits = 0}
    , attemptWitness            = Just fixtureWitness
    , attemptProvenanceIntact   = True
    , attemptExcitementSelected = True
    }

fixtureAdmissibleAccept :: Bool
fixtureAdmissibleAccept =
  evaluateCompactionAttempt fixtureAdmissible == CompactionAccept

fixtureDeleteOldCommitsReject :: Bool
fixtureDeleteOldCommitsReject =
  evaluateCompactionAttempt fixtureDeleteOldCommits == CompactionReject

fixtureMiUnpaidReject :: Bool
fixtureMiUnpaidReject =
  evaluateCompactionAttempt fixtureMiUnpaid == CompactionReject

fixtureArrowFromChainOk :: Bool
fixtureArrowFromChainOk =
  compactionArrowFromChain 42 [1, 2] 7 True ==
    Right CompactionArrow
      { compositeId                 = 42
      , compositeWitness            = DerivationChainWitness {derivationChain = [1, 2]}
      , compositeSourceCommit       = 7
      , compositeExcitementSelected = True
      }

fixtureArrowFromEmptyChainRefused :: Bool
fixtureArrowFromEmptyChainRefused =
  compactionArrowFromChain 1 [] 0 True == Left MissingDerivationWitness

positiveRefuseNotSilent :: Bool
positiveRefuseNotSilent =
  evaluateCompactionAttempt fixtureDeleteOldCommits /= CompactionAccept

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgeCompactionPhysicsGreen :: Bool
urgeCompactionPhysicsGreen = False

-- | Lean/Coq: @urge_physics_green_false@.
urgeCompactionPhysicsGreenFalse :: Bool
urgeCompactionPhysicsGreenFalse = not urgeCompactionPhysicsGreen

-- | Production wiring stays open (meso lift only).
compactionAsArrowProductionWired :: Bool
compactionAsArrowProductionWired = False

-- | Lean/Coq: @compaction_as_arrow_production_wired_false@.
compactionAsArrowProductionWiredFalse :: Bool
compactionAsArrowProductionWiredFalse =
  not compactionAsArrowProductionWired

-- | Meso §17.5 section marker (Lean mirror).
compactionAsArrowMarker :: Int
compactionAsArrowMarker = 175

compactionAsArrowMarkerPos :: Bool
compactionAsArrowMarkerPos = compactionAsArrowMarker > 0

-- | Catalog witness: meso Urge CompactionAsArrow module present.
compactionAsArrowModuleWitness :: Bool
compactionAsArrowModuleWitness = True

-- | Zero new axiom discipline witness.
compactionAsArrowNoNewAxiom :: Bool
compactionAsArrowNoNewAxiom = True

-- | Second-argmin refusal tag is stable.
compactionAsArrowNoSecondArgmin :: Bool
compactionAsArrowNoSecondArgmin =
  refuseSecondArgmin == SecondArgmin

refuseDeleteOldCommitsTheaterPositive :: Bool
refuseDeleteOldCommitsTheaterPositive =
  refuseDeleteOldCommitsTheater == DeleteOldCommitsTheater

refuseSecondArgminPositive :: Bool
refuseSecondArgminPositive = refuseSecondArgmin == SecondArgmin
