-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.HistoryFunctor
-- Description : Meso acting Urge — §5.1 Admissible HistoryFunctor.
--
-- identity: @history_functor@
-- Git-style content-addressed bytes → typed gate-checked history with
-- second-law preservation (Bool witness — not a new axiom).
--
-- Mirrors umst-meta @evaluate_transition@ provenance gate; thermodynamic
-- head moves reuse @UMST.Urge.AdmitKleisli@ carriers.
-- History recovery composes @excitementSelect@ — no second argmin.
--
-- Anchored in @UMST.Urge.AdmitKleisli.admitSecondLaw@ via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.HistoryFunctor
  ( -- * Git-style raw commit bytes → typed history (§5.1)
    RawCommitBytes
  , RawGitCommit (..)
  , RepoStateSlice (..)
  , RepoTransitionStep (..)
  , TransitionVerdict (..)
  , TypedHistory (..)
  , AdmissibleHistoryFunctor (..)
  , historyFunctorIdentity
    -- * Second-law preservation on typed history transitions
  , gateAdmissibleHead
  , preservationProp
  , preservationPropOfAdmissible
    -- * Provenance gate on repository transitions (meta mirror)
  , provenancedOkStep
  , evaluateTransition
  , evaluateTransitionRejectsInventsGreen
  , evaluateTransitionRejectsPhysicsGreenWithoutWitness
  , evaluateTransitionRejectsDropsProvenance
  , provenancedOkStepEvaluatesAccept
    -- * Catalog decode fixture (git bytes → typed history)
  , fixtureState
  , fixtureCommitHash
  , fixturePayload
  , fixtureRawCommit
  , fixtureTypedHistory
  , catalogDecode
  , catalogDecodeFixture
  , catalogDecodePreserveCommitId
  , catalogHistoryFunctor
  , catalogDecodeFixtureFunctor
    -- * Landauer bridge discharge (zero new axioms)
  , preservationPropFromLandauer
  , admissiblePreservesSecondLaw
  , historyFunctorNoNewAxiom
    -- * Excitement composition (no second argmin)
  , historyFunctorSelect
  , historyFunctorSelectEqExcitementSelect
  , historyFunctorSelectEqUrgeRecovery
  , historyFunctorNoLocalArgmin
    -- * Honesty flags + catalog witnesses
  , urgeHistoryFunctorPhysicsGreen
  , urgeHistoryFunctorPhysicsGreenFalse
  , historyFunctorProductionWired
  , historyFunctorProductionWiredFalse
  , historyFunctorModuleWitness
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransition
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.ExcitementImport
  ( HistoryRecoveryCtx (..)
  , urgeRecovery
  , urgeRecoveryEqUrgeRecoverySelect
  , urgeRecoverySelect
  , urgeRecoverySelectEqExcitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Git-style raw commit bytes → typed history (§5.1)
-- ---------------------------------------------------------------------------

-- | Content-addressed byte payload (git-style opaque blob).
type RawCommitBytes = [Int]

-- | Raw git-style commit: hash + payload bytes.
data RawGitCommit = RawGitCommit
  { commitHash :: !Int
  , payload    :: !RawCommitBytes
  } deriving (Show, Eq)

-- | Repository state slice for provenance gate evaluation.
data RepoStateSlice = RepoStateSlice
  { provenanceIntact  :: !Bool
  , physicsGreenClaim :: !Bool
  , witnessPresent    :: !Bool
  } deriving (Show, Eq)

-- | One repository transition step (before/after + provenance metadata).
data RepoTransitionStep = RepoTransitionStep
  { stepBefore          :: !RepoStateSlice
  , stepAfter           :: !RepoStateSlice
  , provenanceStamp     :: !(Maybe String)
  , dropsProvenance     :: !Bool
  , inventsGreen        :: !Bool
  } deriving (Show, Eq)

data TransitionVerdict
  = TransitionAccept
  | TransitionReject
  deriving (Show, Eq)

-- | Typed gate-checked history decoded from raw git bytes.
data TypedHistory = TypedHistory
  { typedSnapshot         :: !HistorySnapshot
  , typedProvenanceIntact :: !Bool
  } deriving (Show, Eq)

-- | Admissible history functor: decode + commit-id preservation law.
data AdmissibleHistoryFunctor = AdmissibleHistoryFunctor
  { historyDecode :: RawGitCommit -> Maybe TypedHistory
  , historyPreserveCommitId
      :: RawGitCommit -> TypedHistory -> Bool
  }

-- | Functor identity string (@history_functor@).
historyFunctorIdentity :: String
historyFunctorIdentity = "history_functor"

-- ---------------------------------------------------------------------------
-- SECTION 2: Second-law preservation on typed history transitions
-- ---------------------------------------------------------------------------

-- | Gate admissibility on history head move (meso Bool witness).
gateAdmissibleHead :: HistoryTransition -> Bool
gateAdmissibleHead t = historyGateAdmissible t

-- | Preservation: second law + gate-checked head move.
preservationProp :: HistoryTransition -> Bool
preservationProp t = admitSecondLaw t && gateAdmissibleHead t

-- | Admissible transition implies preservation property.
preservationPropOfAdmissible :: HistoryTransition -> Bool
preservationPropOfAdmissible t =
  admissibleHistoryTransition t && preservationProp t

-- ---------------------------------------------------------------------------
-- SECTION 3: Provenance gate on repository transitions (meta mirror)
-- ---------------------------------------------------------------------------

-- | Provenance-ok repository transition fixture.
provenancedOkStep :: RepoTransitionStep
provenancedOkStep =
  RepoTransitionStep
    { stepBefore =
        RepoStateSlice
          { provenanceIntact = True
          , physicsGreenClaim = False
          , witnessPresent = False
          }
    , stepAfter =
        RepoStateSlice
          { provenanceIntact = True
          , physicsGreenClaim = False
          , witnessPresent = False
          }
    , provenanceStamp = Just "ucrs:t"
    , dropsProvenance = False
    , inventsGreen = False
    }

-- | umst-meta @evaluate_transition@ mirror — refuse invented GREEN / dropped provenance.
evaluateTransition :: RepoTransitionStep -> TransitionVerdict
evaluateTransition step
  | inventsGreen step = TransitionReject
  | physicsGreenClaim (stepAfter step)
      && not (witnessPresent (stepAfter step)) =
      TransitionReject
  | dropsProvenance step = TransitionReject
  | provenanceIntact (stepBefore step)
      && not (provenanceIntact (stepAfter step)) =
      TransitionReject
  | otherwise =
      case provenanceStamp step of
        Nothing -> TransitionReject
        Just stamp ->
          if null stamp then TransitionReject
          else if provenanceIntact (stepAfter step)
                && not (physicsGreenClaim (stepAfter step))
             then TransitionAccept
             else TransitionReject

-- | Rejects when step invents physics GREEN.
evaluateTransitionRejectsInventsGreen :: RepoTransitionStep -> Bool
evaluateTransitionRejectsInventsGreen step =
  inventsGreen step
    && evaluateTransition step == TransitionReject

-- | Rejects physics GREEN claim without witness.
evaluateTransitionRejectsPhysicsGreenWithoutWitness :: RepoTransitionStep -> Bool
evaluateTransitionRejectsPhysicsGreenWithoutWitness step =
  not (inventsGreen step)
    && physicsGreenClaim (stepAfter step)
    && not (witnessPresent (stepAfter step))
    && evaluateTransition step == TransitionReject

-- | Rejects when provenance is dropped.
evaluateTransitionRejectsDropsProvenance :: RepoTransitionStep -> Bool
evaluateTransitionRejectsDropsProvenance step =
  dropsProvenance step
    && not (inventsGreen step)
    && not (physicsGreenClaim (stepAfter step))
    && evaluateTransition step == TransitionReject

-- | Provenance-ok fixture evaluates to accept.
provenancedOkStepEvaluatesAccept :: Bool
provenancedOkStepEvaluatesAccept =
  evaluateTransition provenancedOkStep == TransitionAccept

-- ---------------------------------------------------------------------------
-- SECTION 4: Catalog decode fixture (git bytes → typed history)
-- ---------------------------------------------------------------------------

-- | Fixture thermodynamic head state.
fixtureState :: ThermodynamicState
fixtureState = ThermodynamicState 2400 0 0 0 0

-- | Fixture commit hash.
fixtureCommitHash :: Int
fixtureCommitHash = 42

-- | Empty fixture payload.
fixturePayload :: RawCommitBytes
fixturePayload = []

-- | Fixture raw git commit.
fixtureRawCommit :: RawGitCommit
fixtureRawCommit =
  RawGitCommit {commitHash = fixtureCommitHash, payload = fixturePayload}

-- | Fixture typed history at catalog hash.
fixtureTypedHistory :: TypedHistory
fixtureTypedHistory =
  TypedHistory
    { typedSnapshot =
        HistorySnapshot
          { historyCommitId = fixtureCommitHash
          , historyHead = fixtureState
          }
    , typedProvenanceIntact = True
    }

-- | Catalog decode: known fixture hash → typed history.
catalogDecode :: RawGitCommit -> Maybe TypedHistory
catalogDecode c =
  if commitHash c == fixtureCommitHash
    then Just fixtureTypedHistory
    else Nothing

-- | Catalog decode maps fixture commit to fixture typed history.
catalogDecodeFixture :: Bool
catalogDecodeFixture =
  catalogDecode fixtureRawCommit == Just fixtureTypedHistory

-- | Commit-id preservation on catalog decode.
catalogDecodePreserveCommitId :: RawGitCommit -> TypedHistory -> Bool
catalogDecodePreserveCommitId c h =
  case catalogDecode c of
    Just decoded ->
      commitHash c == historyCommitId (typedSnapshot decoded)
        && decoded == h
    Nothing -> commitHash c /= fixtureCommitHash

-- | Catalog admissible history functor.
catalogHistoryFunctor :: AdmissibleHistoryFunctor
catalogHistoryFunctor =
  AdmissibleHistoryFunctor
    { historyDecode = catalogDecode
    , historyPreserveCommitId = catalogDecodePreserveCommitId
    }

-- | Catalog functor decodes fixture commit.
catalogDecodeFixtureFunctor :: Bool
catalogDecodeFixtureFunctor =
  historyDecode catalogHistoryFunctor fixtureRawCommit
    == Just fixtureTypedHistory

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge discharge (zero new axioms)
-- ---------------------------------------------------------------------------

-- | Preservation from Landauer-bridged transition + second-law hypothesis.
preservationPropFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
preservationPropFromLandauer b hSL =
  hSL && preservationProp (landauerTransition b)

-- | Admissible transition preserves second law.
admissiblePreservesSecondLaw :: HistoryTransition -> Bool
admissiblePreservesSecondLaw t =
  admissibleHistoryTransition t && admitSecondLaw t

-- | Zero new axiom: preservation from Landauer bridge discharge.
historyFunctorNoNewAxiom :: LandauerHistoryBridge -> Bool -> Bool
historyFunctorNoNewAxiom b hSL =
  preservationPropFromLandauer b hSL

-- ---------------------------------------------------------------------------
-- SECTION 6: Excitement composition (no second argmin)
-- ---------------------------------------------------------------------------

-- | Typed-history recovery composes @excitementSelect@ — not a second argmin.
historyFunctorSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
historyFunctorSelect = urgeRecoverySelect

-- | Definitional witness: history functor selection is @excitementSelect@.
historyFunctorSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
historyFunctorSelectEqExcitementSelect src successors =
  historyFunctorSelect src successors == excitementSelect src successors

-- | History functor selection equals @urgeRecovery@ on recovery context.
historyFunctorSelectEqUrgeRecovery :: HistoryRecoveryCtx -> Bool
historyFunctorSelectEqUrgeRecovery ctx =
  historyFunctorSelect (recoveryPrior ctx) (recoverySuccessors ctx)
    == urgeRecovery ctx

-- | No Urge-local argmin — composes imported @excitementSelect@ only.
historyFunctorNoLocalArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
historyFunctorNoLocalArgmin src successors =
  historyFunctorSelect src successors == excitementSelect src successors
  && urgeRecoverySelectEqExcitementSelect src successors
  && urgeRecoveryEqUrgeRecoverySelect ctx
  where
    ctx =
      HistoryRecoveryCtx
        { recoveryPrior = src
        , recoverySuccessors = successors
        }

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgeHistoryFunctorPhysicsGreen :: Bool
urgeHistoryFunctorPhysicsGreen = False

-- | Lean/Coq: @urge_physics_green_false@.
urgeHistoryFunctorPhysicsGreenFalse :: Bool
urgeHistoryFunctorPhysicsGreenFalse =
  not urgeHistoryFunctorPhysicsGreen

-- | Production wiring stays open (history functor lift only).
historyFunctorProductionWired :: Bool
historyFunctorProductionWired = False

-- | Lean/Coq: @history_functor_production_wired_false@.
historyFunctorProductionWiredFalse :: Bool
historyFunctorProductionWiredFalse = not historyFunctorProductionWired

-- | Catalog witness: meso Urge HistoryFunctor module present.
historyFunctorModuleWitness :: Bool
historyFunctorModuleWitness = True
