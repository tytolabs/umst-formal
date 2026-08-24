-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliRecover
-- Description : Meso acting Urge — §16.7 operator verb `recover` as Kleisli arrow.
--
-- Kleisli gate = Excitement argmin over successors; MergeSafe witness;
-- typed recovery morphism; network egress entity check.
-- Recovery **is** 'excitementSelect' — not rsync theater; no second argmin.
-- Mirrors 'UMST.Urge.CollaborativeObject' excitement + Landauer discipline.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.KleisliRecover
  ( -- * §16.7 recover column carriers + Kleisli arrow witness
    RecoverOperatorVerb (..)
  , NetworkEgressClass (..)
  , RecoverReplicaClass (..)
  , networkEgressAdmits
  , replicaEgressEmpty
  , classifyNetworkEgress
  , RecoverMergeSafeWitness (..)
  , recoverMergeSafeAdmits
  , RecoverUcrsStamp (..)
  , RecoverRecoverySnapshot (..)
  , RecoverRecoveryWitness (..)
  , KleisliGateKind (..)
  , RecoverKleisliArrow (..)
  , RecoverRecoveryMorphism (..)
  , RecoverVerdict (..)
  , RecoverRefusal (..)
  , RecoverVerbRow (..)
  , recoverVerbRowPin
  , kleisliGateMatchesRecover
    -- * §16.7 admissibility conjunct + positive refuse
  , RecoverAdmissibilityConjunct (..)
  , recoverConjunctAdmits
  , RecoverOperationClass (..)
  , evaluateRecoverOperation
  , refuseRsyncTheater
  , witnessFromSnapshot
  , recoverArrowAdmissible
  , evaluateRecoverKleisli
  , applyRecoverRecoveryMorphism
  , refuseProductionWiredRecover
  , refuseSecondArgminRecover
  , refuseSyncGateOnRecover
  , refuseFrugalMiOnRecover
  , recoverVerbRowMergeSafeRequired
  , recoverVerbRowExcitementRequired
  , recoverVerbRowEntityCheckEgress
  , kleisliGateMatchesRecoverExcitement
  , kleisliGateMatchesRecoverRejectsInboundSync
    -- * Recover composes excitementSelect (no second argmin)
  , RecoverCtx (..)
  , recoverSelect
  , recoverSelectBare
  , recoverSelectEqExcitementSelect
  , recoverSelectEqRecoverSelectBare
  , recoverNoLocalArgmin
  , recoverSelectEmpty
  , RecoverExcitementPin (..)
  , recoverExcitementSelect
  , recoverExcitementSelectEqExcitementSelect
  , recoverExcitementSelectRefusesSecondArgmin
    -- * §16.7 fixtures + witness theorems
  , recoverFixtureState
  , recoverFixtureUcrs
  , recoverFixtureMergeSafe
  , recoverFixtureSnapshot
  , recoverFixtureConjunct
  , recoverFixtureAdmittedArrow
  , recoverFixtureMergeFailArrow
  , recoverFixtureEgressFailArrow
  , recoverFixtureRsyncTheaterRefused
  , recoverFixtureApplyMorphismOk
  , recoverFixtureAdmittedOk
  , recoverFixtureMergeSafeRefused
  , recoverFixtureEgressRefused
  , recoverOfflineLuksEgressEmpty
  , recoverDarwinScratchEgressEmpty
  , recoverForgePrimaryEgressNonempty
  , recoverClassifyOfflineLuksEgress
  , recoverFixtureWitnessPreservesUcrs
  , recoverFixtureRefuseSyncGatePositive
  , recoverFixtureRefuseFrugalMiPositive
  , recoverArrowAdmissibleFixture
    -- * Landauer bridge (derived — zero new axioms)
  , RecoverHistoryMove (..)
  , admissibleRecoverHistoryMove
  , RecoverTransition (..)
  , recoverSecondLaw
  , recoverSecondLawFromLandauer
  , recoverFromLandauerAdmitSecondLaw
  , recoverSecondLawFromHypothesis
  , admissibleRecoverHistoryMoveFromLandauer
    -- * Honesty flags + catalog witnesses
  , kleisliRecoverPhysicsGreen
  , kleisliRecoverPhysicsGreenFalse
  , kleisliRecoverProductionWired
  , kleisliRecoverProductionWiredFalse
  , kleisliRecoverModuleWitness
  , kleisliRecoverNoNewAxiom
  , kleisliRecoverPositiveRefuseNotSilent
  , kleisliRecoverProductionWiredRefusePositive
  , kleisliRecoverSecondArgminRefusePositive
  , kleisliRecoverNonClaim
  , kleisliRecoverNonClaimNonempty
  , kleisliRecoverNoSecondArgmin
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

-- ---------------------------------------------------------------------------
-- SECTION 1: §16.7 recover column carriers + Kleisli arrow witness
-- ---------------------------------------------------------------------------

data RecoverOperatorVerb = RecoverVerb
  deriving (Show, Eq)

data NetworkEgressClass
  = EgressEmpty
  | TailscaleAdmin
  | Undeclared
  deriving (Show, Eq)

networkEgressAdmits :: NetworkEgressClass -> Bool
networkEgressAdmits EgressEmpty     = True
networkEgressAdmits TailscaleAdmin  = True
networkEgressAdmits Undeclared      = False

data RecoverReplicaClass
  = ForgePrimary
  | DarwinScratch
  | OfflineLuks
  deriving (Show, Eq)

replicaEgressEmpty :: RecoverReplicaClass -> Bool
replicaEgressEmpty OfflineLuks    = True
replicaEgressEmpty DarwinScratch  = True
replicaEgressEmpty ForgePrimary   = False

classifyNetworkEgress :: RecoverReplicaClass -> NetworkEgressClass
classifyNetworkEgress c =
  if replicaEgressEmpty c then EgressEmpty else TailscaleAdmin

data RecoverMergeSafeWitness = RecoverMergeSafeWitness
  { recoverMergeSafeOk :: !Bool
  } deriving (Show, Eq)

recoverMergeSafeAdmits :: RecoverMergeSafeWitness -> Bool
recoverMergeSafeAdmits w = recoverMergeSafeOk w

data RecoverUcrsStamp = RecoverUcrsStamp
  { recoverUcrsSeq      :: !Int
  , recoverUcrsWallHasT :: !Bool
  } deriving (Show, Eq)

data RecoverRecoverySnapshot = RecoverRecoverySnapshot
  { recoverSnapshotId               :: !Int
  , recoverSnapshotHead             :: !ThermodynamicState
  , recoverSnapshotUcrs             :: !RecoverUcrsStamp
  , recoverSnapshotMergeSafe        :: !RecoverMergeSafeWitness
  , recoverSnapshotProvenanceIntact :: !Bool
  , recoverSnapshotReplica          :: !RecoverReplicaClass
  } deriving (Show, Eq)

data RecoverRecoveryWitness = RecoverRecoveryWitness
  { recoverWitnessUcrs             :: !RecoverUcrsStamp
  , recoverWitnessMergeSafe        :: !RecoverMergeSafeWitness
  , recoverWitnessProvenanceIntact :: !Bool
  } deriving (Show, Eq)

data KleisliGateKind
  = ExcitementArgmin
  | GateCheckBeforeSyncInbound
  | FrugalMiObservation
  deriving (Show, Eq)

data RecoverKleisliArrow = RecoverKleisliArrow
  { recoverArrowVerb      :: !RecoverOperatorVerb
  , recoverArrowMergeSafe :: !RecoverMergeSafeWitness
  , recoverArrowEgress    :: !NetworkEgressClass
  , recoverArrowSnapshot  :: !RecoverRecoverySnapshot
  } deriving (Show, Eq)

data RecoverRecoveryMorphism = RecoverRecoveryMorphism
  { recoverMorphismFrom               :: !RecoverRecoverySnapshot
  , recoverMorphismToReplica          :: !RecoverReplicaClass
  , recoverMorphismWitness            :: !RecoverRecoveryWitness
  , recoverMorphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

data RecoverVerdict
  = RecoverAdmitted
  | RecoverMergeSafeRefused
  | RecoverNetworkEgressRefused
  | RecoverRsyncTheaterRefused
  | RecoverProductionWiredRefused
  | RecoverExcitementResidue
  deriving (Show, Eq)

data RecoverRefusal
  = RecoverRefusalMergeSafe
  | RecoverRefusalNetworkEgress !NetworkEgressClass
  | RecoverRefusalRsyncTheater !Int
  | RecoverRefusalGateRejected !Int
  | RecoverRefusalProvenanceLoss !Int
  | RecoverRefusalProductionWired
  | RecoverRefusalSecondArgmin
  | RecoverRefusalWrongGate !KleisliGateKind
  deriving (Show, Eq)

data RecoverVerbRow = RecoverVerbRow
  { recoverVerbRowVerb               :: !RecoverOperatorVerb
  , recoverVerbRowKleisliGate        :: !KleisliGateKind
  , recoverRowMergeSafeRequired  :: !Bool
  , recoverRowExcitementRequired :: !Bool
  , recoverRowEntityCheckEgress  :: !Bool
  } deriving (Show, Eq)

recoverVerbRowPin :: RecoverVerbRow
recoverVerbRowPin =
  RecoverVerbRow
    { recoverVerbRowVerb = RecoverVerb
    , recoverVerbRowKleisliGate = ExcitementArgmin
    , recoverRowMergeSafeRequired = True
    , recoverRowExcitementRequired = True
    , recoverRowEntityCheckEgress = True
    }

kleisliGateMatchesRecover :: KleisliGateKind -> Bool
kleisliGateMatchesRecover ExcitementArgmin = True
kleisliGateMatchesRecover _                = False

-- ---------------------------------------------------------------------------
-- SECTION 2: §16.7 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

data RecoverAdmissibilityConjunct = RecoverAdmissibilityConjunct
  { recoverConjGateOk                :: !Bool
  , recoverConjMergeSafe             :: !Bool
  , recoverConjExcitementPreserves   :: !Bool
  , recoverConjEgressOk              :: !Bool
  } deriving (Show, Eq)

recoverConjunctAdmits :: RecoverAdmissibilityConjunct -> Bool
recoverConjunctAdmits c =
  recoverConjGateOk c
  && recoverConjMergeSafe c
  && recoverConjExcitementPreserves c
  && recoverConjEgressOk c

data RecoverOperationClass
  = TypedMorphism
  | RsyncTheater
  deriving (Show, Eq)

evaluateRecoverOperation :: RecoverOperationClass -> RecoverVerdict
evaluateRecoverOperation RsyncTheater = RecoverRsyncTheaterRefused
evaluateRecoverOperation TypedMorphism = RecoverAdmitted

refuseRsyncTheater :: Int -> RecoverRefusal
refuseRsyncTheater snapshotId = RecoverRefusalRsyncTheater snapshotId

witnessFromSnapshot :: RecoverRecoverySnapshot -> RecoverRecoveryWitness
witnessFromSnapshot s =
  RecoverRecoveryWitness
    { recoverWitnessUcrs = recoverSnapshotUcrs s
    , recoverWitnessMergeSafe = recoverSnapshotMergeSafe s
    , recoverWitnessProvenanceIntact = recoverSnapshotProvenanceIntact s
    }

recoverArrowAdmissible :: RecoverKleisliArrow -> Bool
recoverArrowAdmissible a =
  recoverMergeSafeAdmits (recoverArrowMergeSafe a)
  && networkEgressAdmits (recoverArrowEgress a)

evaluateRecoverKleisli
  :: RecoverKleisliArrow -> Either RecoverRefusal RecoverVerdict
evaluateRecoverKleisli a
  | not (recoverMergeSafeAdmits (recoverArrowMergeSafe a)) =
      Left RecoverRefusalMergeSafe
  | not (networkEgressAdmits (recoverArrowEgress a)) =
      Left (RecoverRefusalNetworkEgress (recoverArrowEgress a))
  | otherwise =
      Right RecoverAdmitted

applyRecoverRecoveryMorphism
  :: RecoverRecoverySnapshot
  -> RecoverReplicaClass
  -> RecoverAdmissibilityConjunct
  -> Bool
  -> Either RecoverRefusal RecoverRecoveryMorphism
applyRecoverRecoveryMorphism snapshot toReplica conjunct excitementSelected
  | not (recoverConjunctAdmits conjunct) =
      Left (RecoverRefusalGateRejected (recoverUcrsSeq (recoverSnapshotUcrs snapshot)))
  | not (recoverMergeSafeAdmits (recoverSnapshotMergeSafe snapshot)) =
      Left RecoverRefusalMergeSafe
  | not (recoverSnapshotProvenanceIntact snapshot) =
      Left (RecoverRefusalProvenanceLoss (recoverSnapshotId snapshot))
  | not excitementSelected =
      Left (RecoverRefusalProvenanceLoss (recoverSnapshotId snapshot))
  | otherwise =
      Right
        RecoverRecoveryMorphism
          { recoverMorphismFrom = snapshot
          , recoverMorphismToReplica = toReplica
          , recoverMorphismWitness = witnessFromSnapshot snapshot
          , recoverMorphismExcitementSelected = excitementSelected
          }

refuseProductionWiredRecover :: RecoverRefusal
refuseProductionWiredRecover = RecoverRefusalProductionWired

refuseSecondArgminRecover :: RecoverRefusal
refuseSecondArgminRecover = RecoverRefusalSecondArgmin

refuseSyncGateOnRecover :: RecoverRefusal
refuseSyncGateOnRecover = RecoverRefusalWrongGate GateCheckBeforeSyncInbound

refuseFrugalMiOnRecover :: RecoverRefusal
refuseFrugalMiOnRecover = RecoverRefusalWrongGate FrugalMiObservation

recoverVerbRowMergeSafeRequired :: Bool
recoverVerbRowMergeSafeRequired =
  recoverRowMergeSafeRequired recoverVerbRowPin

recoverVerbRowExcitementRequired :: Bool
recoverVerbRowExcitementRequired =
  recoverRowExcitementRequired recoverVerbRowPin

recoverVerbRowEntityCheckEgress :: Bool
recoverVerbRowEntityCheckEgress =
  recoverRowEntityCheckEgress recoverVerbRowPin

kleisliGateMatchesRecoverExcitement :: Bool
kleisliGateMatchesRecoverExcitement =
  kleisliGateMatchesRecover ExcitementArgmin

kleisliGateMatchesRecoverRejectsInboundSync :: Bool
kleisliGateMatchesRecoverRejectsInboundSync =
  not (kleisliGateMatchesRecover GateCheckBeforeSyncInbound)

-- ---------------------------------------------------------------------------
-- SECTION 3: Recover composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

data RecoverCtx = RecoverCtx
  { recoverPrior      :: !ThermodynamicState
  , recoverSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

recoverSelect
  :: RecoverCtx
  -> Either ExcitementResidue HistoryCandidate
recoverSelect ctx =
  excitementSelect (recoverPrior ctx) (recoverSuccessors ctx)

recoverSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
recoverSelectBare = excitementSelect

recoverSelectEqExcitementSelect :: RecoverCtx -> Bool
recoverSelectEqExcitementSelect ctx =
  recoverSelect ctx
    == excitementSelect (recoverPrior ctx) (recoverSuccessors ctx)

recoverSelectEqRecoverSelectBare :: RecoverCtx -> Bool
recoverSelectEqRecoverSelectBare ctx =
  recoverSelect ctx == recoverSelectBare (recoverPrior ctx) (recoverSuccessors ctx)

recoverNoLocalArgmin :: RecoverCtx -> Bool
recoverNoLocalArgmin = recoverSelectEqExcitementSelect

recoverSelectEmpty :: ThermodynamicState -> Bool
recoverSelectEmpty src =
  recoverSelectBare src [] == Left ExcNoCandidates

data RecoverExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

recoverExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> RecoverExcitementPin
  -> Either ExcitementResidue HistoryCandidate
recoverExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
recoverExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

recoverExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
recoverExcitementSelectEqExcitementSelect src cands =
  recoverExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

recoverExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
recoverExcitementSelectRefusesSecondArgmin src cands =
  recoverExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- ---------------------------------------------------------------------------
-- SECTION 4: §16.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

recoverFixtureState :: ThermodynamicState
recoverFixtureState = ThermodynamicState 2400 0 0.3 30 40

recoverFixtureUcrs :: RecoverUcrsStamp
recoverFixtureUcrs = RecoverUcrsStamp {recoverUcrsSeq = 7, recoverUcrsWallHasT = True}

recoverFixtureMergeSafe :: RecoverMergeSafeWitness
recoverFixtureMergeSafe = RecoverMergeSafeWitness {recoverMergeSafeOk = True}

recoverFixtureSnapshot :: RecoverRecoverySnapshot
recoverFixtureSnapshot =
  RecoverRecoverySnapshot
    { recoverSnapshotId = 1
    , recoverSnapshotHead = recoverFixtureState
    , recoverSnapshotUcrs = recoverFixtureUcrs
    , recoverSnapshotMergeSafe = recoverFixtureMergeSafe
    , recoverSnapshotProvenanceIntact = True
    , recoverSnapshotReplica = ForgePrimary
    }

recoverFixtureConjunct :: RecoverAdmissibilityConjunct
recoverFixtureConjunct =
  RecoverAdmissibilityConjunct
    { recoverConjGateOk = True
    , recoverConjMergeSafe = True
    , recoverConjExcitementPreserves = True
    , recoverConjEgressOk = True
    }

recoverFixtureAdmittedArrow :: RecoverKleisliArrow
recoverFixtureAdmittedArrow =
  RecoverKleisliArrow
    { recoverArrowVerb = RecoverVerb
    , recoverArrowMergeSafe = recoverFixtureMergeSafe
    , recoverArrowEgress = TailscaleAdmin
    , recoverArrowSnapshot = recoverFixtureSnapshot
    }

recoverFixtureMergeFailArrow :: RecoverKleisliArrow
recoverFixtureMergeFailArrow =
  RecoverKleisliArrow
    { recoverArrowVerb = RecoverVerb
    , recoverArrowMergeSafe = RecoverMergeSafeWitness {recoverMergeSafeOk = False}
    , recoverArrowEgress = EgressEmpty
    , recoverArrowSnapshot = recoverFixtureSnapshot
    }

recoverFixtureEgressFailArrow :: RecoverKleisliArrow
recoverFixtureEgressFailArrow =
  RecoverKleisliArrow
    { recoverArrowVerb = RecoverVerb
    , recoverArrowMergeSafe = recoverFixtureMergeSafe
    , recoverArrowEgress = Undeclared
    , recoverArrowSnapshot = recoverFixtureSnapshot
    }

recoverFixtureRsyncTheaterRefused :: Bool
recoverFixtureRsyncTheaterRefused =
  evaluateRecoverOperation RsyncTheater == RecoverRsyncTheaterRefused

recoverFixtureApplyMorphismOk :: Bool
recoverFixtureApplyMorphismOk =
  applyRecoverRecoveryMorphism
    recoverFixtureSnapshot
    OfflineLuks
    recoverFixtureConjunct
    True
    == Right
      RecoverRecoveryMorphism
        { recoverMorphismFrom = recoverFixtureSnapshot
        , recoverMorphismToReplica = OfflineLuks
        , recoverMorphismWitness = witnessFromSnapshot recoverFixtureSnapshot
        , recoverMorphismExcitementSelected = True
        }

recoverFixtureAdmittedOk :: Bool
recoverFixtureAdmittedOk =
  evaluateRecoverKleisli recoverFixtureAdmittedArrow == Right RecoverAdmitted

recoverFixtureMergeSafeRefused :: Bool
recoverFixtureMergeSafeRefused =
  evaluateRecoverKleisli recoverFixtureMergeFailArrow
    == Left RecoverRefusalMergeSafe

recoverFixtureEgressRefused :: Bool
recoverFixtureEgressRefused =
  evaluateRecoverKleisli recoverFixtureEgressFailArrow
    == Left (RecoverRefusalNetworkEgress Undeclared)

recoverOfflineLuksEgressEmpty :: Bool
recoverOfflineLuksEgressEmpty = replicaEgressEmpty OfflineLuks

recoverDarwinScratchEgressEmpty :: Bool
recoverDarwinScratchEgressEmpty = replicaEgressEmpty DarwinScratch

recoverForgePrimaryEgressNonempty :: Bool
recoverForgePrimaryEgressNonempty = not (replicaEgressEmpty ForgePrimary)

recoverClassifyOfflineLuksEgress :: Bool
recoverClassifyOfflineLuksEgress =
  classifyNetworkEgress OfflineLuks == EgressEmpty

recoverFixtureWitnessPreservesUcrs :: Bool
recoverFixtureWitnessPreservesUcrs =
  recoverWitnessUcrs (witnessFromSnapshot recoverFixtureSnapshot)
    == recoverFixtureUcrs

recoverFixtureRefuseSyncGatePositive :: Bool
recoverFixtureRefuseSyncGatePositive =
  refuseSyncGateOnRecover
    == RecoverRefusalWrongGate GateCheckBeforeSyncInbound

recoverFixtureRefuseFrugalMiPositive :: Bool
recoverFixtureRefuseFrugalMiPositive =
  refuseFrugalMiOnRecover
    == RecoverRefusalWrongGate FrugalMiObservation

recoverArrowAdmissibleFixture :: Bool
recoverArrowAdmissibleFixture =
  recoverArrowAdmissible recoverFixtureAdmittedArrow

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

data RecoverHistoryMove = RecoverHistoryMove
  { recoverMovePrior        :: !ThermodynamicState
  , recoverMovePost         :: !ThermodynamicState
  , recoverMoveGateChecked  :: !Bool
  , recoverMoveMergeSafe    :: !Bool
  , recoverMoveProvenanceOk :: !Bool
  } deriving (Show, Eq)

admissibleRecoverHistoryMove :: RecoverHistoryMove -> Bool
admissibleRecoverHistoryMove h =
  recoverMoveGateChecked h
  && recoverMoveMergeSafe h
  && recoverMoveProvenanceOk h

data RecoverTransition = RecoverTransition
  { recoverTransMove           :: !RecoverHistoryMove
  , recoverTransBath           :: !HeatBath
  , recoverTransDissipatedWork :: !Double
  , recoverTransEntropyDrop    :: !Double
  } deriving (Show, Eq)

recoverSecondLaw :: RecoverTransition -> Bool
recoverSecondLaw t =
  recoverTransEntropyDrop t
    <= recoverTransDissipatedWork t / bathTemp (recoverTransBath t)

recoverSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
recoverSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

recoverFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
recoverFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

recoverSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
recoverSecondLawFromHypothesis t ok = ok && admitSecondLaw t

admissibleRecoverHistoryMoveFromLandauer
  :: LandauerHistoryBridge -> Bool -> Bool
admissibleRecoverHistoryMoveFromLandauer b hSL =
  hSL && admissibleHistoryTransitionFromLandauerBridge b hSL

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

kleisliRecoverPhysicsGreen :: Bool
kleisliRecoverPhysicsGreen = False

kleisliRecoverPhysicsGreenFalse :: Bool
kleisliRecoverPhysicsGreenFalse = not kleisliRecoverPhysicsGreen

kleisliRecoverProductionWired :: Bool
kleisliRecoverProductionWired = False

kleisliRecoverProductionWiredFalse :: Bool
kleisliRecoverProductionWiredFalse = not kleisliRecoverProductionWired

kleisliRecoverModuleWitness :: Bool
kleisliRecoverModuleWitness = True

kleisliRecoverNoNewAxiom :: Bool
kleisliRecoverNoNewAxiom = True

kleisliRecoverPositiveRefuseNotSilent :: Bool
kleisliRecoverPositiveRefuseNotSilent =
  evaluateRecoverOperation RsyncTheater /= RecoverAdmitted

kleisliRecoverProductionWiredRefusePositive :: Bool
kleisliRecoverProductionWiredRefusePositive =
  refuseProductionWiredRecover == RecoverRefusalProductionWired

kleisliRecoverSecondArgminRefusePositive :: Bool
kleisliRecoverSecondArgminRefusePositive =
  refuseSecondArgminRecover == RecoverRefusalSecondArgmin

kleisliRecoverNonClaim :: String
kleisliRecoverNonClaim =
  "§16.7 recover Kleisli arrow: Excitement argmin + MergeSafe + typed recovery "
    ++ "morphism + network egress; recoverSelect composes excitementSelect; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

kleisliRecoverNonClaimNonempty :: Bool
kleisliRecoverNonClaimNonempty = length kleisliRecoverNonClaim > 0

kleisliRecoverNoSecondArgmin :: Bool
kleisliRecoverNoSecondArgmin =
  recoverNoLocalArgmin
    (RecoverCtx {recoverPrior = recoverFixtureState, recoverSuccessors = []})
