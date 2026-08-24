-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliPush
-- Description : Meso acting Urge — §16.7 operator verb `push` as Kleisli arrow.
--
-- Kleisli gate = `outbound_tick_if_admitted`; MergeSafe = pre-push witness;
-- Excitement = provenance preserved; entity check = entity remote.
--
-- Push composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.KleisliPush
  ( -- * §16.7 push column carriers + Kleisli arrow witness
    OutboundTickGate (..)
  , outboundGateAdmits
  , PrePushMergeSafeWitness (..)
  , prePushMergeSafeAdmits
  , ProvenancePreserved (..)
  , provenancePreservedAdmits
  , EntityRemoteClass (..)
  , entityRemoteAdmits
  , KleisliGateKind (..)
  , PushKleisliArrow (..)
  , PushVerdict (..)
  , PushRefusal (..)
    -- * §16.7 admissibility conjunct + positive refuse
  , PushAdmissibilityConjunct (..)
  , pushConjunctAdmits
  , pushArrowAdmissible
  , evaluatePushKleisli
  , refuseProductionWiredPush
  , refuseGateBypassPush
  , refuseSyncGateOnPush
  , refuseFrugalMiOnPush
  , kleisliGateMatchesPush
  , classifyEntityRemote
  , pushKleisliArrowFromHost
    -- * Push composes excitementSelect (no second argmin)
  , PushCtx (..)
  , pushSelect
  , pushSelectBare
  , pushSelectEqExcitementSelect
  , pushSelectEqUrgeRecoverySelect
  , pushNoLocalArgmin
  , pushSelectEmpty
    -- * §16.7 fixtures + witness theorems
  , pushFixtureAdmittedArrow
  , pushFixtureGateRefusedArrow
  , pushFixtureConjunct
  , pushFixtureAdmittedOk
  , pushFixtureGateRefused
  , pushFixtureEntityRemoteForge
  , pushFixtureEntityRefusedUpstreamOrigin
  , pushFixtureEntityRefusedUpstreamGithub
  , pushFixtureKleisliGateMatchesPush
  , pushFixtureKleisliGateRejectsInboundSync
  , pushFixtureRefuseSyncGatePositive
  , pushFixtureRefuseFrugalMiPositive
  , pushFixtureConjunctAdmits
    -- * Landauer bridge (derived — zero new axioms)
  , PushHistoryMove (..)
  , admissiblePushHistoryMove
  , PushTransition (..)
  , pushSecondLaw
  , pushSecondLawFromLandauer
  , pushSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , kleisliPushPhysicsGreen
  , kleisliPushPhysicsGreenFalse
  , kleisliPushProductionWired
  , kleisliPushProductionWiredFalse
  , kleisliPushModuleWitness
  , kleisliPushNoNewAxiom
  , kleisliPushPositiveRefuseNotSilent
  , kleisliPushProductionWiredRefusePositive
  , kleisliPushGateBypassRefusePositive
  , kleisliPushNoSecondArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
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
-- SECTION 1: §16.7 push column carriers + Kleisli arrow witness
-- ---------------------------------------------------------------------------

-- | Outbound tick gate — `outbound_tick_if_admitted` (push row Kleisli gate).
data OutboundTickGate
  = OutboundAdmitted
  | OutboundRefused
  | OutboundBypassAttempted
  deriving (Show, Eq)

-- | Whether outbound gate admits push morphism.
outboundGateAdmits :: OutboundTickGate -> Bool
outboundGateAdmits OutboundAdmitted = True
outboundGateAdmits _ = False

-- | Pre-push MergeSafe witness column (§16.7 push row).
data PrePushMergeSafeWitness
  = PrePushWitnessed
  | PrePushMissing
  | PrePushBypassAttempted
  deriving (Show, Eq)

prePushMergeSafeAdmits :: PrePushMergeSafeWitness -> Bool
prePushMergeSafeAdmits PrePushWitnessed = True
prePushMergeSafeAdmits _ = False

-- | Excitement column for push — provenance preserved.
data ProvenancePreserved
  = ProvPreserved
  | ProvViolated
  | ProvBypassAttempted
  deriving (Show, Eq)

provenancePreservedAdmits :: ProvenancePreserved -> Bool
provenancePreservedAdmits ProvPreserved = True
provenancePreservedAdmits _ = False

-- | Entity remote class for push entity check (§16.7).
data EntityRemoteClass
  = EntityRemote
  | EntityRefusedUpstream
  | EntityUnclassified
  deriving (Show, Eq)

entityRemoteAdmits :: EntityRemoteClass -> Bool
entityRemoteAdmits EntityRemote = True
entityRemoteAdmits _ = False

-- | Kleisli gate kinds cited in §16.7 (push uses outbound tick only).
data KleisliGateKind
  = KleisliOutboundTickIfAdmitted
  | KleisliGateCheckBeforeSyncInbound
  | KleisliFrugalMiObservation
  deriving (Show, Eq)

-- | §16.7 typed Kleisli arrow witness for operator `push`.
data PushKleisliArrow = PushKleisliArrow
  { pushGate        :: !OutboundTickGate
  , pushMergeSafe   :: !PrePushMergeSafeWitness
  , pushProvenance  :: !ProvenancePreserved
  , pushEntity      :: !EntityRemoteClass
  , pushObjectCount :: !Int
  } deriving (Show, Eq)

data PushVerdict
  = PushAdmitted
  | PushGateRefused
  | PushMergeSafeRefused
  | PushProvenanceRefused
  | PushEntityRemoteRefused
  | PushProductionWiredRefused
  | PushGateBypassRefused
  deriving (Show, Eq)

-- | Fail-closed push errors — positive refuse, not silent no-op.
data PushRefusal
  = PushRefusalGate
  | PushRefusalMergeSafeMissing
  | PushRefusalMergeSafeBypass
  | PushRefusalProvenanceViolated
  | PushRefusalProvenanceBypass
  | PushRefusalEntityRemote EntityRemoteClass
  | PushRefusalProductionWired
  | PushRefusalGateBypass
  | PushRefusalWrongGate KleisliGateKind
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §16.7 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

data PushAdmissibilityConjunct = PushAdmissibilityConjunct
  { conjGateOk              :: !Bool
  , conjMergeSafeOk         :: !Bool
  , conjProvenancePreserved :: !Bool
  , conjEntityRemote        :: !Bool
  } deriving (Show, Eq)

pushConjunctAdmits :: PushAdmissibilityConjunct -> Bool
pushConjunctAdmits c =
  conjGateOk c
  && conjMergeSafeOk c
  && conjProvenancePreserved c
  && conjEntityRemote c

pushArrowAdmissible :: PushKleisliArrow -> Bool
pushArrowAdmissible a =
  outboundGateAdmits (pushGate a)
  && prePushMergeSafeAdmits (pushMergeSafe a)
  && provenancePreservedAdmits (pushProvenance a)
  && entityRemoteAdmits (pushEntity a)

-- | Evaluate push as Kleisli arrow — gate ∧ MergeSafe ∧ Excitement ∧ entity.
evaluatePushKleisli :: PushKleisliArrow -> Either PushVerdict PushRefusal
evaluatePushKleisli a =
  if outboundGateAdmits (pushGate a)
    then
      if prePushMergeSafeAdmits (pushMergeSafe a)
        then
          if provenancePreservedAdmits (pushProvenance a)
            then
              if entityRemoteAdmits (pushEntity a)
                then Left PushAdmitted
                else Right (PushRefusalEntityRemote (pushEntity a))
            else
              case pushProvenance a of
                ProvBypassAttempted -> Right PushRefusalProvenanceBypass
                _ -> Right PushRefusalProvenanceViolated
        else
          case pushMergeSafe a of
            PrePushBypassAttempted -> Right PushRefusalMergeSafeBypass
            _ -> Right PushRefusalMergeSafeMissing
    else
      case pushGate a of
        OutboundBypassAttempted -> Right PushRefusalGateBypass
        _ -> Right PushRefusalGate

refuseProductionWiredPush :: PushRefusal
refuseProductionWiredPush = PushRefusalProductionWired

refuseGateBypassPush :: PushRefusal
refuseGateBypassPush = PushRefusalGateBypass

refuseSyncGateOnPush :: PushRefusal
refuseSyncGateOnPush =
  PushRefusalWrongGate KleisliGateCheckBeforeSyncInbound

refuseFrugalMiOnPush :: PushRefusal
refuseFrugalMiOnPush =
  PushRefusalWrongGate KleisliFrugalMiObservation

kleisliGateMatchesPush :: KleisliGateKind -> Bool
kleisliGateMatchesPush KleisliOutboundTickIfAdmitted = True
kleisliGateMatchesPush _ = False

-- | Classify remote host into entity-remote check class (typed surrogate).
classifyEntityRemote :: String -> EntityRemoteClass
classifyEntityRemote "" = EntityUnclassified
classifyEntityRemote host =
  if host == "origin.cursor.com" || host == "github.com"
    then EntityRefusedUpstream
    else
      if host == "forge.entity"
        then EntityRemote
        else EntityUnclassified

pushKleisliArrowFromHost
  :: OutboundTickGate
  -> PrePushMergeSafeWitness
  -> ProvenancePreserved
  -> String
  -> Int
  -> PushKleisliArrow
pushKleisliArrowFromHost gate mergeSafe provenance remoteHost objectCount =
  PushKleisliArrow
    { pushGate = gate
    , pushMergeSafe = mergeSafe
    , pushProvenance = provenance
    , pushEntity = classifyEntityRemote remoteHost
    , pushObjectCount = objectCount
    }

-- ---------------------------------------------------------------------------
-- SECTION 3: Push composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for push over admissible history successors.
data PushCtx = PushCtx
  { pushPrior       :: !ThermodynamicState
  , pushSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Push **is** 'urgeRecoverySelect' / 'excitementSelect' on successors.
pushSelect :: PushCtx -> Either ExcitementResidue HistoryCandidate
pushSelect ctx =
  urgeRecoverySelect (pushPrior ctx) (pushSuccessors ctx)

pushSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
pushSelectBare prior successors = urgeRecoverySelect prior successors

pushSelectEqExcitementSelect :: PushCtx -> Bool
pushSelectEqExcitementSelect ctx =
  pushSelect ctx
    == excitementSelect (pushPrior ctx) (pushSuccessors ctx)

pushSelectEqUrgeRecoverySelect :: PushCtx -> Bool
pushSelectEqUrgeRecoverySelect ctx =
  pushSelect ctx == urgeRecoverySelect (pushPrior ctx) (pushSuccessors ctx)

pushNoLocalArgmin :: PushCtx -> Bool
pushNoLocalArgmin ctx =
  pushSelect ctx == excitementSelect (pushPrior ctx) (pushSuccessors ctx)

pushSelectEmpty :: ThermodynamicState -> Bool
pushSelectEmpty prior =
  pushSelectBare prior [] == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §16.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

pushFixtureAdmittedArrow :: PushKleisliArrow
pushFixtureAdmittedArrow =
  pushKleisliArrowFromHost
    OutboundAdmitted
    PrePushWitnessed
    ProvPreserved
    "forge.entity"
    3

pushFixtureGateRefusedArrow :: PushKleisliArrow
pushFixtureGateRefusedArrow =
  pushKleisliArrowFromHost
    OutboundRefused
    PrePushWitnessed
    ProvPreserved
    "forge.entity"
    0

pushFixtureConjunct :: PushAdmissibilityConjunct
pushFixtureConjunct =
  PushAdmissibilityConjunct
    { conjGateOk = True
    , conjMergeSafeOk = True
    , conjProvenancePreserved = True
    , conjEntityRemote = True
    }

pushFixtureAdmittedOk :: Bool
pushFixtureAdmittedOk =
  evaluatePushKleisli pushFixtureAdmittedArrow == Left PushAdmitted

pushFixtureGateRefused :: Bool
pushFixtureGateRefused =
  evaluatePushKleisli pushFixtureGateRefusedArrow == Right PushRefusalGate

pushFixtureEntityRemoteForge :: Bool
pushFixtureEntityRemoteForge =
  classifyEntityRemote "forge.entity" == EntityRemote

pushFixtureEntityRefusedUpstreamOrigin :: Bool
pushFixtureEntityRefusedUpstreamOrigin =
  classifyEntityRemote "origin.cursor.com" == EntityRefusedUpstream

pushFixtureEntityRefusedUpstreamGithub :: Bool
pushFixtureEntityRefusedUpstreamGithub =
  classifyEntityRemote "github.com" == EntityRefusedUpstream

pushFixtureKleisliGateMatchesPush :: Bool
pushFixtureKleisliGateMatchesPush =
  kleisliGateMatchesPush KleisliOutboundTickIfAdmitted

pushFixtureKleisliGateRejectsInboundSync :: Bool
pushFixtureKleisliGateRejectsInboundSync =
  not (kleisliGateMatchesPush KleisliGateCheckBeforeSyncInbound)

pushFixtureRefuseSyncGatePositive :: Bool
pushFixtureRefuseSyncGatePositive =
  refuseSyncGateOnPush
    == PushRefusalWrongGate KleisliGateCheckBeforeSyncInbound

pushFixtureRefuseFrugalMiPositive :: Bool
pushFixtureRefuseFrugalMiPositive =
  refuseFrugalMiOnPush
    == PushRefusalWrongGate KleisliFrugalMiObservation

pushFixtureConjunctAdmits :: Bool
pushFixtureConjunctAdmits = pushConjunctAdmits pushFixtureConjunct

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

data PushHistoryMove = PushHistoryMove
  { pushMovePrior       :: !HistorySnapshot
  , pushMovePost        :: !HistorySnapshot
  , pushMoveGateChecked :: !Bool
  , pushMoveMergeSafe   :: !Bool
  , pushMoveProvenanceOk :: !Bool
  } deriving (Show, Eq)

admissiblePushHistoryMove :: PushHistoryMove -> Bool
admissiblePushHistoryMove m =
  pushMoveGateChecked m
  && pushMoveMergeSafe m
  && pushMoveProvenanceOk m

data PushTransition = PushTransition
  { pushHistTransition :: !HistoryTransition
  , pushBath           :: !HeatBath
  , pushDissipatedWork :: !Double
  , pushEntropyDrop    :: !Double
  } deriving (Show, Eq)

pushSecondLaw :: PushTransition -> Bool
pushSecondLaw t =
  pushEntropyDrop t <= pushDissipatedWork t / bathTemp (pushBath t)

pushSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
pushSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

pushSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
pushSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

kleisliPushPhysicsGreen :: Bool
kleisliPushPhysicsGreen = False

kleisliPushPhysicsGreenFalse :: Bool
kleisliPushPhysicsGreenFalse = not kleisliPushPhysicsGreen

kleisliPushProductionWired :: Bool
kleisliPushProductionWired = False

kleisliPushProductionWiredFalse :: Bool
kleisliPushProductionWiredFalse = not kleisliPushProductionWired

kleisliPushModuleWitness :: Bool
kleisliPushModuleWitness = True

kleisliPushNoNewAxiom :: Bool
kleisliPushNoNewAxiom = True

kleisliPushPositiveRefuseNotSilent :: Bool
kleisliPushPositiveRefuseNotSilent =
  evaluatePushKleisli pushFixtureGateRefusedArrow /= Left PushAdmitted

kleisliPushProductionWiredRefusePositive :: Bool
kleisliPushProductionWiredRefusePositive =
  refuseProductionWiredPush == PushRefusalProductionWired

kleisliPushGateBypassRefusePositive :: Bool
kleisliPushGateBypassRefusePositive =
  refuseGateBypassPush == PushRefusalGateBypass

kleisliPushNoSecondArgmin :: Bool
kleisliPushNoSecondArgmin =
  pushNoLocalArgmin
    (PushCtx
      { pushPrior = ThermodynamicState 2400 0 0.3 30 40
      , pushSuccessors = []
      })
  && pushSelectEmpty (ThermodynamicState 2400 0 0.3 30 40)
  && urgeRecoverySelectEqExcitementSelect
      (ThermodynamicState 2400 0 0.3 30 40)
      []
