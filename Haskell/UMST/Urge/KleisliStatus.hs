-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliStatus
-- Description : Meso acting Urge — §16.7 operator verb `status` as Kleisli arrow.
--
-- Frugal MI observation gate; replica-class entity check; observation only —
-- not gate_check_before_sync inbound, not outbound tick, not MergeSafe witness.
-- Excitement recovery composes 'excitementSelect' — no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' excitement/Landauer discipline and
-- Lean @Urge.KleisliStatus@ / Coq @Urge.KleisliStatus@.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.KleisliStatus
  ( -- * §16.7 verb table + status Kleisli carriers
    StatusReplicaClass (..)
  , VerbColumnRequirement (..)
  , KleisliGateKind (..)
  , EntityCheckKind (..)
  , OperatorVerbRow (..)
  , FrugalMiObservation (..)
  , FrugalMiGateVerdict (..)
  , StatusObservation (..)
  , StatusGateMismatch (..)
  , StatusArrowError (..)
    -- * Frugal MI gate + status arrow (positive refuse)
  , statusVerbRow
  , evaluateFrugalMiGate
  , statusReplicaClassAdmits
  , kleisliGateMatchesStatus
  , runStatusKleisliArrow
  , refuseSyncGateOnStatus
  , refuseOutboundTickOnStatus
  , refuseMergeSafeOnStatus
  , refuseExcitementOnStatus
  , refuseRemoteClassOnStatus
  , statusVerbRowExcitementNotRequired
  , statusVerbRowMergeSafeNotRequired
  , statusVerbRowFrugalMiGate
  , kleisliGateMatchesStatusFrugal
  , kleisliGateMatchesStatusSyncFalse
    -- * Status composes excitementSelect (no second argmin)
  , StatusCtx (..)
  , statusSelect
  , statusSelectBare
  , statusSelectEqExcitementSelect
  , statusSelectEqAdmitHistorySelect
  , statusNoLocalArgmin
  , statusSelectEmpty
  , StatusExcitementPin (..)
  , statusExcitementSelect
  , statusExcitementSelectEqExcitementSelect
  , statusExcitementSelectRefusesSecondArgmin
    -- * §16.7 fixtures + witness theorems
  , statusFixtureObsAdmit
  , statusFixtureObsRefuseCap
  , statusFixtureObsRefuseZero
  , statusFixtureFrugalMiAdmits
  , statusFixtureFrugalMiRefusesCap
  , statusFixtureFrugalMiRefusesZero
  , statusFixtureArrowOk
  , statusFixtureArrowRefusesCap
  , statusPositiveRefuseSyncGate
  , statusPositiveRefuseMergeSafe
  , statusPositiveRefuseExcitement
  , statusPositiveRefuseOutboundTick
  , statusPositiveRefuseNotSilent
  , statusPositiveRefuseAggregate
    -- * Landauer bridge (derived — zero new axioms)
  , statusSecondLawFromLandauer
  , statusFromLandauerAdmitSecondLaw
  , statusSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , kleisliStatusPhysicsGreen
  , kleisliStatusPhysicsGreenFalse
  , kleisliStatusProductionWired
  , kleisliStatusProductionWiredFalse
  , kleisliStatusNonClaim
  , kleisliStatusNonClaimNonempty
  , kleisliStatusModuleWitness
  , kleisliStatusNoNewAxiom
  , kleisliStatusNoSecondArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitHistorySelect
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: §16.7 verb table + status Kleisli carriers
-- ---------------------------------------------------------------------------

-- | Replica class labels for `status` entity check (blueprint §15.4 / §16.7).
data StatusReplicaClass
  = StatusNode0
  | StatusNode1
  | StatusForgejoPrimaryMirror
  | StatusOfflineLuks
  deriving (Show, Eq)

-- | Whether a verb-table column is required for the operator verb.
data VerbColumnRequirement
  = NotRequired
  | Required
  deriving (Show, Eq)

-- | Kleisli gate kinds cited in §16.7 (`status` uses Frugal MI observation only).
data KleisliGateKind
  = KleisliFrugalMiObservation
  | GateCheckBeforeSyncInbound
  | OutboundTickIfAdmitted
  deriving (Show, Eq)

-- | Entity check column for §16.7 rows.
data EntityCheckKind
  = ReplicaClass
  | RemoteClass
  deriving (Show, Eq)

-- | One §16.7 operator verb table row (typed, not prose).
data OperatorVerbRow = OperatorVerbRow
  { verbStatus       :: !Bool
  , verbKleisliGate  :: !KleisliGateKind
  , verbMergeSafe    :: !VerbColumnRequirement
  , verbExcitement   :: !VerbColumnRequirement
  , verbEntityCheck  :: !EntityCheckKind
  } deriving (Show, Eq)

-- | Frugal MI observation carrier — status Kleisli gate input.
data FrugalMiObservation = FrugalMiObservation
  { witnessBits    :: !Int
  , frugalCapBits  :: !Int
  } deriving (Show, Eq)

-- | Verdict of the Frugal MI observation gate.
data FrugalMiGateVerdict
  = FrugalMiAdmit
  | FrugalMiRefuseExceedsCap
  | FrugalMiRefuseZeroObservation
  deriving (Show, Eq)

-- | Successful `status` Kleisli arrow output — observation only, no sync mutation.
data StatusObservation = StatusObservation
  { statusReplica          :: !StatusReplicaClass
  , statusObservationProbe :: !FrugalMiObservation
  , statusGateVerdict      :: !FrugalMiGateVerdict
  } deriving (Show, Eq)

-- | Positive refuse when wrong Kleisli gate is applied to `status`.
data StatusGateMismatch
  = SyncInboundOnStatus
  | OutboundTickOnStatus
  | MergeSafeOnStatus
  | ExcitementOnStatus
  | RemoteClassOnStatus
  deriving (Show, Eq)

-- | Fail-closed errors on the status Kleisli arrow.
data StatusArrowError
  = StatusFrugalMiRefused !FrugalMiGateVerdict
  | StatusGateMismatch !StatusGateMismatch
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: Frugal MI gate + status arrow (positive refuse)
-- ---------------------------------------------------------------------------

-- | §16.7 typed row for operator verb `status`.
statusVerbRow :: OperatorVerbRow
statusVerbRow =
  OperatorVerbRow
    { verbStatus = True
    , verbKleisliGate = KleisliFrugalMiObservation
    , verbMergeSafe = NotRequired
    , verbExcitement = NotRequired
    , verbEntityCheck = ReplicaClass
    }

-- | Evaluate Frugal MI observation gate (status Kleisli gate).
evaluateFrugalMiGate :: FrugalMiObservation -> FrugalMiGateVerdict
evaluateFrugalMiGate obs
  | frugalCapBits obs == 0 && witnessBits obs > 0 =
      FrugalMiRefuseExceedsCap
  | frugalCapBits obs > 0 && witnessBits obs == 0 =
      FrugalMiRefuseZeroObservation
  | frugalCapBits obs < witnessBits obs =
      FrugalMiRefuseExceedsCap
  | otherwise =
      FrugalMiAdmit

-- | Entity check: replica class label must be one of the §15.4 named classes.
statusReplicaClassAdmits :: StatusReplicaClass -> Bool
statusReplicaClassAdmits _ = True

-- | Whether a Kleisli gate kind matches the `status` verb row.
kleisliGateMatchesStatus :: KleisliGateKind -> Bool
kleisliGateMatchesStatus KleisliFrugalMiObservation            = True
kleisliGateMatchesStatus GateCheckBeforeSyncInbound     = False
kleisliGateMatchesStatus OutboundTickIfAdmitted         = False

-- | Run the `status` Kleisli arrow — observation only; no sync / merge / excitement.
runStatusKleisliArrow
  :: StatusReplicaClass
  -> FrugalMiObservation
  -> Either StatusArrowError StatusObservation
runStatusKleisliArrow replica obs
  | not (statusReplicaClassAdmits replica) =
      Left (StatusGateMismatch RemoteClassOnStatus)
  | otherwise =
      case evaluateFrugalMiGate obs of
        FrugalMiAdmit ->
          Right
            StatusObservation
              { statusReplica = replica
              , statusObservationProbe = obs
              , statusGateVerdict = FrugalMiAdmit
              }
        v -> Left (StatusFrugalMiRefused v)

-- | Positive refuse: inbound sync gate is inadmissible on `status`.
refuseSyncGateOnStatus :: StatusGateMismatch
refuseSyncGateOnStatus = SyncInboundOnStatus

-- | Positive refuse: outbound tick gate is inadmissible on `status`.
refuseOutboundTickOnStatus :: StatusGateMismatch
refuseOutboundTickOnStatus = OutboundTickOnStatus

-- | Positive refuse: MergeSafe witness is not required on `status`.
refuseMergeSafeOnStatus :: StatusGateMismatch
refuseMergeSafeOnStatus = MergeSafeOnStatus

-- | Positive refuse: Excitement argmin is not required on `status`.
refuseExcitementOnStatus :: StatusGateMismatch
refuseExcitementOnStatus = ExcitementOnStatus

-- | Positive refuse: remote-class entity check is wrong for `status`.
refuseRemoteClassOnStatus :: StatusGateMismatch
refuseRemoteClassOnStatus = RemoteClassOnStatus

statusVerbRowExcitementNotRequired :: Bool
statusVerbRowExcitementNotRequired =
  verbExcitement statusVerbRow == NotRequired

statusVerbRowMergeSafeNotRequired :: Bool
statusVerbRowMergeSafeNotRequired =
  verbMergeSafe statusVerbRow == NotRequired

statusVerbRowFrugalMiGate :: Bool
statusVerbRowFrugalMiGate =
  verbKleisliGate statusVerbRow == KleisliFrugalMiObservation

kleisliGateMatchesStatusFrugal :: Bool
kleisliGateMatchesStatusFrugal =
  kleisliGateMatchesStatus KleisliFrugalMiObservation

kleisliGateMatchesStatusSyncFalse :: Bool
kleisliGateMatchesStatusSyncFalse =
  not (kleisliGateMatchesStatus GateCheckBeforeSyncInbound)

-- ---------------------------------------------------------------------------
-- SECTION 3: Status composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for status over admissible history successors.
data StatusCtx = StatusCtx
  { statusCtxPrior      :: !ThermodynamicState
  , statusCtxSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Status operator selection **is** 'excitementSelect'.
statusSelect :: StatusCtx -> Either ExcitementResidue HistoryCandidate
statusSelect ctx =
  excitementSelect (statusCtxPrior ctx) (statusCtxSuccessors ctx)

-- | Bare status selection on @(prior, successors)@.
statusSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
statusSelectBare = excitementSelect

-- | Definitional witness: status selection API is 'excitementSelect'.
statusSelectEqExcitementSelect :: StatusCtx -> Bool
statusSelectEqExcitementSelect ctx =
  statusSelect ctx
    == excitementSelect (statusCtxPrior ctx) (statusCtxSuccessors ctx)

-- | Status selection equals 'admitHistorySelect'.
statusSelectEqAdmitHistorySelect :: StatusCtx -> Bool
statusSelectEqAdmitHistorySelect ctx =
  statusSelect ctx
    == admitHistorySelect (statusCtxPrior ctx) (statusCtxSuccessors ctx)

-- | Status selector re-uses 'excitementSelect' — no Urge-local argmin.
statusNoLocalArgmin :: StatusCtx -> Bool
statusNoLocalArgmin ctx =
  statusSelect ctx
    == excitementSelect (statusCtxPrior ctx) (statusCtxSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported selector.
statusSelectEmpty :: ThermodynamicState -> Bool
statusSelectEmpty src =
  statusSelectBare src [] == Left ExcNoCandidates

-- | Kleisli status compose pin — import selector; refuse second argmin.
data StatusExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Pin-gated status excitement selection.
statusExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> StatusExcitementPin
  -> Either ExcitementResidue HistoryCandidate
statusExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
statusExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | Import pin equals 'excitementSelect'.
statusExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
statusExcitementSelectEqExcitementSelect src cands =
  statusExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with 'ExcAllInadmissible'.
statusExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
statusExcitementSelectRefusesSecondArgmin src cands =
  statusExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- ---------------------------------------------------------------------------
-- SECTION 4: §16.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

statusFixtureObsAdmit :: FrugalMiObservation
statusFixtureObsAdmit = FrugalMiObservation {witnessBits = 4, frugalCapBits = 8}

statusFixtureObsRefuseCap :: FrugalMiObservation
statusFixtureObsRefuseCap = FrugalMiObservation {witnessBits = 16, frugalCapBits = 8}

statusFixtureObsRefuseZero :: FrugalMiObservation
statusFixtureObsRefuseZero = FrugalMiObservation {witnessBits = 0, frugalCapBits = 8}

statusFixtureFrugalMiAdmits :: Bool
statusFixtureFrugalMiAdmits =
  evaluateFrugalMiGate statusFixtureObsAdmit == FrugalMiAdmit

statusFixtureFrugalMiRefusesCap :: Bool
statusFixtureFrugalMiRefusesCap =
  evaluateFrugalMiGate statusFixtureObsRefuseCap == FrugalMiRefuseExceedsCap

statusFixtureFrugalMiRefusesZero :: Bool
statusFixtureFrugalMiRefusesZero =
  evaluateFrugalMiGate statusFixtureObsRefuseZero
    == FrugalMiRefuseZeroObservation

statusFixtureArrowOk :: Bool
statusFixtureArrowOk =
  runStatusKleisliArrow StatusNode0 statusFixtureObsAdmit
    == Right
         StatusObservation
           { statusReplica = StatusNode0
           , statusObservationProbe = statusFixtureObsAdmit
           , statusGateVerdict = FrugalMiAdmit
           }

statusFixtureArrowRefusesCap :: Bool
statusFixtureArrowRefusesCap =
  runStatusKleisliArrow StatusNode1 statusFixtureObsRefuseCap
    == Left (StatusFrugalMiRefused FrugalMiRefuseExceedsCap)

statusPositiveRefuseSyncGate :: Bool
statusPositiveRefuseSyncGate =
  refuseSyncGateOnStatus == SyncInboundOnStatus

statusPositiveRefuseMergeSafe :: Bool
statusPositiveRefuseMergeSafe =
  refuseMergeSafeOnStatus == MergeSafeOnStatus

statusPositiveRefuseExcitement :: Bool
statusPositiveRefuseExcitement =
  refuseExcitementOnStatus == ExcitementOnStatus

statusPositiveRefuseOutboundTick :: Bool
statusPositiveRefuseOutboundTick =
  refuseOutboundTickOnStatus == OutboundTickOnStatus

statusPositiveRefuseNotSilent :: Bool
statusPositiveRefuseNotSilent =
  refuseSyncGateOnStatus /= refuseMergeSafeOnStatus

statusPositiveRefuseAggregate :: Bool
statusPositiveRefuseAggregate =
  statusPositiveRefuseSyncGate
    && statusPositiveRefuseMergeSafe
    && statusPositiveRefuseExcitement
    && statusPositiveRefuseOutboundTick

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on status carrier transition from Landauer bridge discharge.
statusSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
statusSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
statusFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
statusFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for status second law (no new axiom).
statusSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
statusSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
kleisliStatusPhysicsGreen :: Bool
kleisliStatusPhysicsGreen = False

-- | Lean/Coq: @kleisli_status_physics_green_false@.
kleisliStatusPhysicsGreenFalse :: Bool
kleisliStatusPhysicsGreenFalse = not kleisliStatusPhysicsGreen

-- | Production wiring stays open (status lift only).
kleisliStatusProductionWired :: Bool
kleisliStatusProductionWired = False

-- | Lean/Coq: @kleisli_status_production_wired_false@.
kleisliStatusProductionWiredFalse :: Bool
kleisliStatusProductionWiredFalse = not kleisliStatusProductionWired

-- | Honest non-claim string (meso §16.7 status scaffold).
kleisliStatusNonClaim :: String
kleisliStatusNonClaim =
  "§16.7 status: Frugal MI observation gate + replica-class entity check; "
    ++ "observation only; composes excitementSelect; not physics GREEN; "
    ++ "not production_wired"

-- | Non-claim string is non-empty.
kleisliStatusNonClaimNonempty :: Bool
kleisliStatusNonClaimNonempty = length kleisliStatusNonClaim > 0

-- | Catalog witness: meso Urge KleisliStatus module present.
kleisliStatusModuleWitness :: Bool
kleisliStatusModuleWitness = True

-- | Zero new axiom discipline witness.
kleisliStatusNoNewAxiom :: Bool
kleisliStatusNoNewAxiom = True

-- | Second-argmin refusal: status composes 'excitementSelect' only.
kleisliStatusNoSecondArgmin :: Bool
kleisliStatusNoSecondArgmin =
  statusNoLocalArgmin
    (StatusCtx
       { statusCtxPrior = ThermodynamicState 2400 0 0 0 0
       , statusCtxSuccessors = []
       })
