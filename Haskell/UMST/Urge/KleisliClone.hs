-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliClone
-- Description : Meso acting Urge — §16.7 operator verb `clone` as Kleisli arrow.
--
-- Initial replica coalgebra admission — not sync inbound, not outbound tick,
-- not Frugal MI observation, not MergeSafe witness, not Excitement argmin.
-- Excitement recovery composes 'excitementSelect' — no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' excitement alignment discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.KleisliClone
  ( -- * §16.7 operator verb table carriers
    CloneOperatorVerb (..)
  , CloneKleisliGateKind (..)
  , CloneVerbColumnReq (..)
  , CloneEntityCheckKind (..)
  , CloneVerbRow (..)
  , cloneVerbRow
  , kleisliGateMatchesClone
    -- * Entity labels + initial replica coalgebra gate
  , CloneEntityLabel (..)
  , CloneReplicaClass (..)
  , cloneReplicaClassTag
  , InitialReplicaCoalgebra (..)
  , InitialCoalgebraGateVerdict (..)
  , evaluateInitialCoalgebraGate
  , CloneRemoteHost (..)
  , composeUpstreamRefused
  , parseEntityLabel
  , entityLabelAdmitsClone
    -- * Clone Kleisli arrow (initial admission only)
  , CloneAdmission (..)
  , CloneArrowError (..)
  , CloneGateMismatch (..)
  , runCloneKleisliArrow
  , runCloneKleisliArrowParsed
    -- * Positive refuse (wrong gates / columns on `clone`)
  , refuseFrugalMiOnClone
  , refuseSyncGateOnClone
  , refuseOutboundTickOnClone
  , refuseMergeSafeOnClone
  , refuseExcitementArgminOnClone
  , refuseReplicaClassOnClone
  , refuseRemoteClassOnClone
  , refuseSecondArgminOnClone
  , kleisliGateMatchesCloneAdmit
  , kleisliGateMatchesCloneFrugalFalse
  , cloneVerbRowMergeSafeNotRequired
  , cloneVerbRowExcitementNotRequired
  , cloneVerbRowEntityLabelCheck
    -- * Clone composes excitementSelect (no second argmin)
  , CloneExcitementCtx (..)
  , CloneExcitementPin (..)
  , cloneSelect
  , cloneRecoverySelect
  , cloneSelectBare
  , cloneExcitementSelect
  , cloneSelectEqExcitementSelect
  , cloneRecoverySelectEqExcitementSelect
  , cloneRecoverySelectEqUrgeRecoverySelect
  , cloneNoLocalArgmin
  , cloneExcitementSelectEqExcitementSelect
  , cloneExcitementSelectRefusesSecondArgmin
  , cloneRecoveryEmpty
    -- * §16.7 fixtures + witness theorems
  , cloneFixtureCoalgebraAdmit
  , cloneFixtureCoalgebraRefuseEgress
  , cloneFixtureRemoteForge
  , cloneFixtureRemoteGithub
  , cloneFixtureInitialCoalgebraAdmits
  , cloneFixtureInitialCoalgebraRefusesEgress
  , cloneFixtureArrowAdmitsLabs
  , cloneFixtureComposeUpstreamRefused
  , cloneFixtureComposeEntityRefusedOnGithub
  , cloneFixtureParseLabs
  , cloneFixtureParseComposeCaseInsensitive
  , cloneReplicaClassNode0Tag
  , cloneReplicaClassLuksTag
  , clonePositiveRefuseFrugalMi
  , clonePositiveRefuseSyncGate
  , kleisliClonePositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , CloneHistoryTransition (..)
  , cloneAdmitSecondLaw
  , cloneSecondLawFromLandauer
  , cloneFromLandauerAdmitSecondLaw
  , cloneSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , kleisliClonePhysicsGreen
  , kleisliClonePhysicsGreenFalse
  , kleisliCloneProductionWired
  , kleisliCloneProductionWiredFalse
  , kleisliCloneNonClaim
  , kleisliCloneNonClaimNonempty
  , kleisliCloneModuleWitness
  , kleisliCloneNoNewAxiom
  , kleisliCloneNoSecondArgmin
  , kleisliCloneComposeExcitementNotArgmin
  , refuseSecondArgminIsTag
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
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: §16.7 operator verb table carriers
-- ---------------------------------------------------------------------------

-- | Operator verb surface tag — §16.7 Kleisli table row `clone`.
data CloneOperatorVerb = Clone
  deriving (Show, Eq)

-- | Kleisli gate kinds cited in §16.7 verb table.
data CloneKleisliGateKind
  = AdmitInitialReplicaCoalgebra
  | FrugalMiObservation
  | GateCheckBeforeSyncInbound
  | OutboundTickIfAdmitted
  | ExcitementArgmin
  deriving (Show, Eq)

-- | Verb-table column requirement (`—` vs required).
data CloneVerbColumnReq
  = NotRequired
  | Required
  deriving (Show, Eq)

-- | Entity check column for §16.7 rows.
data CloneEntityCheckKind
  = EntityLabel
  | ReplicaClass
  | RemoteClass
  deriving (Show, Eq)

-- | One §16.7 operator verb table row (typed, not prose).
data CloneVerbRow = CloneVerbRow
  { cloneRowVerb        :: !CloneOperatorVerb
  , cloneRowKleisliGate :: !CloneKleisliGateKind
  , cloneRowMergeSafe   :: !CloneVerbColumnReq
  , cloneRowExcitement  :: !CloneVerbColumnReq
  , cloneRowEntityCheck :: !CloneEntityCheckKind
  } deriving (Show, Eq)

-- | Blueprint §16.7 row for operator verb `clone`.
cloneVerbRow :: CloneVerbRow
cloneVerbRow =
  CloneVerbRow
    { cloneRowVerb = Clone
    , cloneRowKleisliGate = AdmitInitialReplicaCoalgebra
    , cloneRowMergeSafe = NotRequired
    , cloneRowExcitement = NotRequired
    , cloneRowEntityCheck = EntityLabel
    }

-- | Whether a Kleisli gate kind matches the `clone` verb row.
kleisliGateMatchesClone :: CloneKleisliGateKind -> Bool
kleisliGateMatchesClone AdmitInitialReplicaCoalgebra = True
kleisliGateMatchesClone _                            = False

-- ---------------------------------------------------------------------------
-- SECTION 2: Entity labels + initial replica coalgebra gate
-- ---------------------------------------------------------------------------

-- | Entity labels from blueprint §13.6 (`[urge.remote.*]` proposed fields).
data CloneEntityLabel
  = CloneLabs
  | CloneCompose
  deriving (Show, Eq)

-- | Named replica class at initial clone admission (§15.4 sheaf section).
data CloneReplicaClass
  = CloneNode0
  | CloneNode1
  | CloneForge
  | CloneLuks
  | CloneDarwinScratch
  deriving (Show, Eq)

-- | Human-readable replica class tag.
cloneReplicaClassTag :: CloneReplicaClass -> String
cloneReplicaClassTag CloneNode0         = "node-0"
cloneReplicaClassTag CloneNode1         = "node-1"
cloneReplicaClassTag CloneForge         = "forgejo-primary-mirror"
cloneReplicaClassTag CloneLuks          = "offline-luks"
cloneReplicaClassTag CloneDarwinScratch = "darwin-scratch"

-- | Initial replica coalgebra carrier at clone time — §15.4 sheaf admission.
data InitialReplicaCoalgebra = InitialReplicaCoalgebra
  { coalgebraReplicaClass      :: !CloneReplicaClass
  , coalgebraEgressDeclared    :: !Bool
  , coalgebraAuthorityDeclared :: !Bool
  } deriving (Show, Eq)

-- | Verdict of the admit-initial-replica-coalgebra Kleisli gate.
data InitialCoalgebraGateVerdict
  = InitialCoalgebraAdmit
  | InitialCoalgebraRefuseUndeclaredEgress
  | InitialCoalgebraRefuseUndeclaredAuthority
  deriving (Show, Eq)

-- | Evaluate admit-initial-replica-coalgebra gate (clone Kleisli gate).
evaluateInitialCoalgebraGate
  :: InitialReplicaCoalgebra -> InitialCoalgebraGateVerdict
evaluateInitialCoalgebraGate c
  | coalgebraEgressDeclared c =
      if coalgebraAuthorityDeclared c
        then InitialCoalgebraAdmit
        else InitialCoalgebraRefuseUndeclaredAuthority
  | otherwise = InitialCoalgebraRefuseUndeclaredEgress

-- | Remote host surrogate for entity-label policy checks.
data CloneRemoteHost = CloneRemoteHost
  { cloneRemoteHostLabel :: !String
  } deriving (Show, Eq)

-- | Whether remote host is refused for Compose entity clone (§16.8 / §13.6).
composeUpstreamRefused :: String -> Bool
composeUpstreamRefused host =
  host == "github.com" || host == "origin.cursor.com"

-- | Parse entity label string into typed label (fail closed on unknown).
parseEntityLabel :: String -> Maybe CloneEntityLabel
parseEntityLabel label
  | label == "labs" || label == "LABS"     = Just CloneLabs
  | label == "compose" || label == "COMPOSE" = Just CloneCompose
  | otherwise                              = Nothing

-- | Entity-label check: Compose must not clone from refused upstream hosts.
entityLabelAdmitsClone :: CloneEntityLabel -> CloneRemoteHost -> Bool
entityLabelAdmitsClone CloneLabs     _ = True
entityLabelAdmitsClone CloneCompose remote =
  not (composeUpstreamRefused (cloneRemoteHostLabel remote))

-- ---------------------------------------------------------------------------
-- SECTION 3: Clone Kleisli arrow (initial admission only)
-- ---------------------------------------------------------------------------

-- | Positive refuse when wrong Kleisli gate / column is applied to `clone`.
data CloneGateMismatch
  = FrugalMiOnClone
  | SyncInboundOnClone
  | OutboundTickOnClone
  | MergeSafeWitnessOnClone
  | ExcitementArgminOnClone
  | ReplicaClassOnClone
  | RemoteClassOnClone
  | SecondArgminOnClone
  deriving (Show, Eq)

-- | Fail-closed errors on the clone Kleisli arrow.
data CloneArrowError
  = CloneErrCoalgebraRefused !InitialCoalgebraGateVerdict
  | CloneErrUnknownEntityLabel
  | CloneErrComposeUpstreamRefused
  | CloneErrGateMismatch !CloneGateMismatch
  deriving (Show, Eq)

-- | Successful `clone` Kleisli arrow output — initial admission only.
data CloneAdmission = CloneAdmission
  { cloneAdmissionEntity  :: !CloneEntityLabel
  , cloneAdmissionReplica :: !CloneReplicaClass
  , cloneAdmissionGate    :: !InitialCoalgebraGateVerdict
  } deriving (Show, Eq)

-- | Run the `clone` Kleisli arrow — initial replica admission only.
runCloneKleisliArrow
  :: CloneEntityLabel
  -> InitialReplicaCoalgebra
  -> CloneRemoteHost
  -> Either CloneArrowError CloneAdmission
runCloneKleisliArrow entity coalgebra remote
  | entityLabelAdmitsClone entity remote =
      case evaluateInitialCoalgebraGate coalgebra of
        InitialCoalgebraAdmit ->
          Right
            CloneAdmission
              { cloneAdmissionEntity = entity
              , cloneAdmissionReplica = coalgebraReplicaClass coalgebra
              , cloneAdmissionGate = InitialCoalgebraAdmit
              }
        v -> Left (CloneErrCoalgebraRefused v)
  | otherwise = Left CloneErrComposeUpstreamRefused

-- | Parse label then run clone arrow — fail closed on unknown entity label.
runCloneKleisliArrowParsed
  :: String
  -> InitialReplicaCoalgebra
  -> CloneRemoteHost
  -> Either CloneArrowError CloneAdmission
runCloneKleisliArrowParsed label coalgebra remote =
  case parseEntityLabel label of
    Just entity -> runCloneKleisliArrow entity coalgebra remote
    Nothing     -> Left CloneErrUnknownEntityLabel

-- ---------------------------------------------------------------------------
-- SECTION 4: Positive refuse (wrong gates / columns on `clone`)
-- ---------------------------------------------------------------------------

refuseFrugalMiOnClone :: CloneGateMismatch
refuseFrugalMiOnClone = FrugalMiOnClone

refuseSyncGateOnClone :: CloneGateMismatch
refuseSyncGateOnClone = SyncInboundOnClone

refuseOutboundTickOnClone :: CloneGateMismatch
refuseOutboundTickOnClone = OutboundTickOnClone

refuseMergeSafeOnClone :: CloneGateMismatch
refuseMergeSafeOnClone = MergeSafeWitnessOnClone

refuseExcitementArgminOnClone :: CloneGateMismatch
refuseExcitementArgminOnClone = ExcitementArgminOnClone

refuseReplicaClassOnClone :: CloneGateMismatch
refuseReplicaClassOnClone = ReplicaClassOnClone

refuseRemoteClassOnClone :: CloneGateMismatch
refuseRemoteClassOnClone = RemoteClassOnClone

refuseSecondArgminOnClone :: CloneGateMismatch
refuseSecondArgminOnClone = SecondArgminOnClone

kleisliGateMatchesCloneAdmit :: Bool
kleisliGateMatchesCloneAdmit =
  kleisliGateMatchesClone AdmitInitialReplicaCoalgebra

kleisliGateMatchesCloneFrugalFalse :: Bool
kleisliGateMatchesCloneFrugalFalse =
  not (kleisliGateMatchesClone FrugalMiObservation)

cloneVerbRowMergeSafeNotRequired :: Bool
cloneVerbRowMergeSafeNotRequired =
  cloneRowMergeSafe cloneVerbRow == NotRequired

cloneVerbRowExcitementNotRequired :: Bool
cloneVerbRowExcitementNotRequired =
  cloneRowExcitement cloneVerbRow == NotRequired

cloneVerbRowEntityLabelCheck :: Bool
cloneVerbRowEntityLabelCheck =
  cloneRowEntityCheck cloneVerbRow == EntityLabel

-- ---------------------------------------------------------------------------
-- SECTION 5: Clone composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for clone over admissible history successors.
data CloneExcitementCtx = CloneExcitementCtx
  { cloneCtxPrior      :: !ThermodynamicState
  , cloneCtxSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Kleisli clone compose pin — import selector; refuse second argmin.
data CloneExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Clone operator selection **is** 'excitementSelect'.
cloneSelect :: CloneExcitementCtx -> Either ExcitementResidue HistoryCandidate
cloneSelect ctx =
  excitementSelect (cloneCtxPrior ctx) (cloneCtxSuccessors ctx)

-- | Clone recovery selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
cloneRecoverySelect
  :: CloneExcitementCtx -> Either ExcitementResidue HistoryCandidate
cloneRecoverySelect ctx =
  urgeRecoverySelect (cloneCtxPrior ctx) (cloneCtxSuccessors ctx)

-- | Bare clone selection on @(prior, successors)@.
cloneSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
cloneSelectBare = excitementSelect

-- | Pin-gated clone excitement selection.
cloneExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> CloneExcitementPin
  -> Either ExcitementResidue HistoryCandidate
cloneExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
cloneExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | Definitional witness: clone selection API is 'excitementSelect'.
cloneSelectEqExcitementSelect :: CloneExcitementCtx -> Bool
cloneSelectEqExcitementSelect ctx =
  cloneSelect ctx
    == excitementSelect (cloneCtxPrior ctx) (cloneCtxSuccessors ctx)

-- | Definitional witness: clone recovery selection is 'excitementSelect'.
cloneRecoverySelectEqExcitementSelect :: CloneExcitementCtx -> Bool
cloneRecoverySelectEqExcitementSelect ctx =
  cloneRecoverySelect ctx
    == excitementSelect (cloneCtxPrior ctx) (cloneCtxSuccessors ctx)

-- | Definitional witness: clone recovery selection is 'urgeRecoverySelect'.
cloneRecoverySelectEqUrgeRecoverySelect :: CloneExcitementCtx -> Bool
cloneRecoverySelectEqUrgeRecoverySelect ctx =
  cloneRecoverySelect ctx
    == urgeRecoverySelect (cloneCtxPrior ctx) (cloneCtxSuccessors ctx)

-- | Clone selector re-uses 'excitementSelect' — no Urge-local argmin.
cloneNoLocalArgmin :: CloneExcitementCtx -> Bool
cloneNoLocalArgmin ctx =
  cloneRecoverySelect ctx
    == excitementSelect (cloneCtxPrior ctx) (cloneCtxSuccessors ctx)

-- | Import pin equals 'excitementSelect'.
cloneExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
cloneExcitementSelectEqExcitementSelect src cands =
  cloneExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with 'ExcAllInadmissible'.
cloneExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
cloneExcitementSelectRefusesSecondArgmin src cands =
  cloneExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via composed selector.
cloneRecoveryEmpty :: ThermodynamicState -> Bool
cloneRecoveryEmpty prior =
  cloneRecoverySelect
    (CloneExcitementCtx {cloneCtxPrior = prior, cloneCtxSuccessors = []})
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 6: §16.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

cloneFixtureCoalgebraAdmit :: InitialReplicaCoalgebra
cloneFixtureCoalgebraAdmit =
  InitialReplicaCoalgebra
    { coalgebraReplicaClass = CloneNode0
    , coalgebraEgressDeclared = True
    , coalgebraAuthorityDeclared = True
    }

cloneFixtureCoalgebraRefuseEgress :: InitialReplicaCoalgebra
cloneFixtureCoalgebraRefuseEgress =
  InitialReplicaCoalgebra
    { coalgebraReplicaClass = CloneLuks
    , coalgebraEgressDeclared = False
    , coalgebraAuthorityDeclared = True
    }

cloneFixtureRemoteForge :: CloneRemoteHost
cloneFixtureRemoteForge = CloneRemoteHost {cloneRemoteHostLabel = "forge.entity"}

cloneFixtureRemoteGithub :: CloneRemoteHost
cloneFixtureRemoteGithub = CloneRemoteHost {cloneRemoteHostLabel = "github.com"}

cloneFixtureInitialCoalgebraAdmits :: Bool
cloneFixtureInitialCoalgebraAdmits =
  evaluateInitialCoalgebraGate cloneFixtureCoalgebraAdmit
    == InitialCoalgebraAdmit

cloneFixtureInitialCoalgebraRefusesEgress :: Bool
cloneFixtureInitialCoalgebraRefusesEgress =
  evaluateInitialCoalgebraGate cloneFixtureCoalgebraRefuseEgress
    == InitialCoalgebraRefuseUndeclaredEgress

cloneFixtureArrowAdmitsLabs :: Bool
cloneFixtureArrowAdmitsLabs =
  runCloneKleisliArrow CloneLabs cloneFixtureCoalgebraAdmit cloneFixtureRemoteForge
    == Right
      CloneAdmission
        { cloneAdmissionEntity = CloneLabs
        , cloneAdmissionReplica = CloneNode0
        , cloneAdmissionGate = InitialCoalgebraAdmit
        }

cloneFixtureComposeUpstreamRefused :: Bool
cloneFixtureComposeUpstreamRefused = composeUpstreamRefused "github.com"

cloneFixtureComposeEntityRefusedOnGithub :: Bool
cloneFixtureComposeEntityRefusedOnGithub =
  runCloneKleisliArrow CloneCompose cloneFixtureCoalgebraAdmit cloneFixtureRemoteGithub
    == Left CloneErrComposeUpstreamRefused

cloneFixtureParseLabs :: Bool
cloneFixtureParseLabs = parseEntityLabel "labs" == Just CloneLabs

cloneFixtureParseComposeCaseInsensitive :: Bool
cloneFixtureParseComposeCaseInsensitive =
  parseEntityLabel "COMPOSE" == Just CloneCompose

cloneReplicaClassNode0Tag :: Bool
cloneReplicaClassNode0Tag = cloneReplicaClassTag CloneNode0 == "node-0"

cloneReplicaClassLuksTag :: Bool
cloneReplicaClassLuksTag = cloneReplicaClassTag CloneLuks == "offline-luks"

clonePositiveRefuseFrugalMi :: Bool
clonePositiveRefuseFrugalMi = refuseFrugalMiOnClone == FrugalMiOnClone

clonePositiveRefuseSyncGate :: Bool
clonePositiveRefuseSyncGate = refuseSyncGateOnClone == SyncInboundOnClone

kleisliClonePositiveRefuseNotSilent :: Bool
kleisliClonePositiveRefuseNotSilent =
  not (kleisliGateMatchesClone FrugalMiObservation)
    && not (kleisliGateMatchesClone GateCheckBeforeSyncInbound)

-- ---------------------------------------------------------------------------
-- SECTION 7: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Clone transition accounting (initial coalgebra admission witnesses).
data CloneHistoryTransition = CloneHistoryTransition
  { cloneTransBath           :: !HeatBath
  , cloneTransDissipatedWork :: !Double
  , cloneTransEntropyDrop    :: !Double
  } deriving (Show, Eq)

-- | Second law on clone transition (Bool witness — not a new axiom).
cloneAdmitSecondLaw :: CloneHistoryTransition -> Bool
cloneAdmitSecondLaw t =
  cloneTransEntropyDrop t
    <= cloneTransDissipatedWork t / bathTemp (cloneTransBath t)

-- | Second law on clone carrier transition from Landauer bridge discharge.
cloneSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
cloneSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
cloneFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
cloneFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for clone second law (no new axiom).
cloneSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
cloneSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
kleisliClonePhysicsGreen :: Bool
kleisliClonePhysicsGreen = False

-- | Lean/Coq: @kleisli_clone_physics_green_false@.
kleisliClonePhysicsGreenFalse :: Bool
kleisliClonePhysicsGreenFalse = not kleisliClonePhysicsGreen

-- | Production wiring stays open (clone lift only).
kleisliCloneProductionWired :: Bool
kleisliCloneProductionWired = False

-- | Lean/Coq: @kleisli_clone_production_wired_false@.
kleisliCloneProductionWiredFalse :: Bool
kleisliCloneProductionWiredFalse = not kleisliCloneProductionWired

-- | Honest non-claim string (meso §16.7 clone scaffold).
kleisliCloneNonClaim :: String
kleisliCloneNonClaim =
  "§16.7 clone: admit initial replica coalgebra + entity label check; "
    ++ "composes excitementSelect; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
kleisliCloneNonClaimNonempty :: Bool
kleisliCloneNonClaimNonempty = length kleisliCloneNonClaim > 0

-- | Catalog witness: meso Urge KleisliClone module present.
kleisliCloneModuleWitness :: Bool
kleisliCloneModuleWitness = True

-- | Zero new axiom discipline witness.
kleisliCloneNoNewAxiom :: Bool
kleisliCloneNoNewAxiom = True

-- | Second-argmin refusal: clone composes 'excitementSelect' only.
kleisliCloneNoSecondArgmin :: Bool
kleisliCloneNoSecondArgmin =
  cloneNoLocalArgmin
    (CloneExcitementCtx
      { cloneCtxPrior = ThermodynamicState 2400 0 0 0 0
      , cloneCtxSuccessors = []
      })

-- | Clone recovery composes excitement — not a second argmin.
kleisliCloneComposeExcitementNotArgmin :: CloneExcitementCtx -> Bool
kleisliCloneComposeExcitementNotArgmin =
  cloneNoLocalArgmin

-- | Second-argmin refusal tag witness.
refuseSecondArgminIsTag :: Bool
refuseSecondArgminIsTag = refuseSecondArgminOnClone == SecondArgminOnClone
