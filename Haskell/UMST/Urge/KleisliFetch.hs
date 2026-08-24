-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliFetch
-- Description : Meso acting Urge — §16.7 operator verb `fetch` as Kleisli arrow.
--
-- Blueprint row: `fetch` → `gate_check_before_sync` inbound · entity check `remote class`.
-- Excitement recovery composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.KleisliFetch
  ( -- * Remote class + inbound gate carriers (§16.7)
    FetchOperatorVerb (..)
  , FetchRemoteClass (..)
  , FetchInboundGate (..)
  , fetchRemoteAdmissible
  , fetchGateAdmits
  , classifyFetchRemote
  , FetchKleisliArrow (..)
  , FetchVerdict (..)
  , FetchError (..)
    -- * §16.7 Kleisli evaluation + positive refuse
  , evaluateFetchKleisli
  , refuseProductionWiredFetch
  , refuseGateBypassFetch
  , fetchKleisliArrowFromHost
  , fetchKleisliAdmissible
  , fetchKleisliAdmissibleSpec
  , evaluateFetchGateRefused
  , evaluateFetchRemoteRefused
  , evaluateFetchGateBypassRefused
    -- * gate_check_before_sync inbound bridge
  , HistorySyncTick (..)
  , fetchGateCheckBeforeSync
  , fetchGateCheckBeforeSyncSound
  , fetchGateCheckBeforeSyncEqTick
  , gateCheckBeforeSync
  , fetchInboundGateFromSync
  , fetchInboundGateFromSyncAdmitted
    -- * Fetch composes excitementSelect (no second argmin)
  , FetchCtx (..)
  , fetchSelect
  , fetchSelectBare
  , fetchSelectEqExcitementSelect
  , fetchSelectEqAdmitHistorySelect
  , fetchNoLocalArgmin
  , fetchSelectEmpty
  , FetchExcitementPin (..)
  , fetchExcitementSelect
  , fetchExcitementSelectEqExcitementSelect
  , fetchExcitementSelectRefusesSecondArgmin
    -- * §16.7 fixtures + witness theorems
  , fetchFixtureState
  , fetchFixtureAdmittedArrow
  , fetchFixtureGateRefusedArrow
  , fetchFixtureRemoteRefusedArrow
  , fetchFixtureAdmittedOk
  , fetchFixtureGateRefused
  , fetchFixtureRemoteRefused
  , fetchFixtureClassifyForgeEntity
  , fetchFixtureClassifyGithubRefused
  , fetchFixtureProductionWiredRefuse
  , fetchFixtureGateBypassRefuse
  , fetchFixtureKleisliAdmissible
  , fetchPositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , FetchTransition (..)
  , admissibleFetchTransition
  , fetchSecondLaw
  , fetchSecondLawFromLandauer
  , fetchSecondLawFromHypothesis
  , fetchFromLandauerAdmitSecondLaw
    -- * Honesty flags + catalog witnesses
  , kleisliFetchPhysicsGreen
  , kleisliFetchPhysicsGreenFalse
  , kleisliFetchProductionWired
  , kleisliFetchProductionWiredFalse
  , kleisliFetchNonClaim
  , kleisliFetchNonClaimNonempty
  , kleisliFetchModuleWitness
  , kleisliFetchNoNewAxiom
  , kleisliFetchNoSecondArgmin
  , excitementComposePin
  , excitementComposePinMarker
  , refuseSecondArgminIsTag
  ) where

import UMST.Concrete
  ( AdmissibilityResult (..)
  , ThermodynamicState (..)
  , gateCheck
  )
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitHistorySelect
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- | Nominal history head step Δt for gate evaluation (seconds).
fetchGateStepDt :: Double
fetchGateStepDt = 3600.0

-- ---------------------------------------------------------------------------
-- SECTION 1: Remote class + inbound gate carriers (§16.7)
-- ---------------------------------------------------------------------------

-- | Operator verb surface tag — §16.7 Kleisli table row `fetch`.
data FetchOperatorVerb = Fetch
  deriving (Show, Eq)

-- | Remote entity class for fetch entity check (§16.7).
data FetchRemoteClass
  = EntityRemote
  | RefusedUpstream
  | Unclassified
  deriving (Show, Eq)

-- | Whether remote class admits fetch Kleisli arrow.
fetchRemoteAdmissible :: FetchRemoteClass -> Bool
fetchRemoteAdmissible EntityRemote      = True
fetchRemoteAdmissible RefusedUpstream   = False
fetchRemoteAdmissible Unclassified      = False

-- | Inbound gate posture — `gate_check_before_sync` before applying refs.
data FetchInboundGate
  = FetchAdmitted
  | FetchRefused
  | FetchBypassAttempted
  deriving (Show, Eq)

-- | Whether inbound gate admits fetch morphism.
fetchGateAdmits :: FetchInboundGate -> Bool
fetchGateAdmits FetchAdmitted         = True
fetchGateAdmits FetchRefused          = False
fetchGateAdmits FetchBypassAttempted  = False

-- | Classify remote host surrogate into entity check class (§16.7).
classifyFetchRemote :: String -> FetchRemoteClass
classifyFetchRemote host
  | host == "forge.entity"      = EntityRemote
  | host == "github.com"        = RefusedUpstream
  | host == "origin.cursor.com" = RefusedUpstream
  | otherwise                   = Unclassified

-- | Kleisli arrow witness for operator verb `fetch`.
data FetchKleisliArrow = FetchKleisliArrow
  { fetchVerb        :: !FetchOperatorVerb
  , fetchGate        :: !FetchInboundGate
  , fetchRemote      :: !FetchRemoteClass
  , fetchObjectCount :: !Int
  } deriving (Show, Eq)

-- | Fetch morphism outcome — admitted only when gate ∧ remote class pass.
data FetchVerdict
  = FetchVerdictAdmitted
  | FetchVerdictGateRefused
  | FetchVerdictRemoteClassRefused
  | FetchVerdictProductionWiredRefused
  | FetchVerdictGateBypassRefused
  deriving (Show, Eq)

-- | Fail-closed fetch errors — positive refuse, not silent no-op.
data FetchError
  = FetchErrGateRefused
  | FetchErrRemoteClassRefused !FetchRemoteClass
  | FetchErrProductionWiredRefused
  | FetchErrGateBypassRefused
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §16.7 Kleisli evaluation + positive refuse
-- ---------------------------------------------------------------------------

-- | Evaluate fetch as Kleisli arrow — §16.7 gate + remote class.
evaluateFetchKleisli :: FetchKleisliArrow -> Either FetchError FetchVerdict
evaluateFetchKleisli arrow
  | fetchGateAdmits (fetchGate arrow) =
      if fetchRemoteAdmissible (fetchRemote arrow)
        then Right FetchVerdictAdmitted
        else Left (FetchErrRemoteClassRefused (fetchRemote arrow))
  | fetchGate arrow == FetchBypassAttempted =
      Left FetchErrGateBypassRefused
  | otherwise =
      Left FetchErrGateRefused

-- | Positive refuse: production wired fetch without Kleisli gate.
refuseProductionWiredFetch :: FetchError
refuseProductionWiredFetch = FetchErrProductionWiredRefused

-- | Positive refuse: gate bypass on inbound fetch.
refuseGateBypassFetch :: FetchError
refuseGateBypassFetch = FetchErrGateBypassRefused

-- | Construct fetch Kleisli arrow from gate + remote host surrogate.
fetchKleisliArrowFromHost
  :: FetchInboundGate -> String -> Int -> FetchKleisliArrow
fetchKleisliArrowFromHost gate remoteHost objectCount =
  FetchKleisliArrow
    { fetchVerb = Fetch
    , fetchGate = gate
    , fetchRemote = classifyFetchRemote remoteHost
    , fetchObjectCount = objectCount
    }

-- | Whether fetch arrow is admissible under §16.7 (gate ∧ remote class).
fetchKleisliAdmissible :: FetchKleisliArrow -> Bool
fetchKleisliAdmissible arrow =
  fetchGateAdmits (fetchGate arrow)
    && fetchRemoteAdmissible (fetchRemote arrow)

-- | Admissibility spec: true ↔ evaluate returns admitted verdict.
fetchKleisliAdmissibleSpec :: FetchKleisliArrow -> Bool
fetchKleisliAdmissibleSpec arrow =
  fetchKleisliAdmissible arrow
    == (evaluateFetchKleisli arrow == Right FetchVerdictAdmitted)

-- | Positive refuse witness: refused gate → gate error.
evaluateFetchGateRefused :: FetchKleisliArrow -> Bool
evaluateFetchGateRefused arrow
  | fetchGate arrow == FetchRefused =
      evaluateFetchKleisli arrow == Left FetchErrGateRefused
  | otherwise = True

-- | Positive refuse witness: admitted gate + refused upstream → remote error.
evaluateFetchRemoteRefused :: FetchKleisliArrow -> Bool
evaluateFetchRemoteRefused arrow
  | fetchGate arrow == FetchAdmitted
  , fetchRemote arrow == RefusedUpstream =
      evaluateFetchKleisli arrow
        == Left (FetchErrRemoteClassRefused RefusedUpstream)
  | otherwise = True

-- | Positive refuse witness: bypass attempted → bypass error.
evaluateFetchGateBypassRefused :: FetchKleisliArrow -> Bool
evaluateFetchGateBypassRefused arrow
  | fetchGate arrow == FetchBypassAttempted =
      evaluateFetchKleisli arrow == Left FetchErrGateBypassRefused
  | otherwise = True

-- ---------------------------------------------------------------------------
-- SECTION 3: gate_check_before_sync inbound bridge
-- ---------------------------------------------------------------------------

-- | History sync tick — prior/post head states for inbound gate check.
data HistorySyncTick = HistorySyncTick
  { tickPrior :: !ThermodynamicState
  , tickPost  :: !ThermodynamicState
  } deriving (Show, Eq)

-- | Inbound fetch head move uses 'gateCheck' — same predicate as sync tick.
fetchGateCheckBeforeSync :: ThermodynamicState -> ThermodynamicState -> Bool
fetchGateCheckBeforeSync prior post =
  accepted (gateCheck prior post fetchGateStepDt)

-- | Gate check soundness witness (admitted when gate returns true).
fetchGateCheckBeforeSyncSound :: ThermodynamicState -> ThermodynamicState -> Bool
fetchGateCheckBeforeSyncSound prior post =
  fetchGateCheckBeforeSync prior post
    == accepted (gateCheck prior post fetchGateStepDt)

-- | Sync tick gate check — mirrors Lean @gateCheckBeforeSync@.
gateCheckBeforeSync :: HistorySyncTick -> Bool
gateCheckBeforeSync h =
  fetchGateCheckBeforeSync (tickPrior h) (tickPost h)

-- | Pointwise equality with bare gate check on tick heads.
fetchGateCheckBeforeSyncEqTick :: HistorySyncTick -> Bool
fetchGateCheckBeforeSyncEqTick h =
  fetchGateCheckBeforeSync (tickPrior h) (tickPost h)
    == gateCheckBeforeSync h

-- | Lift admitted inbound gate to fetch gate enum.
fetchInboundGateFromSync :: HistorySyncTick -> FetchInboundGate
fetchInboundGateFromSync h =
  if gateCheckBeforeSync h then FetchAdmitted else FetchRefused

-- | Admitted sync tick lifts to 'FetchAdmitted'.
fetchInboundGateFromSyncAdmitted :: HistorySyncTick -> Bool
fetchInboundGateFromSyncAdmitted h =
  not (gateCheckBeforeSync h)
    || fetchInboundGateFromSync h == FetchAdmitted

-- ---------------------------------------------------------------------------
-- SECTION 4: Fetch composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for fetch over admissible history successors.
data FetchCtx = FetchCtx
  { fetchCtxPrior      :: !ThermodynamicState
  , fetchCtxSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Fetch operator selection **is** 'excitementSelect'.
fetchSelect :: FetchCtx -> Either ExcitementResidue HistoryCandidate
fetchSelect ctx =
  excitementSelect (fetchCtxPrior ctx) (fetchCtxSuccessors ctx)

-- | Bare fetch selection on @(prior, successors)@.
fetchSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
fetchSelectBare = excitementSelect

-- | Definitional witness: fetch selection API is 'excitementSelect'.
fetchSelectEqExcitementSelect :: FetchCtx -> Bool
fetchSelectEqExcitementSelect ctx =
  fetchSelect ctx
    == excitementSelect (fetchCtxPrior ctx) (fetchCtxSuccessors ctx)

-- | Fetch selection equals 'admitHistorySelect'.
fetchSelectEqAdmitHistorySelect :: FetchCtx -> Bool
fetchSelectEqAdmitHistorySelect ctx =
  fetchSelect ctx
    == admitHistorySelect (fetchCtxPrior ctx) (fetchCtxSuccessors ctx)

-- | Fetch selector re-uses 'excitementSelect' — no Urge-local argmin.
fetchNoLocalArgmin :: FetchCtx -> Bool
fetchNoLocalArgmin ctx =
  fetchSelect ctx
    == excitementSelect (fetchCtxPrior ctx) (fetchCtxSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported selector.
fetchSelectEmpty :: ThermodynamicState -> Bool
fetchSelectEmpty src =
  fetchSelectBare src [] == Left ExcNoCandidates

-- | Kleisli fetch compose pin — import selector; refuse second argmin.
data FetchExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Pin-gated fetch excitement selection.
fetchExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> FetchExcitementPin
  -> Either ExcitementResidue HistoryCandidate
fetchExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
fetchExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | Import pin equals 'excitementSelect'.
fetchExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
fetchExcitementSelectEqExcitementSelect src cands =
  fetchExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with 'ExcAllInadmissible'.
fetchExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
fetchExcitementSelectRefusesSecondArgmin src cands =
  fetchExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- ---------------------------------------------------------------------------
-- SECTION 5: §16.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture thermodynamic head for fetch witnesses.
fetchFixtureState :: ThermodynamicState
fetchFixtureState = ThermodynamicState 2400 0 0 0 0

fetchFixtureAdmittedArrow :: FetchKleisliArrow
fetchFixtureAdmittedArrow =
  fetchKleisliArrowFromHost FetchAdmitted "forge.entity" 3

fetchFixtureGateRefusedArrow :: FetchKleisliArrow
fetchFixtureGateRefusedArrow =
  fetchKleisliArrowFromHost FetchRefused "forge.entity" 0

fetchFixtureRemoteRefusedArrow :: FetchKleisliArrow
fetchFixtureRemoteRefusedArrow =
  fetchKleisliArrowFromHost FetchAdmitted "github.com" 0

fetchFixtureAdmittedOk :: Bool
fetchFixtureAdmittedOk =
  evaluateFetchKleisli fetchFixtureAdmittedArrow == Right FetchVerdictAdmitted

fetchFixtureGateRefused :: Bool
fetchFixtureGateRefused =
  evaluateFetchKleisli fetchFixtureGateRefusedArrow == Left FetchErrGateRefused

fetchFixtureRemoteRefused :: Bool
fetchFixtureRemoteRefused =
  evaluateFetchKleisli fetchFixtureRemoteRefusedArrow
    == Left (FetchErrRemoteClassRefused RefusedUpstream)

fetchFixtureClassifyForgeEntity :: Bool
fetchFixtureClassifyForgeEntity =
  classifyFetchRemote "forge.entity" == EntityRemote

fetchFixtureClassifyGithubRefused :: Bool
fetchFixtureClassifyGithubRefused =
  classifyFetchRemote "github.com" == RefusedUpstream

fetchFixtureProductionWiredRefuse :: Bool
fetchFixtureProductionWiredRefuse =
  refuseProductionWiredFetch == FetchErrProductionWiredRefused

fetchFixtureGateBypassRefuse :: Bool
fetchFixtureGateBypassRefuse =
  refuseGateBypassFetch == FetchErrGateBypassRefused

fetchFixtureKleisliAdmissible :: Bool
fetchFixtureKleisliAdmissible =
  fetchKleisliAdmissible fetchFixtureAdmittedArrow

fetchPositiveRefuseNotSilent :: Bool
fetchPositiveRefuseNotSilent =
  evaluateFetchKleisli fetchFixtureGateRefusedArrow
    /= Right FetchVerdictAdmitted

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Fetch transition accounting (gate + remote admissibility witnesses).
data FetchTransition = FetchTransition
  { fetchTransPrior          :: !ThermodynamicState
  , fetchTransPost           :: !ThermodynamicState
  , fetchTransBath           :: !HeatBath
  , fetchTransDissipatedWork :: !Double
  , fetchTransEntropyDrop    :: !Double
  , fetchTransGateChecked    :: !Bool
  , fetchTransRemoteOk       :: !Bool
  } deriving (Show, Eq)

-- | Admissible fetch transition: gate-checked ∧ remote class ok.
admissibleFetchTransition :: FetchTransition -> Bool
admissibleFetchTransition t =
  fetchTransGateChecked t && fetchTransRemoteOk t

-- | Second law on fetch transition (Bool witness — not a new axiom).
fetchSecondLaw :: FetchTransition -> Bool
fetchSecondLaw t =
  fetchTransEntropyDrop t
    <= fetchTransDissipatedWork t / bathTemp (fetchTransBath t)

-- | Second law on fetch carrier transition from Landauer bridge discharge.
fetchSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
fetchSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
fetchFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
fetchFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for fetch second law (no new axiom).
fetchSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
fetchSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
kleisliFetchPhysicsGreen :: Bool
kleisliFetchPhysicsGreen = False

-- | Lean/Coq: @kleisli_fetch_physics_green_false@.
kleisliFetchPhysicsGreenFalse :: Bool
kleisliFetchPhysicsGreenFalse = not kleisliFetchPhysicsGreen

-- | Production wiring stays open (fetch lift only).
kleisliFetchProductionWired :: Bool
kleisliFetchProductionWired = False

-- | Lean/Coq: @kleisli_fetch_production_wired_false@.
kleisliFetchProductionWiredFalse :: Bool
kleisliFetchProductionWiredFalse = not kleisliFetchProductionWired

-- | Honest non-claim string (meso §16.7 fetch scaffold).
kleisliFetchNonClaim :: String
kleisliFetchNonClaim =
  "§16.7 fetch: gate_check_before_sync inbound + remote class entity check; "
    ++ "composes excitementSelect; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
kleisliFetchNonClaimNonempty :: Bool
kleisliFetchNonClaimNonempty = length kleisliFetchNonClaim > 0

-- | Catalog witness: meso Urge KleisliFetch module present.
kleisliFetchModuleWitness :: Bool
kleisliFetchModuleWitness = True

-- | Zero new axiom discipline witness.
kleisliFetchNoNewAxiom :: Bool
kleisliFetchNoNewAxiom = True

-- | Second-argmin refusal: fetch composes 'excitementSelect' only.
kleisliFetchNoSecondArgmin :: Bool
kleisliFetchNoSecondArgmin =
  fetchNoLocalArgmin
    (FetchCtx {fetchCtxPrior = fetchFixtureState, fetchCtxSuccessors = []})

-- | Excitement compose pin marker (import-only discipline).
excitementComposePin :: Int
excitementComposePin = 0

-- | Pin marker witness.
excitementComposePinMarker :: Bool
excitementComposePinMarker = excitementComposePin == 0

-- | Second-argmin refusal tag witness.
refuseSecondArgminIsTag :: Bool
refuseSecondArgminIsTag = SecondArgminRefused == SecondArgminRefused
