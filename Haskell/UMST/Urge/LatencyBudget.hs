-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.LatencyBudget
-- Description : Meso acting Urge — §17.8 latency budget as typed predicate on admit.
--
-- Integer surrogate ms vs declared tier ceiling — not wall-clock SLA theater.
-- Merge / recovery slow path composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.LatencyBudget
  ( -- * §17.8 typed budget tiers (not wall-clock GREEN)
    interactiveBudgetMs
  , localCommitBudgetMs
  , mergeRecoveryBudgetMs
  , backgroundBudgetMs
  , LatencyBudgetTier (..)
  , latencyTierBudgetMs
    -- * Candidate + witness carriers (§17.8 morphism mirror)
  , LatencyBudgetCandidate (..)
  , LatencyBudgetWitness (..)
  , LatencyBudgetMorphismWitness (..)
  , LatencyBudgetMorphism (..)
  , LatencyBudgetRefusal (..)
  , LatencyBudgetVerdict (..)
    -- * §17.8 admissibility conjunct + typed predicate
  , LatencyAdmissibilityConjunct (..)
  , latencyConjunctAdmits
  , latencyBudgetAdmitPred
  , evaluateWallClockSlaOperation
  , evaluatePhysicsGreenOperation
  , refuseWallClockSlaTheater
  , refuseUnboundedLatencyRatioTheater
  , evaluateLatencyBudgetAdmit
  , witnessFromCandidate
  , applyLatencyBudgetMorphismAdmitted
  , applyLatencyBudgetMorphism
  , budgetWitnessFor
  , checkTypedBudget
    -- * Merge/recovery composes excitementSelect (no second argmin)
  , LatencyBudgetCtx (..)
  , latencyBudgetRecoverySelect
  , urgeLatencyBudgetSelect
  , latencyBudgetRecoverySelectEqExcitementSelect
  , urgeLatencyBudgetSelectEqExcitementSelect
  , latencyBudgetRecoveryNoSecondArgmin
  , refuseSecondArgmin
    -- * Bridge to physicalSecondLaw (derived — zero new axioms)
  , LatencyHistoryMove (..)
  , admissibleLatencyBudget
  , LatencyTransition (..)
  , latencySecondLaw
  , PhysicalLatencyBridge (..)
  , latencySecondLawFromPhysical
  , admissibleLatencyBudgetFromPhysical
  , physicalSecondLawImported
  , latencyBudgetAdmitSecondLawFromPhysical
    -- * §17.8 fixtures + witness theorems
  , latencyFixtureInteractiveCandidate
  , latencyFixtureLocalCommitCandidate
  , latencyFixtureOverBudgetCandidate
  , latencyFixtureWallClockCandidate
  , latencyFixtureGreenCandidate
  , latencyFixtureConjunct
  , latencyFixtureInteractiveAdmits
  , latencyFixtureLocalCommitAdmits
  , latencyFixtureOverBudgetRefused
  , latencyFixtureWallClockRefused
  , latencyFixturePhysicsGreenRefused
  , latencyFixtureApplyMorphismOk
  , latencyFixtureAdmitPredWithinTier
  , latencyFixtureAdmitPredWallClockFalse
  , latencyBudgetPositiveRefuseNotSilent
  , latencyBudgetSlaTheaterRefusedNotAdmitOk
    -- * Honesty flags + catalog witnesses
  , latencyBudgetPhysicsGreen
  , latencyBudgetPhysicsGreenFalse
  , latencyBudgetProductionWired
  , latencyBudgetProductionWiredFalse
  , latencyBudgetMarker
  , latencyBudgetModuleWitness
  , latencyBudgetNoNewAxiom
  , latencyBudgetNoSecondArgmin
  , latencyBudgetNonClaim
  , latencyBudgetNonClaimNonempty
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
  ( urgeRecoverySelect
  , urgeRecoverySelectEqExcitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: §17.8 typed budget tiers (not wall-clock GREEN)
-- ---------------------------------------------------------------------------

-- | Blueprint §17.8 interactive observation budget (milliseconds, typed).
interactiveBudgetMs :: Int
interactiveBudgetMs = 16

-- | Blueprint §17.8 local commit admission budget (milliseconds, typed).
localCommitBudgetMs :: Int
localCommitBudgetMs = 100

-- | Blueprint §17.8 merge / recovery slow-path budget (milliseconds, typed).
mergeRecoveryBudgetMs :: Int
mergeRecoveryBudgetMs = 1000

-- | Blueprint §17.8 background compaction budget (milliseconds, typed).
backgroundBudgetMs :: Int
backgroundBudgetMs = 10000

-- | Typed budget tier — declared ceiling, not measured wall-clock.
data LatencyBudgetTier
  = LatencyInteractive
  | LatencyLocalCommit
  | LatencyMergeRecovery
  | LatencyBackground
  deriving (Show, Eq)

-- | Declared budget ceiling for each tier (milliseconds, typed — not measured).
latencyTierBudgetMs :: LatencyBudgetTier -> Int
latencyTierBudgetMs LatencyInteractive    = interactiveBudgetMs
latencyTierBudgetMs LatencyLocalCommit    = localCommitBudgetMs
latencyTierBudgetMs LatencyMergeRecovery  = mergeRecoveryBudgetMs
latencyTierBudgetMs LatencyBackground     = backgroundBudgetMs

-- ---------------------------------------------------------------------------
-- SECTION 2: Candidate + witness carriers (§17.8 morphism mirror)
-- ---------------------------------------------------------------------------

-- | Candidate for latency-budget admission — surrogate inputs only.
data LatencyBudgetCandidate = LatencyBudgetCandidate
  { latencyTier              :: !LatencyBudgetTier
  , surrogateMs              :: !Int
  , claimsWallClockSla       :: !Bool
  , claimsPhysicsGreen       :: !Bool
  } deriving (Show, Eq)

-- | Typed budget witness — declared ceiling + surrogate, not measured latency.
data LatencyBudgetWitness = LatencyBudgetWitness
  { witnessTier              :: !LatencyBudgetTier
  , witnessBudgetMs          :: !Int
  , witnessSurrogateMs       :: !Int
  , witnessTypedPredicate    :: !Bool
  } deriving (Show, Eq)

-- | Witness bundle a latency-budget morphism must preserve (§17.8).
data LatencyBudgetMorphismWitness = LatencyBudgetMorphismWitness
  { morphismWitnessTier          :: !LatencyBudgetTier
  , morphismWitnessBudgetMs      :: !Int
  , morphismWitnessSurrogateMs   :: !Int
  , morphismWitnessTypedPredicate :: !Bool
  } deriving (Show, Eq)

-- | Typed latency-budget morphism — admissible admit transition, not SLA theater.
data LatencyBudgetMorphism = LatencyBudgetMorphism
  { morphismFrom           :: !LatencyBudgetCandidate
  , morphismWitness        :: !LatencyBudgetMorphismWitness
  , morphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed latency-budget errors — positive refuse, not silent no-op.
data LatencyBudgetRefusal
  = BudgetExceeded Int Int
  | WallClockSlaTheater
  | PhysicsGreenInvent
  | UnboundedLatencyRatioTheater
  | GateRejected Int
  deriving (Show, Eq)

-- | Verdict of a latency-budget operation class.
data LatencyBudgetVerdict
  = LatencyAdmitOk
  | LatencyWallClockSlaRefused
  | LatencyPhysicsGreenRefused
  | LatencyRatioTheaterRefused
  | LatencyInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 3: §17.8 admissibility conjunct + typed predicate
-- ---------------------------------------------------------------------------

-- | §17.8 admissibility conjunct inputs (surrogate).
data LatencyAdmissibilityConjunct = LatencyAdmissibilityConjunct
  { conjunctGateOk              :: !Bool
  , conjunctTypedPredicate        :: !Bool
  , conjunctExcitementPreserves   :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ typed predicate ∧ Excitement preserves@.
latencyConjunctAdmits :: LatencyAdmissibilityConjunct -> Bool
latencyConjunctAdmits c =
  conjunctGateOk c
  && conjunctTypedPredicate c
  && conjunctExcitementPreserves c

-- | Core typed predicate — surrogate within tier and no SLA / GREEN theater.
latencyBudgetAdmitPred :: LatencyBudgetCandidate -> Bool
latencyBudgetAdmitPred c =
  case (claimsWallClockSla c, claimsPhysicsGreen c) of
    (True, _)   -> False
    (_, True)   -> False
    (False, False) ->
      surrogateMs c <= latencyTierBudgetMs (latencyTier c)

-- | Classify wall-clock SLA theater without performing I/O.
evaluateWallClockSlaOperation :: Bool -> LatencyBudgetVerdict
evaluateWallClockSlaOperation claimsWallClock =
  if claimsWallClock then LatencyWallClockSlaRefused else LatencyAdmitOk

-- | Classify physics GREEN invent without performing I/O.
evaluatePhysicsGreenOperation :: Bool -> LatencyBudgetVerdict
evaluatePhysicsGreenOperation claimsGreen =
  if claimsGreen then LatencyPhysicsGreenRefused else LatencyAdmitOk

-- | Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only.
refuseWallClockSlaTheater :: Either LatencyBudgetRefusal ()
refuseWallClockSlaTheater = Left WallClockSlaTheater

-- | Positive refuse: unbounded f64 latency-ratio theater is inadmissible.
refuseUnboundedLatencyRatioTheater :: Either LatencyBudgetRefusal ()
refuseUnboundedLatencyRatioTheater = Left UnboundedLatencyRatioTheater

-- | Evaluate latency-budget admission — honest refusal on inadmissible inputs.
evaluateLatencyBudgetAdmit
  :: LatencyBudgetCandidate -> Either LatencyBudgetRefusal LatencyBudgetWitness
evaluateLatencyBudgetAdmit c =
  if claimsPhysicsGreen c then
    Left PhysicsGreenInvent
  else if claimsWallClockSla c then
    Left WallClockSlaTheater
  else
    let budgetMs = latencyTierBudgetMs (latencyTier c)
        surrogate = surrogateMs c
     in if surrogate <= budgetMs then
          Right
            LatencyBudgetWitness
              { witnessTier = latencyTier c
              , witnessBudgetMs = budgetMs
              , witnessSurrogateMs = surrogate
              , witnessTypedPredicate = True
              }
        else
          Left (BudgetExceeded surrogate budgetMs)

witnessFromCandidate
  :: LatencyBudgetCandidate -> LatencyBudgetWitness -> LatencyBudgetMorphismWitness
witnessFromCandidate _ w =
  LatencyBudgetMorphismWitness
    { morphismWitnessTier = witnessTier w
    , morphismWitnessBudgetMs = witnessBudgetMs w
    , morphismWitnessSurrogateMs = witnessSurrogateMs w
    , morphismWitnessTypedPredicate = witnessTypedPredicate w
    }

applyLatencyBudgetMorphismAdmitted
  :: LatencyBudgetCandidate -> Bool -> LatencyBudgetWitness -> LatencyBudgetMorphism
applyLatencyBudgetMorphismAdmitted candidate excitementSelected w =
  LatencyBudgetMorphism
    { morphismFrom = candidate
    , morphismWitness = witnessFromCandidate candidate w
    , morphismExcitementSelected = excitementSelected
    }

applyLatencyBudgetMorphism
  :: LatencyBudgetCandidate
  -> LatencyAdmissibilityConjunct
  -> Bool
  -> Either LatencyBudgetRefusal LatencyBudgetMorphism
applyLatencyBudgetMorphism candidate conjunct excitementSelected =
  if not (latencyConjunctAdmits conjunct) then
    Left (GateRejected (surrogateMs candidate))
  else if not (conjunctTypedPredicate conjunct) then
    Left WallClockSlaTheater
  else if not excitementSelected then
    Left
      (BudgetExceeded
        (surrogateMs candidate)
        (latencyTierBudgetMs (latencyTier candidate)))
  else
    case evaluateLatencyBudgetAdmit candidate of
      Left r  -> Left r
      Right w ->
        Right (applyLatencyBudgetMorphismAdmitted candidate excitementSelected w)

budgetWitnessFor :: LatencyBudgetTier -> LatencyBudgetWitness
budgetWitnessFor t =
  LatencyBudgetWitness
    { witnessTier = t
    , witnessBudgetMs = latencyTierBudgetMs t
    , witnessSurrogateMs = 0
    , witnessTypedPredicate = True
    }

checkTypedBudget
  :: LatencyBudgetTier -> Int -> Either LatencyBudgetRefusal LatencyBudgetWitness
checkTypedBudget t surrogate =
  evaluateLatencyBudgetAdmit
    LatencyBudgetCandidate
      { latencyTier = t
      , surrogateMs = surrogate
      , claimsWallClockSla = False
      , claimsPhysicsGreen = False
      }

-- ---------------------------------------------------------------------------
-- SECTION 4: Merge/recovery composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for merge/recovery slow path over admissible history successors.
data LatencyBudgetCtx = LatencyBudgetCtx
  { latencyPrior       :: !ThermodynamicState
  , latencySuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Merge / recovery slow path **is** 'urgeRecoverySelect' / 'excitementSelect'.
latencyBudgetRecoverySelect
  :: LatencyBudgetCtx -> Either ExcitementResidue HistoryCandidate
latencyBudgetRecoverySelect ctx =
  excitementSelect (latencyPrior ctx) (latencySuccessors ctx)

urgeLatencyBudgetSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeLatencyBudgetSelect = excitementSelect

-- | Definitional witness: recovery selection API is 'excitementSelect'.
latencyBudgetRecoverySelectEqExcitementSelect :: LatencyBudgetCtx -> Bool
latencyBudgetRecoverySelectEqExcitementSelect ctx =
  latencyBudgetRecoverySelect ctx
    == excitementSelect (latencyPrior ctx) (latencySuccessors ctx)

-- | Definitional witness: bare alias is 'urgeRecoverySelect'.
urgeLatencyBudgetSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeLatencyBudgetSelectEqExcitementSelect prior successors =
  urgeLatencyBudgetSelect prior successors
    == urgeRecoverySelect prior successors
    && urgeRecoverySelectEqExcitementSelect prior successors

-- | Latency budget selector re-uses 'excitementSelect' — no Urge-local argmin.
latencyBudgetRecoveryNoSecondArgmin :: LatencyBudgetCtx -> Bool
latencyBudgetRecoveryNoSecondArgmin ctx =
  latencyBudgetRecoverySelect ctx
    == excitementSelect (latencyPrior ctx) (latencySuccessors ctx)

refuseSecondArgmin :: LatencyBudgetRefusal
refuseSecondArgmin = UnboundedLatencyRatioTheater

-- ---------------------------------------------------------------------------
-- SECTION 5: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Latency history move gate conjunct (Bool witnesses — not new axioms).
data LatencyHistoryMove = LatencyHistoryMove
  { moveGateChecked     :: !Bool
  , moveTypedPredicate  :: !Bool
  , moveExcitementOk    :: !Bool
  } deriving (Show, Eq)

admissibleLatencyBudget :: LatencyHistoryMove -> Bool
admissibleLatencyBudget h =
  moveGateChecked h
  && moveTypedPredicate h
  && moveExcitementOk h

data LatencyTransition = LatencyTransition
  { latencyMove            :: !LatencyHistoryMove
  , latencyBath            :: !HeatBath
  , latencyDissipatedWork  :: !Double
  , latencyEntropyDrop     :: !Double
  } deriving (Show, Eq)

latencySecondLaw :: LatencyTransition -> Bool
latencySecondLaw t =
  latencyEntropyDrop t
    <= latencyDissipatedWork t / bathTemp (latencyBath t)

data PhysicalLatencyBridge = PhysicalLatencyBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalLatency        :: !LatencyTransition
  , physicalAdmissible     :: !Bool
  } deriving (Show, Eq)

latencySecondLawFromPhysical :: PhysicalLatencyBridge -> Bool -> Bool
latencySecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalLandauerBridge b))
  && latencySecondLaw (physicalLatency b)

admissibleLatencyBudgetFromPhysical :: PhysicalLatencyBridge -> Bool -> Bool
admissibleLatencyBudgetFromPhysical b hSL =
  hSL && physicalAdmissible b
  && admissibleLatencyBudget (latencyMove (physicalLatency b))

physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

latencyBudgetAdmitSecondLawFromPhysical :: LandauerHistoryBridge -> Bool -> Bool
latencyBudgetAdmitSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- ---------------------------------------------------------------------------
-- SECTION 6: §17.8 fixtures + witness theorems
-- ---------------------------------------------------------------------------

latencyFixtureInteractiveCandidate :: LatencyBudgetCandidate
latencyFixtureInteractiveCandidate =
  LatencyBudgetCandidate
    { latencyTier = LatencyInteractive
    , surrogateMs = 10
    , claimsWallClockSla = False
    , claimsPhysicsGreen = False
    }

latencyFixtureLocalCommitCandidate :: LatencyBudgetCandidate
latencyFixtureLocalCommitCandidate =
  LatencyBudgetCandidate
    { latencyTier = LatencyLocalCommit
    , surrogateMs = 80
    , claimsWallClockSla = False
    , claimsPhysicsGreen = False
    }

latencyFixtureOverBudgetCandidate :: LatencyBudgetCandidate
latencyFixtureOverBudgetCandidate =
  LatencyBudgetCandidate
    { latencyTier = LatencyLocalCommit
    , surrogateMs = localCommitBudgetMs + 1
    , claimsWallClockSla = False
    , claimsPhysicsGreen = False
    }

latencyFixtureWallClockCandidate :: LatencyBudgetCandidate
latencyFixtureWallClockCandidate =
  LatencyBudgetCandidate
    { latencyTier = LatencyLocalCommit
    , surrogateMs = 50
    , claimsWallClockSla = True
    , claimsPhysicsGreen = False
    }

latencyFixtureGreenCandidate :: LatencyBudgetCandidate
latencyFixtureGreenCandidate =
  LatencyBudgetCandidate
    { latencyTier = LatencyMergeRecovery
    , surrogateMs = 500
    , claimsWallClockSla = False
    , claimsPhysicsGreen = True
    }

latencyFixtureConjunct :: LatencyAdmissibilityConjunct
latencyFixtureConjunct =
  LatencyAdmissibilityConjunct
    { conjunctGateOk = True
    , conjunctTypedPredicate = True
    , conjunctExcitementPreserves = True
    }

latencyFixtureInteractiveAdmits :: Bool
latencyFixtureInteractiveAdmits =
  evaluateLatencyBudgetAdmit latencyFixtureInteractiveCandidate
    == Right
      LatencyBudgetWitness
        { witnessTier = LatencyInteractive
        , witnessBudgetMs = interactiveBudgetMs
        , witnessSurrogateMs = 10
        , witnessTypedPredicate = True
        }

latencyFixtureLocalCommitAdmits :: Bool
latencyFixtureLocalCommitAdmits =
  evaluateLatencyBudgetAdmit latencyFixtureLocalCommitCandidate
    == Right
      LatencyBudgetWitness
        { witnessTier = LatencyLocalCommit
        , witnessBudgetMs = localCommitBudgetMs
        , witnessSurrogateMs = 80
        , witnessTypedPredicate = True
        }

latencyFixtureOverBudgetRefused :: Bool
latencyFixtureOverBudgetRefused =
  evaluateLatencyBudgetAdmit latencyFixtureOverBudgetCandidate
    == Left (BudgetExceeded (localCommitBudgetMs + 1) localCommitBudgetMs)

latencyFixtureWallClockRefused :: Bool
latencyFixtureWallClockRefused =
  evaluateLatencyBudgetAdmit latencyFixtureWallClockCandidate
    == Left WallClockSlaTheater

latencyFixturePhysicsGreenRefused :: Bool
latencyFixturePhysicsGreenRefused =
  evaluateLatencyBudgetAdmit latencyFixtureGreenCandidate
    == Left PhysicsGreenInvent

latencyFixtureApplyMorphismOk :: Bool
latencyFixtureApplyMorphismOk =
  applyLatencyBudgetMorphism
    latencyFixtureLocalCommitCandidate
    latencyFixtureConjunct
    True
    == Right
      (applyLatencyBudgetMorphismAdmitted
        latencyFixtureLocalCommitCandidate
        True
        LatencyBudgetWitness
          { witnessTier = LatencyLocalCommit
          , witnessBudgetMs = localCommitBudgetMs
          , witnessSurrogateMs = 80
          , witnessTypedPredicate = True
          })

latencyFixtureAdmitPredWithinTier :: Bool
latencyFixtureAdmitPredWithinTier =
  latencyBudgetAdmitPred latencyFixtureLocalCommitCandidate

latencyFixtureAdmitPredWallClockFalse :: Bool
latencyFixtureAdmitPredWallClockFalse =
  not (latencyBudgetAdmitPred latencyFixtureWallClockCandidate)

latencyBudgetPositiveRefuseNotSilent :: Bool
latencyBudgetPositiveRefuseNotSilent =
  evaluateWallClockSlaOperation True /= LatencyAdmitOk

latencyBudgetSlaTheaterRefusedNotAdmitOk :: Bool
latencyBudgetSlaTheaterRefusedNotAdmitOk =
  evaluateLatencyBudgetAdmit latencyFixtureWallClockCandidate
    /= Right
      LatencyBudgetWitness
        { witnessTier = LatencyLocalCommit
        , witnessBudgetMs = localCommitBudgetMs
        , witnessSurrogateMs = 50
        , witnessTypedPredicate = True
        }

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
latencyBudgetPhysicsGreen :: Bool
latencyBudgetPhysicsGreen = False

-- | Lean/Coq: @latency_budget_physics_green_false@.
latencyBudgetPhysicsGreenFalse :: Bool
latencyBudgetPhysicsGreenFalse = not latencyBudgetPhysicsGreen

-- | Production wiring stays open (meso lift only).
latencyBudgetProductionWired :: Bool
latencyBudgetProductionWired = False

-- | Lean/Coq: @latency_budget_production_wired_false@.
latencyBudgetProductionWiredFalse :: Bool
latencyBudgetProductionWiredFalse = not latencyBudgetProductionWired

latencyBudgetMarker :: Int
latencyBudgetMarker = 1

-- | Catalog witness: meso Urge LatencyBudget module present.
latencyBudgetModuleWitness :: Bool
latencyBudgetModuleWitness = True

-- | Zero new axiom discipline witness.
latencyBudgetNoNewAxiom :: Bool
latencyBudgetNoNewAxiom = True

-- | Second-argmin refusal: latency budget composes 'excitementSelect' only.
latencyBudgetNoSecondArgmin :: Bool
latencyBudgetNoSecondArgmin =
  urgeLatencyBudgetSelectEqExcitementSelect (ThermodynamicState 300 0 0.3 30 40) []

-- | Honest non-claim string (meso §17.8 latency budget scaffold).
latencyBudgetNonClaim :: String
latencyBudgetNonClaim =
  "§17.8 latency budget typed surrogate-ms tier ceilings not wall-clock SLA theater; "
    ++ "urgeLatencyBudgetSelect composes excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
latencyBudgetNonClaimNonempty :: Bool
latencyBudgetNonClaimNonempty = length latencyBudgetNonClaim > 0
