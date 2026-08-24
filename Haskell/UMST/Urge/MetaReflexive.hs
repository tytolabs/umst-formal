-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.MetaReflexive
-- Description : Meso acting Urge — §10.5 umst-meta reflexive health of Urge morphisms.
--
-- Reflexive gate on repository + mesh transitions so Urge cannot lie about
-- integrity, residues, or formal coverage. Positive refuse via typed
-- 'MetaReflexiveRefusal' — not only @!physics_green@.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.MetaReflexive
  ( -- * Urge morphism + reflexive health carriers (§10.5)
    UrgeMorphismKind (..)
  , ReflexiveHealthVerdict (..)
  , MetaReflexiveStamp (..)
  , MetaReflexiveWitness (..)
  , UrgeMorphism (..)
  , MetaReflexiveRefusal (..)
  , MetaReflexiveVerdict (..)
  , ReflexiveHealthReport (..)
    -- * §10.5 admissibility conjunct + positive refuse
  , MetaAdmissibilityConjunct (..)
  , metaConjunctAdmits
  , evaluateMetaGateBypass
  , refuseBypassMetaGate
  , refuseSelfExempt
  , refuseInventedGreen
  , refuseFormalOverclaim
  , healthyReport
  , evaluateReflexiveHealthStampFormal
  , evaluateReflexiveHealthAfterSelf
  , evaluateReflexiveHealth
  , applyMetaReflexiveMorphism
    -- * Positive refuse witnesses
  , metaReflexiveBypassRefused
  , metaReflexiveSelfExemptRefused
  , metaReflexiveInventedGreenRefused
  , metaReflexiveFormalOverclaimRefused
  , evaluateMetaGateBypassPositive
  , evaluateMetaGateBypassHonest
    -- * Reflexive recovery composes excitementSelect (no second argmin)
  , MetaReflexiveCtx (..)
  , metaReflexiveSelect
  , metaReflexiveSelectBare
  , metaReflexiveSelectEqExcitementSelect
  , metaReflexiveSelectEqAdmitHistorySelect
  , metaReflexiveNoLocalArgmin
  , metaReflexiveEmpty
    -- * §10.5 fixtures + witness theorems
  , metaFixtureStamp
  , metaFixtureWitness
  , metaFixtureHealthyMorphism
  , metaFixtureBypassMorphism
  , metaFixtureInventedGreen
  , metaFixtureConjunct
  , metaFixtureHealthyReport
  , metaFixtureHealthyAdmits
  , metaFixtureBypassRefused
  , metaFixtureInventedGreenRefused
  , metaFixtureApplyMorphismOk
  , metaFixtureWitnessPreservesStamp
    -- * Landauer bridge (derived — zero new axioms)
  , MetaReflexiveTransition (..)
  , admissibleMetaReflexiveTransition
  , metaReflexiveSecondLaw
  , metaReflexiveSecondLawFromLandauer
  , metaReflexiveSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , metaReflexivePhysicsGreen
  , metaReflexivePhysicsGreenFalse
  , metaReflexiveProductionWired
  , metaReflexiveProductionWiredFalse
  , metaReflexiveModuleWitness
  , metaReflexiveNoNewAxiom
  , metaReflexiveNoSecondArgmin
  , metaReflexiveNonClaim
  , metaReflexiveNonClaimNonempty
  , metaReflexivePositiveRefuseNotSilent
  , metaReflexiveHonest
  , metaReflexivePositiveRefuse
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitHistorySelect
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Urge morphism + reflexive health carriers (§10.5)
-- ---------------------------------------------------------------------------

-- | Urge morphism kinds from blueprint §4 (typed, not prose).
data UrgeMorphismKind
  = CommitPatch
  | Merge
  | Recovery
  | MiObservation
  | SignedPropagate
  deriving (Show, Eq)

-- | Reflexive health verdict on one Urge morphism.
data ReflexiveHealthVerdict
  = ReflexiveHealthy
  | RefuseBypassMeta
  | RefuseSelfExempt
  | RefuseInventedGreen
  | RefuseMissingStamp
  | RefuseFormalOverclaim
  deriving (Show, Eq)

-- | UCRS stamp surrogate carried through reflexive meta health.
data MetaReflexiveStamp = MetaReflexiveStamp
  { metaStampSeq      :: !Int
  , metaStampWallHasT :: !Bool
  } deriving (Show, Eq)

-- | Witness bundle a reflexive morphism must preserve (§10.5).
data MetaReflexiveWitness = MetaReflexiveWitness
  { metaWitnessStamp          :: !MetaReflexiveStamp
  , metaWitnessPresent        :: !Bool
  , metaWitnessFormalCoverage :: !Bool
  } deriving (Show, Eq)

-- | One Urge morphism under reflexive meta health check.
data UrgeMorphism = UrgeMorphism
  { morphismKind               :: !UrgeMorphismKind
  , morphismBypassesMetaGate   :: !Bool
  , morphismSelfExempt         :: !Bool
  , morphismPhysicsGreenClaim  :: !Bool
  , morphismMetaWitnessPresent :: !Bool
  , morphismStamp              :: !MetaReflexiveStamp
  , morphismStampNonempty      :: !Bool
  , morphismFormalOverclaim    :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed reflexive errors — positive refuse, not silent accept.
data MetaReflexiveRefusal
  = BypassMeta !UrgeMorphismKind
  | SelfExempt !UrgeMorphismKind
  | InventedGreen !UrgeMorphismKind
  | MissingStamp !Int
  | FormalOverclaim !UrgeMorphismKind
  deriving (Show, Eq)

-- | Verdict of a reflexive health operation class.
data MetaReflexiveVerdict
  = MetaHealthy
  | MetaBypassRefused
  | MetaInadmissible
  deriving (Show, Eq)

-- | Successful reflexive health report — typed, not bool theater.
data ReflexiveHealthReport = ReflexiveHealthReport
  { reportKind         :: !UrgeMorphismKind
  , reportVerdict      :: !ReflexiveHealthVerdict
  , reportPhysicsGreen :: !Bool
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §10.5 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §10.5 admissibility conjunct inputs (surrogate).
data MetaAdmissibilityConjunct = MetaAdmissibilityConjunct
  { conjunctGateOk              :: !Bool
  , conjunctReflexiveHonest     :: !Bool
  , conjunctExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Conjunct admits when gate, reflexive honesty, and excitement preservation hold.
metaConjunctAdmits :: MetaAdmissibilityConjunct -> Bool
metaConjunctAdmits c =
  conjunctGateOk c
  && conjunctReflexiveHonest c
  && conjunctExcitementPreserves c

-- | Evaluate meta-gate bypass — bypass refused when true.
evaluateMetaGateBypass :: Bool -> MetaReflexiveVerdict
evaluateMetaGateBypass bypasses =
  if bypasses then MetaBypassRefused else MetaHealthy

-- | Positive refuse: bypass meta gate.
refuseBypassMetaGate :: UrgeMorphismKind -> MetaReflexiveRefusal
refuseBypassMetaGate k = BypassMeta k

-- | Positive refuse: self-exempt morphism.
refuseSelfExempt :: UrgeMorphismKind -> MetaReflexiveRefusal
refuseSelfExempt k = SelfExempt k

-- | Positive refuse: invented physics GREEN without witness.
refuseInventedGreen :: UrgeMorphismKind -> MetaReflexiveRefusal
refuseInventedGreen k = InventedGreen k

-- | Positive refuse: formal overclaim.
refuseFormalOverclaim :: UrgeMorphismKind -> MetaReflexiveRefusal
refuseFormalOverclaim k = FormalOverclaim k

-- | Healthy report for morphism kind — physics_green stays false.
healthyReport :: UrgeMorphismKind -> ReflexiveHealthReport
healthyReport k =
  ReflexiveHealthReport
    { reportKind = k
    , reportVerdict = ReflexiveHealthy
    , reportPhysicsGreen = False
    }

-- | Stamp + formal coverage check after self-exempt and invented-green gates.
evaluateReflexiveHealthStampFormal
  :: UrgeMorphism -> Either MetaReflexiveRefusal ReflexiveHealthReport
evaluateReflexiveHealthStampFormal m =
  if morphismStampNonempty m
    then
      if morphismFormalOverclaim m
        then Left (FormalOverclaim (morphismKind m))
        else Right (healthyReport (morphismKind m))
    else Left (MissingStamp (metaStampSeq (morphismStamp m)))

-- | Invented-green check before stamp/formal evaluation.
evaluateReflexiveHealthAfterSelf
  :: UrgeMorphism -> Either MetaReflexiveRefusal ReflexiveHealthReport
evaluateReflexiveHealthAfterSelf m =
  if morphismPhysicsGreenClaim m && not (morphismMetaWitnessPresent m)
    then Left (InventedGreen (morphismKind m))
    else evaluateReflexiveHealthStampFormal m

-- | Full reflexive health evaluation — fail-closed on bypass/self-exempt.
evaluateReflexiveHealth
  :: UrgeMorphism -> Either MetaReflexiveRefusal ReflexiveHealthReport
evaluateReflexiveHealth m
  | morphismBypassesMetaGate m = Left (BypassMeta (morphismKind m))
  | morphismSelfExempt m = Left (SelfExempt (morphismKind m))
  | otherwise = evaluateReflexiveHealthAfterSelf m

-- | Apply reflexive morphism under conjunct + excitement selection gate.
applyMetaReflexiveMorphism
  :: UrgeMorphism
  -> MetaAdmissibilityConjunct
  -> Bool
  -> Either MetaReflexiveRefusal UrgeMorphism
applyMetaReflexiveMorphism m conjunct excitementSelected
  | not (metaConjunctAdmits conjunct) =
      Left (MissingStamp (metaStampSeq (morphismStamp m)))
  | not excitementSelected =
      Left (FormalOverclaim (morphismKind m))
  | otherwise =
      case evaluateReflexiveHealth m of
        Left r -> Left r
        Right _ -> Right m

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Bypass refuse constructor witness.
metaReflexiveBypassRefused :: UrgeMorphismKind -> Bool
metaReflexiveBypassRefused k =
  refuseBypassMetaGate k == BypassMeta k

-- | Self-exempt refuse constructor witness.
metaReflexiveSelfExemptRefused :: UrgeMorphismKind -> Bool
metaReflexiveSelfExemptRefused k =
  refuseSelfExempt k == SelfExempt k

-- | Invented-green refuse constructor witness.
metaReflexiveInventedGreenRefused :: UrgeMorphismKind -> Bool
metaReflexiveInventedGreenRefused k =
  refuseInventedGreen k == InventedGreen k

-- | Formal-overclaim refuse constructor witness.
metaReflexiveFormalOverclaimRefused :: UrgeMorphismKind -> Bool
metaReflexiveFormalOverclaimRefused k =
  refuseFormalOverclaim k == FormalOverclaim k

-- | Bypass evaluation is positive refuse when bypasses=true.
evaluateMetaGateBypassPositive :: Bool
evaluateMetaGateBypassPositive =
  evaluateMetaGateBypass True == MetaBypassRefused

-- | Honest bypass evaluation when bypasses=false.
evaluateMetaGateBypassHonest :: Bool
evaluateMetaGateBypassHonest =
  evaluateMetaGateBypass False == MetaHealthy

-- ---------------------------------------------------------------------------
-- SECTION 4: Reflexive recovery composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for reflexive recovery over admissible history successors.
data MetaReflexiveCtx = MetaReflexiveCtx
  { metaReflexivePrior       :: !ThermodynamicState
  , metaReflexiveSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Reflexive recovery composes 'excitementSelect' on prior + successors.
metaReflexiveSelect
  :: MetaReflexiveCtx
  -> Either ExcitementResidue HistoryCandidate
metaReflexiveSelect ctx =
  excitementSelect (metaReflexivePrior ctx) (metaReflexiveSuccessors ctx)

-- | Bare reflexive recovery — same as 'excitementSelect'.
metaReflexiveSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
metaReflexiveSelectBare = excitementSelect

-- | Definitional witness: reflexive selection API is 'excitementSelect'.
metaReflexiveSelectEqExcitementSelect :: MetaReflexiveCtx -> Bool
metaReflexiveSelectEqExcitementSelect ctx =
  metaReflexiveSelect ctx
    == excitementSelect (metaReflexivePrior ctx) (metaReflexiveSuccessors ctx)

-- | Reflexive selection equals 'admitHistorySelect'.
metaReflexiveSelectEqAdmitHistorySelect :: MetaReflexiveCtx -> Bool
metaReflexiveSelectEqAdmitHistorySelect ctx =
  metaReflexiveSelect ctx
    == admitHistorySelect (metaReflexivePrior ctx) (metaReflexiveSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
metaReflexiveNoLocalArgmin :: MetaReflexiveCtx -> Bool
metaReflexiveNoLocalArgmin ctx =
  metaReflexiveSelect ctx
    == excitementSelect (metaReflexivePrior ctx) (metaReflexiveSuccessors ctx)

-- | Empty successors yield no-candidates residue.
metaReflexiveEmpty :: MetaReflexiveCtx -> Bool
metaReflexiveEmpty ctx =
  metaReflexiveSuccessors ctx == []
  && metaReflexiveSelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §10.5 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture stamp with seq=7 and wallHasT=true.
metaFixtureStamp :: MetaReflexiveStamp
metaFixtureStamp = MetaReflexiveStamp {metaStampSeq = 7, metaStampWallHasT = True}

-- | Fixture witness bundle.
metaFixtureWitness :: MetaReflexiveWitness
metaFixtureWitness =
  MetaReflexiveWitness
    { metaWitnessStamp = metaFixtureStamp
    , metaWitnessPresent = True
    , metaWitnessFormalCoverage = True
    }

-- | Healthy morphism fixture (commitPatch, no bypass/self-exempt).
metaFixtureHealthyMorphism :: UrgeMorphism
metaFixtureHealthyMorphism =
  UrgeMorphism
    { morphismKind = CommitPatch
    , morphismBypassesMetaGate = False
    , morphismSelfExempt = False
    , morphismPhysicsGreenClaim = False
    , morphismMetaWitnessPresent = False
    , morphismStamp = metaFixtureStamp
    , morphismStampNonempty = True
    , morphismFormalOverclaim = False
    }

-- | Bypass morphism fixture — must refuse.
metaFixtureBypassMorphism :: UrgeMorphism
metaFixtureBypassMorphism =
  UrgeMorphism
    { morphismKind = Merge
    , morphismBypassesMetaGate = True
    , morphismSelfExempt = False
    , morphismPhysicsGreenClaim = False
    , morphismMetaWitnessPresent = False
    , morphismStamp = metaFixtureStamp
    , morphismStampNonempty = True
    , morphismFormalOverclaim = False
    }

-- | Invented-green morphism fixture — must refuse.
metaFixtureInventedGreen :: UrgeMorphism
metaFixtureInventedGreen =
  UrgeMorphism
    { morphismKind = Recovery
    , morphismBypassesMetaGate = False
    , morphismSelfExempt = False
    , morphismPhysicsGreenClaim = True
    , morphismMetaWitnessPresent = False
    , morphismStamp = metaFixtureStamp
    , morphismStampNonempty = True
    , morphismFormalOverclaim = False
    }

-- | Admissible conjunct fixture.
metaFixtureConjunct :: MetaAdmissibilityConjunct
metaFixtureConjunct =
  MetaAdmissibilityConjunct
    { conjunctGateOk = True
    , conjunctReflexiveHonest = True
    , conjunctExcitementPreserves = True
    }

-- | Expected healthy report for commitPatch fixture.
metaFixtureHealthyReport :: ReflexiveHealthReport
metaFixtureHealthyReport =
  ReflexiveHealthReport
    { reportKind = CommitPatch
    , reportVerdict = ReflexiveHealthy
    , reportPhysicsGreen = False
    }

-- | Healthy morphism admits with typed report.
metaFixtureHealthyAdmits :: Bool
metaFixtureHealthyAdmits =
  evaluateReflexiveHealth metaFixtureHealthyMorphism
    == Right metaFixtureHealthyReport

-- | Bypass morphism refused with typed bypass error.
metaFixtureBypassRefused :: Bool
metaFixtureBypassRefused =
  evaluateReflexiveHealth metaFixtureBypassMorphism
    == Left (BypassMeta Merge)

-- | Invented-green morphism refused.
metaFixtureInventedGreenRefused :: Bool
metaFixtureInventedGreenRefused =
  evaluateReflexiveHealth metaFixtureInventedGreen
    == Left (InventedGreen Recovery)

-- | Apply morphism on healthy fixture succeeds.
metaFixtureApplyMorphismOk :: Bool
metaFixtureApplyMorphismOk =
  applyMetaReflexiveMorphism metaFixtureHealthyMorphism metaFixtureConjunct True
    == Right metaFixtureHealthyMorphism

-- | Witness stamp projection preserved.
metaFixtureWitnessPreservesStamp :: Bool
metaFixtureWitnessPreservesStamp =
  metaWitnessStamp metaFixtureWitness == metaFixtureStamp

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Meta-reflexive transition with gate + provenance accounting.
data MetaReflexiveTransition = MetaReflexiveTransition
  { metaTransitionPrior           :: !HistorySnapshot
  , metaTransitionPost            :: !HistorySnapshot
  , metaTransitionGateChecked     :: !Bool
  , metaTransitionReflexiveHonest :: !Bool
  , metaTransitionProvenanceOk    :: !Bool
  , metaTransitionBath            :: !HeatBath
  , metaTransitionDissipatedWork  :: !Double
  , metaTransitionEntropyDrop     :: !Double
  } deriving (Show, Eq)

-- | Admissible meta-reflexive transition: gate + honesty + provenance.
admissibleMetaReflexiveTransition :: MetaReflexiveTransition -> Bool
admissibleMetaReflexiveTransition t =
  metaTransitionGateChecked t
  && metaTransitionReflexiveHonest t
  && metaTransitionProvenanceOk t

-- | Second-law accounting on meta-reflexive transition.
metaReflexiveSecondLaw :: MetaReflexiveTransition -> Bool
metaReflexiveSecondLaw t =
  metaTransitionEntropyDrop t
    <= metaTransitionDissipatedWork t / bathTemp (metaTransitionBath t)

-- | Second law on meta-reflexive transition from Landauer bridge discharge.
metaReflexiveSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
metaReflexiveSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for meta-reflexive second law (no new axiom).
metaReflexiveSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
metaReflexiveSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
metaReflexivePhysicsGreen :: Bool
metaReflexivePhysicsGreen = False

-- | Lean/Coq: @meta_reflexive_physics_green_false@.
metaReflexivePhysicsGreenFalse :: Bool
metaReflexivePhysicsGreenFalse = not metaReflexivePhysicsGreen

-- | Production wiring stays open (meta-reflexive lift only).
metaReflexiveProductionWired :: Bool
metaReflexiveProductionWired = False

-- | Lean/Coq: @meta_reflexive_production_wired_false@.
metaReflexiveProductionWiredFalse :: Bool
metaReflexiveProductionWiredFalse = not metaReflexiveProductionWired

-- | Catalog witness: meso Urge MetaReflexive module present.
metaReflexiveModuleWitness :: Bool
metaReflexiveModuleWitness = True

-- | Zero new axiom discipline witness.
metaReflexiveNoNewAxiom :: Bool
metaReflexiveNoNewAxiom = True

-- | Second-argmin refusal: meta-reflexive composes 'excitementSelect' only.
metaReflexiveNoSecondArgmin :: Bool
metaReflexiveNoSecondArgmin =
  metaReflexiveNoLocalArgmin
    (MetaReflexiveCtx (ThermodynamicState 2400 0 0.3 30 40) [])

-- | Honest non-claim string (meso §10.5 meta-reflexive scaffold).
metaReflexiveNonClaim :: String
metaReflexiveNonClaim =
  "§10.5 umst-meta reflexive health of Urge morphisms; "
    ++ "positive refuse via MetaReflexiveRefusal; "
    ++ "not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
metaReflexiveNonClaimNonempty :: Bool
metaReflexiveNonClaimNonempty = length metaReflexiveNonClaim > 0

-- | Bypass evaluation is not silently healthy when bypassing.
metaReflexivePositiveRefuseNotSilent :: Bool
metaReflexivePositiveRefuseNotSilent =
  evaluateMetaGateBypass True /= MetaHealthy

-- | Honesty bundle: physics_green false, healthy admits, bypass refused.
metaReflexiveHonest :: Bool
metaReflexiveHonest =
  metaReflexivePhysicsGreenFalse
  && metaReflexiveProductionWiredFalse
  && metaFixtureHealthyAdmits
  && metaFixtureBypassRefused

-- | Positive refuse constructors for all morphism kinds sampled.
metaReflexivePositiveRefuse :: Bool
metaReflexivePositiveRefuse =
  refuseBypassMetaGate Merge == BypassMeta Merge
  && refuseSelfExempt MiObservation == SelfExempt MiObservation
  && refuseInventedGreen Recovery == InventedGreen Recovery
  && refuseFormalOverclaim SignedPropagate == FormalOverclaim SignedPropagate
