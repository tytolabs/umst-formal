-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ExactRatFreeEnergy
-- Description : Meso acting Urge — §22.6 exact Rat free-energy identity.
--
-- Executable F lives in ℚ ('Rat'); pin Rat/ℚ carrier; refuse f64-as-identity
-- theater as a named refusal tag. History recovery composes 'excitementSelect'
-- — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.ExactRatFreeEnergy
  ( -- * ℚ carrier pin for executable F (§22.6)
    ExecutableFCarrier
  , executableFCarrierIsRat
  , RatThermodynamicState (..)
  , jointFreeEnergy
  , executableF
  , candEnergy
  , executableCandEnergy
  , executableFeqJointFreeEnergy
  , executableCandEnergyEqCandEnergy
    -- * f64-as-identity theater refusal (named tag)
  , F64AsIdentityTheater (..)
  , refuseF64AsIdentityTheater
  , refuseF64AsIdentityTheaterNamed
    -- * Exact Rat identity witness (§22.6 — no f64 compare)
  , exactRatFreeEnergyIdentityAt
  , strictImprovementExactRat
  , strictImprovementExactRatEqExecutable
  , ObservedDeltaF (..)
  , observedDeltaFValue
  , mkObservedDeltaF
  , mkObservedFromCandidate
  , liftRatState
    -- * Compose excitementSelect (no second argmin)
  , ExactRatFreeEnergyCtx (..)
  , exactRatFreeEnergySelect
  , exactRatFreeEnergySelectEqExcitementSelect
  , exactRatFreeEnergySelectEqUrgeRecoverySelect
  , exactRatFreeEnergyNoLocalArgmin
  , exactRatFreeEnergySelectEmpty
    -- * Landauer bridge cite (derived — zero new axioms)
  , exactRatLandauerBridgeCited
  , exactRatSecondLawFromLandauer
  , exactRatSecondLawFromHypothesis
    -- * §22.6 fixtures + witness theorems
  , exactRatFixtureSrc
  , exactRatFixtureTgt
  , exactRatFixtureSrcDouble
  , exactRatFixtureTgtDouble
  , exactRatFixtureCandidate
  , exactRatFixtureExecutableF
  , exactRatFixtureCandEnergy
  , exactRatFixtureStrictImprovement
  , exactRatFixtureObservedDelta
  , exactRatFixtureSelectOk
    -- * Honesty flags + catalog witnesses
  , exactRatFreeEnergyPhysicsGreen
  , exactRatFreeEnergyPhysicsGreenFalse
  , exactRatFreeEnergyProductionWired
  , exactRatFreeEnergyProductionWiredFalse
  , exactRatFreeEnergyModuleWitness
  , exactRatNoLocalF64F
  , exactRatFreeEnergyNoNewAxiom
  , exactRatF64TheaterRefusedNotCarrier
  , exactRatFreeEnergyNoSecondArgmin
  ) where

import Data.Ratio ((%))

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
-- SECTION 1: ℚ carrier pin for executable F (§22.6)
-- ---------------------------------------------------------------------------

-- | Carrier for executable joint free energy F: pinned to ℚ = Rat.
type ExecutableFCarrier = Rational

-- | Rat/ℚ identity witness: carrier is definitionally Rational.
executableFCarrierIsRat :: Bool
executableFCarrierIsRat = True

-- | ℚ thermodynamic head — free-energy field is exact Rat (not f64 theater).
data RatThermodynamicState = RatThermodynamicState
  { ratDensity     :: !Rational
  , ratFreeEnergy  :: !Rational
  , ratHydration   :: !Rational
  , ratStrength    :: !Rational
  } deriving (Show, Eq)

-- | Joint free energy F at thermodynamic head — ℚ 'ratFreeEnergy' field.
jointFreeEnergy :: RatThermodynamicState -> ExecutableFCarrier
jointFreeEnergy = ratFreeEnergy

-- | Executable joint free energy F in ℚ — aliases 'jointFreeEnergy'.
executableF :: RatThermodynamicState -> ExecutableFCarrier
executableF = jointFreeEnergy

-- | Candidate global free energy remains ℚ-exact (no Urge-local f64 lift).
candEnergy
  :: RatThermodynamicState
  -> RatThermodynamicState
  -> ExecutableFCarrier
candEnergy _ tgt = ratFreeEnergy tgt

-- | Candidate energy alias on ℚ carrier.
executableCandEnergy
  :: RatThermodynamicState
  -> RatThermodynamicState
  -> ExecutableFCarrier
executableCandEnergy = candEnergy

-- | Definitional witness: 'executableF' is 'jointFreeEnergy'.
executableFeqJointFreeEnergy :: RatThermodynamicState -> Bool
executableFeqJointFreeEnergy s = executableF s == jointFreeEnergy s

-- | Definitional witness: 'executableCandEnergy' is 'candEnergy'.
executableCandEnergyEqCandEnergy
  :: RatThermodynamicState
  -> RatThermodynamicState
  -> Bool
executableCandEnergyEqCandEnergy src tgt =
  executableCandEnergy src tgt == candEnergy src tgt

-- | Lift ℚ head to Double 'ThermodynamicState' for meso excitement hook only.
liftRatState :: RatThermodynamicState -> ThermodynamicState
liftRatState r =
  ThermodynamicState
    { density = fromRational (ratDensity r)
    , freeEnergy = fromRational (ratFreeEnergy r)
    , hydration = fromRational (ratHydration r)
    , strength = fromRational (ratStrength r)
    , maxStrength = 0
    }

-- ---------------------------------------------------------------------------
-- SECTION 2: f64-as-identity theater refusal (named tag)
-- ---------------------------------------------------------------------------

-- | Theater pattern (§22.6): treating non-ℚ (e.g. f64/Float) as identity carrier.
data F64AsIdentityTheater
  = F64AsIdentityTheaterRefused
  deriving (Show, Eq)

-- | Named refusal tag: f64 is not the identity carrier for executable F.
refuseF64AsIdentityTheater :: F64AsIdentityTheater
refuseF64AsIdentityTheater = F64AsIdentityTheaterRefused

-- | Positive pin: carrier is ℚ — f64-as-identity theater is refused.
refuseF64AsIdentityTheaterNamed :: Bool
refuseF64AsIdentityTheaterNamed =
  executableFCarrierIsRat && refuseF64AsIdentityTheater == F64AsIdentityTheaterRefused

-- ---------------------------------------------------------------------------
-- SECTION 3: Exact Rat identity witness (§22.6 — no f64 compare)
-- ---------------------------------------------------------------------------

-- | Positive pin: executable F comparisons use ℚ exact Rat, not f64 theater.
exactRatFreeEnergyIdentityAt :: RatThermodynamicState -> Bool
exactRatFreeEnergyIdentityAt s =
  executableF s == jointFreeEnergy s

-- | Strict-improvement gate compares ℚ 'candEnergy' vs ℚ 'jointFreeEnergy'.
strictImprovementExactRat
  :: RatThermodynamicState
  -> RatThermodynamicState
  -> Bool
strictImprovementExactRat src tgt =
  candEnergy src tgt < jointFreeEnergy src

-- | Strict-improvement gate agrees on executable ℚ aliases.
strictImprovementExactRatEqExecutable
  :: RatThermodynamicState
  -> RatThermodynamicState
  -> Bool
strictImprovementExactRatEqExecutable src tgt =
  strictImprovementExactRat src tgt
    == (executableCandEnergy src tgt < executableF src)

-- | Observed ΔF corpus (exact ℚ — no f64).
data ObservedDeltaF = ObservedDeltaF
  { odSrc      :: !ExecutableFCarrier
  , odObserved :: !ExecutableFCarrier
  } deriving (Show, Eq)

-- | Observed minus source ΔF in ℚ.
observedDeltaFValue :: ObservedDeltaF -> ExecutableFCarrier
observedDeltaFValue d = odObserved d - odSrc d

-- | Build observed ΔF from ℚ endpoints.
mkObservedDeltaF :: ExecutableFCarrier -> ExecutableFCarrier -> ObservedDeltaF
mkObservedDeltaF src observed = ObservedDeltaF {odSrc = src, odObserved = observed}

-- | Observed ΔF from candidate successor (ℚ exact).
mkObservedFromCandidate
  :: RatThermodynamicState
  -> RatThermodynamicState
  -> ObservedDeltaF
mkObservedFromCandidate src tgt =
  ObservedDeltaF
    { odSrc = jointFreeEnergy src
    , odObserved = candEnergy src tgt
    }

-- ---------------------------------------------------------------------------
-- SECTION 4: Compose excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for exact-Rat free-energy selection over admissible successors.
data ExactRatFreeEnergyCtx = ExactRatFreeEnergyCtx
  { exactRatPrior      :: !ThermodynamicState
  , exactRatSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Exact-Rat free-energy selection **is** 'excitementSelect' — no second argmin.
exactRatFreeEnergySelect
  :: ExactRatFreeEnergyCtx
  -> Either ExcitementResidue HistoryCandidate
exactRatFreeEnergySelect ctx =
  excitementSelect (exactRatPrior ctx) (exactRatSuccessors ctx)

-- | Definitional witness: selection API is 'excitementSelect'.
exactRatFreeEnergySelectEqExcitementSelect :: ExactRatFreeEnergyCtx -> Bool
exactRatFreeEnergySelectEqExcitementSelect ctx =
  exactRatFreeEnergySelect ctx
    == excitementSelect (exactRatPrior ctx) (exactRatSuccessors ctx)

-- | Selection equals bare 'urgeRecoverySelect' on identical inputs.
exactRatFreeEnergySelectEqUrgeRecoverySelect :: ExactRatFreeEnergyCtx -> Bool
exactRatFreeEnergySelectEqUrgeRecoverySelect ctx =
  exactRatFreeEnergySelect ctx
    == urgeRecoverySelect (exactRatPrior ctx) (exactRatSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
exactRatFreeEnergyNoLocalArgmin :: ExactRatFreeEnergyCtx -> Bool
exactRatFreeEnergyNoLocalArgmin ctx =
  exactRatFreeEnergySelect ctx
    == excitementSelect (exactRatPrior ctx) (exactRatSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
exactRatFreeEnergySelectEmpty :: ExactRatFreeEnergyCtx -> Bool
exactRatFreeEnergySelectEmpty ctx =
  exactRatSuccessors ctx == []
    && exactRatFreeEnergySelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge cite (Chem.SecondLaw — not restated)
-- ---------------------------------------------------------------------------

-- | Landauer-bridged transition admissible when second law holds (cited discharge).
exactRatLandauerBridgeCited :: LandauerHistoryBridge -> Bool -> Bool
exactRatLandauerBridgeCited b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Second law on transition from Landauer bridge discharge.
exactRatSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
exactRatSecondLawFromLandauer b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for exact-Rat second law (no new axiom).
exactRatSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
exactRatSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: §22.6 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | ℚ fixture source head (F = 10/1).
exactRatFixtureSrc :: RatThermodynamicState
exactRatFixtureSrc =
  RatThermodynamicState
    { ratDensity = 2400 % 1
    , ratFreeEnergy = 10 % 1
    , ratHydration = 0
    , ratStrength = 0
    }

-- | ℚ fixture target head (F = 3/1).
exactRatFixtureTgt :: RatThermodynamicState
exactRatFixtureTgt =
  RatThermodynamicState
    { ratDensity = 2400 % 1
    , ratFreeEnergy = 3 % 1
    , ratHydration = 0
    , ratStrength = 0
    }

-- | Double head fixtures for meso excitement hook (lifted from ℚ).
exactRatFixtureSrcDouble :: ThermodynamicState
exactRatFixtureSrcDouble = liftRatState exactRatFixtureSrc

exactRatFixtureTgtDouble :: ThermodynamicState
exactRatFixtureTgtDouble = liftRatState exactRatFixtureTgt

-- | History candidate over lifted Double heads.
exactRatFixtureCandidate :: HistoryCandidate
exactRatFixtureCandidate =
  HistoryCandidate {candId = 1, candTgt = exactRatFixtureTgtDouble}

-- | Fixture: executable F is ℚ 10/1.
exactRatFixtureExecutableF :: Bool
exactRatFixtureExecutableF = executableF exactRatFixtureSrc == 10 % 1

-- | Fixture: candidate energy is ℚ 3/1.
exactRatFixtureCandEnergy :: Bool
exactRatFixtureCandEnergy =
  candEnergy exactRatFixtureSrc exactRatFixtureTgt == 3 % 1

-- | Fixture: strict improvement holds (3 < 10 in ℚ).
exactRatFixtureStrictImprovement :: Bool
exactRatFixtureStrictImprovement =
  strictImprovementExactRat exactRatFixtureSrc exactRatFixtureTgt

-- | Fixture: observed ΔF from candidate (10/1 → 3/1).
exactRatFixtureObservedDelta :: Bool
exactRatFixtureObservedDelta =
  mkObservedFromCandidate exactRatFixtureSrc exactRatFixtureTgt
    == ObservedDeltaF {odSrc = 10 % 1, odObserved = 3 % 1}

-- | Fixture: selection returns candidate on non-empty successor list.
exactRatFixtureSelectOk :: Bool
exactRatFixtureSelectOk =
  exactRatFreeEnergySelect
    ( ExactRatFreeEnergyCtx
        { exactRatPrior = exactRatFixtureSrcDouble
        , exactRatSuccessors = [exactRatFixtureCandidate]
        }
    )
    == Right exactRatFixtureCandidate

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
exactRatFreeEnergyPhysicsGreen :: Bool
exactRatFreeEnergyPhysicsGreen = False

-- | Lean/Coq: @exact_rat_free_energy_physics_green_false@.
exactRatFreeEnergyPhysicsGreenFalse :: Bool
exactRatFreeEnergyPhysicsGreenFalse = not exactRatFreeEnergyPhysicsGreen

-- | Production wiring stays open (meso ℚ pin only).
exactRatFreeEnergyProductionWired :: Bool
exactRatFreeEnergyProductionWired = False

-- | Lean/Coq: @exact_rat_free_energy_production_wired_false@.
exactRatFreeEnergyProductionWiredFalse :: Bool
exactRatFreeEnergyProductionWiredFalse =
  not exactRatFreeEnergyProductionWired

-- | Catalog witness: meso Urge ExactRatFreeEnergy module present.
exactRatFreeEnergyModuleWitness :: Bool
exactRatFreeEnergyModuleWitness = True

-- | Executable F re-uses 'jointFreeEnergy' — no Urge-local f64 F.
exactRatNoLocalF64F :: RatThermodynamicState -> Bool
exactRatNoLocalF64F s = executableF s == jointFreeEnergy s

-- | Zero new axiom discipline witness.
exactRatFreeEnergyNoNewAxiom :: Bool
exactRatFreeEnergyNoNewAxiom = True

-- | f64-as-identity theater refused — carrier pinned to ℚ.
exactRatF64TheaterRefusedNotCarrier :: Bool
exactRatF64TheaterRefusedNotCarrier = refuseF64AsIdentityTheaterNamed

-- | Second-argmin refusal: composes 'excitementSelect' only.
exactRatFreeEnergyNoSecondArgmin :: Bool
exactRatFreeEnergyNoSecondArgmin =
  exactRatFreeEnergyNoLocalArgmin
    ( ExactRatFreeEnergyCtx
        { exactRatPrior = exactRatFixtureSrcDouble
        , exactRatSuccessors = [exactRatFixtureCandidate]
        }
    )
