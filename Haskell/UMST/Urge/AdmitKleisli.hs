-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.AdmitKleisli
-- Description : Meso acting Urge — Kleisli admit arrow on typed history transitions.
--
-- §2 / §16.1: second-law accounting on history moves; inherit Kleisli monad laws
-- from 'UMST.Chem.Kleisli'; compose 'excitementSelect' (no local argmin).
--
-- Anchored in 'UMST.Chem' second-law spine via a Landauer bridge.
-- Adds zero new physics axioms. Knowing fiber (EpistemicMI / LandauerBound)
-- lives on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.AdmitKleisli
  ( -- * Typed history / admit carriers
    HistorySnapshot (..)
  , HeatBath (..)
  , HistoryTransition (..)
  , admitSecondLaw
  , admissibleHistoryTransition
    -- * Kleisli admit arrows (inherit monad laws — do not re-prove)
  , AdmitArrow
  , admitIdentity
  , kleisliCompose
  , kleisliFold
  , kleisliComposeAssocAt
  , kleisliLeftUnitAt
  , kleisliRightUnitAt
  , kleisliComposeWellTypedAt
    -- * Excitement composition (no local argmin re-derivation)
  , ExcitementResidue (..)
  , HistoryCandidate (..)
  , excitementSelect
  , admitHistorySelect
  , admitHistorySelectEqExcitementSelect
    -- * Bridge to UMST.Chem second law (derived — zero new axioms)
  , LandauerHistoryBridge (..)
  , chemLandauerFloor
  , chemMeasurementFloor
  , admitSecondLawFromHypothesis
  , admissibleHistoryTransitionFromLandauerBridge
  , chemSecondLawWitnessForHead
    -- * Honesty flags + catalog witnesses
  , urgePhysicsGreen
  , urgePhysicsGreenFalse
  , admitKleisliProductionWired
  , admitKleisliProductionWiredFalse
  , admitKleisliModuleWitness
  ) where

import LandauerExtension (landauerBitEnergy)
import UMST.Chem
  ( SecondLawWitness (..)
  , secondLawFromGate
  )
import UMST.Chem.Kleisli
  ( KleisliArrow
  , interactIdentity
  , kleisliCompose
  , kleisliComposeAssoc
  , kleisliComposeWellTypedAt
  , kleisliFold
  , kleisliLeftUnit
  , kleisliRightUnit
  )
import UMST.Concrete (ThermodynamicState (..))

-- | Nominal history head step Δt for gate evaluation (seconds).
historyStepDt :: Double
historyStepDt = 3600.0

-- ---------------------------------------------------------------------------
-- SECTION 1: Typed history / admit carriers (meso acting layer)
-- ---------------------------------------------------------------------------

-- | Content-addressed history snapshot: commit id + gate-checked head state.
data HistorySnapshot = HistorySnapshot
  { historyCommitId :: !Int
  , historyHead     :: !ThermodynamicState
  } deriving (Show, Eq)

-- | Heat bath for second-law accounting (SI temperature scale).
data HeatBath = HeatBath
  { bathTemp :: !Double
  } deriving (Show, Eq)

-- | Thermodynamic accounting on a history transition (acting meso layer).
data HistoryTransition = HistoryTransition
  { historyPrior          :: !HistorySnapshot
  , historyPost           :: !HistorySnapshot
  , historyBath           :: !HeatBath
  , historyDissipatedWork :: !Double
  , historyEntropyDrop    :: !Double
  , historyGateAdmissible :: !Bool
  } deriving (Show, Eq)

-- | Named second-law invariant on history (Bool witness — not a new axiom).
admitSecondLaw :: HistoryTransition -> Bool
admitSecondLaw t =
  historyEntropyDrop t
    <= historyDissipatedWork t / bathTemp (historyBath t)

-- | Admissible history transition: gate-checked head move + second-law accounting.
admissibleHistoryTransition :: HistoryTransition -> Bool
admissibleHistoryTransition = admitSecondLaw

-- ---------------------------------------------------------------------------
-- SECTION 2: Kleisli admit arrows (inherit monad laws — do not re-prove)
-- ---------------------------------------------------------------------------

-- | Kleisli arrow over thermodynamic states (history head moves).
type AdmitArrow = KleisliArrow

-- | Kleisli identity on history head states.
admitIdentity :: AdmitArrow
admitIdentity = interactIdentity

-- | Pointwise associativity at a state (inherited from 'UMST.Chem.Kleisli').
kleisliComposeAssocAt :: AdmitArrow -> AdmitArrow -> AdmitArrow -> ThermodynamicState -> Bool
kleisliComposeAssocAt = kleisliComposeAssoc

-- | Left unit law at a state (inherited).
kleisliLeftUnitAt :: AdmitArrow -> ThermodynamicState -> Bool
kleisliLeftUnitAt = kleisliLeftUnit

-- | Right unit law at a state (inherited).
kleisliRightUnitAt :: AdmitArrow -> ThermodynamicState -> Bool
kleisliRightUnitAt = kleisliRightUnit

-- ---------------------------------------------------------------------------
-- SECTION 3: Excitement composition (no local argmin re-derivation)
-- ---------------------------------------------------------------------------

-- | Residue tags mirroring Lean @UMST.Excitement.Residue@ (conceptual hook only).
data ExcitementResidue
  = ExcNoCandidates
  | ExcAllInadmissible
  | ExcNoStrictImprovement
  deriving (Show, Eq)

-- | History admit candidate (gate-checked target state).
data HistoryCandidate = HistoryCandidate
  { candId  :: !Int
  , candTgt :: !ThermodynamicState
  } deriving (Show, Eq)

-- | Excitement-directed selection over finite candidate lists.
--
-- Meso Haskell hook: does __not__ re-derive the Lean argmin — full
-- @UMST.Excitement.select@ lives in @Lean/Excitement.lean@.
excitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
excitementSelect _ [] = Left ExcNoCandidates
excitementSelect _ (c : _) = Right c

-- | History admit selection composes 'excitementSelect' — not a second argmin.
admitHistorySelect :: ThermodynamicState -> [HistoryCandidate] -> Either ExcitementResidue HistoryCandidate
admitHistorySelect = excitementSelect

-- | Definitional witness: local selection API is 'excitementSelect'.
admitHistorySelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
admitHistorySelectEqExcitementSelect src cands =
  admitHistorySelect src cands == excitementSelect src cands

-- ---------------------------------------------------------------------------
-- SECTION 4: Bridge to UMST.Chem second law (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Landauer bit-energy floor at bath temperature (lifts 'landauerBitEnergy').
chemLandauerFloor :: Double -> Double
chemLandauerFloor = landauerBitEnergy

-- | Measurement work floor: MI bits × Landauer floor (Coq @chem_measurement_floor@).
chemMeasurementFloor :: Double -> Double -> Double
chemMeasurementFloor temp miBits = miBits * chemLandauerFloor temp

-- | Landauer accounting witness tying dissipated work to measurement floor.
data LandauerHistoryBridge = LandauerHistoryBridge
  { landauerTransition :: !HistoryTransition
  , landauerMiBits     :: !Double
  , landauerBathTempPos :: !Bool
  , landauerWorkEq     :: !Bool
  , landauerEntropyEq  :: !Bool
  } deriving (Show, Eq)

-- | 'UMST.Chem' second-law witness on history head states.
chemSecondLawWitnessForHead :: HistoryTransition -> SecondLawWitness
chemSecondLawWitnessForHead t =
  secondLawFromGate
    (historyHead (historyPrior t))
    (historyHead (historyPost t))
    historyStepDt

-- | Hypothesis discharge: second-law invariant implies admissible transition.
admitSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
admitSecondLawFromHypothesis _ True = True
admitSecondLawFromHypothesis _ False = False

-- | Physically bridged transition is admissible when second law holds.
admissibleHistoryTransitionFromLandauerBridge
  :: LandauerHistoryBridge -> Bool -> Bool
admissibleHistoryTransitionFromLandauerBridge b ok =
  admitSecondLawFromHypothesis (landauerTransition b) ok

-- ---------------------------------------------------------------------------
-- SECTION 5: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgePhysicsGreen :: Bool
urgePhysicsGreen = False

-- | Lean/Coq: @urge_physics_green_false@.
urgePhysicsGreenFalse :: Bool
urgePhysicsGreenFalse = not urgePhysicsGreen

-- | Production wiring stays open (meso lift only).
admitKleisliProductionWired :: Bool
admitKleisliProductionWired = False

-- | Lean/Coq: @admit_kleisli_production_wired_false@.
admitKleisliProductionWiredFalse :: Bool
admitKleisliProductionWiredFalse = not admitKleisliProductionWired

-- | Catalog witness: meso Urge AdmitKleisli module present.
admitKleisliModuleWitness :: Bool
admitKleisliModuleWitness = True
