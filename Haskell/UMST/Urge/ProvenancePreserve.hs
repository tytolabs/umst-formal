-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ProvenancePreserve
-- Description : Meso acting Urge — §17.4 provenance as a type (not prose).
--
-- 'Provenance' = UCRS stamp chain + admitted Kleisli DAG commit + Landauer witness
-- slot. 'preserves' on history transitions; recovery composes 'excitementSelect' —
-- no local argmin re-derivation.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives on
-- @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ProvenancePreserve
  ( -- * Transition + typed provenance carrier (§17.4)
    Transition
  , Provenance (..)
  , genesisProvenance
    -- * §17.4 preservation on transitions
  , preserves
  , preservesChainAppend
  , preservesWitnessRetained
  , preservesDischargesSecondLaw
    -- * Landauer bridge discharge
  , postProvenanceFromLandauer
  , landauerBridgePreserves
  , admissibleHistoryTransitionLandauerPreserves
    -- * Recovery composes excitementSelect (no local argmin)
  , ProvenanceRecoveryCtx (..)
  , provenanceRecovery
  , provenanceRecoverySelect
  , provenanceSelect
  , provenanceSelectEqExcitementSelect
  , provenanceRecoveryEqExcitementSelect
  , provenanceRecoveryNoLocalArgmin
  , excitementSelectRespectsPreserves
    -- * Honesty flags + catalog witnesses
  , urgeProvenancePhysicsGreen
  , urgeProvenancePhysicsGreenFalse
  , provenancePreserveProductionWired
  , provenancePreserveProductionWiredFalse
  , provenancePreserveModuleWitness
  , provenancePreserveNoNewAxiom
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

-- ---------------------------------------------------------------------------
-- SECTION 1: Transition + typed provenance carrier (§17.4)
-- ---------------------------------------------------------------------------

-- | Meso transition carrier (history move with second-law accounting).
type Transition = HistoryTransition

-- | Typed provenance: stamp chain + admitted DAG commit + Landauer witness slot.
data Provenance = Provenance
  { ucrsChain        :: ![Int]
  , dagCommit        :: !Int
  , landauerWitness  :: !Bool
  } deriving (Show, Eq)

-- | Empty provenance at genesis commit (no prior stamps).
genesisProvenance :: Int -> Provenance
genesisProvenance commitId = Provenance
  { ucrsChain       = []
  , dagCommit       = commitId
  , landauerWitness = True
  }

-- ---------------------------------------------------------------------------
-- SECTION 2: §17.4 preservation on transitions
-- ---------------------------------------------------------------------------

-- | §17.4 preservation: post extends stamp chain, aligns DAG endpoints, retains witness.
preserves :: Transition -> Provenance -> Provenance -> Bool
preserves t prior post =
  dagCommit prior == historyCommitId (historyPrior t)
  && dagCommit post == historyCommitId (historyPost t)
  && ucrsChain post == ucrsChain prior ++ [dagCommit prior]
  && (not (landauerWitness prior) || landauerWitness post)
  && (not (landauerWitness post) || admitSecondLaw t)

-- | Chain-append conjunct of 'preserves'.
preservesChainAppend :: Transition -> Provenance -> Provenance -> Bool
preservesChainAppend t prior post =
  preserves t prior post
  && ucrsChain post == ucrsChain prior ++ [dagCommit prior]

-- | Witness retention conjunct of 'preserves'.
preservesWitnessRetained :: Transition -> Provenance -> Provenance -> Bool
preservesWitnessRetained t prior post =
  preserves t prior post
  && (not (landauerWitness prior) || landauerWitness post)

-- | Second-law discharge conjunct of 'preserves'.
preservesDischargesSecondLaw :: Transition -> Provenance -> Provenance -> Bool
preservesDischargesSecondLaw t prior post =
  preserves t prior post
  && (not (landauerWitness post) || admitSecondLaw t)

-- ---------------------------------------------------------------------------
-- SECTION 3: Landauer bridge discharge
-- ---------------------------------------------------------------------------

-- | Post provenance from Landauer bridge + prior chain extension.
postProvenanceFromLandauer
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Provenance
postProvenanceFromLandauer b prior _hPrior _hSL = Provenance
  { ucrsChain = ucrsChain prior ++ [dagCommit prior]
  , dagCommit =
      historyCommitId (historyPost (landauerTransition b))
  , landauerWitness = True
  }

-- | Landauer-bridged transition preserves provenance when prior aligns and SL holds.
landauerBridgePreserves
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
landauerBridgePreserves b prior hPrior hSL =
  hPrior
  && hSL
  && preserves
       (landauerTransition b)
       prior
       (postProvenanceFromLandauer b prior hPrior hSL)

-- | Admissible transition + preservation from Landauer bridge discharge.
admissibleHistoryTransitionLandauerPreserves
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
admissibleHistoryTransitionLandauerPreserves b prior hPrior hSL =
  hPrior
  && hSL
  && admissibleHistoryTransition (landauerTransition b)
  && landauerBridgePreserves b prior hPrior hSL

-- ---------------------------------------------------------------------------
-- SECTION 4: Recovery composes excitementSelect (no local argmin)
-- ---------------------------------------------------------------------------

-- | Context for provenance-aware history recovery.
data ProvenanceRecoveryCtx = ProvenanceRecoveryCtx
  { recoveryPrior       :: !ThermodynamicState
  , recoverySuccessors  :: ![HistoryCandidate]
  , recoveryProvenance  :: !Provenance
  } deriving (Show, Eq)

-- | Provenance recovery composes 'excitementSelect' — not a second argmin.
provenanceRecovery
  :: ProvenanceRecoveryCtx
  -> Either ExcitementResidue HistoryCandidate
provenanceRecovery ctx =
  excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Bare alias on @(prior, successors)@ — same selector, no re-derivation.
provenanceRecoverySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
provenanceRecoverySelect = excitementSelect

-- | Provenance selection composes 'excitementSelect' — not a second argmin.
provenanceSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
provenanceSelect = excitementSelect

-- | Definitional witness: provenance selection API is 'excitementSelect'.
provenanceSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
provenanceSelectEqExcitementSelect src cands =
  provenanceSelect src cands == excitementSelect src cands

-- | Definitional witness: recovery API is 'excitementSelect'.
provenanceRecoveryEqExcitementSelect :: ProvenanceRecoveryCtx -> Bool
provenanceRecoveryEqExcitementSelect ctx =
  provenanceRecovery ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Recovery selector re-uses 'excitementSelect' — no Urge-local argmin.
provenanceRecoveryNoLocalArgmin :: ProvenanceRecoveryCtx -> Bool
provenanceRecoveryNoLocalArgmin ctx =
  provenanceRecovery ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Excitement selection respects preservation obligation (named; wiring open).
excitementSelectRespectsPreserves :: Transition -> Provenance -> Provenance -> Bool
excitementSelectRespectsPreserves t prior post =
  preserves t prior post

-- ---------------------------------------------------------------------------
-- SECTION 5: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgeProvenancePhysicsGreen :: Bool
urgeProvenancePhysicsGreen = False

-- | Lean/Coq: @urge_physics_green_false@.
urgeProvenancePhysicsGreenFalse :: Bool
urgeProvenancePhysicsGreenFalse = not urgeProvenancePhysicsGreen

-- | Production wiring stays open (meso lift only).
provenancePreserveProductionWired :: Bool
provenancePreserveProductionWired = False

-- | Lean/Coq: @provenance_preserve_production_wired_false@.
provenancePreserveProductionWiredFalse :: Bool
provenancePreserveProductionWiredFalse = not provenancePreserveProductionWired

-- | Catalog witness: meso Urge ProvenancePreserve module present.
provenancePreserveModuleWitness :: Bool
provenancePreserveModuleWitness = True

-- | Zero new axiom discipline witness.
provenancePreserveNoNewAxiom :: Bool
provenancePreserveNoNewAxiom = True
