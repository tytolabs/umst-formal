-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ExcitementImport
-- Description : Meso acting Urge — §5.2 / §22.5 excitement import discipline.
--
-- Urge history recovery **is** 'excitementSelect' over admissible history
-- successors; refuse a second argmin / f64 F compare.
--
-- Meso Haskell hook: composes 'UMST.Urge.AdmitKleisli.excitementSelect' — full
-- @UMST.Excitement.select@ lives in @Lean/Excitement.lean@.
--
-- Sole physics axiom remains on Lean @LandauerLaw@ (cited, not restated).
-- Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives on
-- @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ExcitementImport
  ( -- * History recovery carrier (typed successor list)
    HistoryRecoveryCtx (..)
    -- * Recovery **is** excitementSelect (no local argmin)
  , urgeRecovery
  , urgeRecoverySelect
  , urgeRecoveryEqExcitementSelect
  , urgeRecoverySelectEqExcitementSelect
  , urgeRecoveryEqUrgeRecoverySelect
    -- * Imported selector properties (no local re-proof of argmin)
  , urgeRecoveryEmpty
  , urgeRecoveryAdmissibleFromList
    -- * Axiom discipline + honesty flags
  , urgeExcitementPhysicsGreen
  , urgeExcitementPhysicsGreenFalse
  , excitementImportProductionWired
  , excitementImportProductionWiredFalse
  , excitementImportModuleWitness
  , urgeRecoveryNoLocalArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , excitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: History recovery carrier (typed successor list)
-- ---------------------------------------------------------------------------

-- | Context for Urge history recovery: prior head + admissible successors.
data HistoryRecoveryCtx = HistoryRecoveryCtx
  { recoveryPrior       :: !ThermodynamicState
  , recoverySuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: Recovery **is** excitementSelect (no local argmin)
-- ---------------------------------------------------------------------------

-- | Urge history recovery composes 'excitementSelect' — not a second argmin.
urgeRecovery :: HistoryRecoveryCtx -> Either ExcitementResidue HistoryCandidate
urgeRecovery ctx =
  excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Alias on bare @(prior, successors)@ — same selector, no re-derivation.
urgeRecoverySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeRecoverySelect = excitementSelect

-- | Definitional witness: recovery API is 'excitementSelect'.
urgeRecoveryEqExcitementSelect :: HistoryRecoveryCtx -> Bool
urgeRecoveryEqExcitementSelect ctx =
  urgeRecovery ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Definitional witness: bare alias is 'excitementSelect'.
urgeRecoverySelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeRecoverySelectEqExcitementSelect src successors =
  urgeRecoverySelect src successors == excitementSelect src successors

-- | Recovery and bare select agree on identical inputs.
urgeRecoveryEqUrgeRecoverySelect :: HistoryRecoveryCtx -> Bool
urgeRecoveryEqUrgeRecoverySelect ctx =
  urgeRecovery ctx
    == urgeRecoverySelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- ---------------------------------------------------------------------------
-- SECTION 3: Imported selector properties (no local re-proof of argmin)
-- ---------------------------------------------------------------------------

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
urgeRecoveryEmpty :: ThermodynamicState -> Bool
urgeRecoveryEmpty src =
  urgeRecoverySelect src [] == Left ExcNoCandidates

-- | Successful recovery yields a candidate from the input list (meso hook).
urgeRecoveryAdmissibleFromList
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
  -> Bool
urgeRecoveryAdmissibleFromList _ (_ : _) (Right _) = True
urgeRecoveryAdmissibleFromList _ [] (Left ExcNoCandidates) = True
urgeRecoveryAdmissibleFromList _ _ _ = False

-- ---------------------------------------------------------------------------
-- SECTION 4: Axiom discipline + honesty flags
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgeExcitementPhysicsGreen :: Bool
urgeExcitementPhysicsGreen = False

-- | Lean/Coq: @urge_excitement_physics_green_false@.
urgeExcitementPhysicsGreenFalse :: Bool
urgeExcitementPhysicsGreenFalse = not urgeExcitementPhysicsGreen

-- | Production wiring stays open (meso import only).
excitementImportProductionWired :: Bool
excitementImportProductionWired = False

-- | Lean/Coq: @excitement_import_production_wired_false@.
excitementImportProductionWiredFalse :: Bool
excitementImportProductionWiredFalse = not excitementImportProductionWired

-- | Catalog witness: meso Urge ExcitementImport module present.
excitementImportModuleWitness :: Bool
excitementImportModuleWitness = True

-- | Recovery selector re-uses 'excitementSelect' — no Urge-local argmin.
urgeRecoveryNoLocalArgmin :: HistoryRecoveryCtx -> Bool
urgeRecoveryNoLocalArgmin ctx =
  urgeRecovery ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)
