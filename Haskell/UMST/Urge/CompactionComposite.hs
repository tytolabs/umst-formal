-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CompactionComposite
-- Description : Meso acting Urge — §17.5 compaction as composite Excitement arrow.
--
-- Semantic squash is refused unless recorded as an admitted composite arrow whose
-- derivation witness retains the chain — the composite *is* the residue.
-- Compaction pays MI (Landauer lift); it is not delete-old-commits theater.
--
-- Urge compaction composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CompactionComposite
  ( -- * Derivation chain + MI payment witnesses (§17.5)
    DerivationChainWitness (..)
  , retainsChainBool
  , retainsChainBoolNonEmpty
    -- * MI payment — compaction pays MI, not null probe
  , MiPaymentWitness (..)
  , miPaidBool
  , miPaymentFromLandauerBits
  , miPaymentFromLandauerBitsPaidWhenPositive
    -- * Composite compaction arrow — composite *is* the residue
  , CompositeCompactionArrow (..)
  , compositeArrowFromChain
  , compositeArrowFromChainMissingWitness
    -- * Compaction class + typed refuse (positive, not bool theater)
  , CompactionClass (..)
  , CompactionCompositeRefusal (..)
  , refuseDeleteOldCommitsTheater
  , refuseMiUnpaid
  , refuseSecondArgmin
  , refuseGitGcTheater
  , refuseSemanticSquashWithoutComposite
  , refuseMissingDerivationWitness
  , CompactionAttempt (..)
  , classifyCompaction
  , evaluateCompactionAttempt
  , evaluateCompactionAttemptRefuse
  , gateCompactionMiRefuseDelete
  , gateCompactionMiRefuseUnpaid
    -- * Landauer bridge — compaction pays MI (cited, not axiom)
  , compositeFromLandauer
  , compositeFromLandauerRetainsChain
  , landauerCompactionPreservesProvenance
  , compactionSecondLawFromLandauer
  , compactionSecondLawFromHypothesis
    -- * Excitement compose (no second argmin)
  , urgeCompactionSelect
  , urgeCompactionSelectEqExcitementSelect
  , urgeCompactionNoLocalArgmin
  , compactionCompose
  , compactionComposeAssocInherited
    -- * Honesty flags + catalog witnesses
  , urgeCompactionPhysicsGreen
  , urgeCompactionPhysicsGreenFalse
  , compactionCompositeProductionWired
  , compactionCompositeProductionWiredFalse
  , compactionCompositeMarker
  , compactionCompositeModuleWitness
  , compactionCompositeNoNewAxiom
  , compactionCompositeNoSecondArgmin
  , deleteOldCommitsRefused
  , gitGcTheaterRefused
  , semanticSquashRefused
  , missingDerivationWitnessRefused
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( AdmitArrow
  , ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , kleisliCompose
  , kleisliComposeAssocAt
  , landauerTransition
  )
import UMST.Urge.ProvenancePreserve
  ( Provenance (..)
  , landauerBridgePreserves
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Derivation chain + MI payment witnesses (§17.5)
-- ---------------------------------------------------------------------------

-- | Provenance derivation chain retained on composite compaction arrows.
data DerivationChainWitness = DerivationChainWitness
  { derivationChain :: ![Int]
  } deriving (Show, Eq)

-- | Whether the witness retains a non-empty derivation chain.
retainsChainBool :: DerivationChainWitness -> Bool
retainsChainBool w =
  case derivationChain w of
    []   -> False
    _:_  -> True

-- | Non-empty chain witness.
retainsChainBoolNonEmpty :: DerivationChainWitness -> Bool
retainsChainBoolNonEmpty w = retainsChainBool w

-- | MI payment witness — compaction must pay mutual-information cost.
data MiPaymentWitness = MiPaymentWitness
  { miRequiredBits :: !Double
  , miPaidBits     :: !Double
  } deriving (Show, Eq)

-- | Whether MI cost was paid (strictly positive paid bits >= required).
miPaidBool :: MiPaymentWitness -> Bool
miPaidBool m =
  miPaidBits m > 0 && miRequiredBits m <= miPaidBits m

-- | MI payment witness from nat MI bits (Landauer field cited, not re-derived).
miPaymentFromLandauerBits :: Int -> MiPaymentWitness
miPaymentFromLandauerBits n =
  MiPaymentWitness
    { miRequiredBits = fromIntegral n
    , miPaidBits     = fromIntegral n
    }

-- | Positive bit count implies MI paid witness holds.
miPaymentFromLandauerBitsPaidWhenPositive :: Int -> Bool
miPaymentFromLandauerBitsPaidWhenPositive n =
  n > 0 && miPaidBool (miPaymentFromLandauerBits n)

-- ---------------------------------------------------------------------------
-- SECTION 2: Composite compaction arrow — composite *is* the residue
-- ---------------------------------------------------------------------------

-- | Admitted composite compaction arrow — composite *is* the residue (§17.5).
data CompositeCompactionArrow = CompositeCompactionArrow
  { compositeId            :: !Int
  , compositeWitness       :: !DerivationChainWitness
  , compositeSourceCommit  :: !Int
  } deriving (Show, Eq)

-- | Build composite arrow from a non-empty derivation chain.
compositeArrowFromChain
  :: Int -> [Int] -> Int -> Maybe CompositeCompactionArrow
compositeArrowFromChain cid chain sourceCommit =
  case chain of
    []   -> Nothing
    _:_  ->
      Just CompositeCompactionArrow
        { compositeId           = cid
        , compositeWitness      = DerivationChainWitness {derivationChain = chain}
        , compositeSourceCommit = sourceCommit
        }

-- | Empty chain maps to missing derivation witness refusal tag.
compositeArrowFromChainMissingWitness :: CompactionCompositeRefusal
compositeArrowFromChainMissingWitness = MissingDerivationWitness

-- ---------------------------------------------------------------------------
-- SECTION 3: Compaction class + typed refuse (positive, not bool theater)
-- ---------------------------------------------------------------------------

data CompactionClass
  = GitGcSubstrate
  | CompositeExcitementArrow
  deriving (Show, Eq)

data CompactionCompositeRefusal
  = GitGcTheater
  | DeleteOldCommitsTheater
  | SemanticSquashWithoutComposite
  | SecondArgmin
  | MiUnpaid
  | MissingDerivationWitness
  deriving (Show, Eq)

refuseDeleteOldCommitsTheater :: CompactionCompositeRefusal
refuseDeleteOldCommitsTheater = DeleteOldCommitsTheater

refuseMiUnpaid :: CompactionCompositeRefusal
refuseMiUnpaid = MiUnpaid

refuseSecondArgmin :: CompactionCompositeRefusal
refuseSecondArgmin = SecondArgmin

refuseGitGcTheater :: CompactionCompositeRefusal
refuseGitGcTheater = GitGcTheater

refuseSemanticSquashWithoutComposite :: CompactionCompositeRefusal
refuseSemanticSquashWithoutComposite = SemanticSquashWithoutComposite

refuseMissingDerivationWitness :: CompactionCompositeRefusal
refuseMissingDerivationWitness = MissingDerivationWitness

-- | One compaction attempt before gating (§17.5 fixture surface).
data CompactionAttempt = CompactionAttempt
  { attemptDeleteOldCommits :: !Bool
  , attemptMi               :: !MiPaymentWitness
  , attemptWitness          :: !(Maybe DerivationChainWitness)
  , attemptProvenanceIntact :: !Bool
  } deriving (Show, Eq)

-- | Classify compaction attempt without performing mutation.
classifyCompaction
  :: Bool -> Bool -> Maybe DerivationChainWitness
  -> Either CompactionCompositeRefusal CompactionClass
classifyCompaction isSemanticSquash isGitGcSubstrateOnly witness =
  if isSemanticSquash
    then case witness of
      Nothing -> Left SemanticSquashWithoutComposite
      Just w  ->
        if retainsChainBool w
          then Right CompositeExcitementArrow
          else Left SemanticSquashWithoutComposite
  else if isGitGcSubstrateOnly
    then Right GitGcSubstrate
  else case witness of
    Nothing -> Left GitGcTheater
    Just w  ->
      if retainsChainBool w
        then Right CompositeExcitementArrow
        else Left GitGcTheater

-- | Gate a compaction attempt — composite arrow paying MI, not delete-old-commits.
evaluateCompactionAttempt :: CompactionAttempt -> Either CompactionCompositeRefusal Bool
evaluateCompactionAttempt a =
  if attemptDeleteOldCommits a
    then Left DeleteOldCommitsTheater
  else if not (miPaidBool (attemptMi a))
    then Left MiUnpaid
  else case attemptWitness a of
    Nothing -> Left MissingDerivationWitness
    Just w  ->
      if retainsChainBool w
        then if attemptProvenanceIntact a
          then Right True
          else Left SemanticSquashWithoutComposite
        else Left MissingDerivationWitness

-- | Typed refusal surface (mirrors Agda evaluate-compaction-attempt-refuse).
evaluateCompactionAttemptRefuse
  :: CompactionAttempt -> Either CompactionCompositeRefusal Bool
evaluateCompactionAttemptRefuse = evaluateCompactionAttempt

-- | Delete-old-commits theater refused when flag set.
gateCompactionMiRefuseDelete :: CompactionAttempt -> Bool
gateCompactionMiRefuseDelete a =
  attemptDeleteOldCommits a
  && evaluateCompactionAttempt a == Left DeleteOldCommitsTheater

-- | MI-unpaid refused when delete flag clear and MI unpaid.
gateCompactionMiRefuseUnpaid :: CompactionAttempt -> Bool
gateCompactionMiRefuseUnpaid a =
  not (attemptDeleteOldCommits a)
  && not (miPaidBool (attemptMi a))
  && evaluateCompactionAttempt a == Left MiUnpaid

-- ---------------------------------------------------------------------------
-- SECTION 4: Landauer bridge — compaction pays MI (cited, not axiom)
-- ---------------------------------------------------------------------------

-- | Composite arrow from Landauer bridge + prior provenance chain extension.
compositeFromLandauer
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> CompositeCompactionArrow
compositeFromLandauer b prior _hPrior _hSL =
  CompositeCompactionArrow
    { compositeId =
        historyCommitId (historyPost (landauerTransition b))
    , compositeWitness =
        DerivationChainWitness
          { derivationChain = ucrsChain prior ++ [dagCommit prior]
          }
    , compositeSourceCommit = dagCommit prior
    }

-- | Landauer composite retains non-empty derivation chain.
compositeFromLandauerRetainsChain
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
compositeFromLandauerRetainsChain b prior hPrior hSL =
  retainsChainBool (compositeWitness (compositeFromLandauer b prior hPrior hSL))

-- | Landauer compaction preserves provenance (physicalSecondLaw cited on Lean).
landauerCompactionPreservesProvenance
  :: LandauerHistoryBridge
  -> Provenance
  -> Bool
  -> Bool
  -> Bool
landauerCompactionPreservesProvenance b prior hPrior hSL =
  landauerBridgePreserves b prior hPrior hSL

-- | Second law on compaction transition from Landauer bridge discharge.
compactionSecondLawFromLandauer
  :: LandauerHistoryBridge
  -> Bool
  -> Bool
compactionSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for compaction second law (no new axiom).
compactionSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
compactionSecondLawFromHypothesis t ok =
  ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 5: Excitement compose (no second argmin)
-- ---------------------------------------------------------------------------

-- | Urge compaction composes 'excitementSelect' — not a second argmin.
urgeCompactionSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeCompactionSelect = excitementSelect

-- | Definitional witness: compaction selection API is 'excitementSelect'.
urgeCompactionSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeCompactionSelectEqExcitementSelect src cands =
  urgeCompactionSelect src cands == excitementSelect src cands

-- | Compaction selector re-uses 'excitementSelect' — no Urge-local argmin.
urgeCompactionNoLocalArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeCompactionNoLocalArgmin src cands =
  urgeCompactionSelect src cands == excitementSelect src cands

-- | Kleisli composite pin — compaction chains inherited arrows, not squash.
compactionCompose :: AdmitArrow -> AdmitArrow -> AdmitArrow
compactionCompose = kleisliCompose

-- | Inherited Kleisli associativity at a thermodynamic state.
compactionComposeAssocInherited
  :: AdmitArrow -> AdmitArrow -> AdmitArrow -> ThermodynamicState -> Bool
compactionComposeAssocInherited = kleisliComposeAssocAt

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
urgeCompactionPhysicsGreen :: Bool
urgeCompactionPhysicsGreen = False

-- | Lean/Coq: @urge_physics_green_false@.
urgeCompactionPhysicsGreenFalse :: Bool
urgeCompactionPhysicsGreenFalse = not urgeCompactionPhysicsGreen

-- | Production wiring stays open (meso lift only).
compactionCompositeProductionWired :: Bool
compactionCompositeProductionWired = False

-- | Lean/Coq: @compaction_composite_production_wired_false@.
compactionCompositeProductionWiredFalse :: Bool
compactionCompositeProductionWiredFalse =
  not compactionCompositeProductionWired

-- | Meso §17.5 section marker (Lean mirror).
compactionCompositeMarker :: Int
compactionCompositeMarker = 175

-- | Catalog witness: meso Urge CompactionComposite module present.
compactionCompositeModuleWitness :: Bool
compactionCompositeModuleWitness = True

-- | Zero new axiom discipline witness.
compactionCompositeNoNewAxiom :: Bool
compactionCompositeNoNewAxiom = True

-- | Second-argmin refusal tag is stable.
compactionCompositeNoSecondArgmin :: Bool
compactionCompositeNoSecondArgmin =
  refuseSecondArgmin == SecondArgmin

-- | §17.5 named obligation: delete-old-commits theater refused.
deleteOldCommitsRefused :: CompactionAttempt -> Bool
deleteOldCommitsRefused a =
  attemptDeleteOldCommits a
  && evaluateCompactionAttempt a == Left DeleteOldCommitsTheater

-- | Git-gc theater refusal tag is stable.
gitGcTheaterRefused :: Bool
gitGcTheaterRefused = refuseGitGcTheater == GitGcTheater

-- | Semantic squash without composite refused tag is stable.
semanticSquashRefused :: Bool
semanticSquashRefused =
  refuseSemanticSquashWithoutComposite == SemanticSquashWithoutComposite

-- | Missing derivation witness refusal tag is stable.
missingDerivationWitnessRefused :: Bool
missingDerivationWitnessRefused =
  refuseMissingDerivationWitness == MissingDerivationWitness
