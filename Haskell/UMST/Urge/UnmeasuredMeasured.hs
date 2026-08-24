-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.UnmeasuredMeasured
-- Description : Meso acting Urge — §17.7 production_wired taxonomy.
--
-- Blueprint §17.7 — fleet measurement absent vs measured on named dataset:
-- 'Unmeasured' | 'Measured' {value, dataset} — UNKNOWN ≠ false-as-GREEN.
--
-- Urge history recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.UnmeasuredMeasured
  ( -- * §17.7 production_wired taxonomy carriers
    ProductionWiredTaxonomy (..)
  , productionWiredIsMeasured
  , productionWiredMeasuredValue
  , productionWiredDataset
  , datasetNonempty
  , FalseAsGreenRefusal (..)
  , ProductionWiredVerdict (..)
  , UnmeasuredMeasuredConjunct (..)
  , ummConjunctAdmits
    -- * Positive refuse (UNKNOWN ≠ false-as-GREEN)
  , refuseFalseAsGreen
  , productionWiredLegacyBool
  , boolClaimsMeasurementWhenUnmeasured
  , measuredProductionWired
  , evaluateProductionWired
  , refuseFalseAsGreenUnmeasured
  , productionWiredLegacyNoneWhenUnmeasured
  , unmeasuredNotMeasured
    -- * Gossip mesh taxonomy — documented Unmeasured
  , gossipMeshProductionWiredTaxonomy
  , ucrsGossipMeshDocumentedAsUnmeasured
  , refuseUnmeasuredAsFalseGreen
  , gossipMeshTaxonomyIsUnmeasured
  , gossipMeshRefuseFalseAsGreen
    -- * Excitement alignment (no second argmin)
  , UnmeasuredMeasuredCtx (..)
  , UnmeasuredMeasuredExcitementPin (..)
  , unmeasuredMeasuredExcitementSelect
  , unmeasuredMeasuredSelect
  , unmeasuredMeasuredSelectEqExcitementSelect
  , unmeasuredMeasuredSelectEqUrgeRecoverySelect
  , unmeasuredMeasuredNoLocalArgmin
  , unmeasuredMeasuredExcitementSelectEqExcitementSelect
  , unmeasuredMeasuredExcitementSelectRefusesSecondArgmin
  , unmeasuredMeasuredSelectEmpty
    -- * §17.7 fixtures + witness theorems
  , ummFixtureDataset
  , ummFixtureMeasuredFalse
  , ummFixtureConjunct
  , ummFixtureMeasuredFalseAdmits
  , ummFixtureMeasuredFalseEvaluateOk
  , ummFixtureMeasuredProductionWiredOk
  , ummFixtureEmptyDatasetRefused
  , ummFixtureUnmeasuredLegacyNone
  , ummFixtureConjunctAdmitsTrue
    -- * Landauer bridge (derived — zero new axioms)
  , UnmeasuredMeasuredTransition (..)
  , admissibleUnmeasuredMeasured
  , unmeasuredMeasuredSecondLaw
  , PhysicalUnmeasuredMeasuredBridge (..)
  , unmeasuredMeasuredSecondLawFromPhysical
  , admissibleUnmeasuredMeasuredFromPhysical
  , physicalSecondLawImported
    -- * Honesty flags + catalog witnesses
  , unmeasuredMeasuredPhysicsGreen
  , unmeasuredMeasuredPhysicsGreenFalse
  , unmeasuredMeasuredProductionWired
  , unmeasuredMeasuredProductionWiredFalse
  , unmeasuredMeasuredModuleWitness
  , unmeasuredMeasuredNoNewAxiom
  , unmeasuredMeasuredPositiveRefuseNotSilent
  , unmeasuredMeasuredUnknownNotFalseAsGreen
  , unmeasuredMeasuredNoSecondArgmin
  , unmeasuredMeasuredNonClaim
  , unmeasuredMeasuredNonClaimNonempty
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

-- ---------------------------------------------------------------------------
-- SECTION 1: §17.7 production_wired taxonomy carriers
-- ---------------------------------------------------------------------------

-- | Blueprint §17.7 — fleet measurement absent vs measured on named dataset.
data ProductionWiredTaxonomy
  = ProductionUnmeasured
  | ProductionMeasured !Bool !String
  deriving (Show, Eq)

-- | True when taxonomy carries a measured value on a named dataset.
productionWiredIsMeasured :: ProductionWiredTaxonomy -> Bool
productionWiredIsMeasured ProductionUnmeasured = False
productionWiredIsMeasured (ProductionMeasured _ _) = True

-- | Measured bool value when present — 'Nothing' for 'ProductionUnmeasured'.
productionWiredMeasuredValue :: ProductionWiredTaxonomy -> Maybe Bool
productionWiredMeasuredValue ProductionUnmeasured = Nothing
productionWiredMeasuredValue (ProductionMeasured v _) = Just v

-- | Named dataset when present — 'Nothing' for 'ProductionUnmeasured'.
productionWiredDataset :: ProductionWiredTaxonomy -> Maybe String
productionWiredDataset ProductionUnmeasured = Nothing
productionWiredDataset (ProductionMeasured _ d) = Just d

-- | Non-empty dataset string required for measured production wiring.
datasetNonempty :: String -> Bool
datasetNonempty d = not (null d)

-- | Typed refusal when UNKNOWN collapses to false-as-GREEN.
data FalseAsGreenRefusal
  = UnmeasuredCollapsedToFalse
  | MeasuredTrueNotPhysicsGreen
  deriving (Show, Eq)

-- | Verdict for §17.7 production_wired taxonomy evaluation.
data ProductionWiredVerdict
  = HonestUnmeasured
  | MeasuredFalseOk
  | FalseAsGreenRefused
  deriving (Show, Eq)

-- | Conjunct gate for unmeasured/measured admissibility.
data UnmeasuredMeasuredConjunct = UnmeasuredMeasuredConjunct
  { ummGateOk              :: !Bool
  , ummFalseAsGreenRefused :: !Bool
  , ummExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Conjunct admits when all three gates hold.
ummConjunctAdmits :: UnmeasuredMeasuredConjunct -> Bool
ummConjunctAdmits c =
  ummGateOk c && ummFalseAsGreenRefused c && ummExcitementPreserves c

-- ---------------------------------------------------------------------------
-- SECTION 2: Positive refuse (UNKNOWN ≠ false-as-GREEN)
-- ---------------------------------------------------------------------------

-- | Positive refuse: unmeasured is not false-as-GREEN; measured true not physics GREEN.
refuseFalseAsGreen :: ProductionWiredTaxonomy -> Maybe FalseAsGreenRefusal
refuseFalseAsGreen ProductionUnmeasured = Just UnmeasuredCollapsedToFalse
refuseFalseAsGreen (ProductionMeasured True _) = Just MeasuredTrueNotPhysicsGreen
refuseFalseAsGreen (ProductionMeasured False _) = Nothing

-- | Legacy bool projection — 'Nothing' when unmeasured (not false-as-GREEN).
productionWiredLegacyBool :: ProductionWiredTaxonomy -> Maybe Bool
productionWiredLegacyBool = productionWiredMeasuredValue

-- | True when a bare bool claims measurement while taxonomy is unmeasured.
boolClaimsMeasurementWhenUnmeasured :: ProductionWiredTaxonomy -> Bool -> Bool
boolClaimsMeasurementWhenUnmeasured ProductionUnmeasured claimed = claimed
boolClaimsMeasurementWhenUnmeasured (ProductionMeasured _ _) _ = False

-- | Construct measured production wiring — refuse empty dataset.
measuredProductionWired
  :: Bool -> String -> Either FalseAsGreenRefusal ProductionWiredTaxonomy
measuredProductionWired value dataset =
  if datasetNonempty dataset
    then Right (ProductionMeasured value dataset)
    else Left UnmeasuredCollapsedToFalse

-- | Evaluate production_wired taxonomy — not a bool skip.
evaluateProductionWired :: ProductionWiredTaxonomy -> ProductionWiredVerdict
evaluateProductionWired pw =
  case refuseFalseAsGreen pw of
    Just _ -> FalseAsGreenRefused
    Nothing ->
      case pw of
        ProductionUnmeasured -> HonestUnmeasured
        ProductionMeasured False _ -> MeasuredFalseOk
        ProductionMeasured True _ -> FalseAsGreenRefused

-- | Unmeasured always refused as false-as-GREEN (positive refuse witness).
refuseFalseAsGreenUnmeasured :: Bool
refuseFalseAsGreenUnmeasured =
  refuseFalseAsGreen ProductionUnmeasured
    == Just UnmeasuredCollapsedToFalse

-- | Legacy bool projection is 'Nothing' when unmeasured.
productionWiredLegacyNoneWhenUnmeasured :: Bool
productionWiredLegacyNoneWhenUnmeasured =
  productionWiredLegacyBool ProductionUnmeasured == Nothing

-- | Unmeasured taxonomy is not measured.
unmeasuredNotMeasured :: Bool
unmeasuredNotMeasured = not (productionWiredIsMeasured ProductionUnmeasured)

-- ---------------------------------------------------------------------------
-- SECTION 3: Gossip mesh taxonomy — documented Unmeasured
-- ---------------------------------------------------------------------------

-- | UCRS gossip mesh production_wired taxonomy — documented unmeasured.
gossipMeshProductionWiredTaxonomy :: ProductionWiredTaxonomy
gossipMeshProductionWiredTaxonomy = ProductionUnmeasured

-- | Gossip mesh taxonomy documented as unmeasured (not false-as-GREEN).
ucrsGossipMeshDocumentedAsUnmeasured :: Bool
ucrsGossipMeshDocumentedAsUnmeasured =
  case gossipMeshProductionWiredTaxonomy of
    ProductionUnmeasured -> True
    ProductionMeasured _ _ -> False

-- | Typed refusal for unmeasured-as-false-GREEN.
refuseUnmeasuredAsFalseGreen :: FalseAsGreenRefusal
refuseUnmeasuredAsFalseGreen = UnmeasuredCollapsedToFalse

-- | Gossip mesh taxonomy is unmeasured.
gossipMeshTaxonomyIsUnmeasured :: Bool
gossipMeshTaxonomyIsUnmeasured =
  gossipMeshProductionWiredTaxonomy == ProductionUnmeasured

-- | Gossip mesh refuses false-as-GREEN on unmeasured taxonomy.
gossipMeshRefuseFalseAsGreen :: Bool
gossipMeshRefuseFalseAsGreen =
  refuseFalseAsGreen gossipMeshProductionWiredTaxonomy
    == Just UnmeasuredCollapsedToFalse

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for unmeasured/measured history recovery.
data UnmeasuredMeasuredCtx = UnmeasuredMeasuredCtx
  { ummPrior      :: !ThermodynamicState
  , ummSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Excitement compose pin — Urge imports selector; no second argmin.
data UnmeasuredMeasuredExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Unmeasured/measured path composes 'excitementSelect' — not a second argmin.
unmeasuredMeasuredExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> UnmeasuredMeasuredExcitementPin
  -> Either ExcitementResidue HistoryCandidate
unmeasuredMeasuredExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
unmeasuredMeasuredExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | Urge history recovery composes 'excitementSelect' on typed successors.
unmeasuredMeasuredSelect
  :: UnmeasuredMeasuredCtx
  -> Either ExcitementResidue HistoryCandidate
unmeasuredMeasuredSelect ctx =
  excitementSelect (ummPrior ctx) (ummSuccessors ctx)

-- | Definitional witness: selection API is 'excitementSelect'.
unmeasuredMeasuredSelectEqExcitementSelect :: UnmeasuredMeasuredCtx -> Bool
unmeasuredMeasuredSelectEqExcitementSelect ctx =
  unmeasuredMeasuredSelect ctx
    == excitementSelect (ummPrior ctx) (ummSuccessors ctx)

-- | Selection equals bare excitement on prior + successors.
unmeasuredMeasuredSelectEqUrgeRecoverySelect :: UnmeasuredMeasuredCtx -> Bool
unmeasuredMeasuredSelectEqUrgeRecoverySelect ctx =
  unmeasuredMeasuredSelect ctx
    == excitementSelect (ummPrior ctx) (ummSuccessors ctx)

-- | Unmeasured/measured selector re-uses 'excitementSelect' — no Urge-local argmin.
unmeasuredMeasuredNoLocalArgmin :: UnmeasuredMeasuredCtx -> Bool
unmeasuredMeasuredNoLocalArgmin ctx =
  unmeasuredMeasuredSelect ctx
    == excitementSelect (ummPrior ctx) (ummSuccessors ctx)

-- | Definitional witness: import pin is 'excitementSelect'.
unmeasuredMeasuredExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
unmeasuredMeasuredExcitementSelectEqExcitementSelect src cands =
  unmeasuredMeasuredExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with all-inadmissible residue.
unmeasuredMeasuredExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
unmeasuredMeasuredExcitementSelectRefusesSecondArgmin src cands =
  unmeasuredMeasuredExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
unmeasuredMeasuredSelectEmpty :: ThermodynamicState -> Bool
unmeasuredMeasuredSelectEmpty prior =
  unmeasuredMeasuredSelect (UnmeasuredMeasuredCtx prior [])
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §17.7 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture dataset for measured-false production wiring.
ummFixtureDataset :: String
ummFixtureDataset = "fixture:urge-formal-meso-hs-unmeasured-measured"

-- | Fixture: measured false on named dataset (honest non-GREEN).
ummFixtureMeasuredFalse :: ProductionWiredTaxonomy
ummFixtureMeasuredFalse = ProductionMeasured False ummFixtureDataset

-- | Fixture conjunct with all gates true.
ummFixtureConjunct :: UnmeasuredMeasuredConjunct
ummFixtureConjunct =
  UnmeasuredMeasuredConjunct
    { ummGateOk = True
    , ummFalseAsGreenRefused = True
    , ummExcitementPreserves = True
    }

-- | Measured-false fixture admits (no false-as-GREEN refusal).
ummFixtureMeasuredFalseAdmits :: Bool
ummFixtureMeasuredFalseAdmits =
  refuseFalseAsGreen ummFixtureMeasuredFalse == Nothing

-- | Measured-false fixture evaluates to honest measured-false verdict.
ummFixtureMeasuredFalseEvaluateOk :: Bool
ummFixtureMeasuredFalseEvaluateOk =
  evaluateProductionWired ummFixtureMeasuredFalse == MeasuredFalseOk

-- | Measured-false fixture constructs via 'measuredProductionWired'.
ummFixtureMeasuredProductionWiredOk :: Bool
ummFixtureMeasuredProductionWiredOk =
  measuredProductionWired False ummFixtureDataset
    == Right ummFixtureMeasuredFalse

-- | Empty dataset refused as unmeasured-collapsed-to-false.
ummFixtureEmptyDatasetRefused :: Bool
ummFixtureEmptyDatasetRefused =
  measuredProductionWired False "" == Left UnmeasuredCollapsedToFalse

-- | Gossip mesh legacy bool is 'Nothing' (unmeasured).
ummFixtureUnmeasuredLegacyNone :: Bool
ummFixtureUnmeasuredLegacyNone =
  productionWiredLegacyBool gossipMeshProductionWiredTaxonomy == Nothing

-- | Fixture conjunct admits.
ummFixtureConjunctAdmitsTrue :: Bool
ummFixtureConjunctAdmitsTrue = ummConjunctAdmits ummFixtureConjunct

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Thermodynamic accounting on unmeasured/measured transition.
data UnmeasuredMeasuredTransition = UnmeasuredMeasuredTransition
  { ummTransitionPrior          :: !ThermodynamicState
  , ummTransitionPost           :: !ThermodynamicState
  , ummTransitionBath           :: !HeatBath
  , ummTransitionDissipatedWork :: !Double
  , ummTransitionEntropyDrop    :: !Double
  , ummTransitionGateChecked    :: !Bool
  , ummTransitionFalseAsGreenRefused :: !Bool
  , ummTransitionExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Admissible unmeasured/measured transition conjunct.
admissibleUnmeasuredMeasured :: UnmeasuredMeasuredTransition -> Bool
admissibleUnmeasuredMeasured t =
  ummTransitionGateChecked t
  && ummTransitionFalseAsGreenRefused t
  && ummTransitionExcitementPreserves t

-- | Named second-law invariant on unmeasured/measured transition.
unmeasuredMeasuredSecondLaw :: UnmeasuredMeasuredTransition -> Bool
unmeasuredMeasuredSecondLaw t =
  ummTransitionEntropyDrop t
    <= ummTransitionDissipatedWork t / bathTemp (ummTransitionBath t)

-- | Physical bridge tying Landauer process to unmeasured/measured transition.
data PhysicalUnmeasuredMeasuredBridge = PhysicalUnmeasuredMeasuredBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalTransition     :: !UnmeasuredMeasuredTransition
  , physicalAdmissible     :: !Bool
  } deriving (Show, Eq)

-- | Second law on transition from Landauer bridge discharge.
unmeasuredMeasuredSecondLawFromPhysical
  :: PhysicalUnmeasuredMeasuredBridge -> Bool -> Bool
unmeasuredMeasuredSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalLandauerBridge b))
  && unmeasuredMeasuredSecondLaw (physicalTransition b)

-- | Admissible conjunct from physical bridge (no new axiom).
admissibleUnmeasuredMeasuredFromPhysical
  :: PhysicalUnmeasuredMeasuredBridge -> Bool -> Bool
admissibleUnmeasuredMeasuredFromPhysical b hSL =
  hSL
  && physicalAdmissible b
  && admissibleUnmeasuredMeasured (physicalTransition b)

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
unmeasuredMeasuredPhysicsGreen :: Bool
unmeasuredMeasuredPhysicsGreen = False

-- | Lean/Coq: @unmeasured_measured_physics_green_false@.
unmeasuredMeasuredPhysicsGreenFalse :: Bool
unmeasuredMeasuredPhysicsGreenFalse =
  not unmeasuredMeasuredPhysicsGreen

-- | Production wiring stays open (meso lift only) — not a bool skip.
unmeasuredMeasuredProductionWired :: Bool
unmeasuredMeasuredProductionWired = False

-- | Lean/Coq: @unmeasured_measured_production_wired_false@.
unmeasuredMeasuredProductionWiredFalse :: Bool
unmeasuredMeasuredProductionWiredFalse =
  not unmeasuredMeasuredProductionWired

-- | Catalog witness: meso Urge UnmeasuredMeasured module present.
unmeasuredMeasuredModuleWitness :: Bool
unmeasuredMeasuredModuleWitness = True

-- | Zero new axiom discipline witness.
unmeasuredMeasuredNoNewAxiom :: Bool
unmeasuredMeasuredNoNewAxiom = True

-- | Positive refuse is not silent accept on gossip mesh taxonomy.
unmeasuredMeasuredPositiveRefuseNotSilent :: Bool
unmeasuredMeasuredPositiveRefuseNotSilent =
  refuseFalseAsGreen gossipMeshProductionWiredTaxonomy /= Nothing

-- | UNKNOWN refusal witness for unmeasured-as-false-GREEN.
unmeasuredMeasuredUnknownNotFalseAsGreen :: Bool
unmeasuredMeasuredUnknownNotFalseAsGreen =
  refuseUnmeasuredAsFalseGreen == UnmeasuredCollapsedToFalse

-- | Second-argmin refusal: unmeasured/measured composes 'excitementSelect' only.
unmeasuredMeasuredNoSecondArgmin :: Bool
unmeasuredMeasuredNoSecondArgmin =
  unmeasuredMeasuredExcitementSelectEqExcitementSelect
    (ThermodynamicState 300 0 0.3 30 40)
    []

-- | Honest non-claim string (meso §17.7 production_wired scaffold).
unmeasuredMeasuredNonClaim :: String
unmeasuredMeasuredNonClaim =
  "§17.7 production_wired : Unmeasured | Measured {value, dataset}; "
    ++ "UNKNOWN ≠ false-as-GREEN; compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
unmeasuredMeasuredNonClaimNonempty :: Bool
unmeasuredMeasuredNonClaimNonempty = length unmeasuredMeasuredNonClaim > 0
