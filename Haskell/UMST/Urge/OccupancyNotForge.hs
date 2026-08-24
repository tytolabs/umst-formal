-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.OccupancyNotForge
-- Description : Meso acting Urge — §13.1 four names unfused: occupancy ≠ forge ≠ meta ≠ Padma.
--
-- Collapsing them is a category error (process surrogate vs running forge vs transition
-- conjunct vs runtime invariant). Fusion attempts fail closed with positive refuse —
-- not only `!physics_green`. History recovery composes 'excitementSelect' — no second
-- argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.OccupancyNotForge
  ( -- * Four unfused name carriers (§13.1 — Padma not fifth fibre)
    OccupancyName (..)
  , ForgeName (..)
  , MetaName (..)
  , PadmaName (..)
  , UrgeUnfusedName (..)
  , urgeNameTag
  , urgeNameStringTag
  , fourNamesUnfused
  , fourNamesUnfusedHolds
  , fourNameCount
  , fourNameCountIsFour
  , classifyUrgeName
    -- * §13.1 positive refuse fuse (not silent collapse)
  , FusionRefused (..)
  , OccupancyNotForgeVerdict (..)
  , evaluateNameFusion
  , tryMerge
  , refuseOccupancyAsForge
  , refuseForgeAsMeta
  , refuseMetaAsPadma
  , refusePadmaAsOccupancy
  , OccupancyNotForgeConjunct (..)
  , onfConjunctAdmits
  , onfFixtureConjunct
  , onfFixtureConjunctAdmits
    -- * Positive refuse witnesses
  , evaluateNameFusionRefusedWhenAttempt
  , evaluateNameFusionOkWhenHold
  , tryMergeOccupancyForgeRefused
  , tryMergePadmaOccupancyRefused
  , refuseOccupancyAsForgePositive
  , refuseMetaAsPadmaPositive
  , occupancyNotForgePositiveRefuseNotSilent
    -- * Excitement alignment (no second argmin)
  , OccupancyNotForgeCtx (..)
  , occupancyNotForgeSelect
  , occupancyNotForgeSelectBare
  , occupancyNotForgeSelectEqExcitementSelect
  , occupancyNotForgeSelectBareEqExcitementSelect
  , occupancyNotForgeSelectEqAdmitHistorySelect
  , occupancyNotForgeNoLocalArgmin
  , occupancyNotForgeEmpty
    -- * Landauer bridge (derived — zero new axioms)
  , OccupancyNotForgeTransition (..)
  , occupancySecondLaw
  , occupancySecondLawFromLandauer
  , occupancySecondLawFromHypothesis
  , fourNamesUnfusedFromLandauer
    -- * Fixtures + witness theorems
  , onfFixtureOccupancy
  , onfFixtureForge
  , onfFixtureMeta
  , onfFixturePadma
  , onfFixtureOccName
  , onfFixtureForgeName
  , onfFixtureMetaName
  , onfFixturePadmaName
  , onfFixtureFourTagsDistinct
  , onfFixtureOccupancyForgeMergeRefused
  , onfFixturePadmaOccupancyMergeRefused
  , onfFixtureEvaluateFusionRefused
  , padmaNotFifthUrgeName
    -- * Honesty flags + catalog witnesses
  , occupancyNotForgePhysicsGreen
  , occupancyNotForgePhysicsGreenFalse
  , occupancyNotForgeProductionWired
  , occupancyNotForgeProductionWiredFalse
  , occupancyNotForgeMarker
  , occupancyNotForgeMarkerNonempty
  , occupancyNotForgeModuleWitness
  , occupancyNotForgeNoNewAxiom
  , occupancyNotForgeNamedUnfused
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitHistorySelect
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Four unfused name carriers (§13.1 — Padma not fifth fibre)
-- ---------------------------------------------------------------------------

-- | @umst-adk@ path coverage surrogate — not a forge, not meta, not Padma.
data OccupancyName = OccupancyName
  { occupancySurrogate :: !Int
  } deriving (Show, Eq)

-- | India-resident Forgejo forge ops plane — not occupancy, not meta, not Padma.
data ForgeName = ForgeName
  { forgeSurrogate :: !Int
  } deriving (Show, Eq)

-- | Future @umst-meta@ transition conjunct — distinct from forge and Padma.
data MetaName = MetaName
  { metaSurrogate :: !Int
  } deriving (Show, Eq)

-- | Padma runtime invariant (crosswalk only) — not a fifth Urge fibre in §13.1.
data PadmaName = PadmaName
  { padmaSurrogate :: !Int
  } deriving (Show, Eq)

-- | Tagged union preserving the four unfused §13.1 names at the meso layer.
data UrgeUnfusedName
  = UrgeOccupancy !OccupancyName
  | UrgeForge !ForgeName
  | UrgeMeta !MetaName
  | UrgePadma !PadmaName
  deriving (Show, Eq)

-- | Discriminant tag for probe / witness theorems (identity-preserving).
urgeNameTag :: UrgeUnfusedName -> Int
urgeNameTag n = case n of
  UrgeOccupancy _ -> 0
  UrgeForge _ -> 1
  UrgeMeta _ -> 2
  UrgePadma _ -> 3

-- | String tag mirror (ReplicaCoalgebra-style unfusion witness).
urgeNameStringTag :: UrgeUnfusedName -> String
urgeNameStringTag n = case n of
  UrgeOccupancy _ -> "occupancy"
  UrgeForge _ -> "forge"
  UrgeMeta _ -> "meta"
  UrgePadma _ -> "padma"

-- | §13.1 four-name unfusion conjunct (all pairwise string tags distinct).
fourNamesUnfused :: Bool
fourNamesUnfused =
  urgeNameStringTag (UrgeOccupancy (OccupancyName 1))
    /= urgeNameStringTag (UrgeForge (ForgeName 2))
  && urgeNameStringTag (UrgeForge (ForgeName 2))
    /= urgeNameStringTag (UrgeMeta (MetaName 3))
  && urgeNameStringTag (UrgeMeta (MetaName 3))
    /= urgeNameStringTag (UrgePadma (PadmaName 4))
  && urgeNameStringTag (UrgePadma (PadmaName 4))
    /= urgeNameStringTag (UrgeOccupancy (OccupancyName 1))

-- | Witness: four §13.1 names remain unfused at the meso layer.
fourNamesUnfusedHolds :: Bool
fourNamesUnfusedHolds = fourNamesUnfused

-- | Named count of §13.1 unfused carriers (Padma included, not a fifth fibre).
fourNameCount :: Int
fourNameCount = 4

-- | Witness: §13.1 name count is exactly four.
fourNameCountIsFour :: Bool
fourNameCountIsFour = fourNameCount == 4

-- | Classify without fusion — identity-preserving surrogate.
classifyUrgeName :: UrgeUnfusedName -> UrgeUnfusedName
classifyUrgeName = id

-- ---------------------------------------------------------------------------
-- SECTION 2: §13.1 positive refuse fuse (not silent collapse)
-- ---------------------------------------------------------------------------

-- | Fail-closed fusion refusal — pairwise merge of distinct §13.1 names.
data FusionRefused
  = OccupancyForge
  | OccupancyMeta
  | OccupancyPadma
  | ForgeMeta
  | ForgePadma
  | MetaPadma
  | SameDiscriminant
  deriving (Show, Eq)

-- | Verdict of a name-fusion operation class.
data OccupancyNotForgeVerdict
  = OnfUnfusedOk
  | OnfFusionRefused
  deriving (Show, Eq)

-- | Classify merge vs hold-unfused without performing fusion.
evaluateNameFusion :: Bool -> OccupancyNotForgeVerdict
evaluateNameFusion attemptMerge =
  if attemptMerge then OnfFusionRefused else OnfUnfusedOk

-- | Attempt to merge two unfused names — always refused when discriminants differ.
tryMerge :: UrgeUnfusedName -> UrgeUnfusedName -> FusionRefused
tryMerge a b = case (a, b) of
  (UrgeOccupancy _, UrgeForge _) -> OccupancyForge
  (UrgeForge _, UrgeOccupancy _) -> OccupancyForge
  (UrgeOccupancy _, UrgeMeta _) -> OccupancyMeta
  (UrgeMeta _, UrgeOccupancy _) -> OccupancyMeta
  (UrgeOccupancy _, UrgePadma _) -> OccupancyPadma
  (UrgePadma _, UrgeOccupancy _) -> OccupancyPadma
  (UrgeForge _, UrgeMeta _) -> ForgeMeta
  (UrgeMeta _, UrgeForge _) -> ForgeMeta
  (UrgeForge _, UrgePadma _) -> ForgePadma
  (UrgePadma _, UrgeForge _) -> ForgePadma
  (UrgeMeta _, UrgePadma _) -> MetaPadma
  (UrgePadma _, UrgeMeta _) -> MetaPadma
  (_, _) -> SameDiscriminant

-- | Typed refuse: coerce occupancy into forge — inadmissible.
refuseOccupancyAsForge :: OccupancyName -> FusionRefused
refuseOccupancyAsForge _ = OccupancyForge

-- | Typed refuse: coerce forge into meta — inadmissible.
refuseForgeAsMeta :: ForgeName -> FusionRefused
refuseForgeAsMeta _ = ForgeMeta

-- | Typed refuse: coerce meta into Padma — inadmissible.
refuseMetaAsPadma :: MetaName -> FusionRefused
refuseMetaAsPadma _ = MetaPadma

-- | Typed refuse: coerce Padma into occupancy — inadmissible.
refusePadmaAsOccupancy :: PadmaName -> FusionRefused
refusePadmaAsOccupancy _ = OccupancyPadma

-- | §13.1 admissibility conjunct inputs (surrogate).
data OccupancyNotForgeConjunct = OccupancyNotForgeConjunct
  { onfFourNamesDistinct   :: !Bool
  , onfFusionRefused       :: !Bool
  , onfExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate `admit(h) ⟺ four names distinct ∧ fusion refused ∧ Excitement preserves`.
onfConjunctAdmits :: OccupancyNotForgeConjunct -> Bool
onfConjunctAdmits c =
  onfFourNamesDistinct c
  && onfFusionRefused c
  && onfExcitementPreserves c

-- | Fixture conjunct for §13.1 occupancy-not-forge scaffold.
onfFixtureConjunct :: OccupancyNotForgeConjunct
onfFixtureConjunct =
  OccupancyNotForgeConjunct
    { onfFourNamesDistinct = True
    , onfFusionRefused = True
    , onfExcitementPreserves = True
    }

-- | Fixture conjunct admits under §13.1 conjunct gate.
onfFixtureConjunctAdmits :: Bool
onfFixtureConjunctAdmits = onfConjunctAdmits onfFixtureConjunct

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Fusion attempt is positively refused (not silent collapse).
evaluateNameFusionRefusedWhenAttempt :: Bool
evaluateNameFusionRefusedWhenAttempt =
  evaluateNameFusion True == OnfFusionRefused

-- | Holding unfused names admits without fusion.
evaluateNameFusionOkWhenHold :: Bool
evaluateNameFusionOkWhenHold =
  evaluateNameFusion False == OnfUnfusedOk

-- | Occupancy/forged merge is positively refused.
tryMergeOccupancyForgeRefused :: OccupancyName -> ForgeName -> Bool
tryMergeOccupancyForgeRefused o f =
  tryMerge (UrgeOccupancy o) (UrgeForge f) == OccupancyForge

-- | Padma/occupancy merge is positively refused.
tryMergePadmaOccupancyRefused :: PadmaName -> OccupancyName -> Bool
tryMergePadmaOccupancyRefused p o =
  tryMerge (UrgePadma p) (UrgeOccupancy o) == OccupancyPadma

-- | Typed occupancy→forge coercion is positively refused.
refuseOccupancyAsForgePositive :: OccupancyName -> Bool
refuseOccupancyAsForgePositive o =
  refuseOccupancyAsForge o == OccupancyForge

-- | Typed meta→Padma coercion is positively refused.
refuseMetaAsPadmaPositive :: MetaName -> Bool
refuseMetaAsPadmaPositive m =
  refuseMetaAsPadma m == MetaPadma

-- | Positive refuse is not silent collapse to unfused-ok.
occupancyNotForgePositiveRefuseNotSilent :: Bool
occupancyNotForgePositiveRefuseNotSilent =
  evaluateNameFusion True /= OnfUnfusedOk

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for occupancy-not-forge over admissible history successors.
data OccupancyNotForgeCtx = OccupancyNotForgeCtx
  { onfPrior      :: !ThermodynamicState
  , onfSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Occupancy-not-forge history selection **is** 'excitementSelect' — no second argmin.
occupancyNotForgeSelect
  :: OccupancyNotForgeCtx
  -> Either ExcitementResidue HistoryCandidate
occupancyNotForgeSelect ctx =
  excitementSelect (onfPrior ctx) (onfSuccessors ctx)

-- | Alias on bare @(prior, successors)@ — same selector, no re-derivation.
occupancyNotForgeSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
occupancyNotForgeSelectBare = excitementSelect

-- | Definitional witness: ONF selection API is 'excitementSelect'.
occupancyNotForgeSelectEqExcitementSelect :: OccupancyNotForgeCtx -> Bool
occupancyNotForgeSelectEqExcitementSelect ctx =
  occupancyNotForgeSelect ctx
    == excitementSelect (onfPrior ctx) (onfSuccessors ctx)

-- | Definitional witness: bare alias is 'excitementSelect'.
occupancyNotForgeSelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
occupancyNotForgeSelectBareEqExcitementSelect src cands =
  occupancyNotForgeSelectBare src cands == excitementSelect src cands

-- | Definitional witness: ONF selection equals 'admitHistorySelect'.
occupancyNotForgeSelectEqAdmitHistorySelect :: OccupancyNotForgeCtx -> Bool
occupancyNotForgeSelectEqAdmitHistorySelect ctx =
  occupancyNotForgeSelect ctx
    == admitHistorySelect (onfPrior ctx) (onfSuccessors ctx)

-- | ONF selector re-uses 'excitementSelect' — no Urge-local argmin.
occupancyNotForgeNoLocalArgmin :: OccupancyNotForgeCtx -> Bool
occupancyNotForgeNoLocalArgmin ctx =
  occupancyNotForgeSelect ctx
    == excitementSelect (onfPrior ctx) (onfSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
occupancyNotForgeEmpty :: ThermodynamicState -> Bool
occupancyNotForgeEmpty src =
  occupancyNotForgeSelectBare src [] == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | History transition tagged with §13.1 unfusion obligation.
data OccupancyNotForgeTransition = OccupancyNotForgeTransition
  { onfTransition  :: !HistoryTransition
  , onfNamesUnfused :: !Bool
  } deriving (Show, Eq)

-- | Second law on ONF transition (Landauer discharge hook).
occupancySecondLaw :: OccupancyNotForgeTransition -> Bool
occupancySecondLaw t = admitSecondLaw (onfTransition t)

-- | Second law on ONF carrier transition from Landauer bridge discharge.
occupancySecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
occupancySecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for ONF second law (no new axiom).
occupancySecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
occupancySecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- | Four-name unfusion survives Landauer bridge discharge (named conjunct).
fourNamesUnfusedFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
fourNamesUnfusedFromLandauer _ hSL = hSL && fourNamesUnfusedHolds

-- ---------------------------------------------------------------------------
-- SECTION 6: Fixtures + witness theorems
-- ---------------------------------------------------------------------------

onfFixtureOccupancy :: OccupancyName
onfFixtureOccupancy = OccupancyName 1

onfFixtureForge :: ForgeName
onfFixtureForge = ForgeName 2

onfFixtureMeta :: MetaName
onfFixtureMeta = MetaName 3

onfFixturePadma :: PadmaName
onfFixturePadma = PadmaName 4

onfFixtureOccName :: UrgeUnfusedName
onfFixtureOccName = UrgeOccupancy onfFixtureOccupancy

onfFixtureForgeName :: UrgeUnfusedName
onfFixtureForgeName = UrgeForge onfFixtureForge

onfFixtureMetaName :: UrgeUnfusedName
onfFixtureMetaName = UrgeMeta onfFixtureMeta

onfFixturePadmaName :: UrgeUnfusedName
onfFixturePadmaName = UrgePadma onfFixturePadma

-- | Fixture: four §13.1 name tags are pairwise distinct.
onfFixtureFourTagsDistinct :: Bool
onfFixtureFourTagsDistinct =
  urgeNameTag onfFixtureOccName /= urgeNameTag onfFixtureForgeName
  && urgeNameTag onfFixtureForgeName /= urgeNameTag onfFixtureMetaName
  && urgeNameTag onfFixtureMetaName /= urgeNameTag onfFixturePadmaName
  && urgeNameTag onfFixturePadmaName /= urgeNameTag onfFixtureOccName

-- | Fixture: occupancy/forged merge is positively refused.
onfFixtureOccupancyForgeMergeRefused :: Bool
onfFixtureOccupancyForgeMergeRefused =
  tryMerge onfFixtureOccName onfFixtureForgeName == OccupancyForge

-- | Fixture: Padma/occupancy merge is positively refused.
onfFixturePadmaOccupancyMergeRefused :: Bool
onfFixturePadmaOccupancyMergeRefused =
  tryMerge onfFixturePadmaName onfFixtureOccName == OccupancyPadma

-- | Fixture: evaluate-name-fusion positively refuses merge attempt.
onfFixtureEvaluateFusionRefused :: Bool
onfFixtureEvaluateFusionRefused =
  evaluateNameFusion True == OnfFusionRefused

-- | Padma is the fourth tag (3), not a fifth Urge fibre in §13.1.
padmaNotFifthUrgeName :: Bool
padmaNotFifthUrgeName = urgeNameTag onfFixturePadmaName == 3

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
occupancyNotForgePhysicsGreen :: Bool
occupancyNotForgePhysicsGreen = False

-- | Lean/Coq: @occupancy_not_forge_physics_green_false@.
occupancyNotForgePhysicsGreenFalse :: Bool
occupancyNotForgePhysicsGreenFalse = not occupancyNotForgePhysicsGreen

-- | Production wiring stays open (meso lift only).
occupancyNotForgeProductionWired :: Bool
occupancyNotForgeProductionWired = False

-- | Lean/Coq: @occupancy_not_forge_production_wired_false@.
occupancyNotForgeProductionWiredFalse :: Bool
occupancyNotForgeProductionWiredFalse = not occupancyNotForgeProductionWired

-- | Honest marker string (meso §13.1 occupancy-not-forge scaffold).
occupancyNotForgeMarker :: String
occupancyNotForgeMarker = "urge_int_occupancy_not_forge_v1"

-- | Marker string is non-empty.
occupancyNotForgeMarkerNonempty :: Bool
occupancyNotForgeMarkerNonempty = length occupancyNotForgeMarker > 0

-- | Catalog witness: meso Urge OccupancyNotForge module present.
occupancyNotForgeModuleWitness :: Bool
occupancyNotForgeModuleWitness = True

-- | Zero new axiom discipline witness.
occupancyNotForgeNoNewAxiom :: Bool
occupancyNotForgeNoNewAxiom = True

-- | Named unfusion witness (§13.1 four names distinct).
occupancyNotForgeNamedUnfused :: Bool
occupancyNotForgeNamedUnfused = fourNamesUnfusedHolds
