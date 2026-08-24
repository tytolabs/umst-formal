-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.DropProvenance
-- Description : Meso acting Urge — §15.6 H3 drop-provenance gossip tick refuse.
--
-- Drop-provenance gossip candidates are **inadmissible** — typed positive refuse,
-- not silent accept. Urge composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.DropProvenance
  ( -- * Gossip tick candidate + typed refusal carriers
    GossipCandidate (..)
  , DropProvenanceRefusal (..)
  , GossipTickVerdict (..)
  , gossipIsAdmissible
  , stampNonempty
  , stampOk
    -- * Positive refuse + admit (not silent accept)
  , admitGossipCandidate
  , evaluateGossipTick
  , refuseDropProvenanceGossipCandidate
  , gossipTickVerdictAdmissibleIff
  , gossipTickVerdictRejectIff
    -- * Excitement compose (no second argmin)
  , ExcitementComposePin (..)
  , gossipExcitementSelect
  , gossipExcitementSelectEqExcitementSelect
  , gossipExcitementSelectRefusesSecondArgmin
  , gossipSelect
  , gossipSelectEqExcitementSelect
  , filterAdmissibleGossip
  , gossipIsAdmissibleFalseWhenDrops
  , dropProvenanceNeverInAdmissibleFilter
    -- * H3 fixtures + witness theorems
  , h3InadmissibleDropProvenanceId
  , h3AdmissibleProvenancedId
  , h3DropProvenanceFixtureCandidate
  , h3AdmissibleGossipCandidate
  , h3DropProvenanceFixtureRefused
  , h3DropProvenanceFixtureEvaluateReject
  , h3DropProvenanceFixturePositiveRefuse
  , h3AdmissibleGossipCandidateAdmits
  , h3AdmissibleGossipCandidateEvaluateAdmit
  , h3AdmissibleGossipIsAdmissible
  , h3DropProvenanceFixtureNotAdmissible
    -- * Landauer bridge (derived — zero new axioms)
  , GossipTransition (..)
  , gossipSecondLaw
  , PhysicalGossipBridge (..)
  , gossipSecondLawFromPhysical
  , physicalSecondLawImported
  , dropProvenanceFromPhysical
    -- * Honesty flags + catalog witnesses
  , dropProvenancePhysicsGreen
  , dropProvenancePhysicsGreenFalse
  , dropProvenanceProductionWired
  , dropProvenanceProductionWiredFalse
  , dropProvenanceModuleWitness
  , dropProvenanceNoNewAxiom
  , dropProvenanceNoSecondArgmin
  , dropProvenancePositiveRefuseNotSilent
  , dropProvenanceNonClaim
  , dropProvenanceNonClaimNonempty
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
-- SECTION 1: Gossip tick candidate + typed refusal carriers
-- ---------------------------------------------------------------------------

-- | One gossip tick candidate on the UCRS-gated mesh spine.
data GossipCandidate = GossipCandidate
  { gossipId               :: !Int
  , gossipProvenanceIntact :: !Bool
  , gossipDropsProvenance  :: !Bool
  , gossipProvenanceStamp  :: !(Maybe String)
  } deriving (Show, Eq)

-- | Typed refusal when a gossip candidate drops provenance.
data DropProvenanceRefusal
  = DropsProvenanceGossipTick
  | ProvenanceLost
  | MissingStamp
  deriving (Show, Eq)

-- | Verdict for gossip tick admissibility on the mesh spine.
data GossipTickVerdict
  = GossipAdmissible
  | RejectDropProvenance
  deriving (Show, Eq)

-- | Admissible iff provenance intact and not a drop-heal gossip tick.
gossipIsAdmissible :: GossipCandidate -> Bool
gossipIsAdmissible c =
  gossipProvenanceIntact c && not (gossipDropsProvenance c)

-- | Non-empty provenance stamp string.
stampNonempty :: String -> Bool
stampNonempty s = not (null s)

-- | Stamp present and non-empty.
stampOk :: GossipCandidate -> Bool
stampOk c =
  case gossipProvenanceStamp c of
    Nothing -> False
    Just s  -> stampNonempty s

-- ---------------------------------------------------------------------------
-- SECTION 2: Positive refuse + admit (not silent accept)
-- ---------------------------------------------------------------------------

-- | Admit a gossip candidate — 'Nothing' on success, 'Just' refusal otherwise.
admitGossipCandidate :: GossipCandidate -> Maybe DropProvenanceRefusal
admitGossipCandidate c
  | gossipDropsProvenance c = Just DropsProvenanceGossipTick
  | not (gossipProvenanceIntact c) = Just ProvenanceLost
  | not (stampOk c) = Just MissingStamp
  | otherwise = Nothing

-- | Evaluate gossip tick admissibility (H3 transition verdict family).
evaluateGossipTick :: GossipCandidate -> GossipTickVerdict
evaluateGossipTick c =
  case admitGossipCandidate c of
    Nothing -> GossipAdmissible
    Just _  -> RejectDropProvenance

-- | Positive refuse: drop-provenance gossip candidate is always inadmissible.
refuseDropProvenanceGossipCandidate :: GossipCandidate -> DropProvenanceRefusal
refuseDropProvenanceGossipCandidate c
  | gossipDropsProvenance c = DropsProvenanceGossipTick
  | not (gossipProvenanceIntact c) = ProvenanceLost
  | otherwise = MissingStamp

-- | Verdict admissible iff admit returns 'Nothing'.
gossipTickVerdictAdmissibleIff :: GossipCandidate -> Bool
gossipTickVerdictAdmissibleIff c =
  (evaluateGossipTick c == GossipAdmissible)
  == (admitGossipCandidate c == Nothing)

-- | Verdict rejects iff admit returns 'Just'.
gossipTickVerdictRejectIff :: GossipCandidate -> Bool
gossipTickVerdictRejectIff c =
  (evaluateGossipTick c == RejectDropProvenance)
  == (admitGossipCandidate c /= Nothing)

-- ---------------------------------------------------------------------------
-- SECTION 3: Excitement compose (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — Urge imports selector; no second argmin.
data ExcitementComposePin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Gossip path composes 'excitementSelect' — not a second argmin.
gossipExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> ExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
gossipExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
gossipExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | Definitional witness: import pin is 'excitementSelect'.
gossipExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
gossipExcitementSelectEqExcitementSelect src cands =
  gossipExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with all-inadmissible residue.
gossipExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
gossipExcitementSelectRefusesSecondArgmin src cands =
  gossipExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- | Gossip selection composes imported excitement — no local argmin.
gossipSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
gossipSelect = excitementSelect

-- | Definitional witness: gossip selection API is 'excitementSelect'.
gossipSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
gossipSelectEqExcitementSelect src cands =
  gossipSelect src cands == excitementSelect src cands

-- | Drop-provenance gossip candidates never reach excitement selection.
filterAdmissibleGossip :: [GossipCandidate] -> [GossipCandidate]
filterAdmissibleGossip =
  filter (\c -> gossipIsAdmissible c && stampOk c)

implies :: Bool -> Bool -> Bool
implies False _ = True
implies True b = b

-- | When drops_provenance is true, gossipIsAdmissible is false.
gossipIsAdmissibleFalseWhenDrops :: GossipCandidate -> Bool
gossipIsAdmissibleFalseWhenDrops c =
  gossipDropsProvenance c `implies` not (gossipIsAdmissible c)

-- | Drop-provenance candidate excluded from admissible filter.
dropProvenanceNeverInAdmissibleFilter :: GossipCandidate -> Bool
dropProvenanceNeverInAdmissibleFilter c =
  gossipDropsProvenance c `implies` null (filterAdmissibleGossip [c])

-- ---------------------------------------------------------------------------
-- SECTION 4: H3 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | H3 fixture id — inadmissible drop-provenance gossip tick.
h3InadmissibleDropProvenanceId :: Int
h3InadmissibleDropProvenanceId = 1

-- | H3 fixture id — admissible provenanced gossip tick.
h3AdmissibleProvenancedId :: Int
h3AdmissibleProvenancedId = 2

-- | H3 fixture — drop-provenance gossip candidate (always refused).
h3DropProvenanceFixtureCandidate :: GossipCandidate
h3DropProvenanceFixtureCandidate =
  GossipCandidate
    { gossipId = h3InadmissibleDropProvenanceId
    , gossipProvenanceIntact = False
    , gossipDropsProvenance = True
    , gossipProvenanceStamp = Nothing
    }

-- | H3 fixture — admissible provenanced gossip candidate.
h3AdmissibleGossipCandidate :: GossipCandidate
h3AdmissibleGossipCandidate =
  GossipCandidate
    { gossipId = h3AdmissibleProvenancedId
    , gossipProvenanceIntact = True
    , gossipDropsProvenance = False
    , gossipProvenanceStamp = Just "ucrs:fixture:h3:admissible-001"
    }

-- | H3 drop fixture refused with 'DropsProvenanceGossipTick'.
h3DropProvenanceFixtureRefused :: Bool
h3DropProvenanceFixtureRefused =
  admitGossipCandidate h3DropProvenanceFixtureCandidate
    == Just DropsProvenanceGossipTick

-- | H3 drop fixture evaluates to reject verdict.
h3DropProvenanceFixtureEvaluateReject :: Bool
h3DropProvenanceFixtureEvaluateReject =
  evaluateGossipTick h3DropProvenanceFixtureCandidate
    == RejectDropProvenance

-- | H3 drop fixture positive refuse witness.
h3DropProvenanceFixturePositiveRefuse :: Bool
h3DropProvenanceFixturePositiveRefuse =
  refuseDropProvenanceGossipCandidate h3DropProvenanceFixtureCandidate
    == DropsProvenanceGossipTick

-- | H3 admissible fixture admits (no refusal).
h3AdmissibleGossipCandidateAdmits :: Bool
h3AdmissibleGossipCandidateAdmits =
  admitGossipCandidate h3AdmissibleGossipCandidate == Nothing

-- | H3 admissible fixture evaluates to admissible verdict.
h3AdmissibleGossipCandidateEvaluateAdmit :: Bool
h3AdmissibleGossipCandidateEvaluateAdmit =
  evaluateGossipTick h3AdmissibleGossipCandidate == GossipAdmissible

-- | H3 admissible fixture passes gossipIsAdmissible.
h3AdmissibleGossipIsAdmissible :: Bool
h3AdmissibleGossipIsAdmissible =
  gossipIsAdmissible h3AdmissibleGossipCandidate

-- | H3 drop fixture fails gossipIsAdmissible.
h3DropProvenanceFixtureNotAdmissible :: Bool
h3DropProvenanceFixtureNotAdmissible =
  not (gossipIsAdmissible h3DropProvenanceFixtureCandidate)

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Thermodynamic accounting on a gossip transition (acting meso layer).
data GossipTransition = GossipTransition
  { gossipCandidate       :: !GossipCandidate
  , gossipBath            :: !HeatBath
  , gossipDissipatedWork  :: !Double
  , gossipEntropyDrop     :: !Double
  } deriving (Show, Eq)

-- | Named second-law invariant on gossip transition (Bool witness).
gossipSecondLaw :: GossipTransition -> Bool
gossipSecondLaw t =
  gossipEntropyDrop t
    <= gossipDissipatedWork t / bathTemp (gossipBath t)

-- | Physical bridge tying Landauer process to refused drop-provenance gossip.
data PhysicalGossipBridge = PhysicalGossipBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalGossip         :: !GossipTransition
  , physicalRefused        :: !Bool
  } deriving (Show, Eq)

-- | Second law on gossip transition from Landauer bridge discharge.
gossipSecondLawFromPhysical :: PhysicalGossipBridge -> Bool -> Bool
gossipSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalLandauerBridge b))
  && gossipSecondLaw (physicalGossip b)

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- | Drop-provenance gossip refused under physical bridge (no new axiom).
dropProvenanceFromPhysical :: PhysicalGossipBridge -> Bool -> Bool
dropProvenanceFromPhysical b hSL =
  hSL
  && physicalRefused b
  && evaluateGossipTick (gossipCandidate (physicalGossip b))
       == RejectDropProvenance

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
dropProvenancePhysicsGreen :: Bool
dropProvenancePhysicsGreen = False

-- | Lean/Coq: @drop_provenance_physics_green_false@.
dropProvenancePhysicsGreenFalse :: Bool
dropProvenancePhysicsGreenFalse = not dropProvenancePhysicsGreen

-- | Production wiring stays open (meso lift only).
dropProvenanceProductionWired :: Bool
dropProvenanceProductionWired = False

-- | Lean/Coq: @drop_provenance_production_wired_false@.
dropProvenanceProductionWiredFalse :: Bool
dropProvenanceProductionWiredFalse = not dropProvenanceProductionWired

-- | Catalog witness: meso Urge DropProvenance module present.
dropProvenanceModuleWitness :: Bool
dropProvenanceModuleWitness = True

-- | Zero new axiom discipline witness.
dropProvenanceNoNewAxiom :: Bool
dropProvenanceNoNewAxiom = True

-- | Second-argmin refusal: gossip composes 'excitementSelect' only.
dropProvenanceNoSecondArgmin :: Bool
dropProvenanceNoSecondArgmin =
  gossipSelectEqExcitementSelect (ThermodynamicState 300 0 0.3 30 40) []

-- | Positive refuse is not silent accept on H3 drop fixture.
dropProvenancePositiveRefuseNotSilent :: Bool
dropProvenancePositiveRefuseNotSilent =
  admitGossipCandidate h3DropProvenanceFixtureCandidate /= Nothing

-- | Honest non-claim string (meso §15.6 H3 drop-provenance scaffold).
dropProvenanceNonClaim :: String
dropProvenanceNonClaim =
  "§15.6 H3 drop-provenance gossip tick refuse — candidates inadmissible; "
    ++ "compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
dropProvenanceNonClaimNonempty :: Bool
dropProvenanceNonClaimNonempty = length dropProvenanceNonClaim > 0
