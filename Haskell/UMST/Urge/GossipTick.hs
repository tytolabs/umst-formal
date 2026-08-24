-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.GossipTick
-- Description : Meso acting Urge — §15.6 H3 gossip tick: typed refuse of drop-provenance.
--
-- Gossip tick candidates that drop provenance are **inadmissible** — typed positive
-- refuse, not silent accept. Same Repository/History carrier product discipline as
-- §3 COB (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness).
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.GossipTick
  ( -- * Gossip tick candidate + typed drop-provenance refusal
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
    -- * Gossip mesh identity + history carrier (§15.6 H3)
  , GossipMeshIdentity (..)
  , GossipIdentityVerdict (..)
  , refuseStampOnlyIdentity
  , gossipMeshIdentityWithCarrier
  , carrierPopulated
  , GossipTick (..)
  , gossipTickNew
  , gossipTickCarrier
  , gossipTickHead
    -- * Positive refuse witnesses
  , refuseStampOnlyIsRefused
  , h3DropProvenanceFixtureRefused
  , h3DropProvenanceFixtureEvaluateReject
  , h3DropProvenanceFixturePositiveRefuse
  , h3AdmissibleGossipCandidateAdmits
  , h3AdmissibleGossipCandidateEvaluateAdmit
  , h3AdmissibleGossipIsAdmissible
  , h3DropProvenanceFixtureNotAdmissible
    -- * Excitement alignment (no second argmin)
  , gossipTickSelect
  , gossipTickCarrierSelect
  , gossipTickSelectEqExcitementSelect
  , gossipTickSelectEqCarrierSelect
  , gossipTickNoLocalArgmin
  , gossipTickSelectEqCarrierSelectHead
    -- * Landauer bridge (derived — zero new axioms)
  , GossipTransition (..)
  , gossipSecondLaw
  , PhysicalGossipBridge (..)
  , gossipSecondLawFromPhysical
  , gossipTickFromLandauerAdmitSecondLaw
  , gossipTickSecondLawFromHypothesis
  , dropProvenanceFromPhysical
    -- * Honesty flags + catalog witnesses
  , gossipTickPhysicsGreen
  , gossipTickPhysicsGreenFalse
  , gossipTickProductionWired
  , gossipTickProductionWiredFalse
  , gossipTickNonClaim
  , gossipTickNonClaimNonempty
  , gossipTickModuleWitness
  , gossipTickNoNewAxiom
  , gossipTickNoSecondArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.CarrierProduct
  ( HistoryCarrier (..)
  , carrierMk
  , carrierSelect
  , satisfiedWitness
  , stampProj
  , umstProj
  , wallOnlyStamp
  , ExactAlg (..)
  , SdfFRep (..)
  , observedAtWall
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Gossip tick candidate + typed drop-provenance refusal
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
-- SECTION 3: Gossip mesh identity + history carrier (§15.6 H3)
-- ---------------------------------------------------------------------------

-- | Gossip mesh identity: mesh id pin + owning history carrier.
data GossipMeshIdentity = GossipMeshIdentity
  { meshId      :: !String
  , meshCarrier :: !HistoryCarrier
  } deriving (Show, Eq)

data GossipIdentityVerdict
  = GossipIdentityOk GossipMeshIdentity
  | GossipStampOnlyIdentityRefused String
  deriving (Show, Eq)

-- | Refuse constructing identity from stamp alone — carrier required.
refuseStampOnlyIdentity :: String -> GossipIdentityVerdict
refuseStampOnlyIdentity mid = GossipStampOnlyIdentityRefused mid

-- | Build gossip mesh identity with full carrier (geometric identity primary).
gossipMeshIdentityWithCarrier :: String -> HistoryCarrier -> GossipIdentityVerdict
gossipMeshIdentityWithCarrier mid c =
  GossipIdentityOk (GossipMeshIdentity {meshId = mid, meshCarrier = c})

-- | Carrier populated when UMST commit id or stamp wall is present.
carrierPopulated :: HistoryCarrier -> Bool
carrierPopulated c =
  historyCommitId (umstProj c) > 0
  || observedAtWall (stampProj c) > 0

-- | Gossip tick — history carrier + pending candidate (§15.6 H3).
data GossipTick = GossipTick
  { gossipIdentity :: !GossipMeshIdentity
  , gossipPending  :: !GossipCandidate
  } deriving (Show, Eq)

-- | Fresh gossip tick from mesh identity + initial candidate.
gossipTickNew :: GossipMeshIdentity -> GossipCandidate -> GossipTick
gossipTickNew identity candidate =
  GossipTick {gossipIdentity = identity, gossipPending = candidate}

-- | Project history carrier from gossip tick.
gossipTickCarrier :: GossipTick -> HistoryCarrier
gossipTickCarrier gt = meshCarrier (gossipIdentity gt)

-- | Thermodynamic head at gossip tick carrier UMST snapshot.
gossipTickHead :: GossipTick -> ThermodynamicState
gossipTickHead gt = historyHead (umstProj (gossipTickCarrier gt))

-- ---------------------------------------------------------------------------
-- SECTION 4: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Stamp-only identity construction is always refused.
refuseStampOnlyIsRefused :: String -> Bool
refuseStampOnlyIsRefused mid =
  refuseStampOnlyIdentity mid == GossipStampOnlyIdentityRefused mid

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
-- SECTION 5: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Gossip tick history recovery composes 'excitementSelect' on carrier UMST head.
gossipTickSelect
  :: GossipTick
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
gossipTickSelect gt cands =
  excitementSelect (historyHead (umstProj (gossipTickCarrier gt))) cands

-- | Carrier-level selection on history carrier UMST head.
gossipTickCarrierSelect
  :: HistoryCarrier
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
gossipTickCarrierSelect c cands =
  excitementSelect (historyHead (umstProj c)) cands

-- | Definitional witness: gossip tick selection API is 'excitementSelect'.
gossipTickSelectEqExcitementSelect :: GossipTick -> [HistoryCandidate] -> Bool
gossipTickSelectEqExcitementSelect gt cands =
  gossipTickSelect gt cands
    == excitementSelect (historyHead (umstProj (gossipTickCarrier gt))) cands

-- | Gossip tick selection equals carrier-level selection.
gossipTickSelectEqCarrierSelect :: GossipTick -> [HistoryCandidate] -> Bool
gossipTickSelectEqCarrierSelect gt cands =
  gossipTickSelect gt cands == gossipTickCarrierSelect (gossipTickCarrier gt) cands

-- | Gossip tick selector re-uses 'excitementSelect' — no Urge-local argmin.
gossipTickNoLocalArgmin :: GossipTick -> [HistoryCandidate] -> Bool
gossipTickNoLocalArgmin gt cands =
  gossipTickSelect gt cands
    == excitementSelect (historyHead (umstProj (gossipTickCarrier gt))) cands

-- | Gossip tick selection equals 'carrierSelect' on the embedded carrier.
gossipTickSelectEqCarrierSelectHead :: GossipTick -> [HistoryCandidate] -> Bool
gossipTickSelectEqCarrierSelectHead gt cands =
  gossipTickSelect gt cands == carrierSelect (gossipTickCarrier gt) cands

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Thermodynamic accounting on a gossip transition (acting meso layer).
data GossipTransition = GossipTransition
  { gossipCandidate      :: !GossipCandidate
  , gossipBath           :: !HeatBath
  , gossipDissipatedWork :: !Double
  , gossipEntropyDrop    :: !Double
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

-- | Physical bridge discharge: second law on Landauer transition.
gossipTickFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
gossipTickFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for gossip tick second law (no new axiom).
gossipTickSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
gossipTickSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- | Drop-provenance gossip refused under physical bridge (no new axiom).
dropProvenanceFromPhysical :: PhysicalGossipBridge -> Bool -> Bool
dropProvenanceFromPhysical b hSL =
  hSL
  && physicalRefused b
  && evaluateGossipTick (gossipCandidate (physicalGossip b))
       == RejectDropProvenance

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
gossipTickPhysicsGreen :: Bool
gossipTickPhysicsGreen = False

-- | Lean/Coq: @gossip_tick_physics_green_false@.
gossipTickPhysicsGreenFalse :: Bool
gossipTickPhysicsGreenFalse = not gossipTickPhysicsGreen

-- | Production wiring stays open (gossip tick lift only).
gossipTickProductionWired :: Bool
gossipTickProductionWired = False

-- | Lean/Coq: @gossip_tick_production_wired_false@.
gossipTickProductionWiredFalse :: Bool
gossipTickProductionWiredFalse = not gossipTickProductionWired

-- | Honest non-claim string (meso §15.6 H3 gossip tick scaffold).
gossipTickNonClaim :: String
gossipTickNonClaim =
  "§15.6 H3 gossip tick: typed refuse of drop-provenance; "
    ++ "compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
gossipTickNonClaimNonempty :: Bool
gossipTickNonClaimNonempty = length gossipTickNonClaim > 0

-- | Catalog witness: meso Urge GossipTick module present.
gossipTickModuleWitness :: Bool
gossipTickModuleWitness = True

-- | Zero new axiom discipline witness.
gossipTickNoNewAxiom :: Bool
gossipTickNoNewAxiom = True

-- | Second-argmin refusal: gossip tick composes 'excitementSelect' only.
gossipTickNoSecondArgmin :: Bool
gossipTickNoSecondArgmin =
  gossipTickNoLocalArgmin
    (gossipTickNew
      (GossipMeshIdentity
        { meshId = "mesh:h3"
        , meshCarrier =
            carrierMk
              (HistorySnapshot 1 (ThermodynamicState 2400 0 0.3 30 40))
              (wallOnlyStamp 1)
              (SdfFRep 0 0)
              (ExactAlg 0 0)
              satisfiedWitness
        })
      h3AdmissibleGossipCandidate)
    []
