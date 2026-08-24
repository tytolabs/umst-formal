-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.KleisliMerge
-- Description : Meso acting Urge — §16.7 operator verb `merge` as Kleisli arrow.
--
-- Kleisli gate = `gate_check_before_sync` inbound; MergeSafe predicate required;
-- Excitement = provenance preserved; entity check = tier disjoint.
-- Honest refuse on MergeSafe mismatch — no CRDT auto-merge.
--
-- Composes 'excitementSelect' — no second argmin.
-- Mirrors 'UMST.Urge.CollaborativeObject' / Coq @Urge.KleisliMerge@.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.KleisliMerge
  ( -- * §16.7 verb row + merge carriers
    OperatorVerb (..)
  , VerbColumnRequirement (..)
  , KleisliGateKind (..)
  , EntityCheckKind (..)
  , OperatorVerbRow (..)
  , mergeVerbRow
  , MemoryTier (..)
  , MergeHistoryObject (..)
  , InboundGateCheck (..)
  , inboundGateAdmits
  , MergeTransition (..)
  , MergeProvenance (..)
  , MergeKleisliArrow (..)
  , TierDisjointVerdict (..)
  , ProvenancePreserveVerdict (..)
  , MergeArrowRefusal (..)
  , MergeOutcome (..)
    -- * MergeSafe + tier disjoint + provenance (computational)
  , mergeHistoryEntry
  , evaluateTierDisjoint
  , preservesMergeProvenance
  , evaluateMergeKleisli
  , mergeGateCheckBeforeSync
    -- * Verb-row witnesses
  , mergeVerbRowMergeSafeRequired
  , mergeVerbRowExcitementRequired
  , mergeVerbRowTierDisjointEntity
  , kleisliGateMatchesMergeInbound
    -- * Excitement alignment (no second argmin)
  , MergeKleisliCtx (..)
  , mergeKleisliSelect
  , mergeKleisliSelectCtx
  , mergeKleisliSelectEqExcitementSelect
  , mergeKleisliSelectEqAdmitHistorySelect
  , mergeKleisliNoLocalArgmin
    -- * Positive refuse + CRDT + fixtures
  , MergeGateMismatch (..)
  , refuseFrugalMiOnMerge
  , refuseOutboundTickOnMerge
  , refuseRemoteClassOnMerge
  , refuseReplicaClassOnMerge
  , refuseProductionWiredMerge
  , mergeFixtureEntry
  , mergeFixtureObject
  , mergeFixtureState
  , mergeFixtureArrow
  , mergeFixtureArrowGateRefused
  , mergeFixtureArrowMergeSafeRefused
  , mergeFixtureArrowTierDisjointRefused
  , mergeFixtureEvaluateOk
  , mergeFixtureGateRefused
  , mergeFixtureMergeSafeRefused
  , mergeFixtureTierDisjointRefused
  , mergeFixtureCrdtRefused
  , mergeFixturePositiveRefuseGates
    -- * Landauer bridge (derived — zero new axioms)
  , mergeSecondLawFromLandauer
  , mergeFromLandauerAdmitSecondLaw
  , mergeSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , kleisliMergePhysicsGreen
  , kleisliMergePhysicsGreenFalse
  , kleisliMergeProductionWired
  , kleisliMergeProductionWiredFalse
  , kleisliMergeMarker
  , kleisliMergeMarkerPos
  , kleisliMergeModuleWitness
  , kleisliMergeNoNewAxiom
  , kleisliMergeNoSecondArgmin
  , kleisliMergeNonClaim
  , kleisliMergeNonClaimNonempty
  ) where

import UMST.Concrete (AdmissibilityResult (..), ThermodynamicState (..), gateCheck)
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
import UMST.Urge.MergeSafe
  ( CrdtAutoMergeRefused (..)
  , HistoryMemoryEntry (..)
  , MergeSafeVerdict (..)
  , mergeSafe
  , refuseCrdtAutoMerge
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: §16.7 verb row + merge carriers
-- ---------------------------------------------------------------------------

data OperatorVerb = OperatorVerbMerge deriving (Show, Eq)

data VerbColumnRequirement
  = VerbColNotRequired
  | VerbColRequired
  deriving (Show, Eq)

data KleisliGateKind
  = GateCheckBeforeSyncInbound
  | FrugalMiObservation
  | OutboundTickIfAdmitted
  deriving (Show, Eq)

data EntityCheckKind
  = TierDisjoint
  | RemoteClass
  | ReplicaClass
  deriving (Show, Eq)

data OperatorVerbRow = OperatorVerbRow
  { verbRowVerb          :: !OperatorVerb
  , verbRowKleisliGate   :: !KleisliGateKind
  , verbRowMergeSafeCol  :: !VerbColumnRequirement
  , verbRowExcitementCol :: !VerbColumnRequirement
  , verbRowEntityCheck   :: !EntityCheckKind
  } deriving (Show, Eq)

mergeVerbRow :: OperatorVerbRow
mergeVerbRow =
  OperatorVerbRow
    { verbRowVerb = OperatorVerbMerge
    , verbRowKleisliGate = GateCheckBeforeSyncInbound
    , verbRowMergeSafeCol = VerbColRequired
    , verbRowExcitementCol = VerbColRequired
    , verbRowEntityCheck = TierDisjoint
    }

data MemoryTier
  = MemoryEphemeral
  | MemoryDevice
  | MemoryFederated
  deriving (Show, Eq)

data MergeHistoryObject = MergeHistoryObject
  { mergeObjEntry :: !HistoryMemoryEntry
  , mergeObjTier  :: !MemoryTier
  } deriving (Show, Eq)

data InboundGateCheck
  = InboundAdmitted
  | InboundRefused
  | InboundBypassAttempted
  deriving (Show, Eq)

inboundGateAdmits :: InboundGateCheck -> Bool
inboundGateAdmits InboundAdmitted = True
inboundGateAdmits _                 = False

data MergeTransition = MergeTransition
  { mergePriorCommit :: !Int
  , mergePostCommit  :: !Int
  } deriving (Show, Eq)

data MergeProvenance = MergeProvenance
  { mergeUcrsChain       :: ![Int]
  , mergeDagCommit       :: !Int
  , mergeLandauerWitness :: !Bool
  } deriving (Show, Eq)

data MergeKleisliArrow = MergeKleisliArrow
  { mergeArrowVerb         :: !OperatorVerb
  , mergeArrowGate         :: !InboundGateCheck
  , mergeArrowLeft         :: !MergeHistoryObject
  , mergeArrowRight        :: !MergeHistoryObject
  , mergeArrowTransition   :: !MergeTransition
  , mergeArrowPriorProv    :: !MergeProvenance
  , mergeArrowPostProv     :: !MergeProvenance
  , mergeArrowPriorState   :: !ThermodynamicState
  , mergeArrowPostState    :: !ThermodynamicState
  } deriving (Show, Eq)

data TierDisjointVerdict
  = TierDisjointAdmit
  | TierDisjointRefuseCrossTier
  deriving (Show, Eq)

data ProvenancePreserveVerdict
  = ProvenanceAdmit
  | ProvenanceRefusePriorDag
  | ProvenanceRefusePostDag
  | ProvenanceRefuseChain
  | ProvenanceRefuseWitness
  deriving (Show, Eq)

data MergeArrowRefusal
  = MergeWrongVerb
  | MergeGateRefused
  | MergeGateBypassRefused
  | MergeTierDisjoint TierDisjointVerdict
  | MergeSafeRefused
  | MergeProvenanceRefused ProvenancePreserveVerdict
  | MergeProductionWiredRefused
  deriving (Show, Eq)

data MergeOutcome = MergeOutcome
  { mergeOutcomeMerged     :: !MergeHistoryObject
  , mergeOutcomeProvenance :: !ProvenancePreserveVerdict
  , mergeOutcomeTier       :: !TierDisjointVerdict
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: MergeSafe + tier disjoint + provenance (computational)
-- ---------------------------------------------------------------------------

mergeGateDt :: Double
mergeGateDt = 3600.0

thermoStateEqb :: ThermodynamicState -> ThermodynamicState -> Bool
thermoStateEqb s1 s2 =
  density s1 == density s2
  && freeEnergy s1 == freeEnergy s2
  && hydration s1 == hydration s2
  && strength s1 == strength s2
  && maxStrength s1 == maxStrength s2

mergeGateCheckBeforeSync :: ThermodynamicState -> ThermodynamicState -> Bool
mergeGateCheckBeforeSync prior post =
  if thermoStateEqb prior post
    then True
    else accepted (gateCheck prior post mergeGateDt)

memoryTierEqb :: MemoryTier -> MemoryTier -> Bool
memoryTierEqb MemoryEphemeral MemoryEphemeral = True
memoryTierEqb MemoryDevice MemoryDevice       = True
memoryTierEqb MemoryFederated MemoryFederated = True
memoryTierEqb _ _                             = False

evaluateTierDisjoint :: MemoryTier -> MemoryTier -> TierDisjointVerdict
evaluateTierDisjoint t1 t2 =
  if memoryTierEqb t1 t2 then TierDisjointAdmit else TierDisjointRefuseCrossTier

mergeHistoryEntry :: HistoryMemoryEntry -> HistoryMemoryEntry -> Maybe HistoryMemoryEntry
mergeHistoryEntry left right =
  case mergeSafe left right of
    MergeSafeAdmit         -> Just left
    MergeSafeRefuseMismatch -> Nothing

preservesMergeChain :: MergeProvenance -> MergeProvenance -> ProvenancePreserveVerdict
preservesMergeChain prior post =
  let expected = mergeUcrsChain prior ++ [mergeDagCommit prior]
   in if mergeUcrsChain post == expected
        then
          if mergeLandauerWitness prior && not (mergeLandauerWitness post)
            then ProvenanceRefuseWitness
            else ProvenanceAdmit
        else ProvenanceRefuseChain

preservesMergeProvenance
  :: MergeTransition -> MergeProvenance -> MergeProvenance -> ProvenancePreserveVerdict
preservesMergeProvenance tr prior post =
  if mergeDagCommit prior == mergePriorCommit tr
    then
      if mergeDagCommit post == mergePostCommit tr
        then preservesMergeChain prior post
        else ProvenanceRefusePostDag
    else ProvenanceRefusePriorDag

evaluateMergeKleisli :: MergeKleisliArrow -> Either MergeArrowRefusal MergeOutcome
evaluateMergeKleisli a
  | mergeArrowVerb a /= OperatorVerbMerge =
      Left MergeWrongVerb
  | mergeArrowGate a == InboundBypassAttempted =
      Left MergeGateBypassRefused
  | not (inboundGateAdmits (mergeArrowGate a)) =
      Left MergeGateRefused
  | otherwise =
      case evaluateTierDisjoint
             (mergeObjTier (mergeArrowLeft a))
             (mergeObjTier (mergeArrowRight a)) of
        TierDisjointRefuseCrossTier ->
          Left (MergeTierDisjoint TierDisjointRefuseCrossTier)
        TierDisjointAdmit ->
          case mergeHistoryEntry
                 (mergeObjEntry (mergeArrowLeft a))
                 (mergeObjEntry (mergeArrowRight a)) of
            Nothing -> Left MergeSafeRefused
            Just mergedEntry ->
              let prov =
                    preservesMergeProvenance
                      (mergeArrowTransition a)
                      (mergeArrowPriorProv a)
                      (mergeArrowPostProv a)
               in case prov of
                    ProvenanceAdmit ->
                      if mergeGateCheckBeforeSync
                           (mergeArrowPriorState a)
                           (mergeArrowPostState a)
                        then
                          Right
                            MergeOutcome
                              { mergeOutcomeMerged =
                                  MergeHistoryObject
                                    { mergeObjEntry = mergedEntry
                                    , mergeObjTier = mergeObjTier (mergeArrowLeft a)
                                    }
                              , mergeOutcomeProvenance = prov
                              , mergeOutcomeTier = TierDisjointAdmit
                              }
                        else Left MergeGateRefused
                    pv -> Left (MergeProvenanceRefused pv)

-- ---------------------------------------------------------------------------
-- SECTION 3: Verb-row witnesses
-- ---------------------------------------------------------------------------

mergeVerbRowMergeSafeRequired :: Bool
mergeVerbRowMergeSafeRequired = verbRowMergeSafeCol mergeVerbRow == VerbColRequired

mergeVerbRowExcitementRequired :: Bool
mergeVerbRowExcitementRequired = verbRowExcitementCol mergeVerbRow == VerbColRequired

mergeVerbRowTierDisjointEntity :: Bool
mergeVerbRowTierDisjointEntity = verbRowEntityCheck mergeVerbRow == TierDisjoint

kleisliGateMatchesMergeInbound :: Bool
kleisliGateMatchesMergeInbound =
  verbRowKleisliGate mergeVerbRow == GateCheckBeforeSyncInbound

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

data MergeKleisliCtx = MergeKleisliCtx
  { mergeKleisliPrior      :: !ThermodynamicState
  , mergeKleisliSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

mergeKleisliSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
mergeKleisliSelect = excitementSelect

mergeKleisliSelectCtx :: MergeKleisliCtx -> Either ExcitementResidue HistoryCandidate
mergeKleisliSelectCtx ctx =
  excitementSelect (mergeKleisliPrior ctx) (mergeKleisliSuccessors ctx)

mergeKleisliSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
mergeKleisliSelectEqExcitementSelect src cands =
  mergeKleisliSelect src cands == excitementSelect src cands

mergeKleisliSelectEqAdmitHistorySelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
mergeKleisliSelectEqAdmitHistorySelect src cands =
  mergeKleisliSelect src cands == admitHistorySelect src cands

mergeKleisliNoLocalArgmin :: MergeKleisliCtx -> Bool
mergeKleisliNoLocalArgmin ctx =
  mergeKleisliSelectCtx ctx
    == excitementSelect (mergeKleisliPrior ctx) (mergeKleisliSuccessors ctx)

-- ---------------------------------------------------------------------------
-- SECTION 5: Positive refuse + CRDT + fixtures
-- ---------------------------------------------------------------------------

data MergeGateMismatch
  = FrugalMiOnMerge
  | OutboundTickOnMerge
  | RemoteClassOnMerge
  | ReplicaClassOnMerge
  deriving (Show, Eq)

refuseFrugalMiOnMerge :: MergeGateMismatch
refuseFrugalMiOnMerge = FrugalMiOnMerge

refuseOutboundTickOnMerge :: MergeGateMismatch
refuseOutboundTickOnMerge = OutboundTickOnMerge

refuseRemoteClassOnMerge :: MergeGateMismatch
refuseRemoteClassOnMerge = RemoteClassOnMerge

refuseReplicaClassOnMerge :: MergeGateMismatch
refuseReplicaClassOnMerge = ReplicaClassOnMerge

refuseProductionWiredMerge :: MergeArrowRefusal
refuseProductionWiredMerge = MergeProductionWiredRefused

mergeFixtureEntry :: HistoryMemoryEntry
mergeFixtureEntry =
  HistoryMemoryEntry {memoryId = 42, memoryTheoremId = "7"}

mergeFixtureObject :: MergeHistoryObject
mergeFixtureObject =
  MergeHistoryObject {mergeObjEntry = mergeFixtureEntry, mergeObjTier = MemoryDevice}

mergeFixtureState :: ThermodynamicState
mergeFixtureState = ThermodynamicState 2400 0 0 0 0

mergeFixtureProvenance :: Int -> Int -> MergeProvenance
mergeFixtureProvenance prior _post =
  MergeProvenance
    { mergeUcrsChain = [prior]
    , mergeDagCommit = prior
    , mergeLandauerWitness = True
    }

mergeFixturePostProvenance :: Int -> Int -> MergeProvenance
mergeFixturePostProvenance prior post =
  MergeProvenance
    { mergeUcrsChain = [prior, prior]
    , mergeDagCommit = post
    , mergeLandauerWitness = True
    }

mergeFixtureArrow :: MergeKleisliArrow
mergeFixtureArrow =
  MergeKleisliArrow
    { mergeArrowVerb = OperatorVerbMerge
    , mergeArrowGate = InboundAdmitted
    , mergeArrowLeft = mergeFixtureObject
    , mergeArrowRight = mergeFixtureObject
    , mergeArrowTransition = MergeTransition 10 11
    , mergeArrowPriorProv = mergeFixtureProvenance 10 11
    , mergeArrowPostProv = mergeFixturePostProvenance 10 11
    , mergeArrowPriorState = mergeFixtureState
    , mergeArrowPostState = mergeFixtureState
    }

mergeFixtureArrowGateRefused :: MergeKleisliArrow
mergeFixtureArrowGateRefused = mergeFixtureArrow {mergeArrowGate = InboundRefused}

mergeFixtureRightMismatch :: MergeHistoryObject
mergeFixtureRightMismatch =
  MergeHistoryObject
    { mergeObjEntry = HistoryMemoryEntry {memoryId = 99, memoryTheoremId = "7"}
    , mergeObjTier = MemoryDevice
    }

mergeFixtureArrowMergeSafeRefused :: MergeKleisliArrow
mergeFixtureArrowMergeSafeRefused =
  mergeFixtureArrow {mergeArrowRight = mergeFixtureRightMismatch}

mergeFixtureRightCrossTier :: MergeHistoryObject
mergeFixtureRightCrossTier =
  MergeHistoryObject {mergeObjEntry = mergeFixtureEntry, mergeObjTier = MemoryFederated}

mergeFixtureArrowTierDisjointRefused :: MergeKleisliArrow
mergeFixtureArrowTierDisjointRefused =
  mergeFixtureArrow {mergeArrowRight = mergeFixtureRightCrossTier}

mergeFixtureEvaluateOk :: Bool
mergeFixtureEvaluateOk =
  evaluateMergeKleisli mergeFixtureArrow
    == Right
         MergeOutcome
           { mergeOutcomeMerged = mergeFixtureObject
           , mergeOutcomeProvenance = ProvenanceAdmit
           , mergeOutcomeTier = TierDisjointAdmit
           }

mergeFixtureGateRefused :: Bool
mergeFixtureGateRefused =
  evaluateMergeKleisli mergeFixtureArrowGateRefused == Left MergeGateRefused

mergeFixtureMergeSafeRefused :: Bool
mergeFixtureMergeSafeRefused =
  evaluateMergeKleisli mergeFixtureArrowMergeSafeRefused == Left MergeSafeRefused

mergeFixtureTierDisjointRefused :: Bool
mergeFixtureTierDisjointRefused =
  evaluateMergeKleisli mergeFixtureArrowTierDisjointRefused
    == Left (MergeTierDisjoint TierDisjointRefuseCrossTier)

mergeFixtureCrdtRefused :: Bool
mergeFixtureCrdtRefused = refuseCrdtAutoMerge == CrdtAutoMergeRefused

mergeFixturePositiveRefuseGates :: Bool
mergeFixturePositiveRefuseGates =
  refuseFrugalMiOnMerge == FrugalMiOnMerge
  && refuseOutboundTickOnMerge == OutboundTickOnMerge
  && refuseRemoteClassOnMerge == RemoteClassOnMerge
  && refuseReplicaClassOnMerge == ReplicaClassOnMerge

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

mergeSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
mergeSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

mergeFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
mergeFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

mergeSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
mergeSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

kleisliMergePhysicsGreen :: Bool
kleisliMergePhysicsGreen = False

kleisliMergePhysicsGreenFalse :: Bool
kleisliMergePhysicsGreenFalse = not kleisliMergePhysicsGreen

kleisliMergeProductionWired :: Bool
kleisliMergeProductionWired = False

kleisliMergeProductionWiredFalse :: Bool
kleisliMergeProductionWiredFalse = not kleisliMergeProductionWired

kleisliMergeMarker :: Int
kleisliMergeMarker = 167

kleisliMergeMarkerPos :: Bool
kleisliMergeMarkerPos = kleisliMergeMarker > 0

kleisliMergeModuleWitness :: Bool
kleisliMergeModuleWitness = True

kleisliMergeNoNewAxiom :: Bool
kleisliMergeNoNewAxiom = True

kleisliMergeNoSecondArgmin :: Bool
kleisliMergeNoSecondArgmin =
  mergeKleisliNoLocalArgmin
    (MergeKleisliCtx {mergeKleisliPrior = mergeFixtureState, mergeKleisliSuccessors = []})

kleisliMergeNonClaim :: String
kleisliMergeNonClaim =
  "§16.7 merge Kleisli arrow: gate_check_before_sync inbound; MergeSafe required; "
    ++ "tier disjoint entity check; mergeKleisliSelect composes excitementSelect; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

kleisliMergeNonClaimNonempty :: Bool
kleisliMergeNonClaimNonempty = length kleisliMergeNonClaim > 0
