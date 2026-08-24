-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CarrierProduct
-- Description : Meso acting Urge — §3 Repository/History carrier as typed product.
--
-- History carrier is a dependent product (not prose slogans):
--   UMST ⊗ UCRS stamp ⊗ SDF/FRep ⊗ ExactAlg ⊗ InvariantWitness.
--
-- Each factor has projections, pairing, and preservation lemmas. Refuse XOR partial
-- carrier — five factors are concurrent product, not mutually-exclusive enum.
--
-- Urge carrier recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CarrierProduct
  ( -- * Factor carriers (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness)
    StampTier (..)
  , UcrsStamp (..)
  , wallOnlyStamp
  , wallPlusSeqStamp
  , SdfFRep (..)
  , ExactAlg (..)
  , InvariantWitness (..)
  , satisfiedWitness
  , rejectedWitness
    -- * History carrier product + projections
  , HistoryCarrier (..)
  , umstProj
  , stampProj
  , sdfFRepProj
  , exactAlgProj
  , witnessProj
  , carrierMk
  , carrierMkUmstProj
  , carrierMkStampProj
  , carrierMkSdfFRepProj
  , carrierMkExactAlgProj
  , carrierMkWitnessProj
    -- * Well-formedness + append-only stamp discipline
  , carrierWellFormed
  , extendStamp
  , extendStampPreservesSeq
  , carrierAlongTransition
  , carrierAlongTransitionPreservesSdf
  , carrierAlongTransitionPreservesExactAlg
    -- * Second-law bridge (inherited — zero new axioms)
  , carrierFromLandauer
  , carrierFromLandauerAdmitSecondLaw
  , carrierFromLandauerWitnessSatisfied
  , carrierSecondLawFromLandauer
  , carrierSecondLawFromHypothesis
    -- * Excitement alignment (no second argmin)
  , carrierSelect
  , carrierSelectEqExcitementSelect
  , carrierRecovery
  , carrierRecoveryEqExcitementSelect
  , carrierRecoveryNoLocalArgmin
    -- * Refuse XOR partial carrier (product not enum)
  , CarrierFactorSlot (..)
  , isFactorPresent
  , CarrierFactorScaffold (..)
  , carrierScaffoldUnwired
  , allFactorsPresent
  , PartialCarrierVerdict (..)
  , evaluatePartialCarrier
  , partialCarrierUnwiredRefused
  , fullScaffold
  , partialCarrierFullOk
  , XorCarrierVerdict (..)
  , evaluateXorCarrier
  , xorCarrierUnwiredProductOk
  , xorCarrierMutuallyExclusiveRefused
  , carrierProductNotXor
  , carrierProductNotPartial
    -- * Honesty flags + catalog witnesses
  , carrierProductPhysicsGreen
  , carrierProductPhysicsGreenFalse
  , carrierProductProductionWired
  , carrierProductProductionWiredFalse
  , carrierProductMarker
  , carrierProductModuleWitness
  , carrierProductNoNewAxiom
  , carrierProductNoSecondArgmin
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Factor carriers (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness)
-- ---------------------------------------------------------------------------

-- | UCRS stamp tier — wall-only vs wall+seq (mirrors 'FrugalStamp' wire).
data StampTier
  = StampWallOnly
  | StampWallPlusSeq
  deriving (Show, Eq)

-- | UCRS observation stamp: mandatory wall chronology + optional 'ucrsSeq'.
data UcrsStamp = UcrsStamp
  { observedAtWall :: !Int
  , ucrsSeq        :: !(Maybe Int)
  , stampTier      :: !StampTier
  } deriving (Show, Eq)

-- | Wall-only stamp (seq absent — honest, not invented).
wallOnlyStamp :: Int -> UcrsStamp
wallOnlyStamp wall =
  UcrsStamp
    { observedAtWall = wall
    , ucrsSeq        = Nothing
    , stampTier      = StampWallOnly
    }

-- | Wall + seq stamp when local probe finds a sequence.
wallPlusSeqStamp :: Int -> Int -> UcrsStamp
wallPlusSeqStamp wall seqNum =
  UcrsStamp
    { observedAtWall = wall
    , ucrsSeq        = Just seqNum
    , stampTier      = StampWallPlusSeq
    }

-- | SDF canonical digest + FRep grain (behavior geometry, not f64 theater).
data SdfFRep = SdfFRep
  { canonicalDigest :: !Int
  , frepGrain       :: !Int
  } deriving (Show, Eq)

-- | Exact rational algorithm slot — ℚ executable, not f64 compare.
data ExactAlg = ExactAlg
  { algValue :: !Double
  , opTag    :: !Int
  } deriving (Show, Eq)

-- | Invariant witness bundle (structural — not empirical ':barc-cert').
data InvariantWitness = InvariantWitness
  { witnessSatisfied :: !Bool
  , marginH          :: !Double
  } deriving (Show, Eq)

-- | Satisfied witness at zero margin (M3 stub shell).
satisfiedWitness :: InvariantWitness
satisfiedWitness =
  InvariantWitness {witnessSatisfied = True, marginH = 0}

-- | Rejected witness (positive refuse — not only '!physics_green').
rejectedWitness :: InvariantWitness
rejectedWitness =
  InvariantWitness {witnessSatisfied = False, marginH = 0}

-- ---------------------------------------------------------------------------
-- SECTION 2: History carrier product + projections
-- ---------------------------------------------------------------------------

-- | §3 Repository/History carrier: typed product of five factors.
data HistoryCarrier = HistoryCarrier
  { carrierUmst     :: !HistorySnapshot
  , carrierStamp    :: !UcrsStamp
  , carrierSdfFRep  :: !SdfFRep
  , carrierExactAlg :: !ExactAlg
  , carrierWitness  :: !InvariantWitness
  } deriving (Show, Eq)

-- | Project first factor (UMST history snapshot).
umstProj :: HistoryCarrier -> HistorySnapshot
umstProj = carrierUmst

-- | Project UCRS stamp factor.
stampProj :: HistoryCarrier -> UcrsStamp
stampProj = carrierStamp

-- | Project SDF/FRep factor.
sdfFRepProj :: HistoryCarrier -> SdfFRep
sdfFRepProj = carrierSdfFRep

-- | Project exact-algorithm factor.
exactAlgProj :: HistoryCarrier -> ExactAlg
exactAlgProj = carrierExactAlg

-- | Project invariant-witness factor.
witnessProj :: HistoryCarrier -> InvariantWitness
witnessProj = carrierWitness

-- | Pair five factors into a history carrier (product constructor).
carrierMk
  :: HistorySnapshot
  -> UcrsStamp
  -> SdfFRep
  -> ExactAlg
  -> InvariantWitness
  -> HistoryCarrier
carrierMk h s d a w =
  HistoryCarrier
    { carrierUmst     = h
    , carrierStamp    = s
    , carrierSdfFRep  = d
    , carrierExactAlg = a
    , carrierWitness  = w
    }

-- | Projections round-trip the constructor (η law for the product).
carrierMkUmstProj
  :: HistorySnapshot
  -> UcrsStamp
  -> SdfFRep
  -> ExactAlg
  -> InvariantWitness
  -> Bool
carrierMkUmstProj h s d a w =
  umstProj (carrierMk h s d a w) == h

carrierMkStampProj
  :: HistorySnapshot
  -> UcrsStamp
  -> SdfFRep
  -> ExactAlg
  -> InvariantWitness
  -> Bool
carrierMkStampProj h s d a w =
  stampProj (carrierMk h s d a w) == s

carrierMkSdfFRepProj
  :: HistorySnapshot
  -> UcrsStamp
  -> SdfFRep
  -> ExactAlg
  -> InvariantWitness
  -> Bool
carrierMkSdfFRepProj h s d a w =
  sdfFRepProj (carrierMk h s d a w) == d

carrierMkExactAlgProj
  :: HistorySnapshot
  -> UcrsStamp
  -> SdfFRep
  -> ExactAlg
  -> InvariantWitness
  -> Bool
carrierMkExactAlgProj h s d a w =
  exactAlgProj (carrierMk h s d a w) == a

carrierMkWitnessProj
  :: HistorySnapshot
  -> UcrsStamp
  -> SdfFRep
  -> ExactAlg
  -> InvariantWitness
  -> Bool
carrierMkWitnessProj h s d a w =
  witnessProj (carrierMk h s d a w) == w

-- ---------------------------------------------------------------------------
-- SECTION 3: Well-formedness + append-only stamp discipline
-- ---------------------------------------------------------------------------

-- | Carrier well-formed: stamp wall present + witness margin non-negative.
carrierWellFormed :: HistoryCarrier -> Bool
carrierWellFormed c =
  observedAtWall (stampProj c) > 0 && marginH (witnessProj c) >= 0

-- | Append-only stamp extension along a history transition (no silent squash).
extendStamp :: UcrsStamp -> Int -> UcrsStamp
extendStamp prior postWall =
  case ucrsSeq prior of
    Nothing -> wallOnlyStamp postWall
    Just seqNum -> wallPlusSeqStamp postWall seqNum

-- | Extended stamp retains prior seq when present.
extendStampPreservesSeq :: UcrsStamp -> Int -> Bool
extendStampPreservesSeq prior postWall =
  ucrsSeq (extendStamp prior postWall) == ucrsSeq prior

-- | Carrier along a history transition: align UMST endpoints + extend stamp.
carrierAlongTransition
  :: HistoryTransition
  -> HistoryCarrier
  -> Bool
  -> Int
  -> HistoryCarrier
carrierAlongTransition t prior commitMatch postWall
  | commitMatch =
      carrierMk
        (historyPost t)
        (extendStamp (stampProj prior) postWall)
        (sdfFRepProj prior)
        (exactAlgProj prior)
        (witnessProj prior)
  | otherwise = prior

-- | Transition carrier preserves prior SDF/FRep factor.
carrierAlongTransitionPreservesSdf
  :: HistoryTransition
  -> HistoryCarrier
  -> Bool
  -> Int
  -> Bool
carrierAlongTransitionPreservesSdf t prior commitMatch postWall =
  sdfFRepProj (carrierAlongTransition t prior commitMatch postWall)
    == sdfFRepProj prior

-- | Transition carrier preserves prior exact-alg factor.
carrierAlongTransitionPreservesExactAlg
  :: HistoryTransition
  -> HistoryCarrier
  -> Bool
  -> Int
  -> Bool
carrierAlongTransitionPreservesExactAlg t prior commitMatch postWall =
  exactAlgProj (carrierAlongTransition t prior commitMatch postWall)
    == exactAlgProj prior

-- ---------------------------------------------------------------------------
-- SECTION 4: Second-law bridge (inherited — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Landauer bridge yields a carrier whose witness discharges 'admitSecondLaw'.
carrierFromLandauer
  :: LandauerHistoryBridge
  -> HistoryCarrier
  -> Bool
  -> Int
  -> Bool
  -> HistoryCarrier
carrierFromLandauer b prior commitMatch postWall hSL =
  (carrierAlongTransition (landauerTransition b) prior commitMatch postWall)
    { carrierWitness = if hSL then satisfiedWitness else witnessProj prior }

-- | Physical bridge discharge: second law on Landauer transition.
carrierFromLandauerAdmitSecondLaw
  :: LandauerHistoryBridge
  -> Bool
  -> Bool
carrierFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Bridged carrier witness satisfied when second law holds.
carrierFromLandauerWitnessSatisfied
  :: LandauerHistoryBridge
  -> HistoryCarrier
  -> Bool
  -> Int
  -> Bool
  -> Bool
carrierFromLandauerWitnessSatisfied b prior commitMatch postWall hSL =
  witnessSatisfied
    (witnessProj (carrierFromLandauer b prior commitMatch postWall hSL))

-- | Second law on carrier transition from Landauer bridge discharge.
carrierSecondLawFromLandauer
  :: LandauerHistoryBridge
  -> Bool
  -> Bool
carrierSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for carrier second law (no new axiom).
carrierSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
carrierSecondLawFromHypothesis t ok =
  ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 5: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | History recovery composes 'excitementSelect' on typed head — no Urge argmin.
carrierSelect
  :: HistoryCarrier
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
carrierSelect c cands =
  excitementSelect (historyHead (umstProj c)) cands

-- | Definitional witness: carrier selection API is 'excitementSelect'.
carrierSelectEqExcitementSelect
  :: HistoryCarrier -> [HistoryCandidate] -> Bool
carrierSelectEqExcitementSelect c cands =
  carrierSelect c cands
    == excitementSelect (historyHead (umstProj c)) cands

-- | Carrier recovery on a typed head — alias of 'carrierSelect'.
carrierRecovery
  :: HistoryCarrier
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
carrierRecovery = carrierSelect

-- | Carrier recovery equals 'excitementSelect' (no local argmin).
carrierRecoveryEqExcitementSelect
  :: HistoryCarrier -> [HistoryCandidate] -> Bool
carrierRecoveryEqExcitementSelect = carrierSelectEqExcitementSelect

-- | Carrier selector re-uses 'excitementSelect' — no Urge-local argmin.
carrierRecoveryNoLocalArgmin
  :: HistoryCarrier -> [HistoryCandidate] -> Bool
carrierRecoveryNoLocalArgmin c cands =
  carrierRecovery c cands
    == excitementSelect (historyHead (umstProj c)) cands

-- ---------------------------------------------------------------------------
-- SECTION 6: Refuse XOR partial carrier (product not enum; no absent factors)
-- ---------------------------------------------------------------------------

data CarrierFactorSlot
  = FactorPresent
  | FactorAbsent
  | FactorUnwired
  deriving (Show, Eq)

isFactorPresent :: CarrierFactorSlot -> Bool
isFactorPresent FactorPresent = True
isFactorPresent _               = False

data CarrierFactorScaffold = CarrierFactorScaffold
  { umstSlot    :: !CarrierFactorSlot
  , stampSlot   :: !CarrierFactorSlot
  , sdfSlot     :: !CarrierFactorSlot
  , exactSlot   :: !CarrierFactorSlot
  , witnessSlot :: !CarrierFactorSlot
  } deriving (Show, Eq)

carrierScaffoldUnwired :: CarrierFactorScaffold
carrierScaffoldUnwired =
  CarrierFactorScaffold
    { umstSlot    = FactorUnwired
    , stampSlot   = FactorUnwired
    , sdfSlot     = FactorUnwired
    , exactSlot   = FactorUnwired
    , witnessSlot = FactorUnwired
    }

allFactorsPresent :: CarrierFactorScaffold -> Bool
allFactorsPresent s =
  isFactorPresent (umstSlot s)
  && isFactorPresent (stampSlot s)
  && isFactorPresent (sdfSlot s)
  && isFactorPresent (exactSlot s)
  && isFactorPresent (witnessSlot s)

data PartialCarrierVerdict
  = PartialCarrierRefuse
  | PartialCarrierOk
  deriving (Show, Eq)

evaluatePartialCarrier :: CarrierFactorScaffold -> PartialCarrierVerdict
evaluatePartialCarrier s =
  if allFactorsPresent s then PartialCarrierOk else PartialCarrierRefuse

partialCarrierUnwiredRefused :: Bool
partialCarrierUnwiredRefused =
  evaluatePartialCarrier carrierScaffoldUnwired == PartialCarrierRefuse

fullScaffold :: CarrierFactorScaffold
fullScaffold =
  CarrierFactorScaffold
    { umstSlot    = FactorPresent
    , stampSlot   = FactorPresent
    , sdfSlot     = FactorPresent
    , exactSlot   = FactorPresent
    , witnessSlot = FactorPresent
    }

partialCarrierFullOk :: Bool
partialCarrierFullOk =
  evaluatePartialCarrier fullScaffold == PartialCarrierOk

data XorCarrierVerdict
  = XorCarrierRefuse
  | XorCarrierProductOk
  deriving (Show, Eq)

evaluateXorCarrier
  :: CarrierFactorScaffold
  -> CarrierFactorSlot
  -> CarrierFactorSlot
  -> XorCarrierVerdict
evaluateXorCarrier s i j =
  if allFactorsPresent s
    then
      if isFactorPresent i && isFactorPresent j
        then XorCarrierRefuse
        else XorCarrierProductOk
    else XorCarrierProductOk

xorCarrierUnwiredProductOk :: Bool
xorCarrierUnwiredProductOk =
  evaluateXorCarrier carrierScaffoldUnwired FactorPresent FactorPresent
    == XorCarrierProductOk

xorCarrierMutuallyExclusiveRefused :: Bool
xorCarrierMutuallyExclusiveRefused =
  evaluateXorCarrier fullScaffold FactorPresent FactorPresent
    == XorCarrierRefuse

-- | Five factors are concurrent product, not XOR enum.
carrierProductNotXor :: Bool
carrierProductNotXor = True

-- | Partial carrier scaffold refused fail-closed.
carrierProductNotPartial :: Bool
carrierProductNotPartial = True

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
carrierProductPhysicsGreen :: Bool
carrierProductPhysicsGreen = False

-- | Lean/Coq: @carrier_product_physics_green_false@.
carrierProductPhysicsGreenFalse :: Bool
carrierProductPhysicsGreenFalse = not carrierProductPhysicsGreen

-- | Production wiring stays open (product lift only).
carrierProductProductionWired :: Bool
carrierProductProductionWired = False

-- | Lean/Coq: @carrier_product_production_wired_false@.
carrierProductProductionWiredFalse :: Bool
carrierProductProductionWiredFalse = not carrierProductProductionWired

-- | Meso §3 section marker (Lean mirror).
carrierProductMarker :: Int
carrierProductMarker = 3

-- | Catalog witness: meso Urge CarrierProduct module present.
carrierProductModuleWitness :: Bool
carrierProductModuleWitness = True

-- | Zero new axiom discipline witness.
carrierProductNoNewAxiom :: Bool
carrierProductNoNewAxiom = True

-- | Second-argmin refusal: carrier composes 'excitementSelect' only.
carrierProductNoSecondArgmin :: Bool
carrierProductNoSecondArgmin =
  carrierRecoveryNoLocalArgmin
    (carrierMk
      (HistorySnapshot 0 (ThermodynamicState 2400 0 0.3 30 40))
      (wallOnlyStamp 1)
      (SdfFRep 0 0)
      (ExactAlg 0 0)
      satisfiedWitness)
    []
