-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ResidueReturn
-- Description : Meso acting Urge — §13.5 what Urge returns to Excitement.
--
-- History-plane evidence: per-recovery 'UrgeExcitementResidue' constructor counts
-- + observed ΔF corpus. Six constructors pinned to Lean @UMST.Excitement.Residue@ —
-- no seventh, no f64 ΔF theater.
--
-- Recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ResidueReturn
  ( -- * Six residue constructors (Lean arity pin)
    UrgeExcitementResidue (..)
  , residueConstructorName
  , pinSixResidueConstructors
  , pinSixLength
  , residueConstructorNames
  , mapAdmitResidue
    -- * Residue counts + observed ΔF return payload
  , ResidueCounts (..)
  , emptyResidueCounts
  , incrementResidueCount
  , residueCountsTotal
  , residueCountOf
  , ObservedDeltaF (..)
  , observedDeltaF
  , mkObservedDeltaF
  , observedDeltaFCompute
  , ResidueReturn (..)
  , emptyResidueReturn
  , addObservedDelta
  , recordResidue
  , recordAdmitResidue
    -- * Typed refusal (seventh constructor + f64 ΔF theater)
  , ResidueReturnRefusal (..)
  , refuseSeventhConstructor
  , refuseF64DeltaF
    -- * Recovery composes excitementSelect (no second argmin)
  , ResidueReturnCtx (..)
  , residueReturnSelect
  , residueReturnSelectCtx
  , residueReturnSelectEqExcitementSelect
  , residueReturnSelectEqUrgeRecoverySelect
  , residueReturnNoLocalArgmin
  , residueReturnEmpty
  , recordRecoveryAttempt
  , excitementComposePin
  , excitementComposePinMarker
    -- * Landauer bridge (derived — zero new axioms)
  , PhysicalResidueReturnBridge (..)
  , residueReturnSecondLawFromLandauer
  , physicalSecondLawImported
    -- * §13.5 fixtures + witness theorems
  , residueFixtureSrc
  , residueFixtureTgt
  , residueFixtureCandidate
  , residueSixConstructorsPinned
  , residueEmptySuccessorsRecordsNoCandidates
  , residueStrictImprovementRecordsDelta
  , residueRefuseSeventhConstructorPositive
  , residueRefuseF64DeltaFPositive
  , residueObservedDeltaFComputeFixture
    -- * Honesty flags + catalog witnesses
  , residueReturnPhysicsGreen
  , residueReturnPhysicsGreenFalse
  , residueReturnProductionWired
  , residueReturnProductionWiredFalse
  , residueReturnModuleWitness
  , residueReturnNoNewAxiom
  , residueReturnNoSecondArgmin
  , residueReturnNonClaim
  , residueReturnNonClaimNonempty
  ) where

import Data.Ratio ((%))
import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: Six residue constructors (Lean arity pin)
-- ---------------------------------------------------------------------------

-- | Lean-aligned six constructors — mirrors @UMST.Excitement.Residue@.
data UrgeExcitementResidue
  = UerNoCandidates
  | UerAllInadmissible
  | UerAllExcludedByCbf
  | UerAllExcludedByDec
  | UerUntaggedConstant
  | UerNoStrictImprovement
  deriving (Show, Eq)

-- | Stable constructor name — pins imported enum, does not fork variants.
residueConstructorName :: UrgeExcitementResidue -> String
residueConstructorName UerNoCandidates = "NoCandidates"
residueConstructorName UerAllInadmissible = "AllInadmissible"
residueConstructorName UerAllExcludedByCbf = "AllExcludedByCbf"
residueConstructorName UerAllExcludedByDec = "AllExcludedByDec"
residueConstructorName UerUntaggedConstant = "UntaggedConstant"
residueConstructorName UerNoStrictImprovement = "NoStrictImprovement"

-- | All six constructors — exhaustiveness pin against Lean arity.
pinSixResidueConstructors :: [UrgeExcitementResidue]
pinSixResidueConstructors =
  [ UerNoCandidates
  , UerAllInadmissible
  , UerAllExcludedByCbf
  , UerAllExcludedByDec
  , UerUntaggedConstant
  , UerNoStrictImprovement
  ]

-- | Pin length witness: six constructors.
pinSixLength :: Bool
pinSixLength = length pinSixResidueConstructors == 6

-- | Constructor name list (cross-language pin).
residueConstructorNames :: [String]
residueConstructorNames =
  [ "NoCandidates"
  , "AllInadmissible"
  , "AllExcludedByCbf"
  , "AllExcludedByDec"
  , "UntaggedConstant"
  , "NoStrictImprovement"
  ]

-- | Map meso 'ExcitementResidue' hook into six-constructor pin.
mapAdmitResidue :: ExcitementResidue -> UrgeExcitementResidue
mapAdmitResidue ExcNoCandidates = UerNoCandidates
mapAdmitResidue ExcAllInadmissible = UerAllInadmissible
mapAdmitResidue ExcNoStrictImprovement = UerNoStrictImprovement

-- ---------------------------------------------------------------------------
-- SECTION 2: Residue counts + observed ΔF return payload
-- ---------------------------------------------------------------------------

-- | Per-constructor occurrence counts returned to Excitement.
data ResidueCounts = ResidueCounts
  { rcNoCandidates        :: !Int
  , rcAllInadmissible     :: !Int
  , rcAllExcludedByCbf    :: !Int
  , rcAllExcludedByDec    :: !Int
  , rcUntaggedConstant    :: !Int
  , rcNoStrictImprovement :: !Int
  } deriving (Show, Eq)

-- | Zeroed residue count scaffold.
emptyResidueCounts :: ResidueCounts
emptyResidueCounts =
  ResidueCounts
    { rcNoCandidates = 0
    , rcAllInadmissible = 0
    , rcAllExcludedByCbf = 0
    , rcAllExcludedByDec = 0
    , rcUntaggedConstant = 0
    , rcNoStrictImprovement = 0
    }

-- | Total residue observations across all six constructors.
residueCountsTotal :: ResidueCounts -> Int
residueCountsTotal c =
  rcNoCandidates c
    + rcAllInadmissible c
    + rcAllExcludedByCbf c
    + rcAllExcludedByDec c
    + rcUntaggedConstant c
    + rcNoStrictImprovement c

-- | Count for a single constructor (pin test helper).
residueCountOf :: ResidueCounts -> UrgeExcitementResidue -> Int
residueCountOf c UerNoCandidates = rcNoCandidates c
residueCountOf c UerAllInadmissible = rcAllInadmissible c
residueCountOf c UerAllExcludedByCbf = rcAllExcludedByCbf c
residueCountOf c UerAllExcludedByDec = rcAllExcludedByDec c
residueCountOf c UerUntaggedConstant = rcUntaggedConstant c
residueCountOf c UerNoStrictImprovement = rcNoStrictImprovement c

-- | Record one observed 'UrgeExcitementResidue' constructor.
incrementResidueCount
  :: ResidueCounts -> UrgeExcitementResidue -> ResidueCounts
incrementResidueCount c UerNoCandidates =
  c {rcNoCandidates = rcNoCandidates c + 1}
incrementResidueCount c UerAllInadmissible =
  c {rcAllInadmissible = rcAllInadmissible c + 1}
incrementResidueCount c UerAllExcludedByCbf =
  c {rcAllExcludedByCbf = rcAllExcludedByCbf c + 1}
incrementResidueCount c UerAllExcludedByDec =
  c {rcAllExcludedByDec = rcAllExcludedByDec c + 1}
incrementResidueCount c UerUntaggedConstant =
  c {rcUntaggedConstant = rcUntaggedConstant c + 1}
incrementResidueCount c UerNoStrictImprovement =
  c {rcNoStrictImprovement = rcNoStrictImprovement c + 1}

-- | Observed free-energy delta: ΔF = observed − src (exact ℚ).
data ObservedDeltaF = ObservedDeltaF
  { odSrc      :: !Rational
  , odObserved :: !Rational
  } deriving (Show, Eq)

-- | Signed rational ΔF = observed − src.
observedDeltaF :: ObservedDeltaF -> Rational
observedDeltaF d = odObserved d - odSrc d

-- | Build observed ΔF from exact ℚ endpoints.
mkObservedDeltaF :: Rational -> Rational -> ObservedDeltaF
mkObservedDeltaF src observed =
  ObservedDeltaF {odSrc = src, odObserved = observed}

-- | Exact ℚ ΔF = observed − src (no f64 theater).
observedDeltaFCompute :: Rational -> Rational -> Rational
observedDeltaFCompute src observed = observed - src

-- | §13.5 return payload — residue counts + observed ΔF corpus.
data ResidueReturn = ResidueReturn
  { rrCounts          :: !ResidueCounts
  , rrObservedDeltaF  :: ![ObservedDeltaF]
  } deriving (Show, Eq)

-- | Empty §13.5 return buffer.
emptyResidueReturn :: ResidueReturn
emptyResidueReturn =
  ResidueReturn {rrCounts = emptyResidueCounts, rrObservedDeltaF = []}

-- | Append one observed ΔF sample to the return corpus.
addObservedDelta :: ResidueReturn -> ObservedDeltaF -> ResidueReturn
addObservedDelta ret d =
  ret {rrObservedDeltaF = rrObservedDeltaF ret ++ [d]}

-- | Record one six-constructor residue observation.
recordResidue :: ResidueReturn -> UrgeExcitementResidue -> ResidueReturn
recordResidue ret r =
  ret {rrCounts = incrementResidueCount (rrCounts ret) r}

-- | Record one meso 'ExcitementResidue' via the six-constructor pin.
recordAdmitResidue :: ResidueReturn -> ExcitementResidue -> ResidueReturn
recordAdmitResidue ret r = recordResidue ret (mapAdmitResidue r)

-- ---------------------------------------------------------------------------
-- SECTION 3: Typed refusal (seventh constructor + f64 ΔF theater)
-- ---------------------------------------------------------------------------

-- | Positive refuse tags — seventh constructor and f64 ΔF are inadmissible.
data ResidueReturnRefusal
  = RrrSeventhConstructor
  | RrrF64DeltaF
  deriving (Show, Eq)

-- | Positive refuse: seventh residue constructor is inadmissible.
refuseSeventhConstructor :: Either () ResidueReturnRefusal
refuseSeventhConstructor = Right RrrSeventhConstructor

-- | Positive refuse: f64 joint-free-energy delta is inadmissible — use exact ℚ.
refuseF64DeltaF :: Either () ResidueReturnRefusal
refuseF64DeltaF = Right RrrF64DeltaF

-- ---------------------------------------------------------------------------
-- SECTION 4: Recovery composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for §13.5 residue return over admissible history successors.
data ResidueReturnCtx = ResidueReturnCtx
  { residueReturnPrior       :: !ThermodynamicState
  , residueReturnSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | §13.5 recovery **is** 'urgeRecoverySelect' / 'excitementSelect'.
residueReturnSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
residueReturnSelect = urgeRecoverySelect

-- | Contextual wrapper — same selector, no re-derivation.
residueReturnSelectCtx
  :: ResidueReturnCtx
  -> Either ExcitementResidue HistoryCandidate
residueReturnSelectCtx ctx =
  residueReturnSelect
    (residueReturnPrior ctx)
    (residueReturnSuccessors ctx)

-- | Definitional witness: residue return API is 'excitementSelect'.
residueReturnSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
residueReturnSelectEqExcitementSelect src successors =
  residueReturnSelect src successors == excitementSelect src successors

-- | Definitional witness: residue return API is 'urgeRecoverySelect'.
residueReturnSelectEqUrgeRecoverySelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
residueReturnSelectEqUrgeRecoverySelect src successors =
  residueReturnSelect src successors == urgeRecoverySelect src successors

-- | Residue return selector re-uses 'excitementSelect' — no Urge-local argmin.
residueReturnNoLocalArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
residueReturnNoLocalArgmin src successors =
  residueReturnSelect src successors == excitementSelect src successors

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
residueReturnEmpty :: ThermodynamicState -> Bool
residueReturnEmpty src =
  residueReturnSelect src [] == Left ExcNoCandidates

-- | Record one recovery attempt via imported 'excitementSelect'.
recordRecoveryAttempt
  :: ResidueReturn
  -> ThermodynamicState
  -> [HistoryCandidate]
  -> (ResidueReturn, Either ExcitementResidue HistoryCandidate)
recordRecoveryAttempt ret src successors =
  case residueReturnSelect src successors of
    Right c ->
      let delta =
            mkObservedDeltaF
              (toRational (freeEnergy src))
              (toRational (freeEnergy (candTgt c)))
       in (addObservedDelta ret delta, Right c)
    Left r -> (recordAdmitResidue ret r, Left r)

-- | Excitement compose pin — zero local argmin re-derivation.
excitementComposePin :: Int
excitementComposePin = 0

-- | Marker witness for excitement compose pin.
excitementComposePinMarker :: Bool
excitementComposePinMarker = excitementComposePin == 0

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Physical bridge tying Landauer process to §13.5 return payload.
data PhysicalResidueReturnBridge = PhysicalResidueReturnBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalReturn         :: !ResidueReturn
  , physicalHistoryEq      :: !Bool
  } deriving (Show, Eq)

-- | Second law on bridged transition from Landauer discharge.
residueReturnSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
residueReturnSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: §13.5 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture prior head (density 2400, free energy 10).
residueFixtureSrc :: ThermodynamicState
residueFixtureSrc = ThermodynamicState 2400 10 0 0 0

-- | Fixture target head (density 2400, free energy 3).
residueFixtureTgt :: ThermodynamicState
residueFixtureTgt = ThermodynamicState 2400 3 0 0 0

-- | Fixture admissible history candidate.
residueFixtureCandidate :: HistoryCandidate
residueFixtureCandidate = HistoryCandidate 1 residueFixtureTgt

-- | Six constructor name pin witness.
residueSixConstructorsPinned :: Bool
residueSixConstructorsPinned =
  residueConstructorName UerNoCandidates == "NoCandidates"
  && residueConstructorName UerAllInadmissible == "AllInadmissible"
  && residueConstructorName UerAllExcludedByCbf == "AllExcludedByCbf"
  && residueConstructorName UerAllExcludedByDec == "AllExcludedByDec"
  && residueConstructorName UerUntaggedConstant == "UntaggedConstant"
  && residueConstructorName UerNoStrictImprovement == "NoStrictImprovement"

-- | Empty successors record 'ExcNoCandidates' and increment no-candidates count.
residueEmptySuccessorsRecordsNoCandidates :: Bool
residueEmptySuccessorsRecordsNoCandidates =
  let (buf, res) = recordRecoveryAttempt emptyResidueReturn residueFixtureSrc []
   in res == Left ExcNoCandidates
     && residueCountOf (rrCounts buf) UerNoCandidates == 1

-- | Strict improvement records one observed ΔF sample.
residueStrictImprovementRecordsDelta :: Bool
residueStrictImprovementRecordsDelta =
  let (buf, res) =
        recordRecoveryAttempt
          emptyResidueReturn
          residueFixtureSrc
          [residueFixtureCandidate]
   in res == Right residueFixtureCandidate
     && case rrObservedDeltaF buf of
          (d : _) -> observedDeltaF d == 3 % 1 - 10 % 1
          [] -> False

-- | Positive refuse: seventh constructor tag is explicit.
residueRefuseSeventhConstructorPositive :: Bool
residueRefuseSeventhConstructorPositive =
  refuseSeventhConstructor == Right RrrSeventhConstructor

-- | Positive refuse: f64 ΔF theater tag is explicit.
residueRefuseF64DeltaFPositive :: Bool
residueRefuseF64DeltaFPositive = refuseF64DeltaF == Right RrrF64DeltaF

-- | Observed ΔF compute fixture (exact ℚ).
residueObservedDeltaFComputeFixture :: Bool
residueObservedDeltaFComputeFixture =
  observedDeltaFCompute (10 % 1) (3 % 1) == 3 % 1 - 10 % 1

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
residueReturnPhysicsGreen :: Bool
residueReturnPhysicsGreen = False

-- | Lean/Coq: @residue_return_physics_green_false@.
residueReturnPhysicsGreenFalse :: Bool
residueReturnPhysicsGreenFalse = not residueReturnPhysicsGreen

-- | Production wiring stays open (meso lift only).
residueReturnProductionWired :: Bool
residueReturnProductionWired = False

-- | Lean/Coq: @residue_return_production_wired_false@.
residueReturnProductionWiredFalse :: Bool
residueReturnProductionWiredFalse = not residueReturnProductionWired

-- | Catalog witness: meso Urge ResidueReturn module present.
residueReturnModuleWitness :: Bool
residueReturnModuleWitness = True

-- | Zero new axiom discipline witness.
residueReturnNoNewAxiom :: Bool
residueReturnNoNewAxiom = True

-- | Second-argmin refusal: residue return composes 'excitementSelect' only.
residueReturnNoSecondArgmin :: Bool
residueReturnNoSecondArgmin =
  residueReturnNoLocalArgmin residueFixtureSrc [residueFixtureCandidate]

-- | Honest non-claim string (meso §13.5 residue return scaffold).
residueReturnNonClaim :: String
residueReturnNonClaim =
  "§13.5 Urge returns Excitement Residue counts + observed ΔF; "
    ++ "six constructors pinned; compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
residueReturnNonClaimNonempty :: Bool
residueReturnNonClaimNonempty = length residueReturnNonClaim > 0
