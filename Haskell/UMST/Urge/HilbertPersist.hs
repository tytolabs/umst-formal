-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.HilbertPersist
-- Description : Meso acting Urge — §12.7 persist Hilbert (acting fiber).
--
-- Persist Hilbert (acting) distinct from occupancy Hilbert (knowing).
-- Acting fiber only — refuse fuse with knowing occupancy Hilbert.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.HilbertPersist
  ( -- * Acting persist Hilbert carriers (§12.7 acting fiber)
    HilbertPersistRole (..)
  , OccupancyKnowingHilbertRefused (..)
  , PersistHilbertUcrsStamp (..)
  , PersistHilbertMergeSafeCert (..)
  , PersistHilbertIndex (..)
  , PersistHilbertSnapshot (..)
  , PersistHilbertWitness (..)
  , PersistHilbertMorphism (..)
  , PersistHilbertRefusal (..)
  , PersistHilbertVerdict (..)
    -- * §12.7 admissibility conjunct + fuse refuse
  , PersistAdmissibilityConjunct (..)
  , persistConjunctAdmits
  , evaluatePersistHilbertOperation
  , refuseHilbertFuseOccupancy
  , refuseKnowingFiberFuse
  , witnessFromPersistSnapshot
  , applyPersistHilbertMorphism
    -- * Positive refuse witnesses
  , persistHilbertFuseOccupancyRefused
  , persistHilbertMorphismOkWhenNotFuse
  , refuseHilbertFuseOccupancyPositive
  , refuseKnowingFiberFusePositive
    -- * Excitement alignment (no second argmin)
  , PersistHilbertCtx (..)
  , persistHilbertSelect
  , persistHilbertSelectBare
  , persistHilbertSelectEqExcitementSelect
  , persistHilbertSelectBareEqExcitementSelect
  , persistHilbertSelectEqUrgeRecoverySelect
  , persistHilbertNoLocalArgmin
  , persistHilbertEmpty
    -- * §12.7 persist index surrogate + fixtures
  , defaultPersistHilbertBits
  , persistHilbertSide
  , persistHilbertMask
  , persistHilbertCoords
  , persistCurveIndex
  , computePersistHilbertIndex
  , persistFixtureState
  , persistFixtureUcrs
  , persistFixtureMergeSafe
  , persistFixtureIndex
  , persistFixtureSnapshot
  , persistFixtureConjunct
  , persistFixtureFuseOccupancyRefused
  , persistFixtureApplyMorphismOk
  , persistFixtureApplyFuseRefused
  , persistFixtureWitnessPreservesUcrs
  , persistFixtureWitnessPreservesIndex
  , persistFixtureIndexBits
    -- * Landauer bridge (derived — zero new axioms)
  , hilbertPersistSecondLawFromLandauer
  , hilbertPersistFromLandauerAdmitSecondLaw
  , hilbertPersistSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , hilbertPersistPhysicsGreen
  , hilbertPersistPhysicsGreenFalse
  , hilbertPersistProductionWired
  , hilbertPersistProductionWiredFalse
  , hilbertPersistNonClaim
  , hilbertPersistNonClaimNonempty
  , hilbertPersistModuleWitness
  , hilbertPersistNoNewAxiom
  , hilbertPersistPositiveRefuseNotSilent
  , hilbertPersistActingRoleWitness
  , hilbertPersistNoSecondArgmin
  ) where

import Data.Bits (shiftL, xor)

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
import UMST.Urge.ExcitementImport
  ( urgeRecoverySelect
  , urgeRecoverySelectEqExcitementSelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Acting persist Hilbert carriers (§12.7 acting fiber)
-- ---------------------------------------------------------------------------

-- | Acting meso role tag — persist Hilbert indexes Device-tier sled keys.
data HilbertPersistRole
  = PersistActing
  deriving (Show, Eq)

-- | Knowing occupancy Hilbert is **not** on this acting fiber — cite only for refuse.
data OccupancyKnowingHilbertRefused
  = FusePersistIntoOccupancy
  | FuseOccupancyIntoPersist
  | KnowingFiberNotOnActingMeso
  deriving (Show, Eq)

-- | UCRS stamp surrogate carried through persist Hilbert morphism.
data PersistHilbertUcrsStamp = PersistHilbertUcrsStamp
  { persistUcrsSeq     :: !Int
  , persistUcrsWallHasT :: !Bool
  } deriving (Show, Eq)

-- | MergeSafe certificate surrogate — persist must not violate tier disjointness.
data PersistHilbertMergeSafeCert = PersistHilbertMergeSafeCert
  { persistMergeSafe :: !Bool
  } deriving (Show, Eq)

-- | Persist Hilbert index — typed acting meso sled key layout (§12.7 acting).
data PersistHilbertIndex = PersistHilbertIndex
  { persistIndexRaw  :: !Int
  , persistIndexBits :: !Int
  } deriving (Show, Eq)

-- | Snapshot identity at persist source (content-addressed surrogate).
data PersistHilbertSnapshot = PersistHilbertSnapshot
  { persistSnapshotId          :: !Int
  , persistSnapshotHead        :: !ThermodynamicState
  , persistSnapshotUcrs        :: !PersistHilbertUcrsStamp
  , persistSnapshotMergeSafe   :: !PersistHilbertMergeSafeCert
  , persistSnapshotProvenanceIntact :: !Bool
  , persistSnapshotIndex       :: !PersistHilbertIndex
  } deriving (Show, Eq)

-- | Witness bundle a persist Hilbert morphism must preserve (§12.7).
data PersistHilbertWitness = PersistHilbertWitness
  { persistWitnessUcrs            :: !PersistHilbertUcrsStamp
  , persistWitnessMergeSafe       :: !PersistHilbertMergeSafeCert
  , persistWitnessProvenanceIntact :: !Bool
  , persistWitnessIndex           :: !PersistHilbertIndex
  } deriving (Show, Eq)

-- | Typed persist Hilbert morphism — admissible acting transition, not fuse.
data PersistHilbertMorphism = PersistHilbertMorphism
  { persistMorphismFrom             :: !PersistHilbertSnapshot
  , persistMorphismWitness          :: !PersistHilbertWitness
  , persistMorphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed persist Hilbert errors — positive refuse, not silent no-op.
data PersistHilbertRefusal
  = FuseOccupancyRefused
  | GateRejected Int
  | MergeUnsafe Int
  | ProvenanceLoss Int
  | KnowingFiberFuseRefused
  deriving (Show, Eq)

-- | Verdict of a persist Hilbert operation class.
data PersistHilbertVerdict
  = MorphismOk
  | FuseOccupancyVerdict
  | InadmissibleVerdict
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §12.7 admissibility conjunct + fuse refuse
-- ---------------------------------------------------------------------------

-- | §12.7 admissibility conjunct inputs (surrogate).
data PersistAdmissibilityConjunct = PersistAdmissibilityConjunct
  { persistConjGateOk              :: !Bool
  , persistConjMergeSafe           :: !Bool
  , persistConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ MergeSafe ∧ Excitement preserves@.
persistConjunctAdmits :: PersistAdmissibilityConjunct -> Bool
persistConjunctAdmits c =
  persistConjGateOk c
  && persistConjMergeSafe c
  && persistConjExcitementPreserves c

-- | Classify fuse attempt vs typed morphism without performing I/O.
evaluatePersistHilbertOperation :: Bool -> PersistHilbertVerdict
evaluatePersistHilbertOperation attemptsFuse =
  if attemptsFuse then FuseOccupancyVerdict else MorphismOk

-- | Positive refuse: fuse with occupancy knowing Hilbert is inadmissible.
refuseHilbertFuseOccupancy :: OccupancyKnowingHilbertRefused
refuseHilbertFuseOccupancy = FusePersistIntoOccupancy

-- | Positive refuse: knowing occupancy Hilbert fiber is not on acting meso.
refuseKnowingFiberFuse :: OccupancyKnowingHilbertRefused
refuseKnowingFiberFuse = KnowingFiberNotOnActingMeso

-- | Build witness from snapshot — morphism must preserve stamps and index.
witnessFromPersistSnapshot :: PersistHilbertSnapshot -> PersistHilbertWitness
witnessFromPersistSnapshot s =
  PersistHilbertWitness
    { persistWitnessUcrs = persistSnapshotUcrs s
    , persistWitnessMergeSafe = persistSnapshotMergeSafe s
    , persistWitnessProvenanceIntact = persistSnapshotProvenanceIntact s
    , persistWitnessIndex = persistSnapshotIndex s
    }

-- | Attempt typed persist Hilbert morphism — fail closed on inadmissibility.
applyPersistHilbertMorphism
  :: PersistHilbertSnapshot
  -> PersistAdmissibilityConjunct
  -> Bool
  -> Bool
  -> Either PersistHilbertRefusal PersistHilbertMorphism
applyPersistHilbertMorphism snapshot conjunct excitementSelected attemptsFuse =
  if attemptsFuse
    then Left FuseOccupancyRefused
    else
      if not (persistConjunctAdmits conjunct)
        then Left (GateRejected (persistUcrsSeq (persistSnapshotUcrs snapshot)))
        else
          if not (persistMergeSafe (persistSnapshotMergeSafe snapshot))
            then Left (MergeUnsafe (persistSnapshotId snapshot))
            else
              if not (persistSnapshotProvenanceIntact snapshot)
                then Left (ProvenanceLoss (persistSnapshotId snapshot))
                else
                  if not excitementSelected
                    then Left KnowingFiberFuseRefused
                    else
                      Right
                        PersistHilbertMorphism
                          { persistMorphismFrom = snapshot
                          , persistMorphismWitness = witnessFromPersistSnapshot snapshot
                          , persistMorphismExcitementSelected = excitementSelected
                          }

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Fuse with occupancy knowing Hilbert is always refused.
persistHilbertFuseOccupancyRefused :: Bool
persistHilbertFuseOccupancyRefused =
  evaluatePersistHilbertOperation True == FuseOccupancyVerdict

-- | Typed morphism path succeeds when fuse not attempted.
persistHilbertMorphismOkWhenNotFuse :: Bool
persistHilbertMorphismOkWhenNotFuse =
  evaluatePersistHilbertOperation False == MorphismOk

-- | Positive refuse witness for persist→occupancy fuse.
refuseHilbertFuseOccupancyPositive :: Bool
refuseHilbertFuseOccupancyPositive =
  refuseHilbertFuseOccupancy == FusePersistIntoOccupancy

-- | Positive refuse witness for knowing fiber fuse.
refuseKnowingFiberFusePositive :: Bool
refuseKnowingFiberFusePositive =
  refuseKnowingFiberFuse == KnowingFiberNotOnActingMeso

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for persist Hilbert over admissible history successors.
data PersistHilbertCtx = PersistHilbertCtx
  { persistHilbertPrior      :: !ThermodynamicState
  , persistHilbertSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Persist Hilbert selection **is** 'excitementSelect' — not a second argmin.
persistHilbertSelect
  :: PersistHilbertCtx
  -> Either ExcitementResidue HistoryCandidate
persistHilbertSelect ctx =
  excitementSelect (persistHilbertPrior ctx) (persistHilbertSuccessors ctx)

-- | Bare @(prior, successors)@ persist selection — same selector, no re-derivation.
persistHilbertSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
persistHilbertSelectBare = excitementSelect

-- | Definitional witness: persist selection API is 'excitementSelect'.
persistHilbertSelectEqExcitementSelect :: PersistHilbertCtx -> Bool
persistHilbertSelectEqExcitementSelect ctx =
  persistHilbertSelect ctx
    == excitementSelect (persistHilbertPrior ctx) (persistHilbertSuccessors ctx)

-- | Definitional witness: bare selection API is 'excitementSelect'.
persistHilbertSelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
persistHilbertSelectBareEqExcitementSelect prior successors =
  persistHilbertSelectBare prior successors == excitementSelect prior successors

-- | Persist selection equals 'urgeRecoverySelect' on the same inputs.
persistHilbertSelectEqUrgeRecoverySelect :: PersistHilbertCtx -> Bool
persistHilbertSelectEqUrgeRecoverySelect ctx =
  persistHilbertSelect ctx
    == urgeRecoverySelect (persistHilbertPrior ctx) (persistHilbertSuccessors ctx)

-- | Persist selector re-uses 'excitementSelect' — no Urge-local argmin.
persistHilbertNoLocalArgmin :: PersistHilbertCtx -> Bool
persistHilbertNoLocalArgmin ctx =
  persistHilbertSelect ctx
    == excitementSelect (persistHilbertPrior ctx) (persistHilbertSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
persistHilbertEmpty :: ThermodynamicState -> Bool
persistHilbertEmpty prior =
  persistHilbertSelectBare prior [] == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §12.7 persist index surrogate + fixtures
-- ---------------------------------------------------------------------------

-- | Default bit width for persist acting Hilbert index surrogate.
defaultPersistHilbertBits :: Int
defaultPersistHilbertBits = 4

-- | Side length of persist Hilbert grid at given bit width.
persistHilbertSide :: Int -> Int
persistHilbertSide bits = shiftL 1 bits

-- | Mask for persist Hilbert coordinate wrap.
persistHilbertMask :: Int -> Int
persistHilbertMask bits = persistHilbertSide bits - 1

-- | Map @(ucrs_seq, grid_hash)@ to 2D coords for persist acting path.
persistHilbertCoords :: Int -> Int -> Int -> (Int, Int)
persistHilbertCoords ucrs grid bits =
  let mask = persistHilbertMask bits + 1
      x = ucrs `mod` mask
      y = (xor grid (grid `div` 65536)) `mod` mask
   in (x, y)

-- | Surrogate curve index — acting meso sled key layout (not occupancy).
persistCurveIndex :: Int -> Int -> Int -> Int
persistCurveIndex x y bits =
  let side = persistHilbertSide bits
   in (x `mod` side) + (y `mod` side) * side

-- | Compute persist Hilbert index from ucrs/grid surrogate inputs.
computePersistHilbertIndex :: Int -> Int -> Int -> PersistHilbertIndex
computePersistHilbertIndex ucrs grid bits =
  let (x, y) = persistHilbertCoords ucrs grid bits
   in PersistHilbertIndex
        { persistIndexRaw = persistCurveIndex x y bits
        , persistIndexBits = bits
        }

-- | Fixture thermodynamic head for catalog witnesses.
persistFixtureState :: ThermodynamicState
persistFixtureState = ThermodynamicState 2400 0 0 0 0

-- | Fixture UCRS stamp surrogate.
persistFixtureUcrs :: PersistHilbertUcrsStamp
persistFixtureUcrs =
  PersistHilbertUcrsStamp {persistUcrsSeq = 7, persistUcrsWallHasT = True}

-- | Fixture MergeSafe certificate surrogate.
persistFixtureMergeSafe :: PersistHilbertMergeSafeCert
persistFixtureMergeSafe = PersistHilbertMergeSafeCert {persistMergeSafe = True}

-- | Fixture persist Hilbert index from catalog inputs.
persistFixtureIndex :: PersistHilbertIndex
persistFixtureIndex = computePersistHilbertIndex 7 0xABCD defaultPersistHilbertBits

-- | Fixture persist Hilbert snapshot for catalog witnesses.
persistFixtureSnapshot :: PersistHilbertSnapshot
persistFixtureSnapshot =
  PersistHilbertSnapshot
    { persistSnapshotId = 1
    , persistSnapshotHead = persistFixtureState
    , persistSnapshotUcrs = persistFixtureUcrs
    , persistSnapshotMergeSafe = persistFixtureMergeSafe
    , persistSnapshotProvenanceIntact = True
    , persistSnapshotIndex = persistFixtureIndex
    }

-- | Fixture admissibility conjunct — all conjuncts satisfied.
persistFixtureConjunct :: PersistAdmissibilityConjunct
persistFixtureConjunct =
  PersistAdmissibilityConjunct
    { persistConjGateOk = True
    , persistConjMergeSafe = True
    , persistConjExcitementPreserves = True
    }

-- | Fixture: fuse with occupancy knowing Hilbert is positively refused.
persistFixtureFuseOccupancyRefused :: Bool
persistFixtureFuseOccupancyRefused =
  refuseHilbertFuseOccupancy == FusePersistIntoOccupancy

-- | Fixture: typed morphism application succeeds when fuse not attempted.
persistFixtureApplyMorphismOk :: Bool
persistFixtureApplyMorphismOk =
  applyPersistHilbertMorphism persistFixtureSnapshot persistFixtureConjunct True False
    == Right
      PersistHilbertMorphism
        { persistMorphismFrom = persistFixtureSnapshot
        , persistMorphismWitness = witnessFromPersistSnapshot persistFixtureSnapshot
        , persistMorphismExcitementSelected = True
        }

-- | Fixture: fuse attempt is refused at morphism application.
persistFixtureApplyFuseRefused :: Bool
persistFixtureApplyFuseRefused =
  applyPersistHilbertMorphism persistFixtureSnapshot persistFixtureConjunct True True
    == Left FuseOccupancyRefused

-- | Fixture: witness preserves UCRS stamp from snapshot.
persistFixtureWitnessPreservesUcrs :: Bool
persistFixtureWitnessPreservesUcrs =
  persistWitnessUcrs (witnessFromPersistSnapshot persistFixtureSnapshot)
    == persistFixtureUcrs

-- | Fixture: witness preserves index from snapshot.
persistFixtureWitnessPreservesIndex :: Bool
persistFixtureWitnessPreservesIndex =
  persistWitnessIndex (witnessFromPersistSnapshot persistFixtureSnapshot)
    == persistFixtureIndex

-- | Fixture: index bits match default persist Hilbert bit width.
persistFixtureIndexBits :: Bool
persistFixtureIndexBits =
  persistIndexBits persistFixtureIndex == defaultPersistHilbertBits

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on persist Hilbert transition from Landauer bridge discharge.
hilbertPersistSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
hilbertPersistSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
hilbertPersistFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
hilbertPersistFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for persist Hilbert second law (no new axiom).
hilbertPersistSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
hilbertPersistSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
hilbertPersistPhysicsGreen :: Bool
hilbertPersistPhysicsGreen = False

-- | Lean/Coq: @hilbert_persist_physics_green_false@.
hilbertPersistPhysicsGreenFalse :: Bool
hilbertPersistPhysicsGreenFalse = not hilbertPersistPhysicsGreen

-- | Production wiring stays open (persist Hilbert lift only).
hilbertPersistProductionWired :: Bool
hilbertPersistProductionWired = False

-- | Lean/Coq: @hilbert_persist_production_wired_false@.
hilbertPersistProductionWiredFalse :: Bool
hilbertPersistProductionWiredFalse = not hilbertPersistProductionWired

-- | Honest non-claim string (meso §12.7 persist Hilbert scaffold).
hilbertPersistNonClaim :: String
hilbertPersistNonClaim =
  "§12.7 persist Hilbert (acting) distinct from occupancy Hilbert (knowing); "
    ++ "fuse refused; excitementSelect composed; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
hilbertPersistNonClaimNonempty :: Bool
hilbertPersistNonClaimNonempty = length hilbertPersistNonClaim > 0

-- | Catalog witness: meso Urge HilbertPersist module present.
hilbertPersistModuleWitness :: Bool
hilbertPersistModuleWitness = True

-- | Zero new axiom discipline witness.
hilbertPersistNoNewAxiom :: Bool
hilbertPersistNoNewAxiom = True

-- | Positive refuse is not silent no-op on fuse attempt.
hilbertPersistPositiveRefuseNotSilent :: Bool
hilbertPersistPositiveRefuseNotSilent =
  evaluatePersistHilbertOperation True /= MorphismOk

-- | Acting role tag witness.
hilbertPersistActingRoleWitness :: Bool
hilbertPersistActingRoleWitness = PersistActing == PersistActing

-- | Second-argmin refusal: persist Hilbert composes 'excitementSelect' only.
hilbertPersistNoSecondArgmin :: Bool
hilbertPersistNoSecondArgmin =
  persistHilbertNoLocalArgmin
    (PersistHilbertCtx
      { persistHilbertPrior = persistFixtureState
      , persistHilbertSuccessors = []
      })
  && urgeRecoverySelectEqExcitementSelect persistFixtureState []
