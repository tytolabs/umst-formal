-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ThreeDagSeparate
-- Description : Meso acting Urge — §16.11 / §22.2 three DAGs unfused.
--
-- Three unfused DAG substrates: (a) git bytes, (b) Kleisli history,
-- (c) UCRS causal. Agents walk (b) ordered by (c). Typed fusion refuses —
-- not only !physics_green.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ThreeDagSeparate
  ( -- * Three unfused DAG substrates + node carriers
    ThreeDagSubstrate (..)
  , GitCommitNode (..)
  , KleisliHistoryNode (..)
  , UcrsCausalNode (..)
  , ThreeDagCoordinates (..)
  , ThreeDagUcrsStamp (..)
  , ThreeDagWitness (..)
  , ThreeDagMorphism (..)
    -- * Fusion refusal + positive refuse (not silent accept)
  , ThreeDagFusionRefusal (..)
  , ThreeDagWalkerVerdict (..)
  , ThreeDagAdmissibilityConjunct (..)
  , threeDagConjunctAdmits
  , refusesGitKleisliFusion
  , refusesUcrsGitFusion
  , refuseSecondArgminSelector
  , evaluateThreeDagWalk
  , witnessFromCoords
  , applyThreeDagMorphism
    -- * Positive refuse witnesses
  , refuseSecondArgminSelectorPositive
  , refusesGitKleisliFusionDetectsEqual
  , refusesGitKleisliFusionSeparate
  , threeDagFusionRefuseNotSilent
    -- * Excitement alignment (no second argmin)
  , ThreeDagExcitementComposePin (..)
  , ThreeDagCtx (..)
  , threeDagExcitementSelect
  , threeDagSelect
  , threeDagSelectEqExcitementSelect
  , threeDagSelectEqUrgeRecoverySelect
  , threeDagNoLocalArgmin
  , threeDagExcitementSelectEqExcitementSelect
  , threeDagExcitementSelectRefusesSecondArgmin
  , threeDagSelectEmpty
    -- * §16.11 fixtures + witness theorems
  , threeDagFixtureState
  , threeDagFixtureUcrs
  , threeDagFixtureConjunct
  , threeDagFixtureCoords
  , threeDagFixtureKleisli
  , threeDagFixtureUcrsNode
  , threeDagFixtureWalkAdmitted
  , threeDagFixtureFusedCoords
  , threeDagFixtureGitKleisliFusionRefused
  , threeDagFixtureWallClockOrderRefused
  , threeDagFixtureApplyMorphismOk
  , threeDagFixtureWitnessPreservesUcrs
  , threeDagFixturePhysicsGreenInventRefused
    -- * Landauer bridge (derived — zero new axioms)
  , ThreeDagTransition (..)
  , threeDagSecondLaw
  , admissibleThreeDagWalk
  , PhysicalThreeDagBridge (..)
  , threeDagSecondLawFromPhysical
  , admissibleThreeDagWalkFromPhysical
  , threeDagSecondLawFromLandauer
  , threeDagFromLandauerAdmitSecondLaw
  , threeDagSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , threeDagSeparatePhysicsGreen
  , threeDagSeparatePhysicsGreenFalse
  , threeDagSeparateProductionWired
  , threeDagSeparateProductionWiredFalse
  , threeDagSeparateNonClaim
  , threeDagSeparateNonClaimNonempty
  , threeDagSeparateModuleWitness
  , threeDagSeparateNoNewAxiom
  , threeDagSeparateNoSecondArgmin
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
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: Three unfused DAG substrates + node carriers
-- ---------------------------------------------------------------------------

-- | Three unfused DAG substrates from §16.11 / §22.2.
data ThreeDagSubstrate
  = GitBytesSubstrate
  | KleisliHistorySubstrate
  | UcrsCausalSubstrate
  deriving (Show, Eq)

-- | Git commit node on byte substrate (a).
data GitCommitNode = GitCommitNode
  { gitCommitHash :: !Int
  , gitParentHash :: !(Maybe Int)
  } deriving (Show, Eq)

-- | Kleisli admitted-history node on coordination DAG (b).
data KleisliHistoryNode = KleisliHistoryNode
  { kleisliArrowId :: !Int
  , kleisliGateMergeExcitementAdmitted :: !Bool
  } deriving (Show, Eq)

-- | UCRS causal node on seq-ordered DAG (c).
data UcrsCausalNode = UcrsCausalNode
  { ucrsSeq :: !Int
  , ucrsWallStampAudit :: !(Maybe Int)
  , ucrsOrderByWallClock :: !Bool
  } deriving (Show, Eq)

-- | Per-DAG coordinates — unfused; never a single fused id.
data ThreeDagCoordinates = ThreeDagCoordinates
  { tdcGitCommit :: !Int
  , tdcKleisliArrow :: !Int
  , tdcUcrsSeq :: !Int
  } deriving (Show, Eq)

-- | UCRS stamp surrogate carried through three-DAG walker.
data ThreeDagUcrsStamp = ThreeDagUcrsStamp
  { threeDagUcrsSeq :: !Int
  , threeDagUcrsWallHasT :: !Bool
  } deriving (Show, Eq)

-- | Witness bundle three-DAG walk must preserve.
data ThreeDagWitness = ThreeDagWitness
  { witnessUcrs :: !ThreeDagUcrsStamp
  , witnessKleisliAdmitted :: !Bool
  } deriving (Show, Eq)

-- | Typed three-DAG morphism — admissible Kleisli walk, not fused substrates.
data ThreeDagMorphism = ThreeDagMorphism
  { threeDagCoords :: !ThreeDagCoordinates
  , threeDagWitness :: !ThreeDagWitness
  , threeDagExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: Fusion refusal + positive refuse (not silent accept)
-- ---------------------------------------------------------------------------

-- | Typed fusion / discipline refusal — positive properties.
data ThreeDagFusionRefusal
  = GitBytesAsKleisliCoord
  | UcrsSeqFusedWithGitHash
  | WallClockAsUcrsSeq
  | KleisliNotAdmitted
  | SecondArgminRefused
  | PhysicsGreenInvent
  deriving (Show, Eq)

-- | Walker verdict on three unfused DAGs.
data ThreeDagWalkerVerdict
  = ThreeDagAdmitted
  | ThreeDagRefused ThreeDagFusionRefusal
  deriving (Show, Eq)

-- | §16.11 admissibility conjunct inputs (surrogate).
data ThreeDagAdmissibilityConjunct = ThreeDagAdmissibilityConjunct
  { threeDagGateOk :: !Bool
  , threeDagKleisliAdmitted :: !Bool
  , threeDagExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate admit(h) ⟺ gate ∧ Kleisli admitted ∧ Excitement preserves.
threeDagConjunctAdmits :: ThreeDagAdmissibilityConjunct -> Bool
threeDagConjunctAdmits c =
  threeDagGateOk c
  && threeDagKleisliAdmitted c
  && threeDagExcitementPreserves c

-- | Detect git-byte ↔ Kleisli coordination fusion.
refusesGitKleisliFusion :: ThreeDagCoordinates -> Bool
refusesGitKleisliFusion coords =
  tdcGitCommit coords == tdcKleisliArrow coords

-- | Detect UCRS causal ↔ git-byte fusion.
refusesUcrsGitFusion :: ThreeDagCoordinates -> Bool
refusesUcrsGitFusion coords =
  tdcUcrsSeq coords == tdcGitCommit coords

-- | Positive refuse: second Excitement selector — compose 'excitementSelect'.
refuseSecondArgminSelector :: ThreeDagFusionRefusal
refuseSecondArgminSelector = SecondArgminRefused

-- | Evaluate Kleisli walk ordered by UCRS causal seq — refuse substrate fusion.
evaluateThreeDagWalk
  :: ThreeDagCoordinates
  -> KleisliHistoryNode
  -> UcrsCausalNode
  -> Bool
  -> ThreeDagWalkerVerdict
evaluateThreeDagWalk coords kleisli ucrs claimPhysicsGreen =
  if claimPhysicsGreen
    then ThreeDagRefused PhysicsGreenInvent
    else if refusesGitKleisliFusion coords
      then ThreeDagRefused GitBytesAsKleisliCoord
      else if refusesUcrsGitFusion coords
        then ThreeDagRefused UcrsSeqFusedWithGitHash
        else if ucrsOrderByWallClock ucrs
          then ThreeDagRefused WallClockAsUcrsSeq
          else if tdcUcrsSeq coords /= ucrsSeq ucrs
            then ThreeDagRefused WallClockAsUcrsSeq
            else if not (kleisliGateMergeExcitementAdmitted kleisli)
              then ThreeDagRefused KleisliNotAdmitted
              else if kleisliArrowId kleisli /= tdcKleisliArrow coords
                then ThreeDagRefused KleisliNotAdmitted
                else ThreeDagAdmitted

-- | Build witness from coordinates + Kleisli node.
witnessFromCoords
  :: ThreeDagCoordinates
  -> KleisliHistoryNode
  -> ThreeDagUcrsStamp
  -> ThreeDagWitness
witnessFromCoords _coords kleisli stamp =
  ThreeDagWitness
    { witnessUcrs = stamp
    , witnessKleisliAdmitted = kleisliGateMergeExcitementAdmitted kleisli
    }

-- | Attempt typed three-DAG morphism — fail closed on inadmissibility.
applyThreeDagMorphism
  :: ThreeDagCoordinates
  -> KleisliHistoryNode
  -> UcrsCausalNode
  -> ThreeDagAdmissibilityConjunct
  -> ThreeDagUcrsStamp
  -> Bool
  -> Either ThreeDagFusionRefusal ThreeDagMorphism
applyThreeDagMorphism coords kleisli ucrs conjunct stamp excitementSelected =
  if not (threeDagConjunctAdmits conjunct)
    then Left KleisliNotAdmitted
    else if not excitementSelected
      then Left SecondArgminRefused
      else case evaluateThreeDagWalk coords kleisli ucrs False of
        ThreeDagAdmitted ->
          Right
            ThreeDagMorphism
              { threeDagCoords = coords
              , threeDagWitness = witnessFromCoords coords kleisli stamp
              , threeDagExcitementSelected = excitementSelected
              }
        ThreeDagRefused r -> Left r

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Reflexivity witness for 'refuseSecondArgminSelector'.
refuseSecondArgminSelectorPositive :: Bool
refuseSecondArgminSelectorPositive =
  refuseSecondArgminSelector == SecondArgminRefused

-- | Equal git/Kleisli coords detect fusion.
refusesGitKleisliFusionDetectsEqual :: Int -> Bool
refusesGitKleisliFusionDetectsEqual n =
  refusesGitKleisliFusion
    ThreeDagCoordinates {tdcGitCommit = n, tdcKleisliArrow = n, tdcUcrsSeq = 0}

-- | Separate git/Kleisli coords do not fuse.
refusesGitKleisliFusionSeparate :: Int -> Int -> Bool
refusesGitKleisliFusionSeparate g k =
  g /= k
  && not
    ( refusesGitKleisliFusion
        ThreeDagCoordinates {tdcGitCommit = g, tdcKleisliArrow = k, tdcUcrsSeq = 0}
    )

-- | Fusion refusal is not silent accept on fused fixture.
threeDagFusionRefuseNotSilent :: Bool
threeDagFusionRefuseNotSilent =
  evaluateThreeDagWalk
    threeDagFixtureFusedCoords
    KleisliHistoryNode {kleisliArrowId = 66, kleisliGateMergeExcitementAdmitted = True}
    UcrsCausalNode
      { ucrsSeq = 3
      , ucrsWallStampAudit = Nothing
      , ucrsOrderByWallClock = False
      }
    False
    /= ThreeDagAdmitted

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data ThreeDagExcitementComposePin
  = ImportSelectExcitement
  | SecondArgminRefusedPin
  deriving (Show, Eq)

-- | Context for three-DAG selection over admissible history successors.
data ThreeDagCtx = ThreeDagCtx
  { threeDagPrior :: !ThermodynamicState
  , threeDagSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Compose path composes 'excitementSelect' — not a second argmin.
threeDagExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> ThreeDagExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
threeDagExcitementSelect src cands pin =
  case pin of
    ImportSelectExcitement -> excitementSelect src cands
    SecondArgminRefusedPin -> Left ExcAllInadmissible

-- | Three-DAG Kleisli walk **is** 'urgeRecoverySelect' / 'excitementSelect'.
threeDagSelect
  :: ThreeDagCtx
  -> Either ExcitementResidue HistoryCandidate
threeDagSelect ctx =
  urgeRecoverySelect (threeDagPrior ctx) (threeDagSuccessors ctx)

-- | Definitional witness: three-DAG selection API is 'excitementSelect'.
threeDagSelectEqExcitementSelect :: ThreeDagCtx -> Bool
threeDagSelectEqExcitementSelect ctx =
  threeDagSelect ctx
    == excitementSelect (threeDagPrior ctx) (threeDagSuccessors ctx)

-- | Three-DAG selection equals 'urgeRecoverySelect'.
threeDagSelectEqUrgeRecoverySelect :: ThreeDagCtx -> Bool
threeDagSelectEqUrgeRecoverySelect ctx =
  threeDagSelect ctx
    == urgeRecoverySelect (threeDagPrior ctx) (threeDagSuccessors ctx)

-- | Three-DAG selector re-uses 'excitementSelect' — no Urge-local argmin.
threeDagNoLocalArgmin :: ThreeDagCtx -> Bool
threeDagNoLocalArgmin ctx =
  threeDagSelect ctx
    == excitementSelect (threeDagPrior ctx) (threeDagSuccessors ctx)

-- | Definitional witness: excitement compose pin imports 'excitementSelect'.
threeDagExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
threeDagExcitementSelectEqExcitementSelect src cands =
  threeDagExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses via 'ExcAllInadmissible'.
threeDagExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
threeDagExcitementSelectRefusesSecondArgmin src cands =
  threeDagExcitementSelect src cands SecondArgminRefusedPin
    == Left ExcAllInadmissible

-- | Empty successors → 'ExcNoCandidates' via imported selector.
threeDagSelectEmpty :: ThermodynamicState -> Bool
threeDagSelectEmpty src =
  threeDagSelect (ThreeDagCtx {threeDagPrior = src, threeDagSuccessors = []})
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §16.11 fixtures + witness theorems
-- ---------------------------------------------------------------------------

threeDagFixtureState :: ThermodynamicState
threeDagFixtureState = ThermodynamicState 2400 0 0 0 0

threeDagFixtureUcrs :: ThreeDagUcrsStamp
threeDagFixtureUcrs =
  ThreeDagUcrsStamp {threeDagUcrsSeq = 7, threeDagUcrsWallHasT = True}

threeDagFixtureConjunct :: ThreeDagAdmissibilityConjunct
threeDagFixtureConjunct =
  ThreeDagAdmissibilityConjunct
    { threeDagGateOk = True
    , threeDagKleisliAdmitted = True
    , threeDagExcitementPreserves = True
    }

threeDagFixtureCoords :: ThreeDagCoordinates
threeDagFixtureCoords =
  ThreeDagCoordinates {tdcGitCommit = 11, tdcKleisliArrow = 22, tdcUcrsSeq = 7}

threeDagFixtureKleisli :: KleisliHistoryNode
threeDagFixtureKleisli =
  KleisliHistoryNode {kleisliArrowId = 22, kleisliGateMergeExcitementAdmitted = True}

threeDagFixtureUcrsNode :: UcrsCausalNode
threeDagFixtureUcrsNode =
  UcrsCausalNode
    { ucrsSeq = 7
    , ucrsWallStampAudit = Just 42
    , ucrsOrderByWallClock = False
    }

threeDagFixtureWalkAdmitted :: Bool
threeDagFixtureWalkAdmitted =
  evaluateThreeDagWalk
    threeDagFixtureCoords
    threeDagFixtureKleisli
    threeDagFixtureUcrsNode
    False
    == ThreeDagAdmitted

threeDagFixtureFusedCoords :: ThreeDagCoordinates
threeDagFixtureFusedCoords =
  ThreeDagCoordinates {tdcGitCommit = 66, tdcKleisliArrow = 66, tdcUcrsSeq = 3}

threeDagFixtureGitKleisliFusionRefused :: Bool
threeDagFixtureGitKleisliFusionRefused =
  evaluateThreeDagWalk
    threeDagFixtureFusedCoords
    KleisliHistoryNode {kleisliArrowId = 66, kleisliGateMergeExcitementAdmitted = True}
    UcrsCausalNode
      { ucrsSeq = 3
      , ucrsWallStampAudit = Nothing
      , ucrsOrderByWallClock = False
      }
    False
    == ThreeDagRefused GitBytesAsKleisliCoord

threeDagFixtureWallClockOrderRefused :: Bool
threeDagFixtureWallClockOrderRefused =
  evaluateThreeDagWalk
    ThreeDagCoordinates {tdcGitCommit = 33, tdcKleisliArrow = 44, tdcUcrsSeq = 9}
    KleisliHistoryNode {kleisliArrowId = 44, kleisliGateMergeExcitementAdmitted = True}
    UcrsCausalNode
      { ucrsSeq = 9
      , ucrsWallStampAudit = Just 42
      , ucrsOrderByWallClock = True
      }
    False
    == ThreeDagRefused WallClockAsUcrsSeq

threeDagFixtureApplyMorphismOk :: Bool
threeDagFixtureApplyMorphismOk =
  applyThreeDagMorphism
    threeDagFixtureCoords
    threeDagFixtureKleisli
    threeDagFixtureUcrsNode
    threeDagFixtureConjunct
    threeDagFixtureUcrs
    True
    == Right
      ThreeDagMorphism
        { threeDagCoords = threeDagFixtureCoords
        , threeDagWitness =
            witnessFromCoords
              threeDagFixtureCoords
              threeDagFixtureKleisli
              threeDagFixtureUcrs
        , threeDagExcitementSelected = True
        }

threeDagFixtureWitnessPreservesUcrs :: Bool
threeDagFixtureWitnessPreservesUcrs =
  witnessUcrs
    ( witnessFromCoords
        threeDagFixtureCoords
        threeDagFixtureKleisli
        threeDagFixtureUcrs
    )
    == threeDagFixtureUcrs

threeDagFixturePhysicsGreenInventRefused :: Bool
threeDagFixturePhysicsGreenInventRefused =
  evaluateThreeDagWalk
    threeDagFixtureCoords
    threeDagFixtureKleisli
    threeDagFixtureUcrsNode
    True
    == ThreeDagRefused PhysicsGreenInvent

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Three-DAG transition with thermodynamic accounting.
data ThreeDagTransition = ThreeDagTransition
  { tdtCoords :: !ThreeDagCoordinates
  , tdtKleisli :: !KleisliHistoryNode
  , tdtUcrs :: !UcrsCausalNode
  , tdtBath :: !HeatBath
  , tdtDissipatedWork :: !Double
  , tdtEntropyDrop :: !Double
  , tdtConjunct :: !ThreeDagAdmissibilityConjunct
  , tdtExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Second-law accounting on three-DAG transition (Bool witness — not a new axiom).
threeDagSecondLaw :: ThreeDagTransition -> Bool
threeDagSecondLaw t =
  tdtEntropyDrop t <= tdtDissipatedWork t / bathTemp (tdtBath t)

-- | Admissible three-DAG walk: conjunct + walk admitted + excitement selected.
admissibleThreeDagWalk :: ThreeDagTransition -> Bool
admissibleThreeDagWalk t =
  threeDagConjunctAdmits (tdtConjunct t)
  && evaluateThreeDagWalk (tdtCoords t) (tdtKleisli t) (tdtUcrs t) False
    == ThreeDagAdmitted
  && tdtExcitementSelected t

-- | Physical bridge tying three-DAG transition to Landauer discharge.
data PhysicalThreeDagBridge = PhysicalThreeDagBridge
  { pdbTransition :: !ThreeDagTransition
  , pdbAdmissible :: !Bool
  } deriving (Show, Eq)

-- | Second law on bridged transition when physical hypothesis holds.
threeDagSecondLawFromPhysical :: PhysicalThreeDagBridge -> Bool -> Bool
threeDagSecondLawFromPhysical b hSL =
  hSL && pdbAdmissible b && threeDagSecondLaw (pdbTransition b)

-- | Admissible walk from physical bridge (no new axiom).
admissibleThreeDagWalkFromPhysical :: PhysicalThreeDagBridge -> Bool -> Bool
admissibleThreeDagWalkFromPhysical b _hSL =
  pdbAdmissible b && admissibleThreeDagWalk (pdbTransition b)

-- | Second law on Landauer bridge discharge (cited @physicalSecondLaw@).
threeDagSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
threeDagSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
threeDagFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
threeDagFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for three-DAG second law (no new axiom).
threeDagSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
threeDagSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
threeDagSeparatePhysicsGreen :: Bool
threeDagSeparatePhysicsGreen = False

-- | Lean/Coq: @three_dag_separate_physics_green_false@.
threeDagSeparatePhysicsGreenFalse :: Bool
threeDagSeparatePhysicsGreenFalse = not threeDagSeparatePhysicsGreen

-- | Production wiring stays open (three-DAG lift only).
threeDagSeparateProductionWired :: Bool
threeDagSeparateProductionWired = False

-- | Lean/Coq: @three_dag_separate_production_wired_false@.
threeDagSeparateProductionWiredFalse :: Bool
threeDagSeparateProductionWiredFalse = not threeDagSeparateProductionWired

-- | Honest non-claim string (meso §16.11 / §22.2 scaffold).
threeDagSeparateNonClaim :: String
threeDagSeparateNonClaim =
  "§16.11/§22.2 three DAGs unfused: git bytes, Kleisli history, UCRS causal; "
    ++ "compose excitementSelect; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
threeDagSeparateNonClaimNonempty :: Bool
threeDagSeparateNonClaimNonempty = length threeDagSeparateNonClaim > 0

-- | Catalog witness: meso Urge ThreeDagSeparate module present.
threeDagSeparateModuleWitness :: Bool
threeDagSeparateModuleWitness = True

-- | Zero new axiom discipline witness.
threeDagSeparateNoNewAxiom :: Bool
threeDagSeparateNoNewAxiom = True

-- | Second-argmin refusal: three-DAG composes 'excitementSelect' only.
threeDagSeparateNoSecondArgmin :: Bool
threeDagSeparateNoSecondArgmin =
  threeDagNoLocalArgmin
    ( ThreeDagCtx
        { threeDagPrior = threeDagFixtureState
        , threeDagSuccessors = []
        }
    )
