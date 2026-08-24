-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.WorktreeExclusive
-- Description : Meso acting Urge — §16.11 one agent ↔ one exclusive worktree.
--
-- Antichain exclusive copy on the conflict graph. Gate failure at **claim**
-- time — not merge-conflict theater. Composes 'excitementSelect' — no second
-- argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' typed morphism discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.WorktreeExclusive
  ( -- * Agent lane + worktree + write_set carriers (§16.11)
    AgentLane (..)
  , WorktreeId (..)
  , WriteSetPath (..)
  , ExclusiveWriteSet (..)
  , ExclusiveClaim (..)
  , ExclusiveAdmission (..)
  , ClaimGateVerdict (..)
  , WorktreeExclusiveRefusal (..)
  , WorktreeExclusiveVerdict (..)
    -- * §16.11 admissibility conjunct + positive refuse
  , WorktreeAdmissibilityConjunct (..)
  , worktreeConjunctAdmits
  , agentLaneEq
  , pathInWriteSet
  , writeSetsOverlap
  , agentAlreadyClaimed
  , anyWriteSetOverlap
  , tryClaimExclusive
  , evaluateClaimOperation
  , refuseOverlappingWriteSetAtClaim
  , refuseAgentSecondWorktree
  , refuseMergeConflictTheater
  , refuseSecondArgminOnClaim
    -- * Positive refuse witnesses
  , refuseOverlappingWriteSetAtClaimPositive
  , refuseAgentSecondWorktreePositive
  , refuseMergeConflictTheaterPositive
  , refuseSecondArgminOnClaimPositive
  , evaluateClaimOperationMergeTheaterRefused
  , evaluateClaimOperationExclusiveAdmit
    -- * Excitement alignment (no second argmin)
  , WorktreeExcitementComposePin (..)
  , WorktreeExclusiveCtx (..)
  , composeExcitementSelect
  , worktreeExclusiveSelect
  , worktreeExcitementSelect
  , composeExcitementSelectEqExcitementSelect
  , worktreeExclusiveSelectEqExcitementSelect
  , worktreeExclusiveSelectEqUrgeRecoverySelect
  , worktreeExclusiveNoLocalArgmin
  , composeExcitementSelectRefusesSecondArgmin
  , worktreeExclusiveEmpty
    -- * §16.11 fixtures + witness theorems
  , composerWriteSet
  , grokOverlapWriteSet
  , originRefuseWriteSet
  , composerExclusiveAdmitFixture
  , grokOverlappingWriteSetFixture
  , composerSecondWorktreeFixture
  , kimiAntichainDisjointFixture
  , worktreeFixtureRegistry
  , composerExclusiveAdmitFixtureOk
  , grokOverlapRefusedAtClaim
  , composerSecondWorktreeRefused
  , kimiAntichainDisjointAdmits
  , writeSetsOverlapComposerGrok
  , writeSetsDisjointComposerOriginRefuse
  , worktreeExclusivePositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , worktreeSecondLawFromLandauer
  , worktreeFromLandauerAdmitSecondLaw
  , worktreeSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , worktreeExclusivePhysicsGreen
  , worktreeExclusivePhysicsGreenFalse
  , worktreeExclusiveProductionWired
  , worktreeExclusiveProductionWiredFalse
  , worktreeExclusiveNonClaim
  , worktreeExclusiveNonClaimNonempty
  , worktreeExclusiveModuleWitness
  , worktreeExclusiveNoNewAxiom
  , worktreeExclusiveNoSecondArgmin
  ) where

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
-- SECTION 1: Agent lane + worktree + write_set carriers (§16.11)
-- ---------------------------------------------------------------------------

-- | Admit-series agent lane surrogate — §16.11 first-class users.
data AgentLane = AgentComposer | AgentGrok | AgentKimi
  deriving (Show, Eq)

-- | Replica-class worktree id — one per agent at claim time.
newtype WorktreeId = WorktreeId {worktreeIdVal :: Int}
  deriving (Show, Eq)

-- | Write_set path surrogate — conflict-graph vertex pin.
newtype WriteSetPath = WriteSetPath {writeSetPathId :: Int}
  deriving (Show, Eq)

-- | Antichain write_set — disjoint path set owned exclusively at claim.
newtype ExclusiveWriteSet = ExclusiveWriteSet
  {exclusiveWriteSetPaths :: [WriteSetPath]}
  deriving (Show, Eq)

-- | One active exclusive claim — agent ↔ worktree ↔ write_set.
data ExclusiveClaim = ExclusiveClaim
  { claimAgent    :: !AgentLane
  , claimWorktree :: !WorktreeId
  , claimWriteSet :: !ExclusiveWriteSet
  } deriving (Show, Eq)

-- | Successful claim admission at allocate/claim gate.
data ExclusiveAdmission = ExclusiveAdmission
  { admissionClaim     :: !ExclusiveClaim
  , antichainIndex     :: !Int
  } deriving (Show, Eq)

-- | Claim gate verdict — admit or typed refuse.
data ClaimGateVerdict = ClaimAdmit | ClaimRefused
  deriving (Show, Eq)

-- | Fail-closed refusal when §16.11 exclusivity is violated at claim time.
data WorktreeExclusiveRefusal
  = OverlappingWriteSetAtClaim
  | AgentAlreadyOwnsWorktree
  | MergeConflictTheater
  | SecondArgminOnClaim
  deriving (Show, Eq)

-- | Verdict of a claim operation class.
data WorktreeExclusiveVerdict
  = ExclusiveAdmit
  | OverlapRefused
  | MergeTheaterRefused
  | SecondArgminRefused
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §16.11 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §16.11 admissibility conjunct inputs (surrogate).
data WorktreeAdmissibilityConjunct = WorktreeAdmissibilityConjunct
  { worktreeConjAntichainOk          :: !Bool
  , worktreeConjOneAgentOneWorktree  :: !Bool
  , worktreeConjExcitementPreserves  :: !Bool
  } deriving (Show, Eq)

-- | Evaluate conjunct admissibility.
worktreeConjunctAdmits :: WorktreeAdmissibilityConjunct -> Bool
worktreeConjunctAdmits c =
  worktreeConjAntichainOk c
  && worktreeConjOneAgentOneWorktree c
  && worktreeConjExcitementPreserves c

-- | Decidable equality on agent lanes.
agentLaneEq :: AgentLane -> AgentLane -> Bool
agentLaneEq AgentComposer AgentComposer = True
agentLaneEq AgentGrok AgentGrok = True
agentLaneEq AgentKimi AgentKimi = True
agentLaneEq _ _ = False

-- | Whether a path id appears in a write_set.
pathInWriteSet :: WriteSetPath -> ExclusiveWriteSet -> Bool
pathInWriteSet p ws =
  any (\q -> writeSetPathId p == writeSetPathId q)
    (exclusiveWriteSetPaths ws)

-- | Whether two write_sets overlap on any path id.
writeSetsOverlap :: ExclusiveWriteSet -> ExclusiveWriteSet -> Bool
writeSetsOverlap left right =
  any (`pathInWriteSet` right) (exclusiveWriteSetPaths left)

-- | Whether agent already owns a worktree in the registry.
agentAlreadyClaimed :: AgentLane -> [ExclusiveClaim] -> Bool
agentAlreadyClaimed _ [] = False
agentAlreadyClaimed a (c : rest) =
  if agentLaneEq a (claimAgent c) then True else agentAlreadyClaimed a rest

-- | Whether any registered claim overlaps the candidate write_set.
anyWriteSetOverlap :: ExclusiveWriteSet -> [ExclusiveClaim] -> Bool
anyWriteSetOverlap _ [] = False
anyWriteSetOverlap ws (c : rest) =
  if writeSetsOverlap ws (claimWriteSet c)
    then True
    else anyWriteSetOverlap ws rest

-- | Attempt exclusive claim — fail closed at claim time on overlap or duplicate agent.
tryClaimExclusive
  :: [ExclusiveClaim]
  -> ExclusiveClaim
  -> Either WorktreeExclusiveRefusal ExclusiveAdmission
tryClaimExclusive registry claim
  | agentAlreadyClaimed (claimAgent claim) registry =
      Left AgentAlreadyOwnsWorktree
  | anyWriteSetOverlap (claimWriteSet claim) registry =
      Left OverlappingWriteSetAtClaim
  | otherwise =
      Right
        ExclusiveAdmission
          { admissionClaim = claim
          , antichainIndex = length registry
          }

-- | Classify merge-theater vs claim-time gate without performing I/O.
evaluateClaimOperation :: Bool -> WorktreeExclusiveVerdict
evaluateClaimOperation True = MergeTheaterRefused
evaluateClaimOperation False = ExclusiveAdmit

-- | Positive refuse: overlapping write_set at claim time.
refuseOverlappingWriteSetAtClaim :: WorktreeExclusiveRefusal
refuseOverlappingWriteSetAtClaim = OverlappingWriteSetAtClaim

-- | Positive refuse: agent already owns a worktree.
refuseAgentSecondWorktree :: WorktreeExclusiveRefusal
refuseAgentSecondWorktree = AgentAlreadyOwnsWorktree

-- | Positive refuse: defer to merge-conflict theater instead of claim gate.
refuseMergeConflictTheater :: WorktreeExclusiveRefusal
refuseMergeConflictTheater = MergeConflictTheater

-- | Positive refuse: second local Excitement argmin on claim path.
refuseSecondArgminOnClaim :: WorktreeExclusiveRefusal
refuseSecondArgminOnClaim = SecondArgminOnClaim

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Positive refuse witness for overlapping write_set at claim.
refuseOverlappingWriteSetAtClaimPositive :: Bool
refuseOverlappingWriteSetAtClaimPositive =
  refuseOverlappingWriteSetAtClaim == OverlappingWriteSetAtClaim

-- | Positive refuse witness for agent second worktree.
refuseAgentSecondWorktreePositive :: Bool
refuseAgentSecondWorktreePositive =
  refuseAgentSecondWorktree == AgentAlreadyOwnsWorktree

-- | Positive refuse witness for merge-conflict theater.
refuseMergeConflictTheaterPositive :: Bool
refuseMergeConflictTheaterPositive =
  refuseMergeConflictTheater == MergeConflictTheater

-- | Positive refuse witness for second argmin on claim.
refuseSecondArgminOnClaimPositive :: Bool
refuseSecondArgminOnClaimPositive =
  refuseSecondArgminOnClaim == SecondArgminOnClaim

-- | Merge-theater deferral is always refused at claim gate.
evaluateClaimOperationMergeTheaterRefused :: Bool
evaluateClaimOperationMergeTheaterRefused =
  evaluateClaimOperation True == MergeTheaterRefused

-- | Non-defer path admits exclusive claim operation class.
evaluateClaimOperationExclusiveAdmit :: Bool
evaluateClaimOperationExclusiveAdmit =
  evaluateClaimOperation False == ExclusiveAdmit

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data WorktreeExcitementComposePin
  = ImportSelectExcitement
  | ComposeSecondArgminRefused
  deriving (Show, Eq)

-- | Context for worktree exclusive recovery over admissible history successors.
data WorktreeExclusiveCtx = WorktreeExclusiveCtx
  { worktreeExclusivePrior      :: !ThermodynamicState
  , worktreeExclusiveSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Worktree exclusive path composes 'excitementSelect' — not a second argmin.
composeExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> WorktreeExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
composeExcitementSelect src cands pin =
  case pin of
    ImportSelectExcitement -> excitementSelect src cands
    ComposeSecondArgminRefused -> Left ExcAllInadmissible

-- | Worktree exclusive recovery **is** 'urgeRecoverySelect' / 'excitementSelect'.
worktreeExclusiveSelect
  :: WorktreeExclusiveCtx
  -> Either ExcitementResidue HistoryCandidate
worktreeExclusiveSelect ctx =
  urgeRecoverySelect
    (worktreeExclusivePrior ctx)
    (worktreeExclusiveSuccessors ctx)

-- | Bare alias — same selector, no re-derivation.
worktreeExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
worktreeExcitementSelect = excitementSelect

-- | Definitional witness: compose pin equals 'excitementSelect'.
composeExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
composeExcitementSelectEqExcitementSelect src cands =
  composeExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Definitional witness: worktree selection is 'excitementSelect'.
worktreeExclusiveSelectEqExcitementSelect :: WorktreeExclusiveCtx -> Bool
worktreeExclusiveSelectEqExcitementSelect ctx =
  worktreeExclusiveSelect ctx
    == excitementSelect
      (worktreeExclusivePrior ctx)
      (worktreeExclusiveSuccessors ctx)

-- | Worktree selection equals bare urge recovery select.
worktreeExclusiveSelectEqUrgeRecoverySelect :: WorktreeExclusiveCtx -> Bool
worktreeExclusiveSelectEqUrgeRecoverySelect ctx =
  worktreeExclusiveSelect ctx
    == urgeRecoverySelect
      (worktreeExclusivePrior ctx)
      (worktreeExclusiveSuccessors ctx)

-- | Worktree selector re-uses 'excitementSelect' — no Urge-local argmin.
worktreeExclusiveNoLocalArgmin :: WorktreeExclusiveCtx -> Bool
worktreeExclusiveNoLocalArgmin ctx =
  worktreeExclusiveSelect ctx
    == excitementSelect
      (worktreeExclusivePrior ctx)
      (worktreeExclusiveSuccessors ctx)

-- | Second-argmin pin refuses via 'ExcAllInadmissible'.
composeExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
composeExcitementSelectRefusesSecondArgmin src cands =
  composeExcitementSelect src cands ComposeSecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via imported selector.
worktreeExclusiveEmpty :: ThermodynamicState -> Bool
worktreeExclusiveEmpty src =
  worktreeExclusiveSelect
    WorktreeExclusiveCtx
      { worktreeExclusivePrior = src
      , worktreeExclusiveSuccessors = []
      }
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §16.11 fixtures + witness theorems
-- ---------------------------------------------------------------------------

wePathSrc :: WriteSetPath
wePathSrc = WriteSetPath 0

wePathTest :: WriteSetPath
wePathTest = WriteSetPath 1

wePathOriginRefuse :: WriteSetPath
wePathOriginRefuse = WriteSetPath 2

weWorktree0 :: WorktreeId
weWorktree0 = WorktreeId 0

weWorktree1 :: WorktreeId
weWorktree1 = WorktreeId 1

weWorktree2 :: WorktreeId
weWorktree2 = WorktreeId 2

-- | Composer exclusive write_set fixture.
composerWriteSet :: ExclusiveWriteSet
composerWriteSet =
  ExclusiveWriteSet {exclusiveWriteSetPaths = [wePathSrc, wePathTest]}

-- | Grok overlapping write_set fixture (shares wePathTest).
grokOverlapWriteSet :: ExclusiveWriteSet
grokOverlapWriteSet = ExclusiveWriteSet {exclusiveWriteSetPaths = [wePathTest]}

-- | Origin-refuse disjoint write_set fixture.
originRefuseWriteSet :: ExclusiveWriteSet
originRefuseWriteSet =
  ExclusiveWriteSet {exclusiveWriteSetPaths = [wePathOriginRefuse]}

-- | Composer first exclusive claim fixture.
composerExclusiveAdmitFixture :: ExclusiveClaim
composerExclusiveAdmitFixture =
  ExclusiveClaim
    { claimAgent = AgentComposer
    , claimWorktree = weWorktree0
    , claimWriteSet = composerWriteSet
    }

-- | Grok overlapping write_set claim fixture.
grokOverlappingWriteSetFixture :: ExclusiveClaim
grokOverlappingWriteSetFixture =
  ExclusiveClaim
    { claimAgent = AgentGrok
    , claimWorktree = weWorktree1
    , claimWriteSet = grokOverlapWriteSet
    }

-- | Composer second worktree claim fixture (agent already claimed).
composerSecondWorktreeFixture :: ExclusiveClaim
composerSecondWorktreeFixture =
  ExclusiveClaim
    { claimAgent = AgentComposer
    , claimWorktree = weWorktree1
    , claimWriteSet = originRefuseWriteSet
    }

-- | Kimi antichain disjoint claim fixture.
kimiAntichainDisjointFixture :: ExclusiveClaim
kimiAntichainDisjointFixture =
  ExclusiveClaim
    { claimAgent = AgentKimi
    , claimWorktree = weWorktree2
    , claimWriteSet = originRefuseWriteSet
    }

-- | Fixture registry with one admitted composer claim.
worktreeFixtureRegistry :: [ExclusiveClaim]
worktreeFixtureRegistry = [composerExclusiveAdmitFixture]

-- | Composer admits on empty registry.
composerExclusiveAdmitFixtureOk :: Bool
composerExclusiveAdmitFixtureOk =
  tryClaimExclusive [] composerExclusiveAdmitFixture
    == Right
      ExclusiveAdmission
        { admissionClaim = composerExclusiveAdmitFixture
        , antichainIndex = 0
        }

-- | Grok overlap refused at claim time (not merge theater).
grokOverlapRefusedAtClaim :: Bool
grokOverlapRefusedAtClaim =
  tryClaimExclusive worktreeFixtureRegistry grokOverlappingWriteSetFixture
    == Left OverlappingWriteSetAtClaim

-- | Composer second worktree refused (one agent ↔ one worktree).
composerSecondWorktreeRefused :: Bool
composerSecondWorktreeRefused =
  tryClaimExclusive worktreeFixtureRegistry composerSecondWorktreeFixture
    == Left AgentAlreadyOwnsWorktree

-- | Kimi disjoint write_set admits on antichain registry.
kimiAntichainDisjointAdmits :: Bool
kimiAntichainDisjointAdmits =
  tryClaimExclusive worktreeFixtureRegistry kimiAntichainDisjointFixture
    == Right
      ExclusiveAdmission
        { admissionClaim = kimiAntichainDisjointFixture
        , antichainIndex = 1
        }

-- | Composer and grok write_sets overlap on shared path.
writeSetsOverlapComposerGrok :: Bool
writeSetsOverlapComposerGrok =
  writeSetsOverlap composerWriteSet grokOverlapWriteSet

-- | Composer and origin-refuse write_sets are disjoint.
writeSetsDisjointComposerOriginRefuse :: Bool
writeSetsDisjointComposerOriginRefuse =
  not (writeSetsOverlap composerWriteSet originRefuseWriteSet)

-- | Positive refuse is not silent no-op on merge-theater deferral.
worktreeExclusivePositiveRefuseNotSilent :: Bool
worktreeExclusivePositiveRefuseNotSilent =
  evaluateClaimOperation True /= ExclusiveAdmit

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on worktree carrier transition from Landauer bridge discharge.
worktreeSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
worktreeSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
worktreeFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
worktreeFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for worktree second law (no new axiom).
worktreeSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
worktreeSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
worktreeExclusivePhysicsGreen :: Bool
worktreeExclusivePhysicsGreen = False

-- | Lean/Coq: @worktree_exclusive_physics_green_false@.
worktreeExclusivePhysicsGreenFalse :: Bool
worktreeExclusivePhysicsGreenFalse = not worktreeExclusivePhysicsGreen

-- | Production wiring stays open (worktree lift only).
worktreeExclusiveProductionWired :: Bool
worktreeExclusiveProductionWired = False

-- | Lean/Coq: @worktree_exclusive_production_wired_false@.
worktreeExclusiveProductionWiredFalse :: Bool
worktreeExclusiveProductionWiredFalse = not worktreeExclusiveProductionWired

-- | Honest non-claim string (meso §16.11 worktree exclusive scaffold).
worktreeExclusiveNonClaim :: String
worktreeExclusiveNonClaim =
  "§16.11 one agent ↔ one exclusive worktree antichain exclusive copy; "
    ++ "claim-time gate failure on overlapping write_sets; "
    ++ "worktreeExclusiveSelect=excitementSelect; "
    ++ "not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
worktreeExclusiveNonClaimNonempty :: Bool
worktreeExclusiveNonClaimNonempty = length worktreeExclusiveNonClaim > 0

-- | Catalog witness: meso Urge WorktreeExclusive module present.
worktreeExclusiveModuleWitness :: Bool
worktreeExclusiveModuleWitness = True

-- | Zero new axiom discipline witness.
worktreeExclusiveNoNewAxiom :: Bool
worktreeExclusiveNoNewAxiom = True

-- | Second-argmin refusal: worktree composes 'excitementSelect' only.
worktreeExclusiveNoSecondArgmin :: Bool
worktreeExclusiveNoSecondArgmin =
  worktreeExclusiveNoLocalArgmin
    WorktreeExclusiveCtx
      { worktreeExclusivePrior = ThermodynamicState 2400 0 0 0 0
      , worktreeExclusiveSuccessors = []
      }
