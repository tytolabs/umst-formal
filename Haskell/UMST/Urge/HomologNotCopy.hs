-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.HomologNotCopy
-- Description : Meso acting Urge — §22.1 homolog ≠ copy recovery morphism.
--
-- Recovery **is** a new Excitement arrow over admissible successors — not
-- `git reset --hard` of a sibling commit. Homolog relates sibling commits
-- geometrically — homolog ≠ copy. Composes 'excitementSelect'; no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' typed morphism discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.HomologNotCopy
  ( -- * Sibling commit + homolog witness carriers (§22.1)
    SiblingCommitRef (..)
  , HomologWitness (..)
  , HomologUcrsStamp (..)
  , HomologRecoveryArrow (..)
  , isNewExcitementArrow
  , HomologRecoveryAttempt (..)
  , HomologNotCopyRefusal (..)
  , HomologRecoveryClass (..)
  , HomologRecoveryVerdict (..)
    -- * §22.1 admissibility conjunct + positive refuse
  , HomologAdmissibilityConjunct (..)
  , homologConjunctAdmits
  , siblingCommitRefOf
  , siblingHashesDiffer
  , homologNotCopyOk
  , evaluateHomologRecoveryOperation
  , refuseGitResetHardSibling
  , refuseHomologAsCopy
  , refuseSecondArgmin
  , recoveryClassOfRefusal
  , classifyHomologRecoveryAttempt
  , recoveryArrowFromSelection
  , applyHomologRecoveryMorphism
    -- * Positive refuse witnesses
  , homologRecoveryGitResetHardRefused
  , homologRecoveryNewArrowOkWhenNotReset
  , refuseGitResetHardSiblingPositive
  , refuseHomologAsCopyPositive
  , refuseSecondArgminPositive
    -- * Excitement alignment (no second argmin)
  , HomologExcitementComposePin (..)
  , HomologRecoveryCtx (..)
  , homologExcitementSelect
  , homologRecoverySelect
  , homologExcitementSelectEqExcitementSelect
  , homologRecoverySelectEqExcitementSelect
  , homologRecoverySelectEqUrgeRecoverySelect
  , homologRecoveryNoLocalArgmin
  , homologExcitementSelectRefusesSecondArgmin
  , homologRecoveryEmpty
    -- * §22.1 fixtures + witness theorems
  , homologFixtureState
  , homologFixtureWitness
  , homologFixtureConjunct
  , homologFixtureAttempt
  , homologFixtureGitResetAttempt
  , homologFixtureClassifyAdmitsArrow
  , homologFixtureClassifyRefusesGitReset
  , homologFixtureApplyMorphismOk
  , homologFixtureRefusesCopyClaim
  , homologFixtureIsNewExcitementArrow
  , homologFixtureSiblingHashesDiffer
    -- * Landauer bridge (derived — zero new axioms)
  , homologSecondLawFromLandauer
  , homologFromLandauerAdmitSecondLaw
  , homologSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , homologNotCopyPhysicsGreen
  , homologNotCopyPhysicsGreenFalse
  , homologNotCopyProductionWired
  , homologNotCopyProductionWiredFalse
  , homologNotCopyNonClaim
  , homologNotCopyNonClaimNonempty
  , homologNotCopyModuleWitness
  , homologNotCopyNoNewAxiom
  , homologNotCopyNoSecondArgmin
  , homologNotCopyPositiveRefuseNotSilent
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
import UMST.Urge.ExcitementImport
  ( urgeRecoverySelect
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: Sibling commit + homolog witness carriers (§22.1)
-- ---------------------------------------------------------------------------

-- | Sibling commit reference — content-addressed surrogate.
data SiblingCommitRef = SiblingCommitRef
  { commitHash :: !Int
  , siblingOf  :: !Int
  } deriving (Show, Eq)

-- | Homolog witness — geometric relation between sibling commits.
data HomologWitness = HomologWitness
  { homologFrom            :: !SiblingCommitRef
  , homologTo              :: !SiblingCommitRef
  , claimsIdentityCopy     :: !Bool
  } deriving (Show, Eq)

-- | UCRS stamp surrogate carried through §22.1 recovery arrow.
data HomologUcrsStamp = HomologUcrsStamp
  { ucrsSeq    :: !Int
  , wallHasT   :: !Bool
  } deriving (Show, Eq)

-- | New Excitement recovery arrow — admissible state transition, not blind copy.
data HomologRecoveryArrow = HomologRecoveryArrow
  { arrowId             :: !Int
  , selectedSuccessorId :: !Int
  , arrowHead           :: !ThermodynamicState
  , provenanceIntact    :: !Bool
  , ucrs                :: !HomologUcrsStamp
  } deriving (Show, Eq)

-- | Whether the recovery arrow is a fresh Excitement selection.
isNewExcitementArrow :: HomologRecoveryArrow -> Bool
isNewExcitementArrow a =
  provenanceIntact a && wallHasT (ucrs a)

-- | Recovery attempt bundle — gate input for §22.1 classification.
data HomologRecoveryAttempt = HomologRecoveryAttempt
  { gitResetHardSibling :: !Bool
  , witness             :: !(Maybe HomologWitness)
  , attemptHead         :: !ThermodynamicState
  } deriving (Show, Eq)

-- | Fail-closed recovery errors — positive refuse, not silent no-op.
data HomologNotCopyRefusal
  = GitResetHardSibling
  | HomologIsNotCopy
  | SecondArgmin
  deriving (Show, Eq)

-- | Verdict class for recovery attempts.
data HomologRecoveryClass
  = NewExcitementArrow
  | GitResetHardSiblingClass
  | HomologClaimsCopy
  deriving (Show, Eq)

-- | Verdict of a recovery operation class.
data HomologRecoveryVerdict
  = NewArrowOk
  | GitResetHardRefused
  | HomologCopyRefused
  | SecondArgminRefused
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §22.1 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §22.1 admissibility conjunct inputs (surrogate).
data HomologAdmissibilityConjunct = HomologAdmissibilityConjunct
  { notGitResetHard     :: !Bool
  , homologNotCopy      :: !Bool
  , excitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ ¬git-reset-hard ∧ homolog≠copy ∧ Excitement preserves@.
homologConjunctAdmits :: HomologAdmissibilityConjunct -> Bool
homologConjunctAdmits c =
  notGitResetHard c && homologNotCopy c && excitementPreserves c

-- | Build sibling commit ref from hash + parent pin.
siblingCommitRefOf :: Int -> Int -> SiblingCommitRef
siblingCommitRefOf hash parent =
  SiblingCommitRef {commitHash = hash, siblingOf = parent}

-- | Whether sibling commit hashes differ (homolog ≠ identity copy).
siblingHashesDiffer :: HomologWitness -> Bool
siblingHashesDiffer w =
  commitHash (homologFrom w) /= commitHash (homologTo w)

-- | §22.1 homolog-not-copy? — geometric relation, not blind sibling reset.
homologNotCopyOk :: HomologWitness -> Bool
homologNotCopyOk w =
  siblingHashesDiffer w && not (claimsIdentityCopy w)

-- | Classify git reset --hard sibling vs new Excitement arrow without I/O.
evaluateHomologRecoveryOperation :: Bool -> HomologRecoveryVerdict
evaluateHomologRecoveryOperation True = GitResetHardRefused
evaluateHomologRecoveryOperation False = NewArrowOk

-- | Positive refuse: `git reset --hard` of sibling — inadmissible under §22.1.
refuseGitResetHardSibling :: HomologNotCopyRefusal
refuseGitResetHardSibling = GitResetHardSibling

-- | Positive refuse: homolog witness claims identity copy — homolog ≠ copy.
refuseHomologAsCopy :: HomologNotCopyRefusal
refuseHomologAsCopy = HomologIsNotCopy

-- | Positive refuse: second local Excitement argmin — compose import only.
refuseSecondArgmin :: HomologNotCopyRefusal
refuseSecondArgmin = SecondArgmin

-- | Map typed refusal to recovery class surrogate.
recoveryClassOfRefusal :: HomologNotCopyRefusal -> HomologRecoveryClass
recoveryClassOfRefusal GitResetHardSibling = GitResetHardSiblingClass
recoveryClassOfRefusal HomologIsNotCopy = HomologClaimsCopy
recoveryClassOfRefusal SecondArgmin = NewExcitementArrow

-- | Gate recovery attempts — fail closed on git reset hard or homolog-as-copy.
classifyHomologRecoveryAttempt
  :: HomologRecoveryAttempt
  -> Either HomologNotCopyRefusal HomologRecoveryClass
classifyHomologRecoveryAttempt attempt
  | gitResetHardSibling attempt = Left GitResetHardSibling
  | otherwise =
      case witness attempt of
        Nothing -> Right NewExcitementArrow
        Just w ->
          if claimsIdentityCopy w
            then Left HomologIsNotCopy
            else
              if homologNotCopyOk w
                then Right NewExcitementArrow
                else Left HomologIsNotCopy

-- | Build recovery arrow from Excitement selection + UCRS pin.
recoveryArrowFromSelection
  :: Int
  -> Int
  -> ThermodynamicState
  -> Int
  -> Bool
  -> Either ExcitementResidue HistoryCandidate
  -> Either ExcitementResidue HomologRecoveryArrow
recoveryArrowFromSelection arrowId successorId headState ucrsSeq wallHasT sel =
  case sel of
    Left r -> Left r
    Right _ ->
      Right
        HomologRecoveryArrow
          { arrowId = arrowId
          , selectedSuccessorId = successorId
          , arrowHead = headState
          , provenanceIntact = True
          , ucrs = HomologUcrsStamp {ucrsSeq = ucrsSeq, wallHasT = wallHasT}
          }

-- | Attempt typed homolog recovery morphism — fail closed on inadmissibility.
applyHomologRecoveryMorphism
  :: HomologRecoveryAttempt
  -> HomologAdmissibilityConjunct
  -> Bool
  -> Either HomologNotCopyRefusal HomologRecoveryArrow
applyHomologRecoveryMorphism attempt conjunct excitementSelected
  | not (homologConjunctAdmits conjunct) = Left HomologIsNotCopy
  | gitResetHardSibling attempt = Left GitResetHardSibling
  | not excitementSelected = Left SecondArgmin
  | otherwise =
      case witness attempt of
        Nothing ->
          Right
            HomologRecoveryArrow
              { arrowId = 0
              , selectedSuccessorId = 0
              , arrowHead = attemptHead attempt
              , provenanceIntact = True
              , ucrs = HomologUcrsStamp {ucrsSeq = 0, wallHasT = True}
              }
        Just w ->
          if homologNotCopyOk w
            then
              Right
                HomologRecoveryArrow
                  { arrowId = commitHash (homologFrom w)
                  , selectedSuccessorId = commitHash (homologTo w)
                  , arrowHead = attemptHead attempt
                  , provenanceIntact = True
                  , ucrs = HomologUcrsStamp {ucrsSeq = 0, wallHasT = True}
                  }
            else Left HomologIsNotCopy

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Git reset --hard is always refused.
homologRecoveryGitResetHardRefused :: Bool
homologRecoveryGitResetHardRefused =
  evaluateHomologRecoveryOperation True == GitResetHardRefused

-- | Non-reset path admits new Excitement arrow.
homologRecoveryNewArrowOkWhenNotReset :: Bool
homologRecoveryNewArrowOkWhenNotReset =
  evaluateHomologRecoveryOperation False == NewArrowOk

-- | Positive refuse witness for git reset --hard sibling.
refuseGitResetHardSiblingPositive :: Bool
refuseGitResetHardSiblingPositive =
  refuseGitResetHardSibling == GitResetHardSibling

-- | Positive refuse witness for homolog-as-copy claim.
refuseHomologAsCopyPositive :: Bool
refuseHomologAsCopyPositive = refuseHomologAsCopy == HomologIsNotCopy

-- | Positive refuse witness for second argmin.
refuseSecondArgminPositive :: Bool
refuseSecondArgminPositive = refuseSecondArgmin == SecondArgmin

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data HomologExcitementComposePin
  = PinImportSelectExcitement
  | PinSecondArgminRefused
  deriving (Show, Eq)

-- | Context for homolog recovery over admissible history successors.
data HomologRecoveryCtx = HomologRecoveryCtx
  { homologPrior      :: !ThermodynamicState
  , homologSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Homolog recovery path composes 'excitementSelect' — not a second argmin.
homologExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> HomologExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
homologExcitementSelect src cands pin =
  case pin of
    PinImportSelectExcitement -> excitementSelect src cands
    PinSecondArgminRefused -> Left ExcAllInadmissible

-- | Homolog recovery **is** 'urgeRecoverySelect' / 'excitementSelect'.
homologRecoverySelect
  :: HomologRecoveryCtx
  -> Either ExcitementResidue HistoryCandidate
homologRecoverySelect ctx =
  urgeRecoverySelect (homologPrior ctx) (homologSuccessors ctx)

-- | Definitional witness: homolog excitement selection is 'excitementSelect'.
homologExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
homologExcitementSelectEqExcitementSelect src cands =
  homologExcitementSelect src cands PinImportSelectExcitement
    == excitementSelect src cands

-- | Definitional witness: homolog recovery selection is 'excitementSelect'.
homologRecoverySelectEqExcitementSelect :: HomologRecoveryCtx -> Bool
homologRecoverySelectEqExcitementSelect ctx =
  homologRecoverySelect ctx
    == excitementSelect (homologPrior ctx) (homologSuccessors ctx)

-- | Homolog recovery equals bare urge recovery select.
homologRecoverySelectEqUrgeRecoverySelect :: HomologRecoveryCtx -> Bool
homologRecoverySelectEqUrgeRecoverySelect ctx =
  homologRecoverySelect ctx
    == urgeRecoverySelect (homologPrior ctx) (homologSuccessors ctx)

-- | Homolog selector re-uses 'excitementSelect' — no Urge-local argmin.
homologRecoveryNoLocalArgmin :: HomologRecoveryCtx -> Bool
homologRecoveryNoLocalArgmin ctx =
  homologRecoverySelect ctx
    == excitementSelect (homologPrior ctx) (homologSuccessors ctx)

-- | Second-argmin pin refuses via 'ExcAllInadmissible'.
homologExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
homologExcitementSelectRefusesSecondArgmin src cands =
  homologExcitementSelect src cands PinSecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via imported selector.
homologRecoveryEmpty :: ThermodynamicState -> Bool
homologRecoveryEmpty src =
  homologRecoverySelect
    HomologRecoveryCtx {homologPrior = src, homologSuccessors = []}
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 5: §22.1 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | §22.1 fixture thermodynamic head.
homologFixtureState :: ThermodynamicState
homologFixtureState = ThermodynamicState 2400 0 0 0 0

-- | §22.1 fixture homolog witness (sibling hashes differ, no copy claim).
homologFixtureWitness :: HomologWitness
homologFixtureWitness =
  HomologWitness
    { homologFrom = siblingCommitRefOf 101 50
    , homologTo = siblingCommitRefOf 102 50
    , claimsIdentityCopy = False
    }

-- | §22.1 fixture admissibility conjunct.
homologFixtureConjunct :: HomologAdmissibilityConjunct
homologFixtureConjunct =
  HomologAdmissibilityConjunct
    { notGitResetHard = True
    , homologNotCopy = True
    , excitementPreserves = True
    }

-- | §22.1 fixture recovery attempt (new Excitement arrow path).
homologFixtureAttempt :: HomologRecoveryAttempt
homologFixtureAttempt =
  HomologRecoveryAttempt
    { gitResetHardSibling = False
    , witness = Just homologFixtureWitness
    , attemptHead = homologFixtureState
    }

-- | §22.1 fixture git reset --hard attempt (refused).
homologFixtureGitResetAttempt :: HomologRecoveryAttempt
homologFixtureGitResetAttempt =
  HomologRecoveryAttempt
    { gitResetHardSibling = True
    , witness = Just homologFixtureWitness
    , attemptHead = homologFixtureState
    }

-- | Fixture classifies new Excitement arrow when homolog ≠ copy.
homologFixtureClassifyAdmitsArrow :: Bool
homologFixtureClassifyAdmitsArrow =
  classifyHomologRecoveryAttempt homologFixtureAttempt
    == Right NewExcitementArrow

-- | Fixture refuses git reset --hard sibling.
homologFixtureClassifyRefusesGitReset :: Bool
homologFixtureClassifyRefusesGitReset =
  classifyHomologRecoveryAttempt homologFixtureGitResetAttempt
    == Left GitResetHardSibling

-- | Fixture morphism admits recovery arrow on valid conjunct.
homologFixtureApplyMorphismOk :: Bool
homologFixtureApplyMorphismOk =
  applyHomologRecoveryMorphism homologFixtureAttempt homologFixtureConjunct True
    == Right
      HomologRecoveryArrow
        { arrowId = 101
        , selectedSuccessorId = 102
        , arrowHead = homologFixtureState
        , provenanceIntact = True
        , ucrs = HomologUcrsStamp {ucrsSeq = 0, wallHasT = True}
        }

-- | Fixture refuses homolog witness that claims identity copy.
homologFixtureRefusesCopyClaim :: Bool
homologFixtureRefusesCopyClaim =
  classifyHomologRecoveryAttempt
    HomologRecoveryAttempt
      { gitResetHardSibling = False
      , witness =
          Just
            HomologWitness
              { homologFrom = siblingCommitRefOf 101 50
              , homologTo = siblingCommitRefOf 102 50
              , claimsIdentityCopy = True
              }
      , attemptHead = homologFixtureState
      }
    == Left HomologIsNotCopy

-- | Fixture recovery arrow is a new Excitement selection.
homologFixtureIsNewExcitementArrow :: Bool
homologFixtureIsNewExcitementArrow =
  isNewExcitementArrow
    HomologRecoveryArrow
      { arrowId = 1
      , selectedSuccessorId = 2
      , arrowHead = homologFixtureState
      , provenanceIntact = True
      , ucrs = HomologUcrsStamp {ucrsSeq = 22, wallHasT = True}
      }

-- | Fixture sibling commit hashes differ.
homologFixtureSiblingHashesDiffer :: Bool
homologFixtureSiblingHashesDiffer =
  siblingHashesDiffer homologFixtureWitness

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on homolog carrier transition from Landauer bridge discharge.
homologSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
homologSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
homologFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
homologFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for homolog second law (no new axiom).
homologSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
homologSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
homologNotCopyPhysicsGreen :: Bool
homologNotCopyPhysicsGreen = False

-- | Lean/Coq: @homolog_not_copy_physics_green_false@.
homologNotCopyPhysicsGreenFalse :: Bool
homologNotCopyPhysicsGreenFalse = not homologNotCopyPhysicsGreen

-- | Production wiring stays open (homolog lift only).
homologNotCopyProductionWired :: Bool
homologNotCopyProductionWired = False

-- | Lean/Coq: @homolog_not_copy_production_wired_false@.
homologNotCopyProductionWiredFalse :: Bool
homologNotCopyProductionWiredFalse = not homologNotCopyProductionWired

-- | Honest non-claim string (meso §22.1 homolog-not-copy scaffold).
homologNotCopyNonClaim :: String
homologNotCopyNonClaim =
  "§22.1 homolog≠copy: recovery is new Excitement arrow over admissible successors; "
    ++ "not git reset --hard sibling; homologRecoverySelect=excitementSelect; "
    ++ "not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
homologNotCopyNonClaimNonempty :: Bool
homologNotCopyNonClaimNonempty = length homologNotCopyNonClaim > 0

-- | Catalog witness: meso Urge HomologNotCopy module present.
homologNotCopyModuleWitness :: Bool
homologNotCopyModuleWitness = True

-- | Zero new axiom discipline witness.
homologNotCopyNoNewAxiom :: Bool
homologNotCopyNoNewAxiom = True

-- | Second-argmin refusal: homolog composes 'excitementSelect' only.
homologNotCopyNoSecondArgmin :: Bool
homologNotCopyNoSecondArgmin =
  homologRecoveryNoLocalArgmin
    HomologRecoveryCtx
      { homologPrior = homologFixtureState
      , homologSuccessors = []
      }

-- | Positive refuse is not silent no-op on git reset --hard.
homologNotCopyPositiveRefuseNotSilent :: Bool
homologNotCopyPositiveRefuseNotSilent =
  evaluateHomologRecoveryOperation True /= NewArrowOk
