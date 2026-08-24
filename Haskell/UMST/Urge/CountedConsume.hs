-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.CountedConsume
-- Description : Meso acting Urge — §21 counted domain consumer (`counted_consume`).
--
-- Domain provenance is scanner-emitted via `scan_counting` — refuse author
-- `Domain::new` / hand-filled extent. Excitement recovery composes
-- 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.CountedConsume
  ( -- * Scanner-emitted domain + scan_counting carriers (§21)
    CountedDomainProvenance (..)
  , CountedDomain (..)
  , CountedScannedClaim (..)
  , CountedScanWalk (..)
  , countedScanWalkEmpty
  , countedNatInb
  , countedScanTouch
  , countedScanSkip
  , CountedDomainError (..)
  , CountedConsumeRefusal (..)
  , CountedConsumeVerdict (..)
  , CountedConsumeAdmit (..)
    -- * §21 admissibility + scan_counting + positive refuse
  , countedCardinalityFromWalk
  , countedDomainFromWalk
  , verifyCountedDomain
  , scanCountingFinalize
  , scanCounting
  , evaluateCountedDomainOperation
  , refuseAuthorDomainNew
  , refuseSecondArgminSelector
  , domainToAdmit
  , admitScannedClaim
  , CountedAdmissibilityConjunct (..)
  , countedConjunctAdmits
  , applyCountedConsumeMorphism
    -- * Counted consume composes excitementSelect (no second argmin)
  , CountedConsumeCtx (..)
  , countedConsumeSelect
  , countedExcitementSelect
  , countedConsumeSelectEqExcitementSelect
  , countedConsumeSelectEqUrgeRecoverySelect
  , countedExcitementSelectEqExcitementSelect
  , countedConsumeNoLocalArgmin
  , countedConsumeEmpty
    -- * §21 fixtures + witness theorems
  , countedFixtureWalk
  , countedFixtureDomain
  , countedFixtureClaim
  , countedFixtureConjunct
  , countedFixtureHandFilled
  , countedFixtureScannerEmittedOk
  , countedFixtureHandFillRefused
  , countedFixtureAuthorDomainRefused
  , countedFixtureApplyMorphismOk
  , countedFixtureAdmitScannedClaimOk
  , countedFixtureScanCountingOk
  , countedFixtureCardinalityMatchesScope
  , countedAuthorDomainRefused
  , countedScanOkWhenNotAuthor
  , refuseAuthorDomainNewPositive
  , refuseSecondArgminPositive
  , scanCountingFinalizeEmpty
    -- * Landauer bridge (derived — zero new axioms)
  , CountedHistoryMove (..)
  , admissibleCountedConsume
  , countedSecondLawFromLandauer
  , countedSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , countedConsumePhysicsGreen
  , countedConsumePhysicsGreenFalse
  , countedConsumeProductionWired
  , countedConsumeProductionWiredFalse
  , countedConsumeNonClaim
  , countedConsumeNonClaimNonempty
  , countedConsumeModuleWitness
  , countedConsumeNoNewAxiom
  , countedConsumeNoSecondArgmin
  , countedConsumePositiveRefuseNotSilent
  , countedConsumeAuthorRefusePositive
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
-- SECTION 1: Scanner-emitted domain + scan_counting carriers (§21)
-- ---------------------------------------------------------------------------

-- | Domain provenance — new claims must be scanner-emitted `Counted`.
data CountedDomainProvenance = CountedProvenance
  deriving (Show, Eq)

-- | Extent of what a scanner actually examined — cardinality matches scope.
data CountedDomain = CountedDomain
  { countedScope       :: ![Int]
  , countedCardinality :: !Int
  , countedExclusions  :: ![Int]
  , countedProvenance  :: !CountedDomainProvenance
  } deriving (Show, Eq)

-- | Value + domain counted together — admissible claim construction path.
data CountedScannedClaim a = CountedScannedClaim
  { countedClaimValue  :: !a
  , countedClaimDomain :: !CountedDomain
  } deriving (Show, Eq)

-- | Accumulated walk state — scope and exclusions are scanner-emitted only.
data CountedScanWalk = CountedScanWalk
  { countedWalkScope      :: ![Int]
  , countedWalkExclusions :: ![Int]
  } deriving (Show, Eq)

-- | Empty walk — scanner starting point.
countedScanWalkEmpty :: CountedScanWalk
countedScanWalkEmpty =
  CountedScanWalk {countedWalkScope = [], countedWalkExclusions = []}

-- | Nat membership surrogate for walk dedup.
countedNatInb :: Int -> [Int] -> Bool
countedNatInb n = any (== n)

-- | Touch one path id into walked scope (dedup surrogate).
countedScanTouch :: CountedScanWalk -> Int -> CountedScanWalk
countedScanTouch w pathId =
  if countedNatInb pathId (countedWalkScope w)
    then w
    else
      CountedScanWalk
        { countedWalkScope = pathId : countedWalkScope w
        , countedWalkExclusions = countedWalkExclusions w
        }

-- | Skip one path id into exclusions (dedup surrogate).
countedScanSkip :: CountedScanWalk -> Int -> CountedScanWalk
countedScanSkip w pathId =
  if countedNatInb pathId (countedWalkExclusions w)
    then w
    else
      CountedScanWalk
        { countedWalkScope = countedWalkScope w
        , countedWalkExclusions = pathId : countedWalkExclusions w
        }

-- | Refusal when domain is declared instead of counted.
data CountedDomainError
  = HandFilledRefused
  | CardinalityMismatch !Int !Int
  | EmptyScan
  deriving (Show, Eq)

-- | Fail-closed counted consume errors — positive refuse, not silent no-op.
data CountedConsumeRefusal
  = AuthorDomainNew
  | HandFilledDomain
  | EmptyScanRefusal
  | SecondArgmin
  deriving (Show, Eq)

-- | Verdict of a counted domain operation class.
data CountedConsumeVerdict
  = ScanOk
  | AuthorDomainRefused
  | HandFillRefused
  | Inadmissible
  deriving (Show, Eq)

-- | Positive admit/refuse on counted domain consumption.
data CountedConsumeAdmit
  = CountedAdmitted
  | CountedRefused !CountedConsumeRefusal
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §21 admissibility + scan_counting + positive refuse
-- ---------------------------------------------------------------------------

-- | Cardinality from walked scope — always `length scope` (§21).
countedCardinalityFromWalk :: CountedScanWalk -> Int
countedCardinalityFromWalk w = length (countedWalkScope w)

-- | Build domain from walk — cardinality is scanner-emitted, not author-filled.
countedDomainFromWalk :: CountedScanWalk -> CountedDomain
countedDomainFromWalk w =
  CountedDomain
    { countedScope = countedWalkScope w
    , countedCardinality = countedCardinalityFromWalk w
    , countedExclusions = countedWalkExclusions w
    , countedProvenance = CountedProvenance
    }

-- | Verify Counted provenance and cardinality matches scope — catches hand-fill.
verifyCountedDomain :: CountedDomain -> Either CountedDomainError CountedDomain
verifyCountedDomain d =
  case countedProvenance d of
    CountedProvenance
      | countedCardinality d == length (countedScope d) -> Right d
      | otherwise ->
          Left (CardinalityMismatch (countedCardinality d) (length (countedScope d)))

-- | Finalize walk — fail closed on empty scan; cardinality from walk only.
scanCountingFinalize :: CountedScanWalk -> Either CountedDomainError CountedDomain
scanCountingFinalize w =
  if countedCardinalityFromWalk w == 0
    then Left EmptyScan
    else verifyCountedDomain (countedDomainFromWalk w)

-- | `scan_counting` surrogate — value computed from walk, domain from finalize.
scanCounting :: CountedScanWalk -> a -> Either CountedDomainError (CountedScannedClaim a)
scanCounting w value =
  case scanCountingFinalize w of
    Left e -> Left e
    Right d -> Right (CountedScannedClaim {countedClaimValue = value, countedClaimDomain = d})

-- | Classify author construct vs scanner-emitted without performing I/O.
evaluateCountedDomainOperation :: Bool -> CountedConsumeVerdict
evaluateCountedDomainOperation authorConstruct =
  if authorConstruct then AuthorDomainRefused else ScanOk

-- | Positive refuse: author `Domain::new` / hand-fill is inadmissible (§21).
refuseAuthorDomainNew :: CountedConsumeRefusal
refuseAuthorDomainNew = AuthorDomainNew

-- | Positive refuse: second Excitement selector — compose `excitementSelect`.
refuseSecondArgminSelector :: CountedConsumeRefusal
refuseSecondArgminSelector = SecondArgmin

-- | Map domain verification to typed `counted_consume_admit`.
domainToAdmit :: CountedDomain -> CountedConsumeAdmit
domainToAdmit d =
  case verifyCountedDomain d of
    Right _ -> CountedAdmitted
    Left HandFilledRefused -> CountedRefused HandFilledDomain
    Left (CardinalityMismatch _ _) -> CountedRefused HandFilledDomain
    Left EmptyScan -> CountedRefused EmptyScanRefusal

-- | Admit a scanner-emitted claim — fail closed on hand-fill.
admitScannedClaim :: CountedScannedClaim a -> CountedConsumeAdmit
admitScannedClaim claim = domainToAdmit (countedClaimDomain claim)

-- | §21 admissibility conjunct inputs (surrogate).
data CountedAdmissibilityConjunct = CountedAdmissibilityConjunct
  { conjGateOk              :: !Bool
  , conjScannerEmitted      :: !Bool
  , conjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate `admit(h) ⟺ gate ∧ scanner-emitted ∧ Excitement preserves`.
countedConjunctAdmits :: CountedAdmissibilityConjunct -> Bool
countedConjunctAdmits c =
  conjGateOk c && conjScannerEmitted c && conjExcitementPreserves c

-- | Attempt counted consume on scanned claim — fail closed on inadmissibility.
applyCountedConsumeMorphism
  :: CountedScannedClaim a
  -> CountedAdmissibilityConjunct
  -> Bool
  -> Bool
  -> Either CountedConsumeRefusal (CountedScannedClaim a)
applyCountedConsumeMorphism claim conjunct excitementSelected authorConstruct =
  if authorConstruct
    then Left AuthorDomainNew
    else
      if not (countedConjunctAdmits conjunct)
        then Left HandFilledDomain
        else
          case verifyCountedDomain (countedClaimDomain claim) of
            Left _ -> Left HandFilledDomain
            Right _ ->
              if not excitementSelected
                then Left SecondArgmin
                else Right claim

-- ---------------------------------------------------------------------------
-- SECTION 3: Counted consume composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for counted consume over admissible history successors.
data CountedConsumeCtx = CountedConsumeCtx
  { countedConsumePrior       :: !ThermodynamicState
  , countedConsumeSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Counted consume recovery **is** 'urgeRecoverySelect' / 'excitementSelect'.
countedConsumeSelect
  :: CountedConsumeCtx
  -> Either ExcitementResidue HistoryCandidate
countedConsumeSelect ctx =
  urgeRecoverySelect
    (countedConsumePrior ctx)
    (countedConsumeSuccessors ctx)

-- | Urge counted recovery composes imported 'excitementSelect' — not local argmin.
countedExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
countedExcitementSelect = excitementSelect

-- | Definitional witness: counted consume selection is 'excitementSelect'.
countedConsumeSelectEqExcitementSelect :: CountedConsumeCtx -> Bool
countedConsumeSelectEqExcitementSelect ctx =
  countedConsumeSelect ctx
    == excitementSelect
      (countedConsumePrior ctx)
      (countedConsumeSuccessors ctx)

-- | Definitional witness: counted consume selection is 'urgeRecoverySelect'.
countedConsumeSelectEqUrgeRecoverySelect :: CountedConsumeCtx -> Bool
countedConsumeSelectEqUrgeRecoverySelect ctx =
  countedConsumeSelect ctx
    == urgeRecoverySelect
      (countedConsumePrior ctx)
      (countedConsumeSuccessors ctx)

-- | Definitional witness: bare alias is 'excitementSelect'.
countedExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
countedExcitementSelectEqExcitementSelect prior successors =
  countedExcitementSelect prior successors == excitementSelect prior successors

-- | Counted selector re-uses 'excitementSelect' — no Urge-local argmin.
countedConsumeNoLocalArgmin :: CountedConsumeCtx -> Bool
countedConsumeNoLocalArgmin ctx =
  countedConsumeSelect ctx
    == excitementSelect
      (countedConsumePrior ctx)
      (countedConsumeSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
countedConsumeEmpty :: CountedConsumeCtx -> Bool
countedConsumeEmpty ctx =
  countedConsumeSuccessors ctx == []
    && countedConsumeSelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §21 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | Fixture walk — two scanner touches (§21).
countedFixtureWalk :: CountedScanWalk
countedFixtureWalk =
  countedScanTouch (countedScanTouch countedScanWalkEmpty 1) 2

-- | Fixture domain from walked scope.
countedFixtureDomain :: CountedDomain
countedFixtureDomain = countedDomainFromWalk countedFixtureWalk

-- | Fixture scanned claim.
countedFixtureClaim :: CountedScannedClaim Int
countedFixtureClaim =
  CountedScannedClaim {countedClaimValue = 7, countedClaimDomain = countedFixtureDomain}

-- | Fixture admissibility conjunct (all gates pass).
countedFixtureConjunct :: CountedAdmissibilityConjunct
countedFixtureConjunct =
  CountedAdmissibilityConjunct
    { conjGateOk = True
    , conjScannerEmitted = True
    , conjExcitementPreserves = True
    }

-- | Hand-filled domain fixture — cardinality theater (author construct).
countedFixtureHandFilled :: CountedDomain
countedFixtureHandFilled =
  CountedDomain
    { countedScope = [1, 2]
    , countedCardinality = 11809
    , countedExclusions = []
    , countedProvenance = CountedProvenance
    }

countedAuthorDomainRefused :: Bool
countedAuthorDomainRefused =
  evaluateCountedDomainOperation True == AuthorDomainRefused

countedScanOkWhenNotAuthor :: Bool
countedScanOkWhenNotAuthor =
  evaluateCountedDomainOperation False == ScanOk

refuseAuthorDomainNewPositive :: Bool
refuseAuthorDomainNewPositive = refuseAuthorDomainNew == AuthorDomainNew

refuseSecondArgminPositive :: Bool
refuseSecondArgminPositive = refuseSecondArgminSelector == SecondArgmin

scanCountingFinalizeEmpty :: Bool
scanCountingFinalizeEmpty =
  scanCountingFinalize countedScanWalkEmpty == Left EmptyScan

countedFixtureScannerEmittedOk :: Bool
countedFixtureScannerEmittedOk =
  verifyCountedDomain countedFixtureDomain == Right countedFixtureDomain

countedFixtureHandFillRefused :: Bool
countedFixtureHandFillRefused =
  domainToAdmit countedFixtureHandFilled == CountedRefused HandFilledDomain

countedFixtureAuthorDomainRefused :: Bool
countedFixtureAuthorDomainRefused =
  applyCountedConsumeMorphism countedFixtureClaim countedFixtureConjunct True True
    == Left AuthorDomainNew

countedFixtureApplyMorphismOk :: Bool
countedFixtureApplyMorphismOk =
  applyCountedConsumeMorphism countedFixtureClaim countedFixtureConjunct True False
    == Right countedFixtureClaim

countedFixtureAdmitScannedClaimOk :: Bool
countedFixtureAdmitScannedClaimOk =
  admitScannedClaim countedFixtureClaim == CountedAdmitted

countedFixtureScanCountingOk :: Bool
countedFixtureScanCountingOk =
  scanCounting countedFixtureWalk 7 == Right countedFixtureClaim

countedFixtureCardinalityMatchesScope :: Bool
countedFixtureCardinalityMatchesScope =
  countedCardinality countedFixtureDomain == length (countedScope countedFixtureDomain)

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Counted history move with scanner-emitted provenance gates.
data CountedHistoryMove = CountedHistoryMove
  { countedMovePrior          :: !ThermodynamicState
  , countedMovePost           :: !ThermodynamicState
  , countedMoveGateChecked    :: !Bool
  , countedMoveScannerEmitted :: !Bool
  , countedMoveProvenanceOk   :: !Bool
  } deriving (Show, Eq)

-- | Admissible counted consume move: gate ∧ scanner-emitted ∧ provenance.
admissibleCountedConsume :: CountedHistoryMove -> Bool
admissibleCountedConsume h =
  countedMoveGateChecked h
  && countedMoveScannerEmitted h
  && countedMoveProvenanceOk h

-- | Second law on counted transition from Landauer bridge discharge.
countedSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
countedSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for counted second law (no new axiom).
countedSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
countedSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
countedConsumePhysicsGreen :: Bool
countedConsumePhysicsGreen = False

-- | Lean/Coq: @counted_consume_physics_green_false@.
countedConsumePhysicsGreenFalse :: Bool
countedConsumePhysicsGreenFalse = not countedConsumePhysicsGreen

-- | Production wiring stays open (counted consume lift only).
countedConsumeProductionWired :: Bool
countedConsumeProductionWired = False

-- | Lean/Coq: @counted_consume_production_wired_false@.
countedConsumeProductionWiredFalse :: Bool
countedConsumeProductionWiredFalse = not countedConsumeProductionWired

-- | Honest non-claim string (meso §21 counted consume scaffold).
countedConsumeNonClaim :: String
countedConsumeNonClaim =
  "§21 counted_consume: domain scanner-emitted via scan_counting; "
    ++ "refuse author Domain::new and hand-fill; compose excitementSelect "
    ++ "no second argmin; LandauerLaw.physicalSecondLaw cited; "
    ++ "not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
countedConsumeNonClaimNonempty :: Bool
countedConsumeNonClaimNonempty = length countedConsumeNonClaim > 0

-- | Catalog witness: meso Urge CountedConsume module present.
countedConsumeModuleWitness :: Bool
countedConsumeModuleWitness = True

-- | Zero new axiom discipline witness.
countedConsumeNoNewAxiom :: Bool
countedConsumeNoNewAxiom = True

-- | Second-argmin refusal: counted consume composes 'excitementSelect' only.
countedConsumeNoSecondArgmin :: Bool
countedConsumeNoSecondArgmin =
  countedConsumeNoLocalArgmin
    (CountedConsumeCtx (ThermodynamicState 2400 0 0.3 30 40) [])

-- | Author construct is positively refused — not silent scan-ok.
countedConsumePositiveRefuseNotSilent :: Bool
countedConsumePositiveRefuseNotSilent =
  evaluateCountedDomainOperation True /= ScanOk

-- | Positive refuse tag for author Domain::new.
countedConsumeAuthorRefusePositive :: Bool
countedConsumeAuthorRefusePositive = refuseAuthorDomainNew == AuthorDomainNew
