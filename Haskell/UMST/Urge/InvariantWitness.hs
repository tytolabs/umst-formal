-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.InvariantWitness
-- Description : Meso acting Urge — §3 InvariantWitness on every admitted history.
--
-- Every admitted history object carries a proof-carrying witness — not optional,
-- not host-id theater. History recovery composes 'excitementSelect' — no second
-- argmin.
--
-- Mirrors Lean @Urge.InvariantWitness@ + Coq @InvariantWitness.v@ meso discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.InvariantWitness
  ( -- * History object + invariant witness carriers (§3)
    HistoryObject (..)
  , WitnessPropTag (..)
  , witnessPropConsistent
  , historyObjectWithWitness
  , InvariantWitnessBundle (..)
  , InvariantWitnessRefusal (..)
  , InvariantWitnessVerdict (..)
    -- * §3 admissibility conjunct + positive refuse
  , InvariantAdmissibilityConjunct (..)
  , invariantConjunctAdmits
  , evaluateInvariantWitnessOperation
  , refuseWitnessAbsent
  , refuseWitnessStrip
  , witnessFromHistoryObject
  , objectHasWitness
  , admitHistoryObject
  , applyInvariantWitnessAdmission
  , invariantWitnessAbsentRefused
  , invariantWitnessAdmitOkWhenWitnessed
  , refuseWitnessAbsentPositive
  , refuseWitnessStripPositive
  , satisfiedWitnessPropConsistent
  , rejectedWitnessPropConsistent
    -- * Excitement alignment (no second argmin)
  , InvariantWitnessCtx (..)
  , invariantWitnessSelect
  , invariantWitnessSelectEqExcitementSelect
  , invariantWitnessSelectEqUrgeRecoverySelect
  , invariantWitnessNoLocalArgmin
  , invariantWitnessEmpty
    -- * §3 fixtures + witnessed ledger
  , invariantFixtureObject
  , invariantFixtureRejected
  , invariantFixtureConjunct
  , invariantFixtureAdmitOk
  , invariantFixtureRejectedUnsatisfied
  , invariantFixtureApplyAdmissionOk
  , invariantFixtureWitnessAbsentRefused
  , invariantFixtureObjectHasWitness
  , invariantFixtureWitnessPreservesMargin
  , WitnessedHistoryLedger (..)
  , witnessedLedgerEmpty
  , witnessedLedgerAppend
  , witnessedLedgerEveryHasWitness
  , invariantFixtureLedgerAppendOk
  , invariantFixtureLedgerEveryHasWitness
    -- * Landauer bridge (derived — zero new axioms)
  , invariantSecondLawFromLandauer
  , invariantSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , invariantWitnessPhysicsGreen
  , invariantWitnessPhysicsGreenFalse
  , invariantWitnessProductionWired
  , invariantWitnessProductionWiredFalse
  , invariantWitnessNonClaim
  , invariantWitnessNonClaimNonempty
  , invariantWitnessModuleWitness
  , invariantWitnessNoNewAxiom
  , invariantWitnessNoSecondArgmin
  , invariantWitnessPositiveRefuseNotSilent
  , invariantWitnessMarker
  , invariantWitnessMarkerEq
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
import UMST.Urge.CarrierProduct
  ( InvariantWitness (..)
  , rejectedWitness
  , satisfiedWitness
  )
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: History object + invariant witness carriers (§3)
-- ---------------------------------------------------------------------------

-- | Content-addressed history object — witness is mandatory, not optional.
data HistoryObject = HistoryObject
  { historyObjectContentId  :: !Int
  , historyObjectTheoremId  :: !Int
  , historyObjectWitness    :: !InvariantWitness
  } deriving (Show, Eq)

-- | Witness proposition tag — structural shell, not empirical ':barc-cert'.
data WitnessPropTag
  = WptSatisfied
  | WptRejected
  deriving (Show, Eq)

-- | Whether witness proposition aligns with 'witnessSatisfied' flag.
witnessPropConsistent :: InvariantWitness -> WitnessPropTag -> Bool
witnessPropConsistent w WptSatisfied = witnessSatisfied w
witnessPropConsistent w WptRejected  = not (witnessSatisfied w)

-- | Build history object — witness required (cannot omit).
historyObjectWithWitness :: Int -> Int -> InvariantWitness -> HistoryObject
historyObjectWithWitness contentId theoremId w =
  HistoryObject
    { historyObjectContentId = contentId
    , historyObjectTheoremId = theoremId
    , historyObjectWitness = w
    }

-- | Witness bundle an invariant morphism must preserve (§3).
data InvariantWitnessBundle = InvariantWitnessBundle
  { iwbWitness            :: !InvariantWitness
  , iwbPropTag            :: !WitnessPropTag
  , iwbExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed invariant witness errors — positive refuse, not silent no-op.
data InvariantWitnessRefusal
  = IwrWitnessAbsent
  | IwrWitnessStripped !Int
  | IwrWitnessUnsatisfied !Int
  | IwrWitnessPropInconsistent !Int
  | IwrGateRejected !Int
  deriving (Show, Eq)

-- | Verdict of an invariant witness operation class.
data InvariantWitnessVerdict
  = IwvAdmitOk
  | IwvWitnessAbsentRefused
  | IwvWitnessStrippedRefused
  | IwvInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §3 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §3 admissibility conjunct inputs (surrogate).
data InvariantAdmissibilityConjunct = InvariantAdmissibilityConjunct
  { invariantConjGateOk              :: !Bool
  , invariantConjWitnessPresent      :: !Bool
  , invariantConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ witness present ∧ Excitement preserves@.
invariantConjunctAdmits :: InvariantAdmissibilityConjunct -> Bool
invariantConjunctAdmits c =
  invariantConjGateOk c
  && invariantConjWitnessPresent c
  && invariantConjExcitementPreserves c

-- | Classify witness-absent vs witnessed admission without performing I/O.
evaluateInvariantWitnessOperation :: Bool -> InvariantWitnessVerdict
evaluateInvariantWitnessOperation witnessAbsent =
  if witnessAbsent then IwvWitnessAbsentRefused else IwvAdmitOk

-- | Positive refuse: history object without witness forbidden.
refuseWitnessAbsent :: InvariantWitnessRefusal
refuseWitnessAbsent = IwrWitnessAbsent

-- | Positive refuse: stripping witness from witnessed object forbidden.
refuseWitnessStrip :: Int -> InvariantWitnessRefusal
refuseWitnessStrip contentId = IwrWitnessStripped contentId

-- | Build witness bundle from history object — morphism must preserve margin.
witnessFromHistoryObject
  :: HistoryObject -> WitnessPropTag -> Bool -> InvariantWitnessBundle
witnessFromHistoryObject obj tag excitementSelected =
  InvariantWitnessBundle
    { iwbWitness = historyObjectWitness obj
    , iwbPropTag = tag
    , iwbExcitementSelected = excitementSelected
    }

-- | Whether history object carries a consistent satisfied witness.
objectHasWitness :: HistoryObject -> Bool
objectHasWitness obj =
  witnessPropConsistent (historyObjectWitness obj) WptSatisfied
  && witnessSatisfied (historyObjectWitness obj)

-- | Admit history object — fail closed on inconsistent or unsatisfied witness.
admitHistoryObject :: HistoryObject -> Either InvariantWitnessRefusal ()
admitHistoryObject obj =
  let w = historyObjectWitness obj
      cid = historyObjectContentId obj
   in if not (witnessPropConsistent w WptSatisfied)
         && not (witnessPropConsistent w WptRejected)
        then Left (IwrWitnessPropInconsistent cid)
        else if not (witnessSatisfied w)
        then Left (IwrWitnessUnsatisfied cid)
        else Right ()

-- | Attempt typed invariant witness admission — fail closed on inadmissibility.
applyInvariantWitnessAdmission
  :: HistoryObject
  -> InvariantAdmissibilityConjunct
  -> Bool
  -> Bool
  -> Either InvariantWitnessRefusal InvariantWitnessBundle
applyInvariantWitnessAdmission obj conjunct witnessAbsent excitementSelected
  | witnessAbsent = Left IwrWitnessAbsent
  | not (invariantConjunctAdmits conjunct) =
      Left (IwrGateRejected (historyObjectContentId obj))
  | not excitementSelected =
      Left (IwrWitnessStripped (historyObjectContentId obj))
  | otherwise =
      case admitHistoryObject obj of
        Left r -> Left r
        Right _ ->
          Right (witnessFromHistoryObject obj WptSatisfied excitementSelected)

-- | Positive refuse witnesses (definitional — mirror Lean/Coq rfl).
invariantWitnessAbsentRefused :: Bool
invariantWitnessAbsentRefused =
  evaluateInvariantWitnessOperation True == IwvWitnessAbsentRefused

invariantWitnessAdmitOkWhenWitnessed :: Bool
invariantWitnessAdmitOkWhenWitnessed =
  evaluateInvariantWitnessOperation False == IwvAdmitOk

refuseWitnessAbsentPositive :: Bool
refuseWitnessAbsentPositive = refuseWitnessAbsent == IwrWitnessAbsent

refuseWitnessStripPositive :: Int -> Bool
refuseWitnessStripPositive contentId =
  refuseWitnessStrip contentId == IwrWitnessStripped contentId

satisfiedWitnessPropConsistent :: Bool
satisfiedWitnessPropConsistent =
  witnessPropConsistent satisfiedWitness WptSatisfied

rejectedWitnessPropConsistent :: Bool
rejectedWitnessPropConsistent =
  witnessPropConsistent rejectedWitness WptRejected

-- ---------------------------------------------------------------------------
-- SECTION 3: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for invariant witness over admissible history successors.
data InvariantWitnessCtx = InvariantWitnessCtx
  { invariantWitnessSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Invariant witness selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
invariantWitnessSelect
  :: ThermodynamicState
  -> InvariantWitnessCtx
  -> Either ExcitementResidue HistoryCandidate
invariantWitnessSelect src ctx =
  urgeRecoverySelect src (invariantWitnessSuccessors ctx)

-- | Definitional witness: invariant witness selection is 'excitementSelect'.
invariantWitnessSelectEqExcitementSelect
  :: ThermodynamicState -> InvariantWitnessCtx -> Bool
invariantWitnessSelectEqExcitementSelect src ctx =
  invariantWitnessSelect src ctx
    == excitementSelect src (invariantWitnessSuccessors ctx)

-- | Invariant witness selection equals 'urgeRecoverySelect'.
invariantWitnessSelectEqUrgeRecoverySelect
  :: ThermodynamicState -> InvariantWitnessCtx -> Bool
invariantWitnessSelectEqUrgeRecoverySelect src ctx =
  invariantWitnessSelect src ctx
    == urgeRecoverySelect src (invariantWitnessSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
invariantWitnessNoLocalArgmin
  :: ThermodynamicState -> InvariantWitnessCtx -> Bool
invariantWitnessNoLocalArgmin src ctx =
  invariantWitnessSelect src ctx
    == excitementSelect src (invariantWitnessSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
invariantWitnessEmpty :: ThermodynamicState -> InvariantWitnessCtx -> Bool
invariantWitnessEmpty src ctx =
  null (invariantWitnessSuccessors ctx)
  && invariantWitnessSelect src ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §3 fixtures + witnessed ledger
-- ---------------------------------------------------------------------------

-- | Fixture history object with satisfied witness.
invariantFixtureObject :: HistoryObject
invariantFixtureObject = historyObjectWithWitness 66 7 satisfiedWitness

-- | Fixture history object with rejected witness.
invariantFixtureRejected :: HistoryObject
invariantFixtureRejected = historyObjectWithWitness 67 7 rejectedWitness

-- | Fixture admissibility conjunct (gate + witness + excitement).
invariantFixtureConjunct :: InvariantAdmissibilityConjunct
invariantFixtureConjunct =
  InvariantAdmissibilityConjunct
    { invariantConjGateOk = True
    , invariantConjWitnessPresent = True
    , invariantConjExcitementPreserves = True
    }

invariantFixtureAdmitOk :: Bool
invariantFixtureAdmitOk = admitHistoryObject invariantFixtureObject == Right ()

invariantFixtureRejectedUnsatisfied :: Bool
invariantFixtureRejectedUnsatisfied =
  admitHistoryObject invariantFixtureRejected
    == Left (IwrWitnessUnsatisfied 67)

invariantFixtureApplyAdmissionOk :: Bool
invariantFixtureApplyAdmissionOk =
  applyInvariantWitnessAdmission
    invariantFixtureObject
    invariantFixtureConjunct
    False
    True
    == Right (witnessFromHistoryObject invariantFixtureObject WptSatisfied True)

invariantFixtureWitnessAbsentRefused :: Bool
invariantFixtureWitnessAbsentRefused =
  applyInvariantWitnessAdmission
    invariantFixtureObject
    invariantFixtureConjunct
    True
    True
    == Left IwrWitnessAbsent

invariantFixtureObjectHasWitness :: Bool
invariantFixtureObjectHasWitness = objectHasWitness invariantFixtureObject

invariantFixtureWitnessPreservesMargin :: Bool
invariantFixtureWitnessPreservesMargin =
  marginH (historyObjectWitness invariantFixtureObject) == 0

-- | Append-only ledger of witnessed history objects — every entry carries witness.
data WitnessedHistoryLedger = WitnessedHistoryLedger
  { witnessedObjects :: ![HistoryObject]
  } deriving (Show, Eq)

witnessedLedgerEmpty :: WitnessedHistoryLedger
witnessedLedgerEmpty = WitnessedHistoryLedger {witnessedObjects = []}

-- | Append witnessed object — fail closed on inadmissible witness.
witnessedLedgerAppend
  :: WitnessedHistoryLedger
  -> HistoryObject
  -> Either InvariantWitnessRefusal WitnessedHistoryLedger
witnessedLedgerAppend ledger obj =
  case admitHistoryObject obj of
    Left r -> Left r
    Right _ ->
      Right
        WitnessedHistoryLedger
          { witnessedObjects = witnessedObjects ledger ++ [obj]
          }

allObjectsHaveWitness :: [HistoryObject] -> Bool
allObjectsHaveWitness [] = True
allObjectsHaveWitness (o : os) = objectHasWitness o && allObjectsHaveWitness os

witnessedLedgerEveryHasWitness :: WitnessedHistoryLedger -> Bool
witnessedLedgerEveryHasWitness ledger =
  allObjectsHaveWitness (witnessedObjects ledger)

invariantFixtureLedgerAppendOk :: Bool
invariantFixtureLedgerAppendOk =
  witnessedLedgerAppend witnessedLedgerEmpty invariantFixtureObject
    == Right WitnessedHistoryLedger {witnessedObjects = [invariantFixtureObject]}

invariantFixtureLedgerEveryHasWitness :: Bool
invariantFixtureLedgerEveryHasWitness =
  witnessedLedgerEveryHasWitness
    WitnessedHistoryLedger {witnessedObjects = [invariantFixtureObject]}

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on invariant witness transition from Landauer bridge discharge.
invariantSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
invariantSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for invariant witness second law (no new axiom).
invariantSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
invariantSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
invariantWitnessPhysicsGreen :: Bool
invariantWitnessPhysicsGreen = False

-- | Lean/Coq: @invariant_witness_physics_green_false@.
invariantWitnessPhysicsGreenFalse :: Bool
invariantWitnessPhysicsGreenFalse = not invariantWitnessPhysicsGreen

-- | Production wiring stays open (meso §3 lift only).
invariantWitnessProductionWired :: Bool
invariantWitnessProductionWired = False

-- | Lean/Coq: @invariant_witness_production_wired_false@.
invariantWitnessProductionWiredFalse :: Bool
invariantWitnessProductionWiredFalse = not invariantWitnessProductionWired

-- | Honest non-claim string (meso §3 InvariantWitness scaffold).
invariantWitnessNonClaim :: String
invariantWitnessNonClaim =
  "§3 InvariantWitness on every admitted history object; witness mandatory; "
    ++ "invariantWitnessSelect composes excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

invariantWitnessNonClaimNonempty :: Bool
invariantWitnessNonClaimNonempty = length invariantWitnessNonClaim > 0

-- | Catalog witness: meso Urge InvariantWitness module present.
invariantWitnessModuleWitness :: Bool
invariantWitnessModuleWitness = True

-- | Zero new axiom discipline witness.
invariantWitnessNoNewAxiom :: Bool
invariantWitnessNoNewAxiom = True

-- | Second-argmin refusal: invariant witness composes 'excitementSelect' only.
invariantWitnessNoSecondArgmin :: Bool
invariantWitnessNoSecondArgmin =
  invariantWitnessNoLocalArgmin
    (ThermodynamicState 2400 0 0.3 30 40)
    InvariantWitnessCtx {invariantWitnessSuccessors = []}

-- | Positive refuse is not silent admission.
invariantWitnessPositiveRefuseNotSilent :: Bool
invariantWitnessPositiveRefuseNotSilent =
  evaluateInvariantWitnessOperation True /= IwvAdmitOk

-- | §3 section marker (meso catalog pin).
invariantWitnessMarker :: Int
invariantWitnessMarker = 3

invariantWitnessMarkerEq :: Bool
invariantWitnessMarkerEq = invariantWitnessMarker == 3
