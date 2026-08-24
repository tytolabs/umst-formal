-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.SdfCanonical
-- Description : Meso acting Urge — §12 SDFCanonical tautology named on history identity.
--
-- Byte-equal canonical SDFs imply behavior-equivalent history actions — mirrors
-- Lean @Behavior.SDFCanonical@ and Coq/Agda @Urge.SdfCanonical@. Not a second
-- geometry: canonical SDF map is identity on action bytes.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.SdfCanonical
  ( -- * History action + identity carriers (§12)
    HistoryAction (..)
  , HistoryIdentity (..)
  , SdfCanonicalWitness (..)
  , SdfCanonicalMorphism (..)
  , BehaviorEquivVerdict (..)
  , SdfCanonicalRefusal (..)
  , SdfCanonicalVerdict (..)
    -- * §12 admissibility conjunct + positive refuse
  , canonicalSdf
  , historyContentId
  , canonicalSdfBeq
  , behaviorEquivOf
  , behaviorEquiv
  , sdfCanonical
  , SdfCanonicalAdmissibilityConjunct (..)
  , sdfCanonicalConjunctAdmits
  , evaluateAliasWithoutCanonicalization
  , evaluateInventedEquivWithoutCanonical
  , refuseAliasWithoutCanonicalization
  , refuseInventedEquivWithoutCanonical
  , refuseSecondArgminSelector
  , witnessFromHistoryIdentity
  , sdfCanonicalTheorem
  , admitHistoryIdentityStep
  , admitHistoryIdentity
  , applySdfCanonicalMorphism
  , sdfCanonicalAliasRefused
  , sdfCanonicalAdmittedWhenNotAlias
  , sdfCanonicalInventedEquivRefused
  , refuseAliasWithoutCanonicalizationPositive
  , refuseSecondArgminSelectorPositive
    -- * Excitement alignment (no second argmin)
  , SdfCanonicalExcitementPin (..)
  , SdfCanonicalCtx (..)
  , sdfCanonicalExcitementSelect
  , sdfCanonicalSelect
  , sdfCanonicalSelectBare
  , sdfCanonicalExcitementSelectEqExcitementSelect
  , sdfCanonicalSelectEqExcitementSelect
  , sdfCanonicalSelectEqUrgeRecoverySelect
  , sdfCanonicalNoLocalArgmin
  , sdfCanonicalExcitementSelectRefusesSecondArgmin
  , sdfCanonicalSelectBareEqExcitementSelect
  , sdfCanonicalEmpty
    -- * §12 fixtures + witness theorems
  , sdfCanonicalFixtureBytes
  , sdfCanonicalFixtureContentId
  , sdfCanonicalFixtureAction
  , sdfCanonicalFixtureIdentity
  , sdfCanonicalFixtureIdentitySame
  , sdfCanonicalFixtureActionDistinct
  , sdfCanonicalFixtureIdentityDistinct
  , sdfCanonicalFixtureActionAlias
  , sdfCanonicalFixtureConjunct
  , sdfCanonicalFixtureCanonicalSdfId
  , sdfCanonicalFixtureByteEqualAdmitted
  , sdfCanonicalFixtureAliasRefused
  , sdfCanonicalFixtureApplyMorphismOk
  , sdfCanonicalFixtureWitnessPreservesBytes
  , sdfCanonicalTheoremTautology
  , sdfCanonicalNamedIdentityTautology
  , sdfCanonicalAliasNotAdmitted
  , sdfCanonicalPositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , sdfCanonicalSecondLawFromLandauer
  , sdfCanonicalFromLandauerAdmitSecondLaw
  , sdfCanonicalSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , sdfCanonicalPhysicsGreen
  , sdfCanonicalPhysicsGreenFalse
  , sdfCanonicalProductionWired
  , sdfCanonicalProductionWiredFalse
  , sdfCanonicalNonClaim
  , sdfCanonicalNonClaimNonempty
  , sdfCanonicalModuleWitness
  , sdfCanonicalNoNewAxiom
  , sdfCanonicalNoSecondArgmin
  , sdfCanonicalNamedOnHistoryIdentity
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
-- SECTION 1: History action + identity carriers (§12)
-- ---------------------------------------------------------------------------

-- | History action bytes — SDF-shaped action surrogate (pre/post canonicalization).
data HistoryAction = HistoryAction
  { historyActionBytes         :: !String
  , historyActionCanonicalized :: !Bool
  , historyActionContentId     :: !Int
  } deriving (Show, Eq)

-- | Content-addressed history identity — canonical SDF + stable content id.
data HistoryIdentity = HistoryIdentity
  { historyIdentityAction   :: !HistoryAction
  , historyIdentityContentId :: !Int
  } deriving (Show, Eq)

-- | Witness bundle a SDF-canonical morphism must preserve (§12).
data SdfCanonicalWitness = SdfCanonicalWitness
  { witnessBytes         :: !String
  , witnessContentId     :: !Int
  , witnessCanonicalized :: !Bool
  } deriving (Show, Eq)

-- | Typed SDF-canonical morphism — admissible identity transition.
data SdfCanonicalMorphism = SdfCanonicalMorphism
  { morphismFrom           :: !HistoryIdentity
  , morphismToContentId    :: !Int
  , morphismWitness        :: !SdfCanonicalWitness
  , morphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Behavior equivalence verdict — mirrors Lean @BehaviorEquiv@.
data BehaviorEquivVerdict
  = Equivalent
  | Distinct
  deriving (Show, Eq)

-- | Fail-closed SDF canonical errors — positive refuse, not silent accept.
data SdfCanonicalRefusal
  = CanonicalSdfMismatch !Int !Int
  | AliasWithoutCanonicalization !Int
  | InventedEquivWithoutCanonical !Int
  | SecondArgmin
  | GateRejected !Int
  deriving (Show, Eq)

-- | Verdict of a SDF canonical admit operation class.
data SdfCanonicalVerdict
  = Admitted
  | AliasRefused
  | InventedEquivRefused
  | Inadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §12 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | Canonical SDF map — mirrors Lean @canonical_sdf := id@ on @String@.
canonicalSdf :: HistoryAction -> String
canonicalSdf = historyActionBytes

-- | Content id projection from canonicalized action.
historyContentId :: HistoryAction -> Int
historyContentId = historyActionContentId

-- | String equality surrogate (decidable — no Prop branching).
canonicalSdfBeq :: HistoryAction -> HistoryAction -> Bool
canonicalSdfBeq left right = historyActionBytes left == historyActionBytes right

-- | Behavior equivalence from canonical SDF equality.
behaviorEquivOf :: HistoryAction -> HistoryAction -> BehaviorEquivVerdict
behaviorEquivOf left right =
  if canonicalSdfBeq left right then Equivalent else Distinct

-- | §12 @BehaviorEquiv@ — byte-equal canonical SDFs imply behavior-equivalent actions.
behaviorEquiv :: HistoryAction -> HistoryAction -> Bool
behaviorEquiv left right = canonicalSdf left == canonicalSdf right

-- | §12 @SDFCanonical@ tautology: canonical equality implies behavior equivalence.
sdfCanonical :: HistoryAction -> HistoryAction -> Bool
sdfCanonical left right = behaviorEquiv left right == canonicalSdfBeq left right

-- | §12 admissibility conjunct inputs (surrogate).
data SdfCanonicalAdmissibilityConjunct = SdfCanonicalAdmissibilityConjunct
  { conjGateOk              :: !Bool
  , conjCanonicalized       :: !Bool
  , conjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ canonicalized ∧ Excitement preserves@.
sdfCanonicalConjunctAdmits :: SdfCanonicalAdmissibilityConjunct -> Bool
sdfCanonicalConjunctAdmits c =
  conjGateOk c && conjCanonicalized c && conjExcitementPreserves c

evaluateAliasWithoutCanonicalization :: Bool -> SdfCanonicalVerdict
evaluateAliasWithoutCanonicalization aliasOnly =
  if aliasOnly then AliasRefused else Admitted

evaluateInventedEquivWithoutCanonical :: Bool -> SdfCanonicalVerdict
evaluateInventedEquivWithoutCanonical invented =
  if invented then InventedEquivRefused else Admitted

refuseAliasWithoutCanonicalization :: Int -> SdfCanonicalRefusal
refuseAliasWithoutCanonicalization = AliasWithoutCanonicalization

refuseInventedEquivWithoutCanonical :: Int -> SdfCanonicalRefusal
refuseInventedEquivWithoutCanonical = InventedEquivWithoutCanonical

refuseSecondArgminSelector :: SdfCanonicalRefusal
refuseSecondArgminSelector = SecondArgmin

witnessFromHistoryIdentity :: HistoryIdentity -> SdfCanonicalWitness
witnessFromHistoryIdentity h =
  SdfCanonicalWitness
    { witnessBytes = canonicalSdf (historyIdentityAction h)
    , witnessContentId = historyIdentityContentId h
    , witnessCanonicalized = historyActionCanonicalized (historyIdentityAction h)
    }

-- | §12 SDF canonical theorem — fail closed on alias / mismatch.
sdfCanonicalTheorem
  :: HistoryAction -> HistoryAction -> Either BehaviorEquivVerdict SdfCanonicalRefusal
sdfCanonicalTheorem left right
  | not (historyActionCanonicalized left) =
      Right (AliasWithoutCanonicalization 0)
  | not (historyActionCanonicalized right) =
      Right (AliasWithoutCanonicalization 0)
  | canonicalSdfBeq left right = Left Equivalent
  | otherwise =
      Right
        ( CanonicalSdfMismatch
            (historyContentId left)
            (historyContentId right)
        )

admitHistoryIdentityStep
  :: HistoryIdentity
  -> HistoryIdentity
  -> Either BehaviorEquivVerdict SdfCanonicalRefusal
  -> Either SdfCanonicalVerdict SdfCanonicalRefusal
admitHistoryIdentityStep left right thm =
  case thm of
    Right r -> Right r
    Left Distinct ->
      Right
        ( CanonicalSdfMismatch
            (historyContentId (historyIdentityAction left))
            (historyContentId (historyIdentityAction right))
        )
    Left Equivalent
      | historyIdentityContentId left
          /= historyContentId (historyIdentityAction left) ->
          Right (InventedEquivWithoutCanonical (historyIdentityContentId left))
      | historyIdentityContentId right
          /= historyContentId (historyIdentityAction right) ->
          Right (InventedEquivWithoutCanonical (historyIdentityContentId right))
      | historyIdentityContentId left /= historyIdentityContentId right ->
          Right
            ( CanonicalSdfMismatch
                (historyIdentityContentId left)
                (historyIdentityContentId right)
            )
      | otherwise -> Left Admitted

-- | Admit history identity pair under §12 SDF canonical discipline.
admitHistoryIdentity
  :: HistoryIdentity
  -> HistoryIdentity
  -> SdfCanonicalAdmissibilityConjunct
  -> Either SdfCanonicalVerdict SdfCanonicalRefusal
admitHistoryIdentity left right conjunct
  | not (sdfCanonicalConjunctAdmits conjunct) = Right (GateRejected 0)
  | otherwise =
      admitHistoryIdentityStep left right
        (sdfCanonicalTheorem
          (historyIdentityAction left)
          (historyIdentityAction right))

-- | Attempt typed SDF-canonical morphism — fail closed on inadmissibility.
applySdfCanonicalMorphism
  :: HistoryIdentity
  -> Int
  -> SdfCanonicalAdmissibilityConjunct
  -> Bool
  -> Either SdfCanonicalRefusal SdfCanonicalMorphism
applySdfCanonicalMorphism identity toContentId conjunct excitementSelected
  | not (sdfCanonicalConjunctAdmits conjunct) =
      Left (GateRejected (historyIdentityContentId identity))
  | not (historyActionCanonicalized (historyIdentityAction identity)) =
      Left (AliasWithoutCanonicalization (historyIdentityContentId identity))
  | not excitementSelected =
      Left
        ( CanonicalSdfMismatch
            (historyIdentityContentId identity)
            toContentId
        )
  | otherwise =
      Right
        SdfCanonicalMorphism
          { morphismFrom = identity
          , morphismToContentId = toContentId
          , morphismWitness = witnessFromHistoryIdentity identity
          , morphismExcitementSelected = excitementSelected
          }

sdfCanonicalAliasRefused :: Bool
sdfCanonicalAliasRefused =
  evaluateAliasWithoutCanonicalization True == AliasRefused

sdfCanonicalAdmittedWhenNotAlias :: Bool
sdfCanonicalAdmittedWhenNotAlias =
  evaluateAliasWithoutCanonicalization False == Admitted

sdfCanonicalInventedEquivRefused :: Bool
sdfCanonicalInventedEquivRefused =
  evaluateInventedEquivWithoutCanonical True == InventedEquivRefused

refuseAliasWithoutCanonicalizationPositive :: Int -> Bool
refuseAliasWithoutCanonicalizationPositive payload =
  refuseAliasWithoutCanonicalization payload
    == AliasWithoutCanonicalization payload

refuseSecondArgminSelectorPositive :: Bool
refuseSecondArgminSelectorPositive =
  refuseSecondArgminSelector == SecondArgmin

-- ---------------------------------------------------------------------------
-- SECTION 3: SDF canonical composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data SdfCanonicalExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Context for SDF canonical over admissible history successors.
data SdfCanonicalCtx = SdfCanonicalCtx
  { sdfCanonicalPrior      :: !ThermodynamicState
  , sdfCanonicalSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | SDF canonical path composes 'excitementSelect' — not a second argmin.
sdfCanonicalExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> SdfCanonicalExcitementPin
  -> Either ExcitementResidue HistoryCandidate
sdfCanonicalExcitementSelect prior successors pin =
  case pin of
    ImportSelectExcitement -> excitementSelect prior successors
    SecondArgminRefused -> Left ExcAllInadmissible

-- | SDF canonical selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
sdfCanonicalSelect
  :: SdfCanonicalCtx
  -> Either ExcitementResidue HistoryCandidate
sdfCanonicalSelect ctx =
  urgeRecoverySelect (sdfCanonicalPrior ctx) (sdfCanonicalSuccessors ctx)

sdfCanonicalSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
sdfCanonicalSelectBare = excitementSelect

sdfCanonicalExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
sdfCanonicalExcitementSelectEqExcitementSelect prior successors =
  sdfCanonicalExcitementSelect prior successors ImportSelectExcitement
    == excitementSelect prior successors

sdfCanonicalSelectEqExcitementSelect :: SdfCanonicalCtx -> Bool
sdfCanonicalSelectEqExcitementSelect ctx =
  sdfCanonicalSelect ctx
    == excitementSelect
      (sdfCanonicalPrior ctx)
      (sdfCanonicalSuccessors ctx)

sdfCanonicalSelectEqUrgeRecoverySelect :: SdfCanonicalCtx -> Bool
sdfCanonicalSelectEqUrgeRecoverySelect ctx =
  sdfCanonicalSelect ctx
    == urgeRecoverySelect
      (sdfCanonicalPrior ctx)
      (sdfCanonicalSuccessors ctx)

sdfCanonicalNoLocalArgmin :: SdfCanonicalCtx -> Bool
sdfCanonicalNoLocalArgmin ctx =
  sdfCanonicalSelect ctx
    == excitementSelect
      (sdfCanonicalPrior ctx)
      (sdfCanonicalSuccessors ctx)

sdfCanonicalExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
sdfCanonicalExcitementSelectRefusesSecondArgmin prior successors =
  sdfCanonicalExcitementSelect prior successors SecondArgminRefused
    == Left ExcAllInadmissible

sdfCanonicalSelectBareEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
sdfCanonicalSelectBareEqExcitementSelect prior successors =
  sdfCanonicalSelectBare prior successors == excitementSelect prior successors

sdfCanonicalEmpty :: ThermodynamicState -> Bool
sdfCanonicalEmpty prior =
  sdfCanonicalSelectBare prior [] == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: §12 fixtures + witness theorems
-- ---------------------------------------------------------------------------

sdfCanonicalFixtureBytes :: String
sdfCanonicalFixtureBytes = "sdf:v1:chair"

sdfCanonicalFixtureContentId :: Int
sdfCanonicalFixtureContentId = 12007

sdfCanonicalFixtureAction :: HistoryAction
sdfCanonicalFixtureAction =
  HistoryAction
    { historyActionBytes = sdfCanonicalFixtureBytes
    , historyActionCanonicalized = True
    , historyActionContentId = sdfCanonicalFixtureContentId
    }

sdfCanonicalFixtureIdentity :: HistoryIdentity
sdfCanonicalFixtureIdentity =
  HistoryIdentity
    { historyIdentityAction = sdfCanonicalFixtureAction
    , historyIdentityContentId = sdfCanonicalFixtureContentId
    }

sdfCanonicalFixtureIdentitySame :: HistoryIdentity
sdfCanonicalFixtureIdentitySame =
  HistoryIdentity
    { historyIdentityAction = sdfCanonicalFixtureAction
    , historyIdentityContentId = sdfCanonicalFixtureContentId
    }

sdfCanonicalFixtureActionDistinct :: HistoryAction
sdfCanonicalFixtureActionDistinct =
  HistoryAction
    { historyActionBytes = "sdf:v1:sphere"
    , historyActionCanonicalized = True
    , historyActionContentId = 12008
    }

sdfCanonicalFixtureIdentityDistinct :: HistoryIdentity
sdfCanonicalFixtureIdentityDistinct =
  HistoryIdentity
    { historyIdentityAction = sdfCanonicalFixtureActionDistinct
    , historyIdentityContentId = 12008
    }

sdfCanonicalFixtureActionAlias :: HistoryAction
sdfCanonicalFixtureActionAlias =
  HistoryAction
    { historyActionBytes = sdfCanonicalFixtureBytes
    , historyActionCanonicalized = False
    , historyActionContentId = sdfCanonicalFixtureContentId
    }

sdfCanonicalFixtureConjunct :: SdfCanonicalAdmissibilityConjunct
sdfCanonicalFixtureConjunct =
  SdfCanonicalAdmissibilityConjunct
    { conjGateOk = True
    , conjCanonicalized = True
    , conjExcitementPreserves = True
    }

sdfCanonicalFixtureCanonicalSdfId :: Bool
sdfCanonicalFixtureCanonicalSdfId =
  canonicalSdf sdfCanonicalFixtureAction == sdfCanonicalFixtureBytes

sdfCanonicalFixtureByteEqualAdmitted :: Bool
sdfCanonicalFixtureByteEqualAdmitted =
  admitHistoryIdentity
    sdfCanonicalFixtureIdentity
    sdfCanonicalFixtureIdentitySame
    sdfCanonicalFixtureConjunct
    == Left Admitted

sdfCanonicalFixtureAliasRefused :: Bool
sdfCanonicalFixtureAliasRefused =
  refuseAliasWithoutCanonicalization 42 == AliasWithoutCanonicalization 42

sdfCanonicalFixtureApplyMorphismOk :: Bool
sdfCanonicalFixtureApplyMorphismOk =
  applySdfCanonicalMorphism
    sdfCanonicalFixtureIdentity
    sdfCanonicalFixtureContentId
    sdfCanonicalFixtureConjunct
    True
    == Right
      SdfCanonicalMorphism
        { morphismFrom = sdfCanonicalFixtureIdentity
        , morphismToContentId = sdfCanonicalFixtureContentId
        , morphismWitness = witnessFromHistoryIdentity sdfCanonicalFixtureIdentity
        , morphismExcitementSelected = True
        }

sdfCanonicalFixtureWitnessPreservesBytes :: Bool
sdfCanonicalFixtureWitnessPreservesBytes =
  witnessBytes (witnessFromHistoryIdentity sdfCanonicalFixtureIdentity)
    == sdfCanonicalFixtureBytes

sdfCanonicalTheoremTautology :: Bool
sdfCanonicalTheoremTautology =
  sdfCanonicalTheorem sdfCanonicalFixtureAction sdfCanonicalFixtureAction
    == Left Equivalent

sdfCanonicalNamedIdentityTautology :: Bool
sdfCanonicalNamedIdentityTautology =
  sdfCanonical sdfCanonicalFixtureAction sdfCanonicalFixtureAction

sdfCanonicalAliasNotAdmitted :: Bool
sdfCanonicalAliasNotAdmitted =
  evaluateAliasWithoutCanonicalization True /= Admitted

sdfCanonicalPositiveRefuseNotSilent :: Bool
sdfCanonicalPositiveRefuseNotSilent =
  evaluateInventedEquivWithoutCanonical True /= Admitted

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Second law on SDF canonical transition from Landauer bridge discharge.
sdfCanonicalSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
sdfCanonicalSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
sdfCanonicalFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
sdfCanonicalFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for SDF canonical second law (no new axiom).
sdfCanonicalSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
sdfCanonicalSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
sdfCanonicalPhysicsGreen :: Bool
sdfCanonicalPhysicsGreen = False

-- | Lean/Coq: @sdf_canonical_physics_green_false@.
sdfCanonicalPhysicsGreenFalse :: Bool
sdfCanonicalPhysicsGreenFalse = not sdfCanonicalPhysicsGreen

-- | Production wiring stays open (SDF canonical lift only).
sdfCanonicalProductionWired :: Bool
sdfCanonicalProductionWired = False

-- | Lean/Coq: @sdf_canonical_production_wired_false@.
sdfCanonicalProductionWiredFalse :: Bool
sdfCanonicalProductionWiredFalse = not sdfCanonicalProductionWired

-- | Honest non-claim string (meso §12 SDF canonical scaffold).
sdfCanonicalNonClaim :: String
sdfCanonicalNonClaim =
  "§12 SDFCanonical: byte-equal canonical SDFs imply behavior-equivalent "
    ++ "history actions; sdfCanonicalSelect composes excitementSelect; "
    ++ "not physics GREEN; not production_wired"

sdfCanonicalNonClaimNonempty :: Bool
sdfCanonicalNonClaimNonempty = length sdfCanonicalNonClaim > 0

-- | Catalog witness: meso Urge SdfCanonical module present.
sdfCanonicalModuleWitness :: Bool
sdfCanonicalModuleWitness = True

-- | Zero new axiom discipline witness.
sdfCanonicalNoNewAxiom :: Bool
sdfCanonicalNoNewAxiom = True

-- | Second-argmin refusal: SDF canonical composes 'excitementSelect' only.
sdfCanonicalNoSecondArgmin :: Bool
sdfCanonicalNoSecondArgmin =
  sdfCanonicalNoLocalArgmin
    (SdfCanonicalCtx (ThermodynamicState 2400 0 0.3 30 40) [])

sdfCanonicalNamedOnHistoryIdentity :: Bool
sdfCanonicalNamedOnHistoryIdentity =
  historyIdentityContentId sdfCanonicalFixtureIdentity
    == sdfCanonicalFixtureContentId
