-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.SignedPropagate
-- Description : Meso acting Urge — §4 propagation of signed stamped witnessed states.
--
-- Stamp @T@ required; witness retained; unsigned propagation refused — not silent
-- accept. Composes 'excitementSelect' — no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' typed morphism discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms.
module UMST.Urge.SignedPropagate
  ( -- * Signed stamped witnessed carriers (§4)
    SignedPropagateWallStamp (..)
  , SignedStampedWitnessState (..)
  , SignedPropagationStep (..)
  , SignedPropagateWitness (..)
  , SignedPropagateMorphism (..)
  , SignedPropagateRefusal (..)
  , SignedPropagateVerdict (..)
    -- * §4 admissibility conjunct + positive refuse
  , SignedAdmissibilityConjunct (..)
  , wallStampOk
  , witnessPresent
  , signedConjunctAdmits
  , evaluateSignedPropagateOperation
  , refuseUnsignedPropagation
  , witnessFromSignedState
  , signedAddOk
  , propagateSignedState
  , applySignedPropagateMorphism
    -- * Positive refuse witnesses
  , signedPropagateUnsignedRefused
  , signedPropagateMorphismOkWhenNotUnsigned
  , refuseUnsignedPropagationPositive
    -- * Excitement alignment (no second argmin)
  , SignedPropagateExcitementComposePin (..)
  , SignedPropagateCtx (..)
  , signedPropagateSelect
  , urgeSignedPropagateSelect
  , signedPropagateSelectEqExcitementSelect
  , signedPropagateSelectEqUrgeSignedPropagateSelect
  , signedPropagateNoLocalArgmin
  , signedPropagateExcitementSelect
  , signedPropagateExcitementSelectEqExcitementSelect
  , signedPropagateExcitementSelectRefusesSecondArgmin
  , signedPropagateEmpty
  , SignedPropagateComposeRefusal (..)
  , refuseUnsignedPropagationTag
  , refuseSecondArgmin
    -- * §4 fixtures + witness theorems
  , signedFixtureStamp
  , signedFixturePostStamp
  , signedFixtureState
  , signedFixtureStep
  , signedFixtureConjunct
  , signedFixturePostState
  , signedFixtureUnsignedRefused
  , signedFixturePropagateOk
  , signedFixtureApplyMorphismOk
  , signedFixtureUnsignedState
  , signedFixtureUnsignedPropagationRefused
  , signedFixtureWitnessDropStep
  , signedFixtureWitnessDropRefused
  , signedFixtureWitnessPreservesStamp
  , signedFixtureWallStampOk
  , signedFixtureWitnessPresent
  , signedPropagatePositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , SignedPropagateHistoryMove (..)
  , admissibleSignedPropagateHistoryMove
  , SignedPropagateTransition (..)
  , signedPropagateSecondLaw
  , PhysicalSignedPropagateBridge (..)
  , signedPropagateSecondLawFromPhysical
  , admissibleSignedPropagateHistoryMoveFromPhysical
  , landauerAnchorCited
    -- * Honesty flags + catalog witnesses
  , signedPropagatePhysicsGreen
  , signedPropagatePhysicsGreenFalse
  , signedPropagateProductionWired
  , signedPropagateProductionWiredFalse
  , signedPropagateNonClaim
  , signedPropagateNonClaimNonempty
  , signedPropagateModuleWitness
  , signedPropagateNoNewAxiom
  , signedPropagateNoSecondArgmin
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

-- ---------------------------------------------------------------------------
-- SECTION 1: Signed stamped witnessed carriers (§4)
-- ---------------------------------------------------------------------------

-- | Wall ISO chronology stamp surrogate — 'observed_at_wall' must contain @T@.
data SignedPropagateWallStamp = SignedPropagateWallStamp
  { signedWallSeq  :: !Int
  , signedWallHasT :: !Bool
  } deriving (Show, Eq)

-- | Signed payload surrogate on the propagation carrier.
data SignedStampedWitnessState = SignedStampedWitnessState
  { signedValue         :: !Int
  , signedStamp         :: !SignedPropagateWallStamp
  , signedWitnessBits   :: !Int
  } deriving (Show, Eq)

-- | One admissible propagation step — signed delta + post stamp/witness.
data SignedPropagationStep = SignedPropagationStep
  { signedDelta           :: !Int
  , signedPostStamp       :: !SignedPropagateWallStamp
  , signedPostWitnessBits :: !Int
  } deriving (Show, Eq)

-- | Witness bundle a propagation morphism must preserve (§4).
data SignedPropagateWitness = SignedPropagateWitness
  { signedWitnessStamp     :: !SignedPropagateWallStamp
  , signedWitnessBitBudget :: !Int
  } deriving (Show, Eq)

-- | Typed propagation morphism — admissible signed transition, not unsigned carry.
data SignedPropagateMorphism = SignedPropagateMorphism
  { signedMorphismFrom               :: !SignedStampedWitnessState
  , signedMorphismTo                 :: !SignedStampedWitnessState
  , signedMorphismWitness            :: !SignedPropagateWitness
  , signedMorphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | Fail-closed propagation errors — positive refuse, not silent no-op.
data SignedPropagateRefusal
  = SprPriorStampInvalid !Int
  | SprPostStampInvalid !Int
  | SprUnsignedPropagationRefused
  | SprWitnessDropped !Int !Int
  | SprSignedOverflow
  | SprGateRejected !Int
  deriving (Show, Eq)

-- | Verdict of a propagation operation class.
data SignedPropagateVerdict
  = SpvMorphismOk
  | SpvUnsignedPropagationRefused
  | SpvInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §4 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §4 admissibility conjunct inputs (surrogate).
data SignedAdmissibilityConjunct = SignedAdmissibilityConjunct
  { signedConjGateOk              :: !Bool
  , signedConjStampOk             :: !Bool
  , signedConjWitnessPresent      :: !Bool
  , signedConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Whether wall stamp passes minimal ISO @T@ honesty.
wallStampOk :: SignedPropagateWallStamp -> Bool
wallStampOk s = signedWallHasT s

-- | Whether witness is present for propagation (non-zero bits).
witnessPresent :: SignedStampedWitnessState -> Bool
witnessPresent st = signedWitnessBits st > 0

-- | Evaluate @admit(h) ⟺ gate ∧ stamp ∧ witness ∧ Excitement preserves@.
signedConjunctAdmits :: SignedAdmissibilityConjunct -> Bool
signedConjunctAdmits c =
  signedConjGateOk c
  && signedConjStampOk c
  && signedConjWitnessPresent c
  && signedConjExcitementPreserves c

-- | Classify unsigned carry vs typed morphism without performing I/O.
evaluateSignedPropagateOperation :: Bool -> SignedPropagateVerdict
evaluateSignedPropagateOperation True = SpvUnsignedPropagationRefused
evaluateSignedPropagateOperation False = SpvMorphismOk

-- | Positive refuse: unsigned propagation is inadmissible — witness required.
refuseUnsignedPropagation :: SignedPropagateRefusal
refuseUnsignedPropagation = SprUnsignedPropagationRefused

-- | Build witness from prior state — morphism must preserve stamps and witness.
witnessFromSignedState :: SignedStampedWitnessState -> SignedPropagateWitness
witnessFromSignedState st =
  SignedPropagateWitness
    { signedWitnessStamp = signedStamp st
    , signedWitnessBitBudget = signedWitnessBits st
    }

-- | Surrogate signed overflow fence on additive propagation.
signedAddOk :: Int -> Int -> Bool
signedAddOk prior delta =
  let result = prior + delta
   in result >= -1000000 && result <= 1000000

-- | Attempt §4 propagate signed stamped witnessed state — fail closed.
propagateSignedState
  :: SignedStampedWitnessState
  -> SignedPropagationStep
  -> SignedAdmissibilityConjunct
  -> Bool
  -> Either SignedPropagateRefusal SignedStampedWitnessState
propagateSignedState prior step conjunct excitementSelected
  | not (wallStampOk (signedStamp prior)) =
      Left (SprPriorStampInvalid (signedWallSeq (signedStamp prior)))
  | not (witnessPresent prior) = Left SprUnsignedPropagationRefused
  | not (wallStampOk (signedPostStamp step)) =
      Left (SprPostStampInvalid (signedWallSeq (signedPostStamp step)))
  | signedPostWitnessBits step < signedWitnessBits prior =
      Left
        ( SprWitnessDropped
            (signedWitnessBits prior)
            (signedPostWitnessBits step)
        )
  | not (signedAddOk (signedValue prior) (signedDelta step)) =
      Left SprSignedOverflow
  | not (signedConjunctAdmits conjunct) =
      Left (SprGateRejected (signedWallSeq (signedStamp prior)))
  | not excitementSelected = Left SprUnsignedPropagationRefused
  | otherwise =
      Right
        SignedStampedWitnessState
          { signedValue = signedValue prior + signedDelta step
          , signedStamp = signedPostStamp step
          , signedWitnessBits = signedPostWitnessBits step
          }

-- | Attempt typed propagation morphism — packages prior/post + witness.
applySignedPropagateMorphism
  :: SignedStampedWitnessState
  -> SignedPropagationStep
  -> SignedAdmissibilityConjunct
  -> Bool
  -> Either SignedPropagateRefusal SignedPropagateMorphism
applySignedPropagateMorphism prior step conjunct excitementSelected =
  case propagateSignedState prior step conjunct excitementSelected of
    Left r -> Left r
    Right post ->
      Right
        SignedPropagateMorphism
          { signedMorphismFrom = prior
          , signedMorphismTo = post
          , signedMorphismWitness = witnessFromSignedState prior
          , signedMorphismExcitementSelected = excitementSelected
          }

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

-- | Unsigned carry always refused at operation classifier.
signedPropagateUnsignedRefused :: Bool
signedPropagateUnsignedRefused =
  evaluateSignedPropagateOperation True == SpvUnsignedPropagationRefused

-- | Non-unsigned path admits typed morphism verdict.
signedPropagateMorphismOkWhenNotUnsigned :: Bool
signedPropagateMorphismOkWhenNotUnsigned =
  evaluateSignedPropagateOperation False == SpvMorphismOk

-- | Positive refuse witness for unsigned propagation.
refuseUnsignedPropagationPositive :: Bool
refuseUnsignedPropagationPositive =
  refuseUnsignedPropagation == SprUnsignedPropagationRefused

-- ---------------------------------------------------------------------------
-- SECTION 4: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data SignedPropagateExcitementComposePin
  = SpImportSelectExcitement
  | SpSecondArgminRefused
  deriving (Show, Eq)

-- | Context for signed propagation over admissible history successors.
data SignedPropagateCtx = SignedPropagateCtx
  { signedPropagatePrior      :: !ThermodynamicState
  , signedPropagateSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Signed propagation **is** 'excitementSelect' — not a second argmin.
signedPropagateSelect
  :: SignedPropagateCtx
  -> Either ExcitementResidue HistoryCandidate
signedPropagateSelect ctx =
  excitementSelect
    (signedPropagatePrior ctx)
    (signedPropagateSuccessors ctx)

-- | Bare signed propagation selector on prior + successors.
urgeSignedPropagateSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeSignedPropagateSelect = excitementSelect

-- | Definitional witness: signed propagation selection is 'excitementSelect'.
signedPropagateSelectEqExcitementSelect :: SignedPropagateCtx -> Bool
signedPropagateSelectEqExcitementSelect ctx =
  signedPropagateSelect ctx
    == excitementSelect
         (signedPropagatePrior ctx)
         (signedPropagateSuccessors ctx)

-- | Context selector equals bare urge selector.
signedPropagateSelectEqUrgeSignedPropagateSelect :: SignedPropagateCtx -> Bool
signedPropagateSelectEqUrgeSignedPropagateSelect ctx =
  signedPropagateSelect ctx
    == urgeSignedPropagateSelect
         (signedPropagatePrior ctx)
         (signedPropagateSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
signedPropagateNoLocalArgmin :: SignedPropagateCtx -> Bool
signedPropagateNoLocalArgmin ctx =
  signedPropagateSelect ctx
    == excitementSelect
         (signedPropagatePrior ctx)
         (signedPropagateSuccessors ctx)

-- | Signed path composes 'excitementSelect' — not a second argmin.
signedPropagateExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> SignedPropagateExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
signedPropagateExcitementSelect src cands pin =
  case pin of
    SpImportSelectExcitement -> excitementSelect src cands
    SpSecondArgminRefused -> Left ExcAllInadmissible

-- | Definitional witness: import pin is 'excitementSelect'.
signedPropagateExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
signedPropagateExcitementSelectEqExcitementSelect src cands =
  signedPropagateExcitementSelect src cands SpImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses via 'ExcAllInadmissible'.
signedPropagateExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
signedPropagateExcitementSelectRefusesSecondArgmin src cands =
  signedPropagateExcitementSelect src cands SpSecondArgminRefused
    == Left ExcAllInadmissible

-- | Empty successor list → 'ExcNoCandidates' via composed selector.
signedPropagateEmpty :: ThermodynamicState -> Bool
signedPropagateEmpty src =
  urgeSignedPropagateSelect src [] == Left ExcNoCandidates

-- | Compose refusal tags for unsigned propagation / second argmin / witness drop.
data SignedPropagateComposeRefusal
  = UnsignedPropagation
  | SecondArgmin
  | WitnessDrop
  deriving (Show, Eq)

-- | Tag for unsigned propagation refusal.
refuseUnsignedPropagationTag :: SignedPropagateComposeRefusal
refuseUnsignedPropagationTag = UnsignedPropagation

-- | Tag for second local argmin refusal.
refuseSecondArgmin :: SignedPropagateComposeRefusal
refuseSecondArgmin = SecondArgmin

-- ---------------------------------------------------------------------------
-- SECTION 5: §4 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | §4 fixture wall stamp with @T@.
signedFixtureStamp :: SignedPropagateWallStamp
signedFixtureStamp =
  SignedPropagateWallStamp {signedWallSeq = 1, signedWallHasT = True}

-- | §4 fixture post wall stamp with @T@.
signedFixturePostStamp :: SignedPropagateWallStamp
signedFixturePostStamp =
  SignedPropagateWallStamp {signedWallSeq = 2, signedWallHasT = True}

-- | §4 fixture signed stamped witnessed state.
signedFixtureState :: SignedStampedWitnessState
signedFixtureState =
  SignedStampedWitnessState
    { signedValue = 10
    , signedStamp = signedFixtureStamp
    , signedWitnessBits = 4
    }

-- | §4 fixture propagation step.
signedFixtureStep :: SignedPropagationStep
signedFixtureStep =
  SignedPropagationStep
    { signedDelta = 3
    , signedPostStamp = signedFixturePostStamp
    , signedPostWitnessBits = 4
    }

-- | §4 fixture admissibility conjunct.
signedFixtureConjunct :: SignedAdmissibilityConjunct
signedFixtureConjunct =
  SignedAdmissibilityConjunct
    { signedConjGateOk = True
    , signedConjStampOk = True
    , signedConjWitnessPresent = True
    , signedConjExcitementPreserves = True
    }

-- | §4 fixture post state after admissible propagation.
signedFixturePostState :: SignedStampedWitnessState
signedFixturePostState =
  SignedStampedWitnessState
    { signedValue = 13
    , signedStamp = signedFixturePostStamp
    , signedWitnessBits = 4
    }

-- | Fixture unsigned propagation refusal tag.
signedFixtureUnsignedRefused :: Bool
signedFixtureUnsignedRefused =
  refuseUnsignedPropagation == SprUnsignedPropagationRefused

-- | Fixture propagation admits post state.
signedFixturePropagateOk :: Bool
signedFixturePropagateOk =
  propagateSignedState
    signedFixtureState
    signedFixtureStep
    signedFixtureConjunct
    True
    == Right signedFixturePostState

-- | Fixture morphism packages prior/post + witness.
signedFixtureApplyMorphismOk :: Bool
signedFixtureApplyMorphismOk =
  applySignedPropagateMorphism
    signedFixtureState
    signedFixtureStep
    signedFixtureConjunct
    True
    == Right
      SignedPropagateMorphism
        { signedMorphismFrom = signedFixtureState
        , signedMorphismTo = signedFixturePostState
        , signedMorphismWitness = witnessFromSignedState signedFixtureState
        , signedMorphismExcitementSelected = True
        }

-- | Fixture unsigned state — zero witness bits.
signedFixtureUnsignedState :: SignedStampedWitnessState
signedFixtureUnsignedState =
  SignedStampedWitnessState
    { signedValue = 1
    , signedStamp = signedFixtureStamp
    , signedWitnessBits = 0
    }

-- | Fixture unsigned propagation refused (missing witness).
signedFixtureUnsignedPropagationRefused :: Bool
signedFixtureUnsignedPropagationRefused =
  propagateSignedState
    signedFixtureUnsignedState
    signedFixtureStep
    signedFixtureConjunct
    True
    == Left SprUnsignedPropagationRefused

-- | Fixture step that drops witness bits (refused).
signedFixtureWitnessDropStep :: SignedPropagationStep
signedFixtureWitnessDropStep =
  SignedPropagationStep
    { signedDelta = 1
    , signedPostStamp = signedFixturePostStamp
    , signedPostWitnessBits = 2
    }

-- | Fixture witness drop refused with typed error.
signedFixtureWitnessDropRefused :: Bool
signedFixtureWitnessDropRefused =
  propagateSignedState
    signedFixtureState
    signedFixtureWitnessDropStep
    signedFixtureConjunct
    True
    == Left (SprWitnessDropped 4 2)

-- | Fixture witness preserves prior stamp.
signedFixtureWitnessPreservesStamp :: Bool
signedFixtureWitnessPreservesStamp =
  signedWitnessStamp (witnessFromSignedState signedFixtureState)
    == signedFixtureStamp

-- | Fixture wall stamp passes @T@ honesty.
signedFixtureWallStampOk :: Bool
signedFixtureWallStampOk = wallStampOk signedFixtureStamp

-- | Fixture state has present witness.
signedFixtureWitnessPresent :: Bool
signedFixtureWitnessPresent = witnessPresent signedFixtureState

-- | Positive refuse is not silent accept on unsigned carry.
signedPropagatePositiveRefuseNotSilent :: Bool
signedPropagatePositiveRefuseNotSilent =
  evaluateSignedPropagateOperation True /= SpvMorphismOk

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | History move on signed propagation carrier (thermodynamic surrogate).
data SignedPropagateHistoryMove = SignedPropagateHistoryMove
  { spPrior        :: !ThermodynamicState
  , spPost         :: !ThermodynamicState
  , spGateChecked  :: !Bool
  , spMergeSafe    :: !Bool
  , spProvenanceOk :: !Bool
  } deriving (Show, Eq)

-- | Admissible signed propagation history move.
admissibleSignedPropagateHistoryMove :: SignedPropagateHistoryMove -> Bool
admissibleSignedPropagateHistoryMove h =
  spGateChecked h && spMergeSafe h && spProvenanceOk h

-- | Thermodynamic accounting on signed propagation transition.
data SignedPropagateTransition = SignedPropagateTransition
  { spMove           :: !SignedPropagateHistoryMove
  , spBath           :: !HeatBath
  , spDissipatedWork :: !Double
  , spEntropyDrop    :: !Double
  } deriving (Show, Eq)

-- | Named second-law invariant on signed propagation transition.
signedPropagateSecondLaw :: SignedPropagateTransition -> Bool
signedPropagateSecondLaw t =
  spEntropyDrop t <= spDissipatedWork t / bathTemp (spBath t)

-- | Physical bridge tying Landauer process to signed propagation move.
data PhysicalSignedPropagateBridge = PhysicalSignedPropagateBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalTransition     :: !SignedPropagateTransition
  , physicalAdmissible     :: !Bool
  } deriving (Show, Eq)

-- | Second law on signed propagation from Landauer bridge discharge.
signedPropagateSecondLawFromPhysical :: PhysicalSignedPropagateBridge -> Bool -> Bool
signedPropagateSecondLawFromPhysical b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalLandauerBridge b))
  && signedPropagateSecondLaw (physicalTransition b)

-- | Admissible history move from physical bridge (no new axiom).
admissibleSignedPropagateHistoryMoveFromPhysical
  :: PhysicalSignedPropagateBridge -> Bool -> Bool
admissibleSignedPropagateHistoryMoveFromPhysical b hSL =
  hSL
  && physicalAdmissible b
  && admissibleSignedPropagateHistoryMove (spMove (physicalTransition b))

-- | Landauer @physicalSecondLaw@ anchor cited (hypothesis discharge witness).
landauerAnchorCited :: HistoryTransition -> Bool -> Bool
landauerAnchorCited t hSL = hSL && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
signedPropagatePhysicsGreen :: Bool
signedPropagatePhysicsGreen = False

-- | Lean/Coq: @signed_propagate_physics_green_false@.
signedPropagatePhysicsGreenFalse :: Bool
signedPropagatePhysicsGreenFalse = not signedPropagatePhysicsGreen

-- | Production wiring stays open (signed propagate lift only).
signedPropagateProductionWired :: Bool
signedPropagateProductionWired = False

-- | Lean/Coq: @signed_propagate_production_wired_false@.
signedPropagateProductionWiredFalse :: Bool
signedPropagateProductionWiredFalse = not signedPropagateProductionWired

-- | Honest non-claim string (meso §4 signed propagation scaffold).
signedPropagateNonClaim :: String
signedPropagateNonClaim =
  "§4 signed propagation: stamp T required; witness retained; unsigned refused; "
    ++ "signedPropagateSelect=excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
signedPropagateNonClaimNonempty :: Bool
signedPropagateNonClaimNonempty = length signedPropagateNonClaim > 0

-- | Catalog witness: meso Urge SignedPropagate module present.
signedPropagateModuleWitness :: Bool
signedPropagateModuleWitness = True

-- | Zero new axiom discipline witness.
signedPropagateNoNewAxiom :: Bool
signedPropagateNoNewAxiom = True

-- | Second-argmin refusal: signed propagate composes 'excitementSelect' only.
signedPropagateNoSecondArgmin :: Bool
signedPropagateNoSecondArgmin =
  signedPropagateNoLocalArgmin
    SignedPropagateCtx
      { signedPropagatePrior = ThermodynamicState 2400 0 0.3 30 40
      , signedPropagateSuccessors = []
      }
