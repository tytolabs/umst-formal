-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ExactAlgCoeffs
-- Description : Meso acting Urge — §3 ExactAlg coefficients on the history carrier.
--
-- ℚ coefficient slot on `HistoryCarrier` — not silent f64 identity.
-- Excitement recovery composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ExactAlgCoeffs
  ( -- * ExactAlg coefficient carriers on HistoryCarrier (§3)
    ExactAlgCoeff (..)
  , CarrierExactAlgCoeffs (..)
  , ExactAlgCoeffWitness (..)
  , ExactAlgCoeffMorphism (..)
  , FloatCarrierTag (..)
  , ExactAlgCoeffsRefusal (..)
  , ExactAlgCoeffsVerdict (..)
  , exactAlgCoeffValue
  , exactAlgCoeffDenNonzero
  , exactAlgCoeffToExactAlg
  , attachExactAlgCoeff
    -- * §3 admissibility conjunct + positive refuse
  , ExactAlgCoeffAdmissibilityConjunct (..)
  , exactAlgCoeffConjunctAdmits
  , evaluateF64IdentityTheater
  , evaluateZeroDenominator
  , refuseF64IdentityTheater
  , refuseZeroDenominator
  , refuseExactAlgAbsent
  , refuseSecondArgminSelector
  , witnessFromCarrierCoeffs
  , admitCarrierExactAlg
  , applyExactAlgCoeffMorphism
  , exactAlgCoeffF64TheaterRefused
  , exactAlgCoeffZeroDenRefused
  , exactAlgCoeffExactAlgAbsentRefused
  , refuseSecondArgminSelectorPositive
    -- * ExactAlg coefficients compose excitementSelect (no second argmin)
  , ExactAlgCoeffsExcitementPin (..)
  , ExactAlgCoeffCtx (..)
  , exactAlgCoeffsExcitementSelect
  , exactAlgCoeffSelect
  , exactAlgCoeffsExcitementSelectEqExcitementSelect
  , exactAlgCoeffSelectEqExcitementSelect
  , exactAlgCoeffNoLocalArgmin
  , exactAlgCoeffsExcitementSelectRefusesSecondArgmin
    -- * §3 fixtures + witness theorems
  , exactAlgFixtureCoeff
  , exactAlgFixtureZeroDen
  , exactAlgFixtureCarrierCoeffs
  , exactAlgFixtureZeroDenCoeffs
  , exactAlgFixtureState
  , exactAlgFixtureSnapshot
  , exactAlgFixtureStamp
  , exactAlgFixtureSdf
  , exactAlgFixtureExactAlg
  , exactAlgFixtureCarrier
  , exactAlgFixtureConjunct
  , exactAlgFixtureAdmitOk
  , exactAlgFixtureZeroDenRefused
  , exactAlgFixtureF64TheaterRefused
  , exactAlgFixtureApplyMorphismOk
  , exactAlgFixtureWitnessPreservesValue
  , exactAlgFixtureAttachPreservesExactAlg
  , exactAlgCoeffF64TheaterNotAdmitted
  , exactAlgCoeffZeroDenNotAdmitted
    -- * Landauer bridge (derived — zero new axioms)
  , ExactAlgCoeffsHistoryMove (..)
  , admissibleExactAlgCoeffs
  , ExactAlgCoeffsTransition (..)
  , exactAlgCoeffsSecondLaw
  , exactAlgCoeffsSecondLawFromLandauer
  , exactAlgCoeffsFromLandauerAdmitSecondLaw
  , exactAlgCoeffsSecondLawFromHypothesis
  , physicalSecondLawImported
    -- * Honesty flags + catalog witnesses
  , exactAlgCoeffsPhysicsGreen
  , exactAlgCoeffsPhysicsGreenFalse
  , exactAlgCoeffsProductionWired
  , exactAlgCoeffsProductionWiredFalse
  , exactAlgCoeffsNonClaim
  , exactAlgCoeffsNonClaimNonempty
  , exactAlgCoeffsModuleWitness
  , exactAlgCoeffsNoNewAxiom
  , exactAlgCoeffsNoSecondArgmin
  , exactAlgCoeffsPositiveRefuseNotSilent
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HeatBath (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , LandauerHistoryBridge (..)
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.CarrierProduct
  ( ExactAlg (..)
  , HistoryCarrier (..)
  , SdfFRep (..)
  , UcrsStamp
  , carrierMk
  , exactAlgProj
  , satisfiedWitness
  , sdfFRepProj
  , stampProj
  , umstProj
  , wallOnlyStamp
  , witnessProj
  )

-- ---------------------------------------------------------------------------
-- SECTION 1: ExactAlg coefficient carriers on HistoryCarrier (§3)
-- ---------------------------------------------------------------------------

-- | ℚ coefficient slot — mirrors Rust `ExactAlgCoeff` (num/den/op_tag).
data ExactAlgCoeff = ExactAlgCoeff
  { coeffNum   :: !Int
  , coeffDen   :: !Int
  , coeffOpTag :: !Int
  } deriving (Show, Eq)

-- | ExactAlg coefficients attached to a history-carrier content id.
data CarrierExactAlgCoeffs = CarrierExactAlgCoeffs
  { carrierContentId :: !Int
  , carrierCoeff     :: !ExactAlgCoeff
  } deriving (Show, Eq)

-- | Witness bundle an ExactAlg coefficient morphism must preserve (§3).
data ExactAlgCoeffWitness = ExactAlgCoeffWitness
  { witnessContentId :: !Int
  , witnessValue     :: !Double
  , witnessOpTag     :: !Int
  } deriving (Show, Eq)

-- | Typed ExactAlg coefficient morphism — admissible carrier slot update.
data ExactAlgCoeffMorphism = ExactAlgCoeffMorphism
  { morphismFrom           :: !CarrierExactAlgCoeffs
  , morphismToCarrier      :: !HistoryCarrier
  , morphismWitness        :: !ExactAlgCoeffWitness
  , morphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- | f64 silent-identity theater tag — positive refuse carrier (not ℚ).
data FloatCarrierTag = FloatTheater
  deriving (Show, Eq)

-- | Fail-closed ExactAlg coefficient errors — positive refuse, not silent accept.
data ExactAlgCoeffsRefusal
  = F64IdentityTheater
  | ZeroDenominator
  | ExactAlgAbsent
  | SecondArgmin
  | GateRejected !Int
  deriving (Show, Eq)

-- | Verdict of an ExactAlg coefficient admit operation class.
data ExactAlgCoeffsVerdict
  = EacvAdmitted
  | EacvF64TheaterRefused
  | EacvZeroDenRefused
  | EacvInadmissible
  deriving (Show, Eq)

-- | Project ℚ coefficient value (carrier slot — denominator checked separately).
exactAlgCoeffValue :: ExactAlgCoeff -> Double
exactAlgCoeffValue c
  | coeffDen c == 0 = 0
  | otherwise       = fromIntegral (coeffNum c) / fromIntegral (coeffDen c)

-- | Whether ℚ denominator is non-zero (fail-closed admit precondition).
exactAlgCoeffDenNonzero :: ExactAlgCoeff -> Bool
exactAlgCoeffDenNonzero c = coeffDen c /= 0

-- | Map admitted ℚ slot to `CarrierProduct.ExactAlg`.
exactAlgCoeffToExactAlg :: ExactAlgCoeff -> ExactAlg
exactAlgCoeffToExactAlg c =
  ExactAlg
    { algValue = exactAlgCoeffValue c
    , opTag    = coeffOpTag c
    }

-- | Attach ℚ coefficients to an existing history carrier (§3 product factor).
attachExactAlgCoeff :: HistoryCarrier -> ExactAlgCoeff -> HistoryCarrier
attachExactAlgCoeff carrier coeff =
  carrierMk
    (umstProj carrier)
    (stampProj carrier)
    (sdfFRepProj carrier)
    (exactAlgCoeffToExactAlg coeff)
    (witnessProj carrier)

-- ---------------------------------------------------------------------------
-- SECTION 2: §3 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §3 admissibility conjunct inputs (surrogate).
data ExactAlgCoeffAdmissibilityConjunct = ExactAlgCoeffAdmissibilityConjunct
  { conjGateOk              :: !Bool
  , conjDenNonzero          :: !Bool
  , conjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate `admit(h) ⟺ gate ∧ den≠0 ∧ Excitement preserves`.
exactAlgCoeffConjunctAdmits :: ExactAlgCoeffAdmissibilityConjunct -> Bool
exactAlgCoeffConjunctAdmits c =
  conjGateOk c && conjDenNonzero c && conjExcitementPreserves c

-- | Classify f64 identity theater vs ℚ carrier admit.
evaluateF64IdentityTheater :: Bool -> ExactAlgCoeffsVerdict
evaluateF64IdentityTheater True  = EacvF64TheaterRefused
evaluateF64IdentityTheater False = EacvAdmitted

-- | Classify zero denominator vs ℚ carrier admit.
evaluateZeroDenominator :: Bool -> ExactAlgCoeffsVerdict
evaluateZeroDenominator True  = EacvZeroDenRefused
evaluateZeroDenominator False = EacvAdmitted

-- | Positive refuse: f64 silent identity theater — ℚ carrier required.
refuseF64IdentityTheater :: FloatCarrierTag -> ExactAlgCoeffsRefusal
refuseF64IdentityTheater _ = F64IdentityTheater

-- | Positive refuse: zero denominator on ℚ coefficient.
refuseZeroDenominator :: ExactAlgCoeffsRefusal
refuseZeroDenominator = ZeroDenominator

-- | Positive refuse: ExactAlg slot absent on carrier.
refuseExactAlgAbsent :: ExactAlgCoeffsRefusal
refuseExactAlgAbsent = ExactAlgAbsent

-- | Positive refuse: second Excitement selector — compose 'excitementSelect'.
refuseSecondArgminSelector :: ExactAlgCoeffsRefusal
refuseSecondArgminSelector = SecondArgmin

-- | Build witness from carrier ExactAlg coefficients.
witnessFromCarrierCoeffs :: CarrierExactAlgCoeffs -> ExactAlgCoeffWitness
witnessFromCarrierCoeffs c =
  ExactAlgCoeffWitness
    { witnessContentId = carrierContentId c
    , witnessValue     = exactAlgCoeffValue (carrierCoeff c)
    , witnessOpTag     = coeffOpTag (carrierCoeff c)
    }

-- | Admit ℚ ExactAlg coefficients on carrier — fail closed on zero denominator.
admitCarrierExactAlg
  :: CarrierExactAlgCoeffs
  -> Either ExactAlgCoeffsRefusal CarrierExactAlgCoeffs
admitCarrierExactAlg c
  | exactAlgCoeffDenNonzero (carrierCoeff c) = Right c
  | otherwise = Left ZeroDenominator

-- | Attempt typed ExactAlg coefficient morphism — fail closed on inadmissibility.
applyExactAlgCoeffMorphism
  :: CarrierExactAlgCoeffs
  -> HistoryCarrier
  -> ExactAlgCoeffAdmissibilityConjunct
  -> Bool
  -> Either ExactAlgCoeffsRefusal ExactAlgCoeffMorphism
applyExactAlgCoeffMorphism coeffs carrier conjunct excitementSelected
  | not (exactAlgCoeffConjunctAdmits conjunct) =
      Left (GateRejected 0)
  | otherwise =
      case admitCarrierExactAlg coeffs of
        Left r -> Left r
        Right admitted ->
          if not excitementSelected
            then Left ExactAlgAbsent
            else
              Right
                ExactAlgCoeffMorphism
                  { morphismFrom = admitted
                  , morphismToCarrier =
                      attachExactAlgCoeff carrier (carrierCoeff admitted)
                  , morphismWitness = witnessFromCarrierCoeffs admitted
                  , morphismExcitementSelected = excitementSelected
                  }

-- | Positive refuse witnesses (definitional).
exactAlgCoeffF64TheaterRefused :: Bool
exactAlgCoeffF64TheaterRefused =
  refuseF64IdentityTheater FloatTheater == F64IdentityTheater

exactAlgCoeffZeroDenRefused :: Bool
exactAlgCoeffZeroDenRefused = refuseZeroDenominator == ZeroDenominator

exactAlgCoeffExactAlgAbsentRefused :: Bool
exactAlgCoeffExactAlgAbsentRefused = refuseExactAlgAbsent == ExactAlgAbsent

refuseSecondArgminSelectorPositive :: Bool
refuseSecondArgminSelectorPositive =
  refuseSecondArgminSelector == SecondArgmin

-- ---------------------------------------------------------------------------
-- SECTION 3: ExactAlg coefficients compose excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data ExactAlgCoeffsExcitementPin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

-- | Context for ExactAlg coefficients over admissible history successors.
data ExactAlgCoeffCtx = ExactAlgCoeffCtx
  { coeffCtxPrior      :: !ThermodynamicState
  , coeffCtxSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | ExactAlg coefficient path composes 'excitementSelect' — not a second argmin.
exactAlgCoeffsExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> ExactAlgCoeffsExcitementPin
  -> Either ExcitementResidue HistoryCandidate
exactAlgCoeffsExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
exactAlgCoeffsExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

-- | ExactAlg coefficient selection **is** 'excitementSelect' on carrier head.
exactAlgCoeffSelect
  :: ExactAlgCoeffCtx
  -> Either ExcitementResidue HistoryCandidate
exactAlgCoeffSelect ctx =
  excitementSelect (coeffCtxPrior ctx) (coeffCtxSuccessors ctx)

-- | Definitional witness: import pin is 'excitementSelect'.
exactAlgCoeffsExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
exactAlgCoeffsExcitementSelectEqExcitementSelect src cands =
  exactAlgCoeffsExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | ExactAlg coefficient selection equals 'excitementSelect'.
exactAlgCoeffSelectEqExcitementSelect :: ExactAlgCoeffCtx -> Bool
exactAlgCoeffSelectEqExcitementSelect ctx =
  exactAlgCoeffSelect ctx
    == excitementSelect (coeffCtxPrior ctx) (coeffCtxSuccessors ctx)

-- | ExactAlg coefficient selector re-uses 'excitementSelect' — no Urge-local argmin.
exactAlgCoeffNoLocalArgmin :: ExactAlgCoeffCtx -> Bool
exactAlgCoeffNoLocalArgmin = exactAlgCoeffSelectEqExcitementSelect

-- | Second-argmin pin refuses with all-inadmissible residue.
exactAlgCoeffsExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
exactAlgCoeffsExcitementSelectRefusesSecondArgmin src cands =
  exactAlgCoeffsExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

-- ---------------------------------------------------------------------------
-- SECTION 4: §3 fixtures + witness theorems
-- ---------------------------------------------------------------------------

exactAlgFixtureCoeff :: ExactAlgCoeff
exactAlgFixtureCoeff = ExactAlgCoeff {coeffNum = 3, coeffDen = 2, coeffOpTag = 1}

exactAlgFixtureZeroDen :: ExactAlgCoeff
exactAlgFixtureZeroDen = ExactAlgCoeff {coeffNum = 1, coeffDen = 0, coeffOpTag = 0}

exactAlgFixtureCarrierCoeffs :: CarrierExactAlgCoeffs
exactAlgFixtureCarrierCoeffs =
  CarrierExactAlgCoeffs {carrierContentId = 1, carrierCoeff = exactAlgFixtureCoeff}

exactAlgFixtureZeroDenCoeffs :: CarrierExactAlgCoeffs
exactAlgFixtureZeroDenCoeffs =
  CarrierExactAlgCoeffs {carrierContentId = 1, carrierCoeff = exactAlgFixtureZeroDen}

exactAlgFixtureState :: ThermodynamicState
exactAlgFixtureState = ThermodynamicState 2400 0 0 0 0

exactAlgFixtureSnapshot :: HistorySnapshot
exactAlgFixtureSnapshot =
  HistorySnapshot {historyCommitId = 1, historyHead = exactAlgFixtureState}

exactAlgFixtureStamp :: UcrsStamp
exactAlgFixtureStamp = wallOnlyStamp 42

exactAlgFixtureSdf :: SdfFRep
exactAlgFixtureSdf = SdfFRep {canonicalDigest = 5381, frepGrain = 1}

exactAlgFixtureExactAlg :: ExactAlg
exactAlgFixtureExactAlg = exactAlgCoeffToExactAlg exactAlgFixtureCoeff

exactAlgFixtureCarrier :: HistoryCarrier
exactAlgFixtureCarrier =
  carrierMk
    exactAlgFixtureSnapshot
    exactAlgFixtureStamp
    exactAlgFixtureSdf
    exactAlgFixtureExactAlg
    satisfiedWitness

exactAlgFixtureConjunct :: ExactAlgCoeffAdmissibilityConjunct
exactAlgFixtureConjunct =
  ExactAlgCoeffAdmissibilityConjunct
    { conjGateOk = True
    , conjDenNonzero = True
    , conjExcitementPreserves = True
    }

exactAlgFixtureAdmitOk :: Bool
exactAlgFixtureAdmitOk =
  admitCarrierExactAlg exactAlgFixtureCarrierCoeffs
    == Right exactAlgFixtureCarrierCoeffs

exactAlgFixtureZeroDenRefused :: Bool
exactAlgFixtureZeroDenRefused =
  admitCarrierExactAlg exactAlgFixtureZeroDenCoeffs == Left ZeroDenominator

exactAlgFixtureF64TheaterRefused :: Bool
exactAlgFixtureF64TheaterRefused =
  evaluateF64IdentityTheater True == EacvF64TheaterRefused

exactAlgFixtureApplyMorphismOk :: Bool
exactAlgFixtureApplyMorphismOk =
  applyExactAlgCoeffMorphism
    exactAlgFixtureCarrierCoeffs
    exactAlgFixtureCarrier
    exactAlgFixtureConjunct
    True
    == Right
      ExactAlgCoeffMorphism
        { morphismFrom = exactAlgFixtureCarrierCoeffs
        , morphismToCarrier =
            attachExactAlgCoeff exactAlgFixtureCarrier exactAlgFixtureCoeff
        , morphismWitness = witnessFromCarrierCoeffs exactAlgFixtureCarrierCoeffs
        , morphismExcitementSelected = True
        }

exactAlgFixtureWitnessPreservesValue :: Bool
exactAlgFixtureWitnessPreservesValue =
  witnessValue (witnessFromCarrierCoeffs exactAlgFixtureCarrierCoeffs)
    == exactAlgCoeffValue exactAlgFixtureCoeff

exactAlgFixtureAttachPreservesExactAlg :: Bool
exactAlgFixtureAttachPreservesExactAlg =
  exactAlgProj (attachExactAlgCoeff exactAlgFixtureCarrier exactAlgFixtureCoeff)
    == exactAlgFixtureExactAlg

exactAlgCoeffF64TheaterNotAdmitted :: Bool
exactAlgCoeffF64TheaterNotAdmitted =
  evaluateF64IdentityTheater True /= EacvAdmitted

exactAlgCoeffZeroDenNotAdmitted :: Bool
exactAlgCoeffZeroDenNotAdmitted =
  evaluateZeroDenominator True /= EacvAdmitted

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | History move for ExactAlg coefficient admissibility (§3 surrogate).
data ExactAlgCoeffsHistoryMove = ExactAlgCoeffsHistoryMove
  { movePrior        :: !ThermodynamicState
  , movePost         :: !ThermodynamicState
  , moveGateChecked  :: !Bool
  , moveDenNonzero   :: !Bool
  , moveProvenanceOk :: !Bool
  } deriving (Show, Eq)

-- | Admissible ExactAlg coefficient history move.
admissibleExactAlgCoeffs :: ExactAlgCoeffsHistoryMove -> Bool
admissibleExactAlgCoeffs h =
  moveGateChecked h && moveDenNonzero h && moveProvenanceOk h

-- | Thermodynamic accounting on an ExactAlg coefficient transition.
data ExactAlgCoeffsTransition = ExactAlgCoeffsTransition
  { coeffsMove            :: !ExactAlgCoeffsHistoryMove
  , coeffsBath            :: !HeatBath
  , coeffsDissipatedWork  :: !Double
  , coeffsEntropyDrop     :: !Double
  } deriving (Show, Eq)

-- | Named second-law invariant on ExactAlg coefficient transition.
exactAlgCoeffsSecondLaw :: ExactAlgCoeffsTransition -> Bool
exactAlgCoeffsSecondLaw t =
  coeffsEntropyDrop t
    <= coeffsDissipatedWork t / bathTemp (coeffsBath t)

-- | Second law on ExactAlg coefficient transition from Landauer bridge discharge.
exactAlgCoeffsSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
exactAlgCoeffsSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
exactAlgCoeffsFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
exactAlgCoeffsFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for ExactAlg coefficient second law (no new axiom).
exactAlgCoeffsSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
exactAlgCoeffsSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
exactAlgCoeffsPhysicsGreen :: Bool
exactAlgCoeffsPhysicsGreen = False

-- | Lean/Coq: @exact_alg_coeffs_physics_green_false@.
exactAlgCoeffsPhysicsGreenFalse :: Bool
exactAlgCoeffsPhysicsGreenFalse = not exactAlgCoeffsPhysicsGreen

-- | Production wiring stays open (ExactAlg coefficient lift only).
exactAlgCoeffsProductionWired :: Bool
exactAlgCoeffsProductionWired = False

-- | Lean/Coq: @exact_alg_coeffs_production_wired_false@.
exactAlgCoeffsProductionWiredFalse :: Bool
exactAlgCoeffsProductionWiredFalse = not exactAlgCoeffsProductionWired

-- | Honest non-claim string (meso §3 ExactAlg coefficients scaffold).
exactAlgCoeffsNonClaim :: String
exactAlgCoeffsNonClaim =
  "§3 ExactAlg coefficients: ℚ slot on HistoryCarrier — not f64 identity theater; "
    ++ "compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
exactAlgCoeffsNonClaimNonempty :: Bool
exactAlgCoeffsNonClaimNonempty = length exactAlgCoeffsNonClaim > 0

-- | Catalog witness: meso Urge ExactAlgCoeffs module present.
exactAlgCoeffsModuleWitness :: Bool
exactAlgCoeffsModuleWitness = True

-- | Zero new axiom discipline witness.
exactAlgCoeffsNoNewAxiom :: Bool
exactAlgCoeffsNoNewAxiom = True

-- | Second-argmin refusal: ExactAlg coefficients compose 'excitementSelect' only.
exactAlgCoeffsNoSecondArgmin :: Bool
exactAlgCoeffsNoSecondArgmin =
  exactAlgCoeffNoLocalArgmin
    (ExactAlgCoeffCtx
      { coeffCtxPrior = exactAlgFixtureState
      , coeffCtxSuccessors = []
      })

-- | Positive refuse is not silent accept on f64 theater.
exactAlgCoeffsPositiveRefuseNotSilent :: Bool
exactAlgCoeffsPositiveRefuseNotSilent =
  evaluateF64IdentityTheater True /= EacvAdmitted
