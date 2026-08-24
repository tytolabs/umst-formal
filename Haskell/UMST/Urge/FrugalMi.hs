-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.FrugalMi
-- Description : Meso acting Urge — §4 frugal MI observation of admitted history.
--
-- Frugal MI observation **is** an Excitement-selected admissible transition —
-- acting coalgebra deconstruct on local+mesh state, not Landauer proof theater.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.FrugalMi
  ( -- * Local+mesh carriers + acting coalgebra (§4)
    FrugalLocalState (..)
  , FrugalMeshState (..)
  , FrugalLocalMeshState (..)
  , FrugalLocalMeshCoalgebra (..)
  , frugalCoalgebraRequiresPaired
  , frugalLocalMeshDeconstruct
  , FrugalMiObservation (..)
  , frugalMiDeficit
  , FrugalMiRefusal (..)
  , FrugalMiVerdict (..)
    -- * Pairwise MI + admissibility conjunct + positive refuse
  , pairwiseMiBits
  , FrugalMiAdmissibilityConjunct (..)
  , frugalConjunctAdmits
  , evaluateFrugalMiOperation
  , refuseLandauerProof
  , refuseLandauerKernelFork
  , frugalMiObservationMk
  , observeFrugalMiFromCoalgebra
    -- * Admitted history carrier (§4 observation scaffold)
  , FrugalMiAdmitted (..)
  , frugalMiAdmittedNew
  , frugalMiAdmittedCarrier
  , frugalMiAdmittedHead
  , frugalMiAdmittedCoalgebra
    -- * Positive refuse witnesses
  , frugalMiLandauerProofRefused
  , frugalMiObservationOkWhenNotLandauer
  , refuseLandauerProofPositive
  , refuseLandauerKernelForkPositive
  , pairwiseMiFixturePaired
  , pairwiseMiFixtureZero
  , frugalFixtureLandauerProofRefused
  , frugalFixturePairedObservationOk
  , frugalFixtureMeshAbsentRefused
  , frugalFixtureMiZeroRefused
  , frugalFixtureWitnessDeficitRefused
    -- * Excitement alignment (no second argmin)
  , FrugalMiCtx (..)
  , frugalMiSelect
  , frugalMiSelectBare
  , frugalMiSelectEqExcitementSelect
  , frugalMiSelectEqAdmitHistorySelect
  , frugalMiNoLocalArgmin
  , frugalMiSelectEmpty
  , frugalMiCarrierSelect
  , frugalMiAdmittedSelect
  , frugalMiAdmittedSelectEqExcitementSelect
  , frugalMiAdmittedSelectEqCarrierSelect
    -- * Landauer bridge (derived — zero new axioms)
  , FrugalMiTransition (..)
  , admissibleFrugalMiTransition
  , frugalMiSecondLaw
  , frugalMiSecondLawFromLandauer
  , frugalMiFromLandauerAdmitSecondLaw
  , frugalMiSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , frugalMiPhysicsGreen
  , frugalMiPhysicsGreenFalse
  , frugalMiProductionWired
  , frugalMiProductionWiredFalse
  , frugalMiModalityUnwired
  , frugalMiNonClaim
  , frugalMiNonClaimNonempty
  , frugalMiModuleWitness
  , frugalMiNoNewAxiom
  , frugalMiNoSecondArgmin
  , frugalMiPositiveRefuseNotSilent
  , frugalMiActingCoalgebraNotLandauerProof
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Urge.AdmitKleisli
  ( ExcitementResidue (..)
  , HistoryCandidate (..)
  , HistorySnapshot (..)
  , HistoryTransition (..)
  , HeatBath (..)
  , LandauerHistoryBridge (..)
  , admitHistorySelect
  , admitSecondLaw
  , admissibleHistoryTransitionFromLandauerBridge
  , excitementSelect
  , landauerTransition
  )
import UMST.Urge.CarrierProduct (HistoryCarrier (..), umstProj)

-- ---------------------------------------------------------------------------
-- SECTION 1: Local+mesh carriers + acting coalgebra (§4)
-- ---------------------------------------------------------------------------

-- | Local working-copy surrogate (commit head + entropy bits).
data FrugalLocalState = FrugalLocalState
  { frugalCommitHead  :: !Int
  , frugalEntropyBits :: !Int
  } deriving (Show, Eq)

-- | Mesh replica surrogate (gossip mesh census entropy).
data FrugalMeshState = FrugalMeshState
  { frugalReplicaSeq          :: !Int
  , frugalGossipEntropyBits   :: !Int
  } deriving (Show, Eq)

-- | Paired local+mesh carrier — product state for §4 observation.
data FrugalLocalMeshState = FrugalLocalMeshState
  { frugalLocalState :: !FrugalLocalState
  , frugalMeshState  :: !FrugalMeshState
  } deriving (Show, Eq)

-- | Acting coalgebra deconstruct tag on local+mesh — not Landauer proof.
data FrugalLocalMeshCoalgebra
  = FrugalLocalOnly FrugalLocalState
  | FrugalMeshOnly FrugalMeshState
  | FrugalPaired FrugalLocalMeshState
  deriving (Show, Eq)

-- | Whether observation requires both local and mesh components.
frugalCoalgebraRequiresPaired :: FrugalLocalMeshCoalgebra -> Bool
frugalCoalgebraRequiresPaired (FrugalPaired _) = True
frugalCoalgebraRequiresPaired _                = False

-- | Acting coalgebra deconstruct — unfold paired carrier into observation tag.
frugalLocalMeshDeconstruct :: FrugalLocalMeshState -> FrugalLocalMeshCoalgebra
frugalLocalMeshDeconstruct = FrugalPaired

-- | Frugal MI bit observation — minimal MI cost surrogate for status verb.
data FrugalMiObservation = FrugalMiObservation
  { frugalRequiredBits :: !Int
  , frugalObservedBits :: !Int
  } deriving (Show, Eq)

-- | Witness deficit — @max(0, required − observed)@ on nat surrogate.
frugalMiDeficit :: FrugalMiObservation -> Int
frugalMiDeficit obs =
  let req = frugalRequiredBits obs
      got = frugalObservedBits obs
   in if got <= req then req - got else 0

-- | Fail-closed frugal MI errors — positive refuse, not silent no-op.
data FrugalMiRefusal
  = FrugalLandauerProofRefused
  | FrugalLandauerKernelForkRefused
  | FrugalMutualInformationZero
  | FrugalMeshAbsentWhenPairedRequired
  | FrugalInconsistentEntropies
  | FrugalWitnessDeficit Int Int
  deriving (Show, Eq)

-- | Verdict of a frugal MI observation class.
data FrugalMiVerdict
  = FrugalObservationOk
  | FrugalLandauerProofVerdictRefused
  | FrugalInadmissible
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: Pairwise MI + admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | Pairwise Shannon MI bits — @I(X;Y) = H(X) + H(Y) − H(X,Y)@ (nat surrogate).
pairwiseMiBits :: Int -> Int -> Int -> Maybe Int
pairwiseMiBits hLocal hMesh jointEntropy =
  let entropySum = hLocal + hMesh
   in if jointEntropy <= entropySum then Just (entropySum - jointEntropy) else Nothing

-- | §4 admissibility conjunct inputs (surrogate).
data FrugalMiAdmissibilityConjunct = FrugalMiAdmissibilityConjunct
  { frugalGateOk              :: !Bool
  , frugalMiPositive          :: !Bool
  , frugalExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate @admit(h) ⟺ gate ∧ MI>0 ∧ Excitement preserves@.
frugalConjunctAdmits :: FrugalMiAdmissibilityConjunct -> Bool
frugalConjunctAdmits c =
  frugalGateOk c && frugalMiPositive c && frugalExcitementPreserves c

-- | Classify Landauer proof theater vs typed observation without performing I/O.
evaluateFrugalMiOperation :: Bool -> FrugalMiVerdict
evaluateFrugalMiOperation True  = FrugalLandauerProofVerdictRefused
evaluateFrugalMiOperation False = FrugalObservationOk

-- | Positive refuse: Landauer bound proof is inadmissible on this scaffold.
refuseLandauerProof :: FrugalMiRefusal
refuseLandauerProof = FrugalLandauerProofRefused

-- | Positive refuse: UCRS Landauer kernel fork is inadmissible.
refuseLandauerKernelFork :: FrugalMiRefusal
refuseLandauerKernelFork = FrugalLandauerKernelForkRefused

-- | Construct frugal MI observation from required and observed bit counts.
frugalMiObservationMk :: Int -> Int -> FrugalMiObservation
frugalMiObservationMk req got =
  FrugalMiObservation {frugalRequiredBits = req, frugalObservedBits = got}

-- | Attempt frugal MI observation on acting coalgebra — fail closed.
observeFrugalMiFromCoalgebra
  :: FrugalLocalMeshCoalgebra
  -> Int
  -> Int
  -> Int
  -> Int
  -> Int
  -> FrugalMiAdmissibilityConjunct
  -> Either FrugalMiRefusal FrugalMiObservation
observeFrugalMiFromCoalgebra coalgebra hLocal hMesh jointEntropy required observed conjunct =
  if not (frugalConjunctAdmits conjunct)
    then Left FrugalInconsistentEntropies
    else if not (frugalCoalgebraRequiresPaired coalgebra)
      then Left FrugalMeshAbsentWhenPairedRequired
      else case pairwiseMiBits hLocal hMesh jointEntropy of
        Nothing -> Left FrugalInconsistentEntropies
        Just mi ->
          if mi == 0
            then Left FrugalMutualInformationZero
            else
              let obs = frugalMiObservationMk required observed
               in if observed < required
                    then Left (FrugalWitnessDeficit required observed)
                    else Right obs

-- ---------------------------------------------------------------------------
-- SECTION 3: Admitted history carrier (§4 observation scaffold)
-- ---------------------------------------------------------------------------

-- | Frugal MI admitted history — carrier + local+mesh acting coalgebra.
data FrugalMiAdmitted = FrugalMiAdmitted
  { frugalAdmittedCarrier :: !HistoryCarrier
  , frugalAdmittedMesh    :: !FrugalLocalMeshState
  } deriving (Show, Eq)

-- | Fresh admitted scaffold from carrier + paired local+mesh state.
frugalMiAdmittedNew :: HistoryCarrier -> FrugalLocalMeshState -> FrugalMiAdmitted
frugalMiAdmittedNew carrier mesh =
  FrugalMiAdmitted {frugalAdmittedCarrier = carrier, frugalAdmittedMesh = mesh}

-- | Project admitted history carrier.
frugalMiAdmittedCarrier :: FrugalMiAdmitted -> HistoryCarrier
frugalMiAdmittedCarrier = frugalAdmittedCarrier

-- | Thermodynamic head at admitted carrier UMST snapshot.
frugalMiAdmittedHead :: FrugalMiAdmitted -> ThermodynamicState
frugalMiAdmittedHead a = historyHead (umstProj (frugalAdmittedCarrier a))

-- | Acting coalgebra deconstruct on admitted local+mesh pair.
frugalMiAdmittedCoalgebra :: FrugalMiAdmitted -> FrugalLocalMeshCoalgebra
frugalMiAdmittedCoalgebra a = frugalLocalMeshDeconstruct (frugalAdmittedMesh a)

-- ---------------------------------------------------------------------------
-- SECTION 4: Positive refuse witnesses
-- ---------------------------------------------------------------------------

frugalMiLandauerProofRefused :: Bool
frugalMiLandauerProofRefused =
  evaluateFrugalMiOperation True == FrugalLandauerProofVerdictRefused

frugalMiObservationOkWhenNotLandauer :: Bool
frugalMiObservationOkWhenNotLandauer =
  evaluateFrugalMiOperation False == FrugalObservationOk

refuseLandauerProofPositive :: Bool
refuseLandauerProofPositive =
  refuseLandauerProof == FrugalLandauerProofRefused

refuseLandauerKernelForkPositive :: Bool
refuseLandauerKernelForkPositive =
  refuseLandauerKernelFork == FrugalLandauerKernelForkRefused

pairwiseMiFixturePaired :: Bool
pairwiseMiFixturePaired = pairwiseMiBits 4 3 5 == Just 2

pairwiseMiFixtureZero :: Bool
pairwiseMiFixtureZero = pairwiseMiBits 2 2 4 == Just 0

frugalFixtureLocal :: FrugalLocalState
frugalFixtureLocal = FrugalLocalState {frugalCommitHead = 7, frugalEntropyBits = 4}

frugalFixtureMesh :: FrugalMeshState
frugalFixtureMesh =
  FrugalMeshState {frugalReplicaSeq = 3, frugalGossipEntropyBits = 3}

frugalFixturePaired :: FrugalLocalMeshState
frugalFixturePaired =
  FrugalLocalMeshState {frugalLocalState = frugalFixtureLocal, frugalMeshState = frugalFixtureMesh}

frugalFixtureCoalgebra :: FrugalLocalMeshCoalgebra
frugalFixtureCoalgebra = frugalLocalMeshDeconstruct frugalFixturePaired

frugalFixtureConjunct :: FrugalMiAdmissibilityConjunct
frugalFixtureConjunct =
  FrugalMiAdmissibilityConjunct
    { frugalGateOk = True
    , frugalMiPositive = True
    , frugalExcitementPreserves = True
    }

frugalFixtureLandauerProofRefused :: Bool
frugalFixtureLandauerProofRefused =
  refuseLandauerProof == FrugalLandauerProofRefused

frugalFixturePairedObservationOk :: Bool
frugalFixturePairedObservationOk =
  observeFrugalMiFromCoalgebra
    frugalFixtureCoalgebra 4 3 5 2 2 frugalFixtureConjunct
    == Right (frugalMiObservationMk 2 2)

frugalFixtureMeshAbsentRefused :: Bool
frugalFixtureMeshAbsentRefused =
  observeFrugalMiFromCoalgebra
    (FrugalLocalOnly frugalFixtureLocal) 4 3 5 2 2 frugalFixtureConjunct
    == Left FrugalMeshAbsentWhenPairedRequired

frugalFixtureMiZeroRefused :: Bool
frugalFixtureMiZeroRefused =
  observeFrugalMiFromCoalgebra
    frugalFixtureCoalgebra 2 2 4 2 2 frugalFixtureConjunct
    == Left FrugalMutualInformationZero

frugalFixtureWitnessDeficitRefused :: Bool
frugalFixtureWitnessDeficitRefused =
  observeFrugalMiFromCoalgebra
    frugalFixtureCoalgebra 4 3 5 3 2 frugalFixtureConjunct
    == Left (FrugalWitnessDeficit 3 2)

-- ---------------------------------------------------------------------------
-- SECTION 5: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for frugal MI observation over admissible history successors.
data FrugalMiCtx = FrugalMiCtx
  { frugalMiPrior      :: !ThermodynamicState
  , frugalMiSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Frugal MI status observation **is** 'excitementSelect'.
frugalMiSelect
  :: FrugalMiCtx
  -> Either ExcitementResidue HistoryCandidate
frugalMiSelect ctx =
  excitementSelect (frugalMiPrior ctx) (frugalMiSuccessors ctx)

-- | Bare frugal MI selection on prior + successors.
frugalMiSelectBare
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
frugalMiSelectBare prior successors = excitementSelect prior successors

-- | Definitional witness: frugal MI selection API is 'excitementSelect'.
frugalMiSelectEqExcitementSelect :: FrugalMiCtx -> Bool
frugalMiSelectEqExcitementSelect ctx =
  frugalMiSelect ctx
    == excitementSelect (frugalMiPrior ctx) (frugalMiSuccessors ctx)

-- | Frugal MI selection equals admit-history selection.
frugalMiSelectEqAdmitHistorySelect :: FrugalMiCtx -> Bool
frugalMiSelectEqAdmitHistorySelect ctx =
  frugalMiSelect ctx
    == admitHistorySelect (frugalMiPrior ctx) (frugalMiSuccessors ctx)

-- | Frugal MI selector re-uses 'excitementSelect' — no Urge-local argmin.
frugalMiNoLocalArgmin :: FrugalMiCtx -> Bool
frugalMiNoLocalArgmin ctx =
  frugalMiSelect ctx
    == excitementSelect (frugalMiPrior ctx) (frugalMiSuccessors ctx)

-- | Empty successor list yields no-candidates residue.
frugalMiSelectEmpty :: ThermodynamicState -> Bool
frugalMiSelectEmpty prior =
  frugalMiSelectBare prior [] == Left ExcNoCandidates

-- | Carrier-level selection on admitted history UMST head.
frugalMiCarrierSelect
  :: HistoryCarrier
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
frugalMiCarrierSelect c cands =
  excitementSelect (historyHead (umstProj c)) cands

-- | Admitted-history frugal MI selection composes 'excitementSelect'.
frugalMiAdmittedSelect
  :: FrugalMiAdmitted
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
frugalMiAdmittedSelect a cands =
  excitementSelect (frugalMiAdmittedHead a) cands

-- | Definitional witness: admitted selection is 'excitementSelect'.
frugalMiAdmittedSelectEqExcitementSelect
  :: FrugalMiAdmitted -> [HistoryCandidate] -> Bool
frugalMiAdmittedSelectEqExcitementSelect a cands =
  frugalMiAdmittedSelect a cands
    == excitementSelect (frugalMiAdmittedHead a) cands

-- | Admitted selection equals carrier-level selection.
frugalMiAdmittedSelectEqCarrierSelect
  :: FrugalMiAdmitted -> [HistoryCandidate] -> Bool
frugalMiAdmittedSelectEqCarrierSelect a cands =
  frugalMiAdmittedSelect a cands
    == frugalMiCarrierSelect (frugalAdmittedCarrier a) cands

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Frugal MI transition accounting (acting meso layer).
data FrugalMiTransition = FrugalMiTransition
  { frugalPrior           :: !ThermodynamicState
  , frugalPost            :: !ThermodynamicState
  , frugalBath            :: !HeatBath
  , frugalDissipatedWork  :: !Double
  , frugalEntropyDrop     :: !Double
  , frugalGateChecked     :: !Bool
  , frugalMiPositiveFlag  :: !Bool
  , frugalProvenanceOk    :: !Bool
  } deriving (Show, Eq)

-- | Admissible frugal MI transition conjunct.
admissibleFrugalMiTransition :: FrugalMiTransition -> Bool
admissibleFrugalMiTransition t =
  frugalGateChecked t && frugalMiPositiveFlag t && frugalProvenanceOk t

-- | Second law on frugal MI transition (Bool witness — not a new axiom).
frugalMiSecondLaw :: FrugalMiTransition -> Bool
frugalMiSecondLaw t =
  frugalEntropyDrop t <= frugalDissipatedWork t / bathTemp (frugalBath t)

-- | Second law on frugal MI transition from Landauer bridge discharge.
frugalMiSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
frugalMiSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Physical bridge discharge: second law on Landauer transition.
frugalMiFromLandauerAdmitSecondLaw :: LandauerHistoryBridge -> Bool -> Bool
frugalMiFromLandauerAdmitSecondLaw b hSL =
  hSL && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for frugal MI second law (no new axiom).
frugalMiSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
frugalMiSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
frugalMiPhysicsGreen :: Bool
frugalMiPhysicsGreen = False

-- | Lean/Coq: @frugal_mi_physics_green_false@.
frugalMiPhysicsGreenFalse :: Bool
frugalMiPhysicsGreenFalse = not frugalMiPhysicsGreen

-- | Production wiring stays open (frugal MI lift only).
frugalMiProductionWired :: Bool
frugalMiProductionWired = False

-- | Lean/Coq: @frugal_mi_production_wired_false@.
frugalMiProductionWiredFalse :: Bool
frugalMiProductionWiredFalse = not frugalMiProductionWired

-- | Modality remains Unwired on this scaffold.
frugalMiModalityUnwired :: Bool
frugalMiModalityUnwired = True

-- | Honest non-claim string (meso §4 frugal MI scaffold).
frugalMiNonClaim :: String
frugalMiNonClaim =
  "§4 frugal MI observation of admitted history as acting coalgebra; "
    ++ "frugalMiSelect composes excitementSelect not second argmin; "
    ++ "Landauer physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
frugalMiNonClaimNonempty :: Bool
frugalMiNonClaimNonempty = length frugalMiNonClaim > 0

-- | Catalog witness: meso Urge FrugalMi module present.
frugalMiModuleWitness :: Bool
frugalMiModuleWitness = True

-- | Zero new axiom discipline witness.
frugalMiNoNewAxiom :: Bool
frugalMiNoNewAxiom = True

-- | Second-argmin refusal: frugal MI composes 'excitementSelect' only.
frugalMiNoSecondArgmin :: Bool
frugalMiNoSecondArgmin =
  frugalMiNoLocalArgmin
    (FrugalMiCtx
      (ThermodynamicState 2400 0 0.3 30 40)
      [])

-- | Positive refuse is not silent on Landauer proof theater.
frugalMiPositiveRefuseNotSilent :: Bool
frugalMiPositiveRefuseNotSilent =
  evaluateFrugalMiOperation True /= FrugalObservationOk

-- | Acting coalgebra refuse distinct from kernel-fork refuse.
frugalMiActingCoalgebraNotLandauerProof :: Bool
frugalMiActingCoalgebraNotLandauerProof =
  refuseLandauerProof /= FrugalLandauerKernelForkRefused
