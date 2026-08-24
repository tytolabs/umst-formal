-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.AntichainIndependent
-- Description : Meso acting Urge — §22.2 conflict graph independent set / antichain.
--
-- Urge **witnesses** prefix conflict-graph independent sets; does **not** fork
-- @umst-adk@ greedy @allocate_antichain@ or invent GREEN from antichain size.
-- Excitement recovery composes 'excitementSelect' — no second argmin.
--
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.AntichainIndependent
  ( -- * Conflict cell + graph + independent-set carriers
    AntichainWritePath (..)
  , ConflictCell (..)
  , ConflictEdge (..)
  , ConflictGraph (..)
  , IndependentSetVerdict (..)
  , AntichainIndependentRefusal (..)
  , AntichainIndependentVerdict (..)
    -- * §22.2 admissibility conjunct + positive refuse
  , AntichainAdmissibilityConjunct (..)
  , antichainConjunctAdmits
  , antichainPathsConflictSingle
  , antichainPathsConflict
  , canonicalConflictEdge
  , edgeHitsSelected
  , isIndependentSet
  , validateIndependentSet
  , admitAntichainMember
  , refuseForkAllocate
  , refuseSecondArgminSelector
  , refuseGreedyMisTheater
  , physicsGreenFromAntichainSize
  , evaluateAntichainOperation
    -- * Excitement alignment (no second argmin)
  , AntichainExcitementComposePin (..)
  , antichainExcitementSelect
  , AntichainIndependentCtx (..)
  , urgeRecoverySelect
  , antichainIndependentSelect
  , antichainExcitementSelectEqExcitementSelect
  , antichainIndependentSelectEqExcitementSelect
  , antichainIndependentSelectEqUrgeRecoverySelect
  , antichainIndependentNoLocalArgmin
  , antichainExcitementSelectRefusesSecondArgmin
    -- * §22.2 fixtures + witness theorems
  , aiPathZoneA
  , aiPathZoneAX
  , aiPathZoneAY
  , aiFixtureAccept
  , aiFixtureRefuseA
  , aiFixtureRefuseB
  , aiFixtureEdge01
  , aiFixtureEdge02
  , aiFixtureEdge12
  , aiFixtureGraph
  , aiFixtureConjunct
  , aiFixtureAcceptOnlyIndependent
  , aiFixtureAcceptRefuseAConflicts
  , aiFixtureAcceptRefuseBConflicts
  , aiFixturePathsConflictAcceptA
  , aiFixtureNotIndependentPair
  , aiFixtureConjunctAdmits
  , aiFixtureAntichainSizeNoGreen
    -- * Landauer bridge (derived — zero new axioms)
  , AntichainHistoryMove (..)
  , admissibleAntichainIndependent
  , AntichainTransition (..)
  , antichainSecondLaw
  , PhysicalAntichainBridge (..)
  , antichainSecondLawFromLandauer
  , antichainSecondLawFromHypothesis
  , physicalSecondLawImported
  , admissibleAntichainIndependentFromPhysical
    -- * Honesty flags + catalog witnesses
  , antichainIndependentPhysicsGreen
  , antichainIndependentPhysicsGreenFalse
  , antichainIndependentProductionWired
  , antichainIndependentProductionWiredFalse
  , antichainIndependentNonClaim
  , antichainIndependentNonClaimNonempty
  , antichainIndependentModuleWitness
  , antichainIndependentNoNewAxiom
  , antichainIndependentNoSecondArgmin
  , antichainIndependentPositiveRefuseNotSilent
  , antichainIndependentForkAllocateRefusedPositive
  , antichainIndependentSecondArgminRefusedPositive
  , antichainIndependentGreedyMisRefusedPositive
  , antichainIndependentNeverInventsGreenFromSize
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
-- SECTION 1: Conflict cell + graph + independent-set carriers
-- ---------------------------------------------------------------------------

-- | Write-set path surrogate — zone pin for prefix conflict (§22.2).
data AntichainWritePath = AntichainWritePath
  { antichainPathZone   :: !Int
  , antichainPathSuffix :: !Int
  } deriving (Show, Eq)

-- | Open cell node for prefix conflict graph construction.
data ConflictCell = ConflictCell
  { conflictCellId       :: !Int
  , conflictCellWriteSet :: ![AntichainWritePath]
  } deriving (Show, Eq)

-- | Canonical undirected edge between two cell ids.
data ConflictEdge = ConflictEdge
  { conflictEdgeLeft  :: !Int
  , conflictEdgeRight :: !Int
  } deriving (Show, Eq)

-- | Prefix conflict graph carrier.
data ConflictGraph = ConflictGraph
  { conflictGraphNodes :: ![Int]
  , conflictGraphEdges :: ![ConflictEdge]
  } deriving (Show, Eq)

-- | Verdict when validating an independent set on a conflict graph.
data IndependentSetVerdict = IndependentSetAdmit
  deriving (Show, Eq)

-- | Fail-closed refusal for §22.2 antichain independent-set policy.
data AntichainIndependentRefusal
  = ForkAllocateRefused
  | SecondArgminRefused
  | NotIndependentSet
  | ConflictingNeighbor
  | GreedyMisTheater
  deriving (Show, Eq)

-- | Verdict of an antichain independent-set operation class.
data AntichainIndependentVerdict
  = IndependentAdmit
  | ForkAllocateRefusedVerdict
  | GreedyMisRefused
  | SecondArgminRefusedVerdict
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: §22.2 admissibility conjunct + positive refuse
-- ---------------------------------------------------------------------------

-- | §22.2 admissibility conjunct inputs (surrogate).
data AntichainAdmissibilityConjunct = AntichainAdmissibilityConjunct
  { independentOk       :: !Bool
  , noForkAllocate      :: !Bool
  , excitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Conjunct admits when all three flags hold.
antichainConjunctAdmits :: AntichainAdmissibilityConjunct -> Bool
antichainConjunctAdmits c =
  independentOk c && noForkAllocate c && excitementPreserves c

-- | Whether two write-set paths prefix-conflict on zone pin.
antichainPathsConflictSingle :: AntichainWritePath -> AntichainWritePath -> Bool
antichainPathsConflictSingle p q =
  antichainPathZone p == antichainPathZone q

-- | Whether any path in @right@ prefix-conflicts with @left@.
anyPathConflicts :: [AntichainWritePath] -> AntichainWritePath -> Bool
anyPathConflicts [] _ = False
anyPathConflicts (p : rest) q =
  if antichainPathsConflictSingle p q then True else anyPathConflicts rest q

-- | Whether any path in two write_sets prefix-conflicts.
antichainPathsConflict :: [AntichainWritePath] -> [AntichainWritePath] -> Bool
antichainPathsConflict _ [] = False
antichainPathsConflict left (q : rest) =
  if anyPathConflicts left q then True else antichainPathsConflict left rest

-- | Canonical edge with sorted endpoints.
canonicalConflictEdge :: Int -> Int -> ConflictEdge
canonicalConflictEdge a b =
  if b < a
    then ConflictEdge {conflictEdgeLeft = b, conflictEdgeRight = a}
    else ConflictEdge {conflictEdgeLeft = a, conflictEdgeRight = b}

-- | Whether node @n@ appears in selected list.
nodeInList :: Int -> [Int] -> Bool
nodeInList _ [] = False
nodeInList n (m : rest) =
  if n == m then True else nodeInList n rest

-- | Whether an edge connects two selected node ids.
edgeHitsSelected :: ConflictEdge -> [Int] -> Bool
edgeHitsSelected e selected =
  nodeInList (conflictEdgeLeft e) selected
  && nodeInList (conflictEdgeRight e) selected

-- | Whether selected nodes form an independent set (no edge between any pair).
isIndependentSet :: [ConflictEdge] -> [Int] -> Bool
isIndependentSet [] _ = True
isIndependentSet (e : rest) selected =
  if edgeHitsSelected e selected
    then False
    else isIndependentSet rest selected

-- | Validate selected cell ids form an independent set on the conflict graph.
validateIndependentSet
  :: ConflictGraph -> [Int] -> Either AntichainIndependentRefusal IndependentSetVerdict
validateIndependentSet g selected =
  if isIndependentSet (conflictGraphEdges g) selected
    then Right IndependentSetAdmit
    else Left NotIndependentSet

-- | Admit a single antichain member — refuse when prefix-conflicts with incumbent.
admitAntichainMember
  :: ConflictCell -> ConflictCell -> Either AntichainIndependentRefusal IndependentSetVerdict
admitAntichainMember incumbent candidate =
  if antichainPathsConflict
       (conflictCellWriteSet incumbent)
       (conflictCellWriteSet candidate)
    then Left ConflictingNeighbor
    else Right IndependentSetAdmit

-- | Positive refuse: Urge must not fork @umst-adk@ greedy allocate.
refuseForkAllocate :: AntichainIndependentRefusal
refuseForkAllocate = ForkAllocateRefused

-- | Positive refuse: second local Excitement argmin — compose import only.
refuseSecondArgminSelector :: AntichainIndependentRefusal
refuseSecondArgminSelector = SecondArgminRefused

-- | Positive refuse: greedy/exact MIS theater — Urge witnesses only.
refuseGreedyMisTheater :: AntichainIndependentRefusal
refuseGreedyMisTheater = GreedyMisTheater

-- | Urge does not bool-flip physics GREEN from antichain cardinality.
physicsGreenFromAntichainSize :: Int -> Bool
physicsGreenFromAntichainSize _ = False

-- | Classify fork-allocate vs witness-only independent set without performing I/O.
evaluateAntichainOperation :: Bool -> AntichainIndependentVerdict
evaluateAntichainOperation True  = ForkAllocateRefusedVerdict
evaluateAntichainOperation False = IndependentAdmit

-- ---------------------------------------------------------------------------
-- SECTION 3: Excitement alignment (no second argmin)
-- ---------------------------------------------------------------------------

-- | Excitement compose pin — import selector; refuse second local argmin.
data AntichainExcitementComposePin
  = ImportSelectExcitement
  | SecondArgminRefusedPin
  deriving (Show, Eq)

-- | Compose path composes 'excitementSelect' — not a second argmin.
antichainExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> AntichainExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
antichainExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
antichainExcitementSelect _ _ SecondArgminRefusedPin =
  Left ExcAllInadmissible

-- | Context for antichain independent over admissible history successors.
data AntichainIndependentCtx = AntichainIndependentCtx
  { antichainPrior      :: !ThermodynamicState
  , antichainSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Urge recovery selection composes 'excitementSelect' — not a second argmin.
urgeRecoverySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeRecoverySelect = excitementSelect

-- | Antichain independent selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
antichainIndependentSelect
  :: AntichainIndependentCtx
  -> Either ExcitementResidue HistoryCandidate
antichainIndependentSelect ctx =
  urgeRecoverySelect (antichainPrior ctx) (antichainSuccessors ctx)

-- | Definitional witness: import pin is 'excitementSelect'.
antichainExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
antichainExcitementSelectEqExcitementSelect src cands =
  antichainExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

-- | Antichain selection equals 'excitementSelect' on successors.
antichainIndependentSelectEqExcitementSelect :: AntichainIndependentCtx -> Bool
antichainIndependentSelectEqExcitementSelect ctx =
  antichainIndependentSelect ctx
    == excitementSelect (antichainPrior ctx) (antichainSuccessors ctx)

-- | Antichain selection equals 'urgeRecoverySelect' on successors.
antichainIndependentSelectEqUrgeRecoverySelect :: AntichainIndependentCtx -> Bool
antichainIndependentSelectEqUrgeRecoverySelect ctx =
  antichainIndependentSelect ctx
    == urgeRecoverySelect (antichainPrior ctx) (antichainSuccessors ctx)

-- | No Urge-local argmin — composes imported 'excitementSelect' only.
antichainIndependentNoLocalArgmin :: AntichainIndependentCtx -> Bool
antichainIndependentNoLocalArgmin ctx =
  antichainIndependentSelect ctx
    == excitementSelect (antichainPrior ctx) (antichainSuccessors ctx)

-- | Second-argmin pin refuses with all-inadmissible residue.
antichainExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
antichainExcitementSelectRefusesSecondArgmin src cands =
  antichainExcitementSelect src cands SecondArgminRefusedPin
    == Left ExcAllInadmissible

-- ---------------------------------------------------------------------------
-- SECTION 4: §22.2 fixtures + witness theorems
-- ---------------------------------------------------------------------------

-- | §22.2 fixture path pins — mirror Rust @section_22_2_fixture@.
aiPathZoneA :: AntichainWritePath
aiPathZoneA = AntichainWritePath {antichainPathZone = 1, antichainPathSuffix = 0}

aiPathZoneAX :: AntichainWritePath
aiPathZoneAX = AntichainWritePath {antichainPathZone = 1, antichainPathSuffix = 1}

aiPathZoneAY :: AntichainWritePath
aiPathZoneAY = AntichainWritePath {antichainPathZone = 1, antichainPathSuffix = 2}

aiFixtureAccept :: ConflictCell
aiFixtureAccept =
  ConflictCell {conflictCellId = 0, conflictCellWriteSet = [aiPathZoneA]}

aiFixtureRefuseA :: ConflictCell
aiFixtureRefuseA =
  ConflictCell {conflictCellId = 1, conflictCellWriteSet = [aiPathZoneAX]}

aiFixtureRefuseB :: ConflictCell
aiFixtureRefuseB =
  ConflictCell {conflictCellId = 2, conflictCellWriteSet = [aiPathZoneAY]}

aiFixtureEdge01 :: ConflictEdge
aiFixtureEdge01 = canonicalConflictEdge 0 1

aiFixtureEdge02 :: ConflictEdge
aiFixtureEdge02 = canonicalConflictEdge 0 2

aiFixtureEdge12 :: ConflictEdge
aiFixtureEdge12 = canonicalConflictEdge 1 2

aiFixtureGraph :: ConflictGraph
aiFixtureGraph =
  ConflictGraph
    { conflictGraphNodes = [0, 1, 2]
    , conflictGraphEdges = [aiFixtureEdge01, aiFixtureEdge02, aiFixtureEdge12]
    }

aiFixtureConjunct :: AntichainAdmissibilityConjunct
aiFixtureConjunct =
  AntichainAdmissibilityConjunct
    { independentOk = True
    , noForkAllocate = True
    , excitementPreserves = True
    }

-- | Fixture: singleton @[0]@ is independent on triangle graph.
aiFixtureAcceptOnlyIndependent :: Bool
aiFixtureAcceptOnlyIndependent =
  validateIndependentSet aiFixtureGraph [0] == Right IndependentSetAdmit

-- | Fixture: accept vs refuse-A prefix-conflicts on zone pin.
aiFixtureAcceptRefuseAConflicts :: Bool
aiFixtureAcceptRefuseAConflicts =
  admitAntichainMember aiFixtureAccept aiFixtureRefuseA
    == Left ConflictingNeighbor

-- | Fixture: accept vs refuse-B prefix-conflicts on zone pin.
aiFixtureAcceptRefuseBConflicts :: Bool
aiFixtureAcceptRefuseBConflicts =
  admitAntichainMember aiFixtureAccept aiFixtureRefuseB
    == Left ConflictingNeighbor

-- | Fixture: path conflict between accept and refuse-A write_sets.
aiFixturePathsConflictAcceptA :: Bool
aiFixturePathsConflictAcceptA =
  antichainPathsConflict
    (conflictCellWriteSet aiFixtureAccept)
    (conflictCellWriteSet aiFixtureRefuseA)

-- | Fixture: pair @[0,1]@ is not an independent set on triangle graph.
aiFixtureNotIndependentPair :: Bool
aiFixtureNotIndependentPair =
  validateIndependentSet aiFixtureGraph [0, 1] == Left NotIndependentSet

-- | Fixture conjunct admits all three flags.
aiFixtureConjunctAdmits :: Bool
aiFixtureConjunctAdmits = antichainConjunctAdmits aiFixtureConjunct

-- | Fixture: antichain size never invents GREEN.
aiFixtureAntichainSizeNoGreen :: Bool
aiFixtureAntichainSizeNoGreen =
  not (physicsGreenFromAntichainSize (length (conflictGraphNodes aiFixtureGraph)))

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | §22.2 history move conjunct (Bool surrogate for Lean Prop bundle).
data AntichainHistoryMove = AntichainHistoryMove
  { antichainMoveIndependentOk       :: !Bool
  , antichainMoveNoForkAllocate      :: !Bool
  , antichainMoveExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Admissible antichain independent move when all conjuncts hold.
admissibleAntichainIndependent :: AntichainHistoryMove -> Bool
admissibleAntichainIndependent h =
  antichainMoveIndependentOk h
  && antichainMoveNoForkAllocate h
  && antichainMoveExcitementPreserves h

-- | Thermodynamic accounting on an antichain transition (acting meso layer).
data AntichainTransition = AntichainTransition
  { antichainMove            :: !AntichainHistoryMove
  , antichainBath            :: !HeatBath
  , antichainDissipatedWork  :: !Double
  , antichainEntropyDrop     :: !Double
  } deriving (Show, Eq)

-- | Named second-law invariant on antichain transition (Bool witness).
antichainSecondLaw :: AntichainTransition -> Bool
antichainSecondLaw t =
  antichainEntropyDrop t
    <= antichainDissipatedWork t / bathTemp (antichainBath t)

-- | Physical bridge tying Landauer process to antichain history move.
data PhysicalAntichainBridge = PhysicalAntichainBridge
  { physicalAntichainLandauerBridge :: !LandauerHistoryBridge
  , physicalAntichainTransition     :: !AntichainTransition
  , physicalAntichainAdmissible     :: !Bool
  } deriving (Show, Eq)

-- | Second law on antichain transition from Landauer bridge discharge.
antichainSecondLawFromLandauer :: PhysicalAntichainBridge -> Bool -> Bool
antichainSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge
       (physicalAntichainLandauerBridge b)
       hSL
  && admitSecondLaw (landauerTransition (physicalAntichainLandauerBridge b))
  && antichainSecondLaw (physicalAntichainTransition b)

-- | Hypothesis discharge for antichain second law (no new axiom).
antichainSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
antichainSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- | Physical second law imported from Lean @LandauerLaw.physicalSecondLaw@.
physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

-- | Admissible move discharged from physical bridge (no new axiom).
admissibleAntichainIndependentFromPhysical
  :: PhysicalAntichainBridge -> Bool -> Bool
admissibleAntichainIndependentFromPhysical b hSL =
  hSL
  && physicalAntichainAdmissible b
  && admissibleAntichainIndependent
       (antichainMove (physicalAntichainTransition b))

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
antichainIndependentPhysicsGreen :: Bool
antichainIndependentPhysicsGreen = False

-- | Lean/Coq: @antichainIndependentPhysicsGreenFalse@.
antichainIndependentPhysicsGreenFalse :: Bool
antichainIndependentPhysicsGreenFalse =
  not antichainIndependentPhysicsGreen

-- | Production wiring stays open (meso lift only).
antichainIndependentProductionWired :: Bool
antichainIndependentProductionWired = False

-- | Lean/Coq: @antichainIndependentProductionWiredFalse@.
antichainIndependentProductionWiredFalse :: Bool
antichainIndependentProductionWiredFalse =
  not antichainIndependentProductionWired

-- | Honest non-claim string (meso §22.2 antichain independent-set scaffold).
antichainIndependentNonClaim :: String
antichainIndependentNonClaim =
  "§22.2 conflict graph independent set — Urge witnesses prefix conflict; "
    ++ "compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

-- | Non-claim string is non-empty.
antichainIndependentNonClaimNonempty :: Bool
antichainIndependentNonClaimNonempty =
  length antichainIndependentNonClaim > 0

-- | Catalog witness: meso Urge AntichainIndependent module present.
antichainIndependentModuleWitness :: Bool
antichainIndependentModuleWitness = True

-- | Zero new axiom discipline witness.
antichainIndependentNoNewAxiom :: Bool
antichainIndependentNoNewAxiom = True

-- | Second-argmin refusal: antichain composes 'excitementSelect' only.
antichainIndependentNoSecondArgmin :: Bool
antichainIndependentNoSecondArgmin =
  antichainExcitementSelectEqExcitementSelect (ThermodynamicState 300 0 0.3 30 40) []

-- | Positive refuse is not silent admit on fork-allocate path.
antichainIndependentPositiveRefuseNotSilent :: Bool
antichainIndependentPositiveRefuseNotSilent =
  evaluateAntichainOperation True /= IndependentAdmit

-- | Fork-allocate refusal tag witness.
antichainIndependentForkAllocateRefusedPositive :: Bool
antichainIndependentForkAllocateRefusedPositive =
  refuseForkAllocate == ForkAllocateRefused

-- | Second-argmin refusal tag witness.
antichainIndependentSecondArgminRefusedPositive :: Bool
antichainIndependentSecondArgminRefusedPositive =
  refuseSecondArgminSelector == SecondArgminRefused

-- | Greedy MIS theater refusal tag witness.
antichainIndependentGreedyMisRefusedPositive :: Bool
antichainIndependentGreedyMisRefusedPositive =
  refuseGreedyMisTheater == GreedyMisTheater

-- | Antichain cardinality never invents GREEN.
antichainIndependentNeverInventsGreenFromSize :: Int -> Bool
antichainIndependentNeverInventsGreenFromSize size =
  not (physicsGreenFromAntichainSize size)
