-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ReplicaCoalgebra
-- Description : Meso acting Urge — §15.4 admissible replica coalgebra.
--
-- node-0 / node-1 / Forgejo / LUKS are **replica classes** — sample sections of
-- one mesh sheaf, not XOR worlds.  Inbound merge:
--
--   admit(h) ⟺ gate_check(h) ∧ MergeSafe(h) ∧ Excitement preserves provenance(h)
--
-- Backup is a **typed recovery morphism** (Excitement 'excitementSelect', not
-- rsync theater).  Offline LUKS replica class carries @network-egress: []@.
--
-- Excitement recovery composes 'excitementSelect' — no second argmin.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ReplicaCoalgebra
  ( -- * Replica classes (sample sections — not XOR worlds)
    ReplicaClass (..)
  , replicaClassTag
  , replicaClassTagNode0
  , replicaClassTagNode1
  , replicaClassTagForge
  , replicaClassTagLuks
  , replicaClassTagNode0NeNode1
  , replicaClassTagNode0NeForge
  , replicaClassTagNode0NeLuks
  , replicaClassTagNode1NeForge
  , replicaClassTagNode1NeLuks
  , replicaClassTagForgeNeLuks
  , replicaClassesNotXor
  , replicaClassesNotXorHolds
  , replicaClassCount
  , replicaClassCountIsFour
    -- * Mesh sheaf + coalgebra observe
  , ReplicaMeshSheaf (..)
  , node0SampleSection
  , node1SampleSection
  , forgeSampleSection
  , luksSampleSection
  , sampleSectionAt
  , ReplicaSectionBundle (..)
  , replicaCoalgebraObserve
  , replicaCoalgebraObserveComponents
  , sampleSectionAtNode0
  , sampleSectionAtNode1
  , sampleSectionAtForge
  , sampleSectionAtLuks
  , witnessReplicaSheaf
  , node0DoesNotCloseLuks
    -- * Network egress (offline LUKS carries empty egress)
  , networkEgress
  , luksNetworkEgressEmpty
  , node0NetworkEgressTailscale
  , offlineLuksIsNetworkEgressEmpty
    -- * Admissible replica coalgebra (gate ∧ MergeSafe ∧ provenance)
  , ReplicaHistoryMove (..)
  , admissibleReplicaCoalgebra
  , admissibleReplicaCoalgebraIntro
  , admitReplicaInbound
    -- * Typed recovery morphism (Excitement — no second argmin)
  , RecoveryCtx (..)
  , typedRecoveryMorphism
  , typedRecoverySelect
  , typedRecoveryMorphismEqExcitementSelect
  , typedRecoverySelectEqExcitementSelect
  , typedRecoveryMorphismEqTypedRecoverySelect
  , replicaSelect
  , replicaSelectEqExcitementSelect
  , replicaSelectEqTypedRecoverySelect
  , replicaNoLocalArgmin
  , ReplicaExcitementComposePin (..)
  , replicaExcitementSelect
  , replicaExcitementSelectEqExcitementSelect
  , replicaExcitementSelectRefusesSecondArgmin
  , replicaSelectEmpty
    -- * §15.4 fixtures + witness theorems
  , replicaFixtureState
  , replicaFixtureAdmissibleMove
  , replicaFixtureInadmissibleMove
  , replicaFixtureAdmissibleOk
  , replicaFixtureInadmissibleRefused
  , replicaFixtureExcitementCompose
  , replicaFixtureClassesNotXor
  , replicaFixtureLuksOffline
  , replicaPositiveRefuseNotSilent
    -- * Landauer bridge (derived — zero new axioms)
  , ReplicaTransition (..)
  , replicaSecondLaw
  , PhysicalReplicaBridge (..)
  , replicaSecondLawFromPhysical
  , admissibleReplicaCoalgebraFromPhysical
  , replicaSecondLawFromHypothesis
  , replicaFromLandauerAdmitSecondLaw
    -- * Honesty flags + catalog witnesses
  , replicaCoalgebraPhysicsGreen
  , replicaCoalgebraPhysicsGreenFalse
  , replicaCoalgebraProductionWired
  , replicaCoalgebraProductionWiredFalse
  , replicaCoalgebraNonClaim
  , replicaCoalgebraNonClaimNonempty
  , replicaCoalgebraModuleWitness
  , replicaCoalgebraNoNewAxiom
  , replicaCoalgebraNoSecondArgmin
  , replicaCoalgebraNamedNotXor
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
-- SECTION 1: Replica classes (sample sections — not XOR worlds)
-- ---------------------------------------------------------------------------

-- | Four replica classes on one mesh sheaf — concurrent sections, not XOR worlds.
data ReplicaClass
  = ReplicaNode0
  | ReplicaNode1
  | ReplicaForge
  | ReplicaLuks
  deriving (Show, Eq)

-- | Human-readable class tag (deployment naming — not XOR partition).
replicaClassTag :: ReplicaClass -> String
replicaClassTag c = case c of
  ReplicaNode0 -> "node-0"
  ReplicaNode1 -> "node-1"
  ReplicaForge -> "forge"
  ReplicaLuks  -> "luks"

replicaClassTagNode0 :: Bool
replicaClassTagNode0 = replicaClassTag ReplicaNode0 == "node-0"

replicaClassTagNode1 :: Bool
replicaClassTagNode1 = replicaClassTag ReplicaNode1 == "node-1"

replicaClassTagForge :: Bool
replicaClassTagForge = replicaClassTag ReplicaForge == "forge"

replicaClassTagLuks :: Bool
replicaClassTagLuks = replicaClassTag ReplicaLuks == "luks"

replicaClassTagNode0NeNode1 :: Bool
replicaClassTagNode0NeNode1 =
  replicaClassTag ReplicaNode0 /= replicaClassTag ReplicaNode1

replicaClassTagNode0NeForge :: Bool
replicaClassTagNode0NeForge =
  replicaClassTag ReplicaNode0 /= replicaClassTag ReplicaForge

replicaClassTagNode0NeLuks :: Bool
replicaClassTagNode0NeLuks =
  replicaClassTag ReplicaNode0 /= replicaClassTag ReplicaLuks

replicaClassTagNode1NeForge :: Bool
replicaClassTagNode1NeForge =
  replicaClassTag ReplicaNode1 /= replicaClassTag ReplicaForge

replicaClassTagNode1NeLuks :: Bool
replicaClassTagNode1NeLuks =
  replicaClassTag ReplicaNode1 /= replicaClassTag ReplicaLuks

replicaClassTagForgeNeLuks :: Bool
replicaClassTagForgeNeLuks =
  replicaClassTag ReplicaForge /= replicaClassTag ReplicaLuks

-- | Replica classes are distinct tags — concurrent sections, not XOR worlds.
replicaClassesNotXor :: Bool
replicaClassesNotXor =
  replicaClassTagNode0NeNode1
  && replicaClassTagNode0NeForge
  && replicaClassTagNode0NeLuks
  && replicaClassTagNode1NeForge
  && replicaClassTagNode1NeLuks
  && replicaClassTagForgeNeLuks

replicaClassesNotXorHolds :: Bool
replicaClassesNotXorHolds = replicaClassesNotXor

replicaClassCount :: Int
replicaClassCount = 4

replicaClassCountIsFour :: Bool
replicaClassCountIsFour = replicaClassCount == 4

-- ---------------------------------------------------------------------------
-- SECTION 2: Mesh sheaf + coalgebra observe (concurrent sections)
-- ---------------------------------------------------------------------------

-- | One mesh sheaf: probe each replica class for its sample section.
data ReplicaMeshSheaf = ReplicaMeshSheaf
  { sectionProbe :: ReplicaClass -> Int
  }

probeAt :: ReplicaMeshSheaf -> ReplicaClass -> Int
probeAt r c = sectionProbe r c

instance Show ReplicaMeshSheaf where
  show r =
    "ReplicaMeshSheaf"
      ++ " { node0="
      ++ show (probeAt r ReplicaNode0)
      ++ ", node1="
      ++ show (probeAt r ReplicaNode1)
      ++ ", forge="
      ++ show (probeAt r ReplicaForge)
      ++ ", luks="
      ++ show (probeAt r ReplicaLuks)
      ++ " }"

instance Eq ReplicaMeshSheaf where
  a == b =
    probeAt a ReplicaNode0 == probeAt b ReplicaNode0
    && probeAt a ReplicaNode1 == probeAt b ReplicaNode1
    && probeAt a ReplicaForge == probeAt b ReplicaForge
    && probeAt a ReplicaLuks == probeAt b ReplicaLuks

node0SampleSection :: ReplicaMeshSheaf -> Int
node0SampleSection r = probeAt r ReplicaNode0

node1SampleSection :: ReplicaMeshSheaf -> Int
node1SampleSection r = probeAt r ReplicaNode1

forgeSampleSection :: ReplicaMeshSheaf -> Int
forgeSampleSection r = probeAt r ReplicaForge

luksSampleSection :: ReplicaMeshSheaf -> Int
luksSampleSection r = probeAt r ReplicaLuks

sampleSectionAt :: ReplicaClass -> ReplicaMeshSheaf -> Int
sampleSectionAt c r = probeAt r c

-- | Observed section bundle — coalgebra output over all replica classes.
data ReplicaSectionBundle = ReplicaSectionBundle
  { secNode0 :: !Int
  , secNode1 :: !Int
  , secForge :: !Int
  , secLuks  :: !Int
  } deriving (Show, Eq)

replicaCoalgebraObserve :: ReplicaMeshSheaf -> ReplicaSectionBundle
replicaCoalgebraObserve r =
  ReplicaSectionBundle
    { secNode0 = node0SampleSection r
    , secNode1 = node1SampleSection r
    , secForge = forgeSampleSection r
    , secLuks  = luksSampleSection r
    }

replicaCoalgebraObserveComponents :: ReplicaMeshSheaf -> Bool
replicaCoalgebraObserveComponents r =
  let b = replicaCoalgebraObserve r
   in secNode0 b == node0SampleSection r
      && secNode1 b == node1SampleSection r
      && secForge b == forgeSampleSection r
      && secLuks b == luksSampleSection r

sampleSectionAtNode0 :: ReplicaMeshSheaf -> Bool
sampleSectionAtNode0 r =
  sampleSectionAt ReplicaNode0 r == node0SampleSection r

sampleSectionAtNode1 :: ReplicaMeshSheaf -> Bool
sampleSectionAtNode1 r =
  sampleSectionAt ReplicaNode1 r == node1SampleSection r

sampleSectionAtForge :: ReplicaMeshSheaf -> Bool
sampleSectionAtForge r =
  sampleSectionAt ReplicaForge r == forgeSampleSection r

sampleSectionAtLuks :: ReplicaMeshSheaf -> Bool
sampleSectionAtLuks r =
  sampleSectionAt ReplicaLuks r == luksSampleSection r

-- | Witness sheaf: sections differ across classes (not one XOR world).
witnessReplicaSheaf :: ReplicaMeshSheaf
witnessReplicaSheaf =
  ReplicaMeshSheaf
    { sectionProbe = \c -> case c of
        ReplicaNode0 -> 1
        ReplicaNode1 -> 2
        ReplicaForge -> 3
        ReplicaLuks  -> 4
    }

node0DoesNotCloseLuks :: Bool
node0DoesNotCloseLuks =
  node0SampleSection witnessReplicaSheaf
    /= luksSampleSection witnessReplicaSheaf

-- ---------------------------------------------------------------------------
-- SECTION 3: Network egress (offline LUKS carries empty egress)
-- ---------------------------------------------------------------------------

networkEgress :: ReplicaClass -> [String]
networkEgress c = case c of
  ReplicaLuks -> []
  _           -> ["tailscale-admin"]

luksNetworkEgressEmpty :: Bool
luksNetworkEgressEmpty = networkEgress ReplicaLuks == []

node0NetworkEgressTailscale :: Bool
node0NetworkEgressTailscale =
  networkEgress ReplicaNode0 == ["tailscale-admin"]

offlineLuksIsNetworkEgressEmpty :: Bool
offlineLuksIsNetworkEgressEmpty =
  luksNetworkEgressEmpty && replicaClassTagLuks

-- ---------------------------------------------------------------------------
-- SECTION 4: Admissible replica coalgebra (gate ∧ MergeSafe ∧ provenance)
-- ---------------------------------------------------------------------------

-- | Inbound replica history move with typed obligation slots.
data ReplicaHistoryMove = ReplicaHistoryMove
  { replicaPrior        :: !ThermodynamicState
  , replicaPost         :: !ThermodynamicState
  , replicaGateChecked  :: !Bool
  , replicaMergeSafe    :: !Bool
  , replicaProvenanceOk :: !Bool
  } deriving (Show, Eq)

admissibleReplicaCoalgebra :: ReplicaHistoryMove -> Bool
admissibleReplicaCoalgebra h =
  replicaGateChecked h
  && replicaMergeSafe h
  && replicaProvenanceOk h

admissibleReplicaCoalgebraIntro
  :: ReplicaHistoryMove -> Bool -> Bool -> Bool -> Bool
admissibleReplicaCoalgebraIntro h hg hm hp =
  hg && hm && hp && admissibleReplicaCoalgebra h

admitReplicaInbound :: ReplicaHistoryMove -> Bool
admitReplicaInbound = admissibleReplicaCoalgebra

-- ---------------------------------------------------------------------------
-- SECTION 5: Typed recovery morphism (Excitement — no second argmin)
-- ---------------------------------------------------------------------------

-- | Recovery context: prior state + admissible successor candidates.
data RecoveryCtx = RecoveryCtx
  { recoveryPrior      :: !ThermodynamicState
  , recoverySuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Typed recovery morphism composes 'excitementSelect' — not rsync theater.
typedRecoveryMorphism
  :: RecoveryCtx -> Either ExcitementResidue HistoryCandidate
typedRecoveryMorphism ctx =
  excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

typedRecoverySelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
typedRecoverySelect = excitementSelect

typedRecoveryMorphismEqExcitementSelect :: RecoveryCtx -> Bool
typedRecoveryMorphismEqExcitementSelect ctx =
  typedRecoveryMorphism ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

typedRecoverySelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
typedRecoverySelectEqExcitementSelect src cands =
  typedRecoverySelect src cands == excitementSelect src cands

typedRecoveryMorphismEqTypedRecoverySelect :: RecoveryCtx -> Bool
typedRecoveryMorphismEqTypedRecoverySelect ctx =
  typedRecoveryMorphism ctx
    == typedRecoverySelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Replica history recovery composes 'excitementSelect' on prior head.
replicaSelect
  :: RecoveryCtx -> Either ExcitementResidue HistoryCandidate
replicaSelect = typedRecoveryMorphism

replicaSelectEqExcitementSelect :: RecoveryCtx -> Bool
replicaSelectEqExcitementSelect = typedRecoveryMorphismEqExcitementSelect

replicaSelectEqTypedRecoverySelect :: RecoveryCtx -> Bool
replicaSelectEqTypedRecoverySelect = typedRecoveryMorphismEqTypedRecoverySelect

replicaNoLocalArgmin :: RecoveryCtx -> Bool
replicaNoLocalArgmin ctx =
  replicaSelect ctx
    == excitementSelect (recoveryPrior ctx) (recoverySuccessors ctx)

-- | Excitement compose pin — Urge imports selector; no second argmin.
data ReplicaExcitementComposePin
  = ReplicaImportSelectExcitement
  | ReplicaPinSecondArgminRefused
  deriving (Show, Eq)

replicaExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> ReplicaExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
replicaExcitementSelect src cands pin =
  case pin of
    ReplicaImportSelectExcitement -> excitementSelect src cands
    ReplicaPinSecondArgminRefused  -> Left ExcAllInadmissible

replicaExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
replicaExcitementSelectEqExcitementSelect src cands =
  replicaExcitementSelect src cands ReplicaImportSelectExcitement
    == excitementSelect src cands

replicaExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
replicaExcitementSelectRefusesSecondArgmin src cands =
  replicaExcitementSelect src cands ReplicaPinSecondArgminRefused
    == Left ExcAllInadmissible

replicaSelectEmpty :: ThermodynamicState -> Bool
replicaSelectEmpty src =
  replicaSelect
    (RecoveryCtx {recoveryPrior = src, recoverySuccessors = []})
    == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 6: §15.4 fixtures + witness theorems
-- ---------------------------------------------------------------------------

replicaFixtureState :: ThermodynamicState
replicaFixtureState = ThermodynamicState 2400 0 0.3 30 40

replicaFixtureAdmissibleMove :: ReplicaHistoryMove
replicaFixtureAdmissibleMove =
  ReplicaHistoryMove
    { replicaPrior = replicaFixtureState
    , replicaPost = ThermodynamicState 2500 0 0.3 30 40
    , replicaGateChecked = True
    , replicaMergeSafe = True
    , replicaProvenanceOk = True
    }

replicaFixtureInadmissibleMove :: ReplicaHistoryMove
replicaFixtureInadmissibleMove =
  ReplicaHistoryMove
    { replicaPrior = replicaFixtureState
    , replicaPost = ThermodynamicState 2500 0 0.3 30 40
    , replicaGateChecked = True
    , replicaMergeSafe = False
    , replicaProvenanceOk = True
    }

replicaFixtureAdmissibleOk :: Bool
replicaFixtureAdmissibleOk =
  admissibleReplicaCoalgebra replicaFixtureAdmissibleMove

replicaFixtureInadmissibleRefused :: Bool
replicaFixtureInadmissibleRefused =
  not (admissibleReplicaCoalgebra replicaFixtureInadmissibleMove)

replicaFixtureExcitementCompose :: Bool
replicaFixtureExcitementCompose =
  replicaExcitementSelect
    replicaFixtureState
    []
    ReplicaImportSelectExcitement
    == Left ExcNoCandidates

replicaFixtureClassesNotXor :: Bool
replicaFixtureClassesNotXor = replicaClassesNotXorHolds

replicaFixtureLuksOffline :: Bool
replicaFixtureLuksOffline = offlineLuksIsNetworkEgressEmpty

replicaPositiveRefuseNotSilent :: Bool
replicaPositiveRefuseNotSilent =
  not (admissibleReplicaCoalgebra replicaFixtureInadmissibleMove)

-- ---------------------------------------------------------------------------
-- SECTION 7: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Replica transition with thermodynamic accounting.
data ReplicaTransition = ReplicaTransition
  { replicaMove           :: !ReplicaHistoryMove
  , replicaBath           :: !HeatBath
  , replicaDissipatedWork :: !Double
  , replicaEntropyDrop    :: !Double
  } deriving (Show, Eq)

replicaSecondLaw :: ReplicaTransition -> Bool
replicaSecondLaw t =
  replicaEntropyDrop t
    <= replicaDissipatedWork t / bathTemp (replicaBath t)

-- | Physical bridge: Landauer discharge + admissible replica coalgebra.
data PhysicalReplicaBridge = PhysicalReplicaBridge
  { physicalLandauerBridge :: !LandauerHistoryBridge
  , physicalReplicaMove    :: !ReplicaHistoryMove
  , physicalAdmissible     :: !Bool
  } deriving (Show, Eq)

replicaSecondLawFromPhysical :: PhysicalReplicaBridge -> Bool -> Bool
replicaSecondLawFromPhysical b hSL =
  hSL
  && physicalAdmissible b
  && admitSecondLaw (landauerTransition (physicalLandauerBridge b))

admissibleReplicaCoalgebraFromPhysical
  :: PhysicalReplicaBridge -> Bool -> Bool
admissibleReplicaCoalgebraFromPhysical b hSL =
  hSL && physicalAdmissible b

replicaSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
replicaSecondLawFromHypothesis t ok = ok && admitSecondLaw t

replicaFromLandauerAdmitSecondLaw
  :: LandauerHistoryBridge -> Bool -> Bool
replicaFromLandauerAdmitSecondLaw b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- ---------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

replicaCoalgebraPhysicsGreen :: Bool
replicaCoalgebraPhysicsGreen = False

replicaCoalgebraPhysicsGreenFalse :: Bool
replicaCoalgebraPhysicsGreenFalse = not replicaCoalgebraPhysicsGreen

replicaCoalgebraProductionWired :: Bool
replicaCoalgebraProductionWired = False

replicaCoalgebraProductionWiredFalse :: Bool
replicaCoalgebraProductionWiredFalse = not replicaCoalgebraProductionWired

replicaCoalgebraNonClaim :: String
replicaCoalgebraNonClaim =
  "§15.4 admissible replica coalgebra; node-0/node-1/forge/luks are replica "
    ++ "classes not XOR worlds; typed recovery morphism composes excitementSelect "
    ++ "not second argmin; Landauer physicalSecondLaw cited; not physics GREEN; "
    ++ "not production_wired"

replicaCoalgebraNonClaimNonempty :: Bool
replicaCoalgebraNonClaimNonempty = length replicaCoalgebraNonClaim > 0

replicaCoalgebraModuleWitness :: Bool
replicaCoalgebraModuleWitness = True

replicaCoalgebraNoNewAxiom :: Bool
replicaCoalgebraNoNewAxiom = True

replicaCoalgebraNoSecondArgmin :: Bool
replicaCoalgebraNoSecondArgmin =
  replicaNoLocalArgmin
    (RecoveryCtx
      { recoveryPrior = replicaFixtureState
      , recoverySuccessors = []
      })

replicaCoalgebraNamedNotXor :: Bool
replicaCoalgebraNamedNotXor = replicaClassesNotXorHolds
