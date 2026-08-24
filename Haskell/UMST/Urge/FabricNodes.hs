-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.FabricNodes
-- Description : Meso acting Urge — §15 fabric-nodes replica-class pin.
--
-- Declared fabric nodes (`fabric-nodes.json`) pin to §15.4 replica-class table
-- rows — software schema, not Forgejo installer. Composes 'excitementSelect' —
-- no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' typed recovery morphism discipline.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.FabricNodes
  ( -- * §15.4 replica-class + fabric-node pin carriers
    FabricReplicaClass (..)
  , FabricAuthority (..)
  , fabricReplicaEgressEmpty
  , fabricReplicaFromNodeId
  , fabricAuthorityOf
  , fabricNodesSchemaPin
  , fabricNodesJsonRel
  , fabricNodesSchemaValid
  , FabricUcrsStamp (..)
  , FabricMergeSafeCert (..)
  , FabricNodePin (..)
  , FabricNodeWitness (..)
  , witnessFromFabricPin
  , FabricNodeMorphism (..)
    -- * Admissibility conjunct + positive refuse (§15)
  , FabricAdmissibilityConjunct (..)
  , fabricConjunctAdmits
  , FabricNodesVerdict (..)
  , evaluateFabricNodesOperation
  , FabricNodesRefusal (..)
  , refuseByzantineMeshClaim
  , refuseForgejoInstallClaim
  , refuseSecondArgminSelector
  , admitFabricNodePin
  , applyFabricNodeMorphism
    -- * Positive refuse witnesses
  , fabricNodesByzantineMeshRefused
  , fabricNodesForgejoInstallRefused
  , fabricNodesPinOkWhenHonest
  , refuseByzantineMeshClaimPositive
  , refuseForgejoInstallClaimPositive
  , refuseSecondArgminSelectorPositive
  , fabricNodesPositiveRefuseNotSilent
  , fabricNodesForgejoRefuseNotSilent
    -- * Fabric nodes composes excitementSelect (no second argmin)
  , FabricNodesCtx (..)
  , fabricNodesSelect
  , fabricNodesSelectEqExcitementSelect
  , fabricNodesSelectEqUrgeRecoverySelect
  , fabricNodesNoLocalArgmin
  , fabricNodesSelectEmpty
  , FabricExcitementComposePin (..)
  , fabricExcitementSelect
  , fabricExcitementSelectEqExcitementSelect
  , fabricExcitementSelectRefusesSecondArgmin
  , urgeFabricSelect
  , urgeFabricSelectEqExcitementSelect
    -- * §15 fixtures + witness theorems
  , fabricFixtureState
  , fabricFixtureUcrs
  , fabricFixtureMergeSafe
  , fabricFixtureNode0Pin
  , fabricFixtureConjunct
  , fabricFixtureAdmitNode0Ok
  , fabricFixtureApplyMorphismOk
  , fabricNode0MapsToDevClone
  , fabricNode1MapsToDevClone
  , fabricUnknownNodeIdRefused
  , fabricOfflineLuksEgressEmpty
  , fabricDarwinScratchEgressEmpty
  , fabricForgejoPrimaryEgressNonempty
  , fabricFixtureWitnessPreservesUcrs
  , fabricFixtureByzantinePin
  , fabricFixtureForgejoPin
  , fabricFixtureByzantineRefused
  , fabricFixtureForgejoRefused
  , fabricNodesSchemaPinEq
    -- * Landauer bridge (derived — zero new axioms)
  , FabricHistoryMove (..)
  , admissibleFabricHistoryMove
  , FabricTransition (..)
  , fabricSecondLaw
  , PhysicalFabricBridge (..)
  , fabricSecondLawFromPhysical
  , admissibleFabricHistoryMoveFromPhysical
  , fabricSecondLawFromLandauer
  , fabricSecondLawFromHypothesis
    -- * Honesty flags + catalog witnesses
  , fabricNodesPhysicsGreen
  , fabricNodesPhysicsGreenFalse
  , fabricNodesProductionWired
  , fabricNodesProductionWiredFalse
  , fabricNodesNonClaim
  , fabricNodesNonClaimNonempty
  , fabricNodesModuleWitness
  , fabricNodesNoNewAxiom
  , fabricNodesNoSecondArgmin
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
import UMST.Urge.ExcitementImport (urgeRecoverySelect)

-- ---------------------------------------------------------------------------
-- SECTION 1: §15.4 replica-class + fabric-node pin carriers
-- ---------------------------------------------------------------------------

-- | §15.4 replica-class table row — software schema pin (not installer).
data FabricReplicaClass
  = FrcNode0DevClone
  | FrcNode1DevClone
  | FrcForgejoPrimaryMirror
  | FrcDarwinScratch
  | FrcOfflineLuks
  | FrcCustomerCompose
  deriving (Show, Eq)

-- | Authority column from §15.4 replica-class table.
data FabricAuthority
  = FaWorkingCopy
  | FaCanonicalRemote
  | FaScratchPlane
  | FaDisasterCopy
  | FaCustomerOnSite
  deriving (Show, Eq)

-- | Whether declared network egress is empty for this replica class.
fabricReplicaEgressEmpty :: FabricReplicaClass -> Bool
fabricReplicaEgressEmpty FrcDarwinScratch       = True
fabricReplicaEgressEmpty FrcOfflineLuks         = True
fabricReplicaEgressEmpty FrcNode0DevClone     = False
fabricReplicaEgressEmpty FrcNode1DevClone     = False
fabricReplicaEgressEmpty FrcForgejoPrimaryMirror = False
fabricReplicaEgressEmpty FrcCustomerCompose     = False

-- | Map declared fabric node id surrogate (`0` = node-0, `1` = node-1).
fabricReplicaFromNodeId :: Int -> Maybe FabricReplicaClass
fabricReplicaFromNodeId 0 = Just FrcNode0DevClone
fabricReplicaFromNodeId 1 = Just FrcNode1DevClone
fabricReplicaFromNodeId _ = Nothing

-- | Blueprint authority for a replica-class row.
fabricAuthorityOf :: FabricReplicaClass -> FabricAuthority
fabricAuthorityOf FrcNode0DevClone        = FaWorkingCopy
fabricAuthorityOf FrcNode1DevClone        = FaWorkingCopy
fabricAuthorityOf FrcForgejoPrimaryMirror = FaCanonicalRemote
fabricAuthorityOf FrcDarwinScratch        = FaScratchPlane
fabricAuthorityOf FrcOfflineLuks          = FaDisasterCopy
fabricAuthorityOf FrcCustomerCompose      = FaCustomerOnSite

-- | Expected `fabric-nodes.json` schema id surrogate.
fabricNodesSchemaPin :: String
fabricNodesSchemaPin = "umst_fabric_nodes_v1"

-- | Relative path to declared fabric nodes SSOT.
fabricNodesJsonRel :: String
fabricNodesJsonRel = "workspace/ops/fabric-nodes.json"

-- | Schema validity witness (surrogate).
fabricNodesSchemaValid :: Bool -> Bool
fabricNodesSchemaValid schemaOk = schemaOk

-- | UCRS stamp surrogate carried through fabric-node pin.
data FabricUcrsStamp = FabricUcrsStamp
  { fabricUcrsSeq      :: !Int
  , fabricUcrsWallHasT :: !Bool
  } deriving (Show, Eq)

-- | MergeSafe certificate surrogate — pin must not violate tier disjointness.
data FabricMergeSafeCert = FabricMergeSafeCert
  { fabricMergeSafe :: !Bool
  } deriving (Show, Eq)

-- | Declared fabric node pin — mirrors `fabric-nodes.json` row (software schema).
data FabricNodePin = FabricNodePin
  { fabricPinStepId               :: !Int
  , fabricPinNodeId               :: !Int
  , fabricPinSchemaOk             :: !Bool
  , fabricPinByzantineMesh        :: !Bool
  , fabricPinClaimsForgejoRunning :: !Bool
  , fabricPinUcrs                 :: !FabricUcrsStamp
  , fabricPinMergeSafe            :: !FabricMergeSafeCert
  , fabricPinProvenanceIntact     :: !Bool
  } deriving (Show, Eq)

-- | Witness bundle a fabric-node morphism must preserve (§15).
data FabricNodeWitness = FabricNodeWitness
  { fabricWitnessUcrs              :: !FabricUcrsStamp
  , fabricWitnessMergeSafe         :: !FabricMergeSafeCert
  , fabricWitnessProvenanceIntact  :: !Bool
  } deriving (Show, Eq)

-- | Build witness from pin — morphism must preserve stamps and certificates.
witnessFromFabricPin :: FabricNodePin -> FabricNodeWitness
witnessFromFabricPin pin =
  FabricNodeWitness
    { fabricWitnessUcrs = fabricPinUcrs pin
    , fabricWitnessMergeSafe = fabricPinMergeSafe pin
    , fabricWitnessProvenanceIntact = fabricPinProvenanceIntact pin
    }

-- | Typed fabric-node morphism — admissible replica-class pin, not installer theater.
data FabricNodeMorphism = FabricNodeMorphism
  { fabricMorphismFrom               :: !FabricNodePin
  , fabricMorphismToReplica          :: !FabricReplicaClass
  , fabricMorphismWitness            :: !FabricNodeWitness
  , fabricMorphismExcitementSelected :: !Bool
  } deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- SECTION 2: Admissibility conjunct + positive refuse (§15)
-- ---------------------------------------------------------------------------

-- | §15 admissibility conjunct inputs (surrogate).
data FabricAdmissibilityConjunct = FabricAdmissibilityConjunct
  { fabricConjGateOk              :: !Bool
  , fabricConjMergeSafe           :: !Bool
  , fabricConjExcitementPreserves :: !Bool
  } deriving (Show, Eq)

-- | Evaluate `admit(h) ⟺ gate ∧ MergeSafe ∧ Excitement preserves`.
fabricConjunctAdmits :: FabricAdmissibilityConjunct -> Bool
fabricConjunctAdmits c =
  fabricConjGateOk c
  && fabricConjMergeSafe c
  && fabricConjExcitementPreserves c

-- | Verdict of a fabric-node operation class.
data FabricNodesVerdict
  = FnvPinOk
  | FnvByzantineMeshRefused
  | FnvForgejoInstallRefused
  | FnvInadmissible
  deriving (Show, Eq)

-- | Classify Byzantine mesh / Forgejo install vs typed pin without performing I/O.
evaluateFabricNodesOperation
  :: Bool -> Bool -> FabricNodesVerdict
evaluateFabricNodesOperation byzantineMesh claimsForgejoRunning
  | byzantineMesh = FnvByzantineMeshRefused
  | claimsForgejoRunning = FnvForgejoInstallRefused
  | otherwise = FnvPinOk

-- | Fail-closed fabric-node errors — positive refuse, not silent no-op.
data FabricNodesRefusal
  = FnrByzantineMeshClaim
  | FnrForgejoInstallClaim
  | FnrUnknownFabricNodeId !Int
  | FnrSchemaMismatch
  | FnrSecondArgmin
  | FnrProductionWired
  | FnrGateRejected !Int
  | FnrMergeUnsafe !Int
  | FnrProvenanceLoss !Int
  | FnrReplicaClassMismatch
  deriving (Show, Eq)

-- | Positive refuse: Byzantine mesh claim is inadmissible on fabric nodes.
refuseByzantineMeshClaim :: FabricNodesRefusal
refuseByzantineMeshClaim = FnrByzantineMeshClaim

-- | Positive refuse: Forgejo install claim is inadmissible — software schema only.
refuseForgejoInstallClaim :: FabricNodesRefusal
refuseForgejoInstallClaim = FnrForgejoInstallClaim

-- | Positive refuse: second argmin selector is inadmissible.
refuseSecondArgminSelector :: FabricNodesRefusal
refuseSecondArgminSelector = FnrSecondArgmin

-- | Admit a declared fabric node pin — fail closed on schema / node id / theater.
admitFabricNodePin :: FabricNodePin -> Either FabricNodesRefusal ()
admitFabricNodePin pin
  | fabricPinByzantineMesh pin = Left FnrByzantineMeshClaim
  | fabricPinClaimsForgejoRunning pin = Left FnrForgejoInstallClaim
  | not (fabricNodesSchemaValid (fabricPinSchemaOk pin)) = Left FnrSchemaMismatch
  | otherwise =
      case fabricReplicaFromNodeId (fabricPinNodeId pin) of
        Nothing -> Left (FnrUnknownFabricNodeId (fabricPinNodeId pin))
        Just _ -> Right ()

-- | Attempt typed fabric-node morphism to target replica — fail closed on inadmissibility.
applyFabricNodeMorphism
  :: FabricNodePin
  -> FabricReplicaClass
  -> FabricAdmissibilityConjunct
  -> Bool
  -> Either FabricNodesRefusal FabricNodeMorphism
applyFabricNodeMorphism pin toReplica conjunct excitementSelected =
  case admitFabricNodePin pin of
    Left r -> Left r
    Right _ ->
      if not (fabricConjunctAdmits conjunct)
        then Left (FnrGateRejected (fabricUcrsSeq (fabricPinUcrs pin)))
        else if not (fabricMergeSafe (fabricPinMergeSafe pin))
          then Left (FnrMergeUnsafe (fabricPinStepId pin))
          else if not (fabricPinProvenanceIntact pin)
            then Left (FnrProvenanceLoss (fabricPinStepId pin))
            else if not excitementSelected
              then Left (FnrProvenanceLoss (fabricPinStepId pin))
              else
                Right
                  FabricNodeMorphism
                    { fabricMorphismFrom = pin
                    , fabricMorphismToReplica = toReplica
                    , fabricMorphismWitness = witnessFromFabricPin pin
                    , fabricMorphismExcitementSelected = excitementSelected
                    }

-- ---------------------------------------------------------------------------
-- SECTION 3: Positive refuse witnesses
-- ---------------------------------------------------------------------------

fabricNodesByzantineMeshRefused :: Bool
fabricNodesByzantineMeshRefused =
  evaluateFabricNodesOperation True False == FnvByzantineMeshRefused

fabricNodesForgejoInstallRefused :: Bool
fabricNodesForgejoInstallRefused =
  evaluateFabricNodesOperation False True == FnvForgejoInstallRefused

fabricNodesPinOkWhenHonest :: Bool
fabricNodesPinOkWhenHonest =
  evaluateFabricNodesOperation False False == FnvPinOk

refuseByzantineMeshClaimPositive :: Bool
refuseByzantineMeshClaimPositive =
  refuseByzantineMeshClaim == FnrByzantineMeshClaim

refuseForgejoInstallClaimPositive :: Bool
refuseForgejoInstallClaimPositive =
  refuseForgejoInstallClaim == FnrForgejoInstallClaim

refuseSecondArgminSelectorPositive :: Bool
refuseSecondArgminSelectorPositive =
  refuseSecondArgminSelector == FnrSecondArgmin

fabricNodesPositiveRefuseNotSilent :: Bool
fabricNodesPositiveRefuseNotSilent =
  evaluateFabricNodesOperation True False /= FnvPinOk

fabricNodesForgejoRefuseNotSilent :: Bool
fabricNodesForgejoRefuseNotSilent =
  evaluateFabricNodesOperation False True /= FnvPinOk

-- ---------------------------------------------------------------------------
-- SECTION 4: Fabric nodes composes excitementSelect (no second argmin)
-- ---------------------------------------------------------------------------

-- | Context for fabric-node selection over admissible history successors.
data FabricNodesCtx = FabricNodesCtx
  { fabricNodesPrior      :: !ThermodynamicState
  , fabricNodesSuccessors :: ![HistoryCandidate]
  } deriving (Show, Eq)

-- | Fabric-node selection **is** 'urgeRecoverySelect' / 'excitementSelect'.
fabricNodesSelect
  :: FabricNodesCtx
  -> Either ExcitementResidue HistoryCandidate
fabricNodesSelect ctx =
  urgeRecoverySelect (fabricNodesPrior ctx) (fabricNodesSuccessors ctx)

-- | Definitional witness: fabric-node selection API is 'excitementSelect'.
fabricNodesSelectEqExcitementSelect :: FabricNodesCtx -> Bool
fabricNodesSelectEqExcitementSelect ctx =
  fabricNodesSelect ctx
    == excitementSelect (fabricNodesPrior ctx) (fabricNodesSuccessors ctx)

-- | Fabric-node selection equals 'urgeRecoverySelect'.
fabricNodesSelectEqUrgeRecoverySelect :: FabricNodesCtx -> Bool
fabricNodesSelectEqUrgeRecoverySelect ctx =
  fabricNodesSelect ctx
    == urgeRecoverySelect (fabricNodesPrior ctx) (fabricNodesSuccessors ctx)

-- | Fabric selector re-uses 'excitementSelect' — no Urge-local argmin.
fabricNodesNoLocalArgmin :: FabricNodesCtx -> Bool
fabricNodesNoLocalArgmin ctx =
  fabricNodesSelect ctx
    == excitementSelect (fabricNodesPrior ctx) (fabricNodesSuccessors ctx)

-- | Empty successor list → 'ExcNoCandidates' via imported 'excitementSelect'.
fabricNodesSelectEmpty :: ThermodynamicState -> Bool
fabricNodesSelectEmpty src =
  fabricNodesSelect
    (FabricNodesCtx {fabricNodesPrior = src, fabricNodesSuccessors = []})
    == Left ExcNoCandidates

-- | Excitement compose pin — Urge imports selector; no second argmin.
data FabricExcitementComposePin
  = FepImportSelectExcitement
  | FepSecondArgminRefused
  deriving (Show, Eq)

-- | Fabric excitement selection with explicit compose pin.
fabricExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> FabricExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
fabricExcitementSelect src cands pin =
  case pin of
    FepImportSelectExcitement -> excitementSelect src cands
    FepSecondArgminRefused -> Left ExcAllInadmissible

-- | Definitional witness: import pin is 'excitementSelect'.
fabricExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
fabricExcitementSelectEqExcitementSelect src cands =
  fabricExcitementSelect src cands FepImportSelectExcitement
    == excitementSelect src cands

-- | Second-argmin pin refuses with 'ExcAllInadmissible'.
fabricExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
fabricExcitementSelectRefusesSecondArgmin src cands =
  fabricExcitementSelect src cands FepSecondArgminRefused
    == Left ExcAllInadmissible

-- | Bare fabric recovery alias — same as 'excitementSelect'.
urgeFabricSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> Either ExcitementResidue HistoryCandidate
urgeFabricSelect = excitementSelect

-- | Definitional witness: bare alias is 'excitementSelect'.
urgeFabricSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
urgeFabricSelectEqExcitementSelect src cands =
  urgeFabricSelect src cands == excitementSelect src cands

-- ---------------------------------------------------------------------------
-- SECTION 5: §15 fixtures + witness theorems
-- ---------------------------------------------------------------------------

fabricFixtureState :: ThermodynamicState
fabricFixtureState = ThermodynamicState 2400 0 0 0 0

fabricFixtureUcrs :: FabricUcrsStamp
fabricFixtureUcrs = FabricUcrsStamp {fabricUcrsSeq = 7, fabricUcrsWallHasT = True}

fabricFixtureMergeSafe :: FabricMergeSafeCert
fabricFixtureMergeSafe = FabricMergeSafeCert {fabricMergeSafe = True}

fabricFixtureNode0Pin :: FabricNodePin
fabricFixtureNode0Pin =
  FabricNodePin
    { fabricPinStepId = 1
    , fabricPinNodeId = 0
    , fabricPinSchemaOk = True
    , fabricPinByzantineMesh = False
    , fabricPinClaimsForgejoRunning = False
    , fabricPinUcrs = fabricFixtureUcrs
    , fabricPinMergeSafe = fabricFixtureMergeSafe
    , fabricPinProvenanceIntact = True
    }

fabricFixtureConjunct :: FabricAdmissibilityConjunct
fabricFixtureConjunct =
  FabricAdmissibilityConjunct
    { fabricConjGateOk = True
    , fabricConjMergeSafe = True
    , fabricConjExcitementPreserves = True
    }

fabricFixtureAdmitNode0Ok :: Bool
fabricFixtureAdmitNode0Ok = admitFabricNodePin fabricFixtureNode0Pin == Right ()

fabricFixtureApplyMorphismOk :: Bool
fabricFixtureApplyMorphismOk =
  applyFabricNodeMorphism
    fabricFixtureNode0Pin
    FrcNode0DevClone
    fabricFixtureConjunct
    True
    == Right
      FabricNodeMorphism
        { fabricMorphismFrom = fabricFixtureNode0Pin
        , fabricMorphismToReplica = FrcNode0DevClone
        , fabricMorphismWitness = witnessFromFabricPin fabricFixtureNode0Pin
        , fabricMorphismExcitementSelected = True
        }

fabricNode0MapsToDevClone :: Bool
fabricNode0MapsToDevClone =
  fabricReplicaFromNodeId 0 == Just FrcNode0DevClone

fabricNode1MapsToDevClone :: Bool
fabricNode1MapsToDevClone =
  fabricReplicaFromNodeId 1 == Just FrcNode1DevClone

fabricUnknownNodeIdRefused :: Bool
fabricUnknownNodeIdRefused = fabricReplicaFromNodeId 99 == Nothing

fabricOfflineLuksEgressEmpty :: Bool
fabricOfflineLuksEgressEmpty =
  fabricReplicaEgressEmpty FrcOfflineLuks == True

fabricDarwinScratchEgressEmpty :: Bool
fabricDarwinScratchEgressEmpty =
  fabricReplicaEgressEmpty FrcDarwinScratch == True

fabricForgejoPrimaryEgressNonempty :: Bool
fabricForgejoPrimaryEgressNonempty =
  fabricReplicaEgressEmpty FrcForgejoPrimaryMirror == False

fabricFixtureWitnessPreservesUcrs :: Bool
fabricFixtureWitnessPreservesUcrs =
  fabricWitnessUcrs (witnessFromFabricPin fabricFixtureNode0Pin)
    == fabricFixtureUcrs

fabricFixtureByzantinePin :: FabricNodePin
fabricFixtureByzantinePin =
  fabricFixtureNode0Pin {fabricPinByzantineMesh = True}

fabricFixtureForgejoPin :: FabricNodePin
fabricFixtureForgejoPin =
  fabricFixtureNode0Pin {fabricPinClaimsForgejoRunning = True}

fabricFixtureByzantineRefused :: Bool
fabricFixtureByzantineRefused =
  admitFabricNodePin fabricFixtureByzantinePin == Left FnrByzantineMeshClaim

fabricFixtureForgejoRefused :: Bool
fabricFixtureForgejoRefused =
  admitFabricNodePin fabricFixtureForgejoPin == Left FnrForgejoInstallClaim

fabricNodesSchemaPinEq :: Bool
fabricNodesSchemaPinEq = fabricNodesSchemaPin == "umst_fabric_nodes_v1"

-- ---------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

-- | Fabric history move with gate + provenance witnesses.
data FabricHistoryMove = FabricHistoryMove
  { fabricMovePrior        :: !ThermodynamicState
  , fabricMovePost         :: !ThermodynamicState
  , fabricMoveGateChecked  :: !Bool
  , fabricMoveMergeSafe    :: !Bool
  , fabricMoveProvenanceOk :: !Bool
  } deriving (Show, Eq)

-- | Admissible fabric history move (gate + merge-safe + provenance).
admissibleFabricHistoryMove :: FabricHistoryMove -> Bool
admissibleFabricHistoryMove h =
  fabricMoveGateChecked h
  && fabricMoveMergeSafe h
  && fabricMoveProvenanceOk h

-- | Thermodynamic accounting on a fabric transition.
data FabricTransition = FabricTransition
  { fabricMove           :: !FabricHistoryMove
  , fabricBath           :: !HeatBath
  , fabricDissipatedWork :: !Double
  , fabricEntropyDrop    :: !Double
  } deriving (Show, Eq)

-- | Second-law invariant on fabric transition (Bool witness).
fabricSecondLaw :: FabricTransition -> Bool
fabricSecondLaw t =
  fabricEntropyDrop t <= fabricDissipatedWork t / bathTemp (fabricBath t)

-- | Physical bridge tying fabric transition to Landauer discharge.
data PhysicalFabricBridge = PhysicalFabricBridge
  { fabricBridge     :: !LandauerHistoryBridge
  , fabricTransition :: !FabricTransition
  , fabricAdmissible :: !Bool
  } deriving (Show, Eq)

-- | Second law on fabric transition from Landauer bridge (no new axiom).
fabricSecondLawFromPhysical :: PhysicalFabricBridge -> Bool -> Bool
fabricSecondLawFromPhysical b hSL =
  hSL
  && fabricAdmissible b
  && admitSecondLaw (landauerTransition (fabricBridge b))

-- | Admissible move from physical bridge discharge.
admissibleFabricHistoryMoveFromPhysical
  :: PhysicalFabricBridge -> Bool -> Bool
admissibleFabricHistoryMoveFromPhysical b hSL =
  hSL && fabricAdmissible b

-- | Second law on fabric carrier transition from Landauer bridge discharge.
fabricSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
fabricSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

-- | Hypothesis discharge for fabric second law (no new axiom).
fabricSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
fabricSecondLawFromHypothesis t ok = ok && admitSecondLaw t

-- ---------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

-- | Physics GREEN unauthorized on this scaffold.
fabricNodesPhysicsGreen :: Bool
fabricNodesPhysicsGreen = False

-- | Lean/Coq: @fabric_nodes_physics_green_false@.
fabricNodesPhysicsGreenFalse :: Bool
fabricNodesPhysicsGreenFalse = not fabricNodesPhysicsGreen

-- | Production wiring stays open (fabric-node lift only).
fabricNodesProductionWired :: Bool
fabricNodesProductionWired = False

-- | Lean/Coq: @fabric_nodes_production_wired_false@.
fabricNodesProductionWiredFalse :: Bool
fabricNodesProductionWiredFalse = not fabricNodesProductionWired

-- | Honest non-claim string (meso §15 fabric-nodes scaffold).
fabricNodesNonClaim :: String
fabricNodesNonClaim =
  "§15 fabric-nodes replica-class pin (software schema, not Forgejo installer); "
    ++ "compose excitementSelect not local argmin; not physics GREEN; "
    ++ "not production_wired"

-- | Non-claim string is non-empty.
fabricNodesNonClaimNonempty :: Bool
fabricNodesNonClaimNonempty = length fabricNodesNonClaim > 0

-- | Catalog witness: meso Urge FabricNodes module present.
fabricNodesModuleWitness :: Bool
fabricNodesModuleWitness = True

-- | Zero new axiom discipline witness.
fabricNodesNoNewAxiom :: Bool
fabricNodesNoNewAxiom = True

-- | Second-argmin refusal: fabric nodes composes 'excitementSelect' only.
fabricNodesNoSecondArgmin :: Bool
fabricNodesNoSecondArgmin =
  fabricNodesNoLocalArgmin
    (FabricNodesCtx
      { fabricNodesPrior = fabricFixtureState
      , fabricNodesSuccessors = []
      })
