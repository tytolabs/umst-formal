-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.ReplicaClass
-- Description : Meso acting Urge — §15.4 replica-class table + fabric-nodes pin.
--
-- §15.4: replica-class table + `fabric-nodes.json` `class` field pin.
-- Positive refuse via typed errors — not only `!physics_green`. Fabric-nodes
-- consume this table. Composes 'excitementSelect' — no second argmin.
--
-- Mirrors 'UMST.Urge.CollaborativeObject' / Lean @Urge.ReplicaClass@.
-- Anchored in 'UMST.Urge.AdmitKleisli.admitSecondLaw' via Landauer bridge.
-- Sole physics axiom remains on Lean @LandauerLaw.physicalSecondLaw@ (cited,
-- not restated). Adds zero new physics axioms. Knowing fiber (EpistemicMI) lives
-- on @umst-formal-double-slit@ — cited, not restated here.
module UMST.Urge.ReplicaClass
  ( -- * §15.4 replica-class table (six named rows)
    ReplicaClassLabel (..)
  , replicaClassClassField
  , rclNode0LegacyField
  , rclNode1LegacyField
  , parseReplicaClassField
  , ReplicaNetworkEgress (..)
  , replicaEgressEmpty
  , ReplicaAuthority (..)
  , ReplicaClassTableRow (..)
  , replicaClassBlueprintRow
  , replicaClassTableCardinality
  , replicaClassLabelToNat
    -- * fabric-nodes.json class pin + positive refuse
  , FabricNodeClassPin (..)
  , ReplicaClassAdmit (..)
  , FabricNodeClassVerdict (..)
  , ReplicaClassRefusal (..)
  , FabricNodeClassRow (..)
  , evaluateFabricNodeClass
  , refuseInventedPhysicsGreen
  , refuseMissingClassField
  , refuseCustomerComposeLabsGossip
  , refuseSecondExcitementArgmin
  , refuseInventedPhysicsGreenPositive
  , refuseMissingClassFieldPositive
  , refuseCustomerComposeLabsGossipPositive
  , refuseSecondExcitementArgminPositive
    -- * Replica class composes excitementSelect (no argmin)
  , ReplicaExcitementComposePin (..)
  , ReplicaClassCtx (..)
  , composeReplicaExcitementSelect
  , replicaClassSelect
  , composeReplicaExcitementSelectEqExcitementSelect
  , replicaClassSelectEqExcitementSelect
  , replicaClassSelectEqUrgeRecoverySelect
  , replicaClassNoLocalArgmin
  , composeReplicaExcitementSelectRefusesSecondArgmin
  , replicaClassSelectEmpty
    -- * fabric-nodes.json census + §15.4 fixtures
  , fabricNodesJsonRel
  , fabricNodesSchemaPin
  , replicaClassFixtureState
  , replicaClassFixtureNode0Pin
  , replicaClassFixtureInventGreenPin
  , replicaClassFixtureComposeGossipPin
  , replicaClassFixtureNode0Admitted
  , replicaClassFixtureInventGreenRefused
  , replicaClassFixtureComposeGossipRefused
  , replicaClassOfflineLuksEgressEmpty
  , replicaClassDarwinScratchEgressEmpty
  , replicaClassForgejoEgressNonempty
  , replicaClassTableCardinalitySix
  , replicaClassNode0ClassField
  , replicaClassParseLegacyNode0
  , replicaClassParseUnknownNone
  , replicaClassPositiveRefuseNotSilent
  , replicaClassComposeExcitementNotArgmin
    -- * Landauer bridge (derived — zero new axioms)
  , replicaClassSecondLawFromLandauer
  , replicaClassSecondLawFromHypothesis
  , physicalSecondLawImported
  , landauerAnchorCited
    -- * Honesty flags + catalog witnesses
  , replicaClassPhysicsGreen
  , replicaClassPhysicsGreenFalse
  , replicaClassProductionWired
  , replicaClassProductionWiredFalse
  , replicaClassMarker
  , replicaClassMarkerEq
  , replicaClassModuleWitness
  , replicaClassNoNewAxiom
  , replicaClassNoSecondArgmin
  , replicaClassNonClaim
  , replicaClassNonClaimNonempty
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
-- SECTION 1: §15.4 replica-class table (six named rows)
-- ---------------------------------------------------------------------------

-- | Named replica class row from blueprint §15.4.
data ReplicaClassLabel
  = Node0DevClone
  | Node1DevClone
  | ForgejoPrimaryMirror
  | DarwinScratch
  | OfflineLuks
  | CustomerCompose
  deriving (Show, Eq)

-- | Stable `fabric-nodes.json` `class` field value.
replicaClassClassField :: ReplicaClassLabel -> String
replicaClassClassField Node0DevClone         = "node-0-dev-clone"
replicaClassClassField Node1DevClone         = "node-1-dev-clone"
replicaClassClassField ForgejoPrimaryMirror  = "forgejo-primary-mirror"
replicaClassClassField DarwinScratch         = "darwin-scratch"
replicaClassClassField OfflineLuks           = "offline-luks"
replicaClassClassField CustomerCompose       = "customer-compose"

rclNode0LegacyField :: String
rclNode0LegacyField = "node-0"

rclNode1LegacyField :: String
rclNode1LegacyField = "node-1"

-- | Parse a `class` field string into a §15.4 row (also accepts legacy node ids).
parseReplicaClassField :: String -> Maybe ReplicaClassLabel
parseReplicaClassField raw
  | raw == "node-0-dev-clone"       = Just Node0DevClone
  | raw == rclNode0LegacyField      = Just Node0DevClone
  | raw == "node-1-dev-clone"       = Just Node1DevClone
  | raw == rclNode1LegacyField      = Just Node1DevClone
  | raw == "forgejo-primary-mirror" = Just ForgejoPrimaryMirror
  | raw == "darwin-scratch"         = Just DarwinScratch
  | raw == "offline-luks"           = Just OfflineLuks
  | raw == "customer-compose"         = Just CustomerCompose
  | otherwise                       = Nothing

-- | Network egress column from §15.4 replica-class table.
data ReplicaNetworkEgress
  = TailscaleAdminOnly
  | TailscaleNoPublicPorts
  | EgressEmpty
  | MountOnly
  | CustomerPolicy
  deriving (Show, Eq)

-- | Whether egress is explicitly empty (offline LUKS / Darwin scratch).
replicaEgressEmpty :: ReplicaNetworkEgress -> Bool
replicaEgressEmpty EgressEmpty = True
replicaEgressEmpty MountOnly   = True
replicaEgressEmpty _           = False

-- | Authority column from §15.4 replica-class table.
data ReplicaAuthority
  = WorkingCopy
  | CanonicalRemote
  | BackupScratch
  | DisasterCopy
  | OnSiteRecord
  deriving (Show, Eq)

-- | One §15.4 replica-class table row — network egress + authority typed.
data ReplicaClassTableRow = ReplicaClassTableRow
  { replicaRowClass     :: !ReplicaClassLabel
  , replicaRowEgress    :: !ReplicaNetworkEgress
  , replicaRowAuthority :: !ReplicaAuthority
  } deriving (Show, Eq)

-- | Blueprint §15.4 default row for a named replica class.
replicaClassBlueprintRow :: ReplicaClassLabel -> ReplicaClassTableRow
replicaClassBlueprintRow Node0DevClone =
  ReplicaClassTableRow
    { replicaRowClass = Node0DevClone
    , replicaRowEgress = TailscaleAdminOnly
    , replicaRowAuthority = WorkingCopy
    }
replicaClassBlueprintRow Node1DevClone =
  ReplicaClassTableRow
    { replicaRowClass = Node1DevClone
    , replicaRowEgress = TailscaleAdminOnly
    , replicaRowAuthority = WorkingCopy
    }
replicaClassBlueprintRow ForgejoPrimaryMirror =
  ReplicaClassTableRow
    { replicaRowClass = ForgejoPrimaryMirror
    , replicaRowEgress = TailscaleNoPublicPorts
    , replicaRowAuthority = CanonicalRemote
    }
replicaClassBlueprintRow DarwinScratch =
  ReplicaClassTableRow
    { replicaRowClass = DarwinScratch
    , replicaRowEgress = MountOnly
    , replicaRowAuthority = BackupScratch
    }
replicaClassBlueprintRow OfflineLuks =
  ReplicaClassTableRow
    { replicaRowClass = OfflineLuks
    , replicaRowEgress = EgressEmpty
    , replicaRowAuthority = DisasterCopy
    }
replicaClassBlueprintRow CustomerCompose =
  ReplicaClassTableRow
    { replicaRowClass = CustomerCompose
    , replicaRowEgress = CustomerPolicy
    , replicaRowAuthority = OnSiteRecord
    }

replicaClassTableCardinality :: Int
replicaClassTableCardinality = 6

replicaClassLabelToNat :: ReplicaClassLabel -> Int
replicaClassLabelToNat Node0DevClone        = 0
replicaClassLabelToNat Node1DevClone        = 1
replicaClassLabelToNat ForgejoPrimaryMirror = 2
replicaClassLabelToNat DarwinScratch        = 3
replicaClassLabelToNat OfflineLuks          = 4
replicaClassLabelToNat CustomerCompose      = 5

-- ---------------------------------------------------------------------------
-- SECTION 2: fabric-nodes.json class pin + positive refuse
-- ---------------------------------------------------------------------------

-- | Fabric node pin — `fabric-nodes.json` node with optional `class` field.
data FabricNodeClassPin = FabricNodeClassPin
  { fabricNodeId               :: !String
  , fabricClassField           :: !(Maybe String)
  , fabricPhysicsGreenClaim    :: !Bool
  , fabricJoinsLabsPublicGossip :: !Bool
  } deriving (Show, Eq)

data ReplicaClassAdmit = ReplicaClassAdmitted deriving (Show, Eq)

data FabricNodeClassVerdict = FabricNodeClassAccept deriving (Show, Eq)

-- | Typed refusal — positive errors, not silent `!physics_green`.
data ReplicaClassRefusal
  = MissingClassField
  | UnknownReplicaClass
  | InventedPhysicsGreen
  | CustomerComposeLabsGossip
  | SecondExcitementArgmin
  deriving (Show, Eq)

-- | Evaluated fabric node class row after §15.4 gate.
data FabricNodeClassRow = FabricNodeClassRow
  { fabricRowNodeId   :: !String
  , fabricRowClass    :: !ReplicaClassLabel
  , fabricRowTable    :: !ReplicaClassTableRow
  , fabricRowVerdict  :: !FabricNodeClassVerdict
  , fabricRowAdmit    :: !ReplicaClassAdmit
  } deriving (Show, Eq)

-- | Evaluate one fabric node `class` pin against §15.4 table.
evaluateFabricNodeClass
  :: FabricNodeClassPin
  -> Either ReplicaClassRefusal FabricNodeClassRow
evaluateFabricNodeClass pin
  | fabricPhysicsGreenClaim pin =
      Left InventedPhysicsGreen
  | otherwise =
      case fabricClassField pin of
        Nothing -> Left MissingClassField
        Just raw ->
          case parseReplicaClassField raw of
            Nothing -> Left UnknownReplicaClass
            Just cls ->
              if cls == CustomerCompose && fabricJoinsLabsPublicGossip pin
                then Left CustomerComposeLabsGossip
                else
                  Right
                    FabricNodeClassRow
                      { fabricRowNodeId = fabricNodeId pin
                      , fabricRowClass = cls
                      , fabricRowTable = replicaClassBlueprintRow cls
                      , fabricRowVerdict = FabricNodeClassAccept
                      , fabricRowAdmit = ReplicaClassAdmitted
                      }

refuseInventedPhysicsGreen :: ReplicaClassRefusal
refuseInventedPhysicsGreen = InventedPhysicsGreen

refuseMissingClassField :: ReplicaClassRefusal
refuseMissingClassField = MissingClassField

refuseCustomerComposeLabsGossip :: ReplicaClassRefusal
refuseCustomerComposeLabsGossip = CustomerComposeLabsGossip

refuseSecondExcitementArgmin :: ReplicaClassRefusal
refuseSecondExcitementArgmin = SecondExcitementArgmin

refuseInventedPhysicsGreenPositive :: Bool
refuseInventedPhysicsGreenPositive =
  refuseInventedPhysicsGreen == InventedPhysicsGreen

refuseMissingClassFieldPositive :: Bool
refuseMissingClassFieldPositive =
  refuseMissingClassField == MissingClassField

refuseCustomerComposeLabsGossipPositive :: Bool
refuseCustomerComposeLabsGossipPositive =
  refuseCustomerComposeLabsGossip == CustomerComposeLabsGossip

refuseSecondExcitementArgminPositive :: Bool
refuseSecondExcitementArgminPositive =
  refuseSecondExcitementArgmin == SecondExcitementArgmin

-- ---------------------------------------------------------------------------
-- SECTION 3: Replica class composes excitementSelect (no argmin)
-- ---------------------------------------------------------------------------

data ReplicaExcitementComposePin
  = ImportSelectExcitement
  | SecondArgminRefused
  deriving (Show, Eq)

data ReplicaClassCtx = ReplicaClassCtx
  { replicaClassPrior       :: !ThermodynamicState
  , replicaClassSuccessors  :: ![HistoryCandidate]
  } deriving (Show, Eq)

composeReplicaExcitementSelect
  :: ThermodynamicState
  -> [HistoryCandidate]
  -> ReplicaExcitementComposePin
  -> Either ExcitementResidue HistoryCandidate
composeReplicaExcitementSelect src cands ImportSelectExcitement =
  excitementSelect src cands
composeReplicaExcitementSelect _ _ SecondArgminRefused =
  Left ExcAllInadmissible

replicaClassSelect
  :: ReplicaClassCtx
  -> Either ExcitementResidue HistoryCandidate
replicaClassSelect ctx =
  urgeRecoverySelect (replicaClassPrior ctx) (replicaClassSuccessors ctx)

composeReplicaExcitementSelectEqExcitementSelect
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
composeReplicaExcitementSelectEqExcitementSelect src cands =
  composeReplicaExcitementSelect src cands ImportSelectExcitement
    == excitementSelect src cands

replicaClassSelectEqExcitementSelect :: ReplicaClassCtx -> Bool
replicaClassSelectEqExcitementSelect ctx =
  replicaClassSelect ctx
    == excitementSelect (replicaClassPrior ctx) (replicaClassSuccessors ctx)

replicaClassSelectEqUrgeRecoverySelect :: ReplicaClassCtx -> Bool
replicaClassSelectEqUrgeRecoverySelect ctx =
  replicaClassSelect ctx
    == urgeRecoverySelect (replicaClassPrior ctx) (replicaClassSuccessors ctx)

replicaClassNoLocalArgmin :: ReplicaClassCtx -> Bool
replicaClassNoLocalArgmin ctx =
  replicaClassSelect ctx
    == excitementSelect (replicaClassPrior ctx) (replicaClassSuccessors ctx)

composeReplicaExcitementSelectRefusesSecondArgmin
  :: ThermodynamicState -> [HistoryCandidate] -> Bool
composeReplicaExcitementSelectRefusesSecondArgmin src cands =
  composeReplicaExcitementSelect src cands SecondArgminRefused
    == Left ExcAllInadmissible

replicaClassSelectEmpty :: ReplicaClassCtx -> Bool
replicaClassSelectEmpty ctx =
  replicaClassSelect ctx == Left ExcNoCandidates

-- ---------------------------------------------------------------------------
-- SECTION 4: fabric-nodes.json census + §15.4 fixtures
-- ---------------------------------------------------------------------------

fabricNodesJsonRel :: String
fabricNodesJsonRel = "workspace/ops/fabric-nodes.json"

fabricNodesSchemaPin :: String
fabricNodesSchemaPin = "umst_fabric_nodes_v1"

replicaClassFixtureState :: ThermodynamicState
replicaClassFixtureState = ThermodynamicState 2400 0 0.3 30 40

replicaClassFixtureNode0Pin :: FabricNodeClassPin
replicaClassFixtureNode0Pin =
  FabricNodeClassPin
    { fabricNodeId = "node-0"
    , fabricClassField = Just "node-0-dev-clone"
    , fabricPhysicsGreenClaim = False
    , fabricJoinsLabsPublicGossip = False
    }

replicaClassFixtureInventGreenPin :: FabricNodeClassPin
replicaClassFixtureInventGreenPin =
  FabricNodeClassPin
    { fabricNodeId = "node-invent-green"
    , fabricClassField = Just "node-1-dev-clone"
    , fabricPhysicsGreenClaim = True
    , fabricJoinsLabsPublicGossip = False
    }

replicaClassFixtureComposeGossipPin :: FabricNodeClassPin
replicaClassFixtureComposeGossipPin =
  FabricNodeClassPin
    { fabricNodeId = "compose-customer"
    , fabricClassField = Just "customer-compose"
    , fabricPhysicsGreenClaim = False
    , fabricJoinsLabsPublicGossip = True
    }

replicaClassFixtureNode0Admitted :: Bool
replicaClassFixtureNode0Admitted =
  evaluateFabricNodeClass replicaClassFixtureNode0Pin ==
    Right
      FabricNodeClassRow
        { fabricRowNodeId = "node-0"
        , fabricRowClass = Node0DevClone
        , fabricRowTable = replicaClassBlueprintRow Node0DevClone
        , fabricRowVerdict = FabricNodeClassAccept
        , fabricRowAdmit = ReplicaClassAdmitted
        }

replicaClassFixtureInventGreenRefused :: Bool
replicaClassFixtureInventGreenRefused =
  evaluateFabricNodeClass replicaClassFixtureInventGreenPin
    == Left InventedPhysicsGreen

replicaClassFixtureComposeGossipRefused :: Bool
replicaClassFixtureComposeGossipRefused =
  evaluateFabricNodeClass replicaClassFixtureComposeGossipPin
    == Left CustomerComposeLabsGossip

replicaClassOfflineLuksEgressEmpty :: Bool
replicaClassOfflineLuksEgressEmpty =
  replicaEgressEmpty
    (replicaRowEgress (replicaClassBlueprintRow OfflineLuks))

replicaClassDarwinScratchEgressEmpty :: Bool
replicaClassDarwinScratchEgressEmpty =
  replicaEgressEmpty
    (replicaRowEgress (replicaClassBlueprintRow DarwinScratch))

replicaClassForgejoEgressNonempty :: Bool
replicaClassForgejoEgressNonempty =
  not
    (replicaEgressEmpty
       (replicaRowEgress (replicaClassBlueprintRow ForgejoPrimaryMirror)))

replicaClassTableCardinalitySix :: Bool
replicaClassTableCardinalitySix = replicaClassTableCardinality == 6

replicaClassNode0ClassField :: Bool
replicaClassNode0ClassField =
  replicaClassClassField Node0DevClone == "node-0-dev-clone"

replicaClassParseLegacyNode0 :: Bool
replicaClassParseLegacyNode0 =
  parseReplicaClassField rclNode0LegacyField == Just Node0DevClone

replicaClassParseUnknownNone :: Bool
replicaClassParseUnknownNone =
  parseReplicaClassField "unknown-class" == Nothing

replicaClassPositiveRefuseNotSilent :: Bool
replicaClassPositiveRefuseNotSilent =
  evaluateFabricNodeClass replicaClassFixtureInventGreenPin
    /= Right
         FabricNodeClassRow
           { fabricRowNodeId = "node-invent-green"
           , fabricRowClass = Node1DevClone
           , fabricRowTable = replicaClassBlueprintRow Node1DevClone
           , fabricRowVerdict = FabricNodeClassAccept
           , fabricRowAdmit = ReplicaClassAdmitted
           }

replicaClassComposeExcitementNotArgmin :: ReplicaClassCtx -> Bool
replicaClassComposeExcitementNotArgmin = replicaClassNoLocalArgmin

-- ---------------------------------------------------------------------------
-- SECTION 5: Landauer bridge (derived — zero new axioms)
-- ---------------------------------------------------------------------------

replicaClassSecondLawFromLandauer :: LandauerHistoryBridge -> Bool -> Bool
replicaClassSecondLawFromLandauer b hSL =
  hSL
  && admissibleHistoryTransitionFromLandauerBridge b hSL
  && admitSecondLaw (landauerTransition b)

replicaClassSecondLawFromHypothesis :: HistoryTransition -> Bool -> Bool
replicaClassSecondLawFromHypothesis t ok = ok && admitSecondLaw t

physicalSecondLawImported :: HistoryTransition -> Bool -> Bool
physicalSecondLawImported t hSL = hSL && admitSecondLaw t

landauerAnchorCited :: LandauerHistoryBridge -> Bool -> Bool
landauerAnchorCited b hSL = replicaClassSecondLawFromLandauer b hSL

-- ---------------------------------------------------------------------------
-- SECTION 6: Honesty flags + catalog witnesses
-- ---------------------------------------------------------------------------

replicaClassPhysicsGreen :: Bool
replicaClassPhysicsGreen = False

replicaClassPhysicsGreenFalse :: Bool
replicaClassPhysicsGreenFalse = not replicaClassPhysicsGreen

replicaClassProductionWired :: Bool
replicaClassProductionWired = False

replicaClassProductionWiredFalse :: Bool
replicaClassProductionWiredFalse = not replicaClassProductionWired

replicaClassMarker :: Int
replicaClassMarker = 1

replicaClassMarkerEq :: Bool
replicaClassMarkerEq = replicaClassMarker == 1

replicaClassModuleWitness :: Bool
replicaClassModuleWitness = True

replicaClassNoNewAxiom :: Bool
replicaClassNoNewAxiom = True

replicaClassNoSecondArgmin :: Bool
replicaClassNoSecondArgmin =
  replicaClassNoLocalArgmin
    ReplicaClassCtx
      { replicaClassPrior = replicaClassFixtureState
      , replicaClassSuccessors = []
      }

replicaClassNonClaim :: String
replicaClassNonClaim =
  "§15.4 replica-class table + fabric-nodes.json class field pin; "
    ++ "fabric-nodes consume table; compose excitementSelect not second argmin; "
    ++ "LandauerLaw.physicalSecondLaw cited; not physics GREEN; not production_wired"

replicaClassNonClaimNonempty :: Bool
replicaClassNonClaimNonempty = length replicaClassNonClaim > 0
