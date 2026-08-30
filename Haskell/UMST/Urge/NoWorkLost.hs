-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.NoWorkLost
-- Description : Meso acting Urge — BP II §1 No-Loss pin (umst-formal acting fiber).
--
-- URGE-II-FORMAL-NOLOSS-HS. Once admitted, a change stays reachable from ≥1 replica.
-- Eight mechanisms pinned; reconcile/transport wired=false until §13 lands.
-- Sole physics axiom remains on Lean @LandauerLaw@ (cited, not restated).
-- Zero new physics axioms. Knowing fiber (EpistemicMI) lives on
-- @umst-formal-double-slit@ — cited, not restated here.
-- physics_green = False.
module UMST.Urge.NoWorkLost
  ( -- * Eight mechanisms
    NoLossMechanism (..)
  , eightMechanisms
  , eightMechanismsLength
  , mechanismWired
  , reconcileAbsentHonest
  , transportAbsentHonest
    -- * Reachability carriers
  , AdmittedChange (..)
  , ReplicaReachability (..)
  , reachableFromSomeReplica
  , orphansAdmittedChange
    -- * Honesty
  , noWorkLostPhysicsGreen
  , noWorkLostPhysicsGreenFalse
  , noWorkLostProductionWired
  , noWorkLostGuardBuilt
  , noNewAxiom
  , noWorkLostModuleWitness
  ) where

-- ---------------------------------------------------------------------------
-- SECTION 1: Eight No-Loss mechanisms (BP II §1)
-- ---------------------------------------------------------------------------

data NoLossMechanism
  = NlmProvenanceOnEveryChange
  | NlmAppendOnlyAdmittedHistory
  | NlmContentAddressing
  | NlmUnionPreservingReconcile
  | NlmRefusalHoldsNeverDiscards
  | NlmCompactionSupersedesNotDeletes
  | NlmReplicaCoalgebraTypedBackup
  | NlmMultiTransportRedundancy
  deriving (Show, Eq)

eightMechanisms :: [NoLossMechanism]
eightMechanisms =
  [ NlmProvenanceOnEveryChange
  , NlmAppendOnlyAdmittedHistory
  , NlmContentAddressing
  , NlmUnionPreservingReconcile
  , NlmRefusalHoldsNeverDiscards
  , NlmCompactionSupersedesNotDeletes
  , NlmReplicaCoalgebraTypedBackup
  , NlmMultiTransportRedundancy
  ]

eightMechanismsLength :: Int
eightMechanismsLength = length eightMechanisms

mechanismWired :: NoLossMechanism -> Bool
mechanismWired NlmProvenanceOnEveryChange = True
mechanismWired NlmAppendOnlyAdmittedHistory = True
mechanismWired NlmContentAddressing = True
mechanismWired NlmUnionPreservingReconcile = False
mechanismWired NlmRefusalHoldsNeverDiscards = True
mechanismWired NlmCompactionSupersedesNotDeletes = True
mechanismWired NlmReplicaCoalgebraTypedBackup = True
mechanismWired NlmMultiTransportRedundancy = False

reconcileAbsentHonest :: Bool
reconcileAbsentHonest = not (mechanismWired NlmUnionPreservingReconcile)

transportAbsentHonest :: Bool
transportAbsentHonest = not (mechanismWired NlmMultiTransportRedundancy)

-- ---------------------------------------------------------------------------
-- SECTION 2: Admitted change + replica reachability
-- ---------------------------------------------------------------------------

data AdmittedChange = AdmittedChange
  { acChangeId  :: !Integer
  , acContentId :: !Integer
  , acCommitId  :: !Integer
  } deriving (Show, Eq)

data ReplicaReachability = ReplicaReachability
  { rrReplicaId    :: !Integer
  , rrReachableIds :: ![Integer]
  } deriving (Show, Eq)

reachableFromSomeReplica :: AdmittedChange -> [ReplicaReachability] -> Bool
reachableFromSomeReplica c =
  any (\r -> acChangeId c `elem` rrReachableIds r)

orphansAdmittedChange :: AdmittedChange -> [ReplicaReachability] -> Bool
orphansAdmittedChange c rs = not (reachableFromSomeReplica c rs)

-- ---------------------------------------------------------------------------
-- SECTION 3: Honesty flags
-- ---------------------------------------------------------------------------

noWorkLostPhysicsGreen :: Bool
noWorkLostPhysicsGreen = False

noWorkLostPhysicsGreenFalse :: Bool
noWorkLostPhysicsGreenFalse = not noWorkLostPhysicsGreen

noWorkLostProductionWired :: Bool
noWorkLostProductionWired = False

noWorkLostGuardBuilt :: Bool
noWorkLostGuardBuilt = False

noNewAxiom :: Bool
noNewAxiom = True

noWorkLostModuleWitness :: Bool
noWorkLostModuleWitness = True
