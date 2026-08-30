-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
module UMST.Urge.Supervision
  ( SupervisionPhase (..)
  , SupervisionTier (..)
  , budgetUs
  , phaseOrder
  , localCycleAdmissible
  , supervisionFixturesHonest
  , supervisionPhysicsGreen
  ) where

import UMST.Urge.Transport (Transport (..), canCarry)

data SupervisionPhase
  = Observe | Reconcile | SelfHeal | Verify | Record
  deriving (Show, Eq)

data SupervisionTier = Fast | Slow deriving (Show, Eq)

budgetUs :: SupervisionTier -> Int
budgetUs Fast = 100000
budgetUs Slow = 1000000

phaseOrder :: [SupervisionPhase]
phaseOrder = [Observe, Reconcile, SelfHeal, Verify, Record]

localCycleAdmissible :: Transport -> Bool
localCycleAdmissible = canCarry

supervisionPhysicsGreen :: Bool
supervisionPhysicsGreen = False

supervisionFixturesHonest :: Bool
supervisionFixturesHonest =
  length phaseOrder == 5
    && localCycleAdmissible Local
    && not (localCycleAdmissible Offline)
    && not supervisionPhysicsGreen
