-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.Transport
-- Description : Meso acting Urge — BP II §5.3 transport seam channel set.
-- No System.IO. physics_green = False.
module UMST.Urge.Transport
  ( Transport (..)
  , TransportError (..)
  , canCarry
  , admitCarry
  , channelSet
  , transportFixturesHonest
  , transportPhysicsGreen
  , transportPhysicsGreenFalse
  ) where

data Transport
  = Local
  | Git
  | Mesh
  | Remote
  | Offline
  deriving (Show, Eq)

data TransportError
  = OfflineCannotCarry
  deriving (Show, Eq)

canCarry :: Transport -> Bool
canCarry Offline = False
canCarry _       = True

admitCarry :: Transport -> Either TransportError ()
admitCarry t
  | canCarry t = Right ()
  | otherwise  = Left OfflineCannotCarry

channelSet :: [Transport]
channelSet = [Local, Git, Mesh, Remote, Offline]

transportFixturesHonest :: Bool
transportFixturesHonest =
  canCarry Local
    && not (canCarry Offline)
    && admitCarry Local == Right ()
    && admitCarry Offline == Left OfflineCannotCarry
    && length channelSet == 5
    && not transportPhysicsGreen

transportPhysicsGreen :: Bool
transportPhysicsGreen = False

transportPhysicsGreenFalse :: Bool
transportPhysicsGreenFalse = not transportPhysicsGreen
