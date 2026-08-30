-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Urge.Reconcile
-- Description : Meso acting Urge — BP II §5.2 both-way union-preserving reconcile.
--
-- Value-level mirror of Rust reconcile_heads + ContentConflict refuse. No System.IO.
-- physics_green = False. Zero new physics axioms. Machine-checkable Bool probes.
module UMST.Urge.Reconcile
  ( Head (..)
  , StateSummary (..)
  , BothWayDiff (..)
  , ReconcileError (..)
  , reconcileHeads
  , unionPreservingOk
  , contentConflictRefused
  , reconcileFixturesHonest
  , reconcilePhysicsGreen
  , reconcilePhysicsGreenFalse
  ) where

data Head = Head
  { headId     :: Int
  , headDigest :: Int
  } deriving (Show, Eq)

newtype StateSummary = StateSummary { summaryHeads :: [Head] }
  deriving (Show, Eq)

data BothWayDiff = BothWayDiff
  { leftOnly  :: [Head]
  , rightOnly :: [Head]
  , unionH    :: [Head]
  } deriving (Show, Eq)

data ReconcileError
  = ContentConflict Int
  deriving (Show, Eq)

lookupDigest :: [Head] -> Int -> Maybe Int
lookupDigest [] _ = Nothing
lookupDigest (h:hs) i
  | headId h == i = Just (headDigest h)
  | otherwise = lookupDigest hs i

uniqueIds :: [Head] -> [Head] -> [Int]
uniqueIds left right =
  go [] (map headId left ++ map headId right)
  where
    go acc [] = reverse acc
    go acc (x:xs)
      | x `elem` acc = go acc xs
      | otherwise = go (x:acc) xs

reconcileHeads :: StateSummary -> StateSummary -> Either ReconcileError BothWayDiff
reconcileHeads (StateSummary left) (StateSummary right) =
  go [] [] [] (uniqueIds left right)
  where
    go lo ro uni [] = Right (BothWayDiff (reverse lo) (reverse ro) (reverse uni))
    go lo ro uni (i:is) =
      case (lookupDigest left i, lookupDigest right i) of
        (Just dL, Just dR)
          | dL /= dR -> Left (ContentConflict i)
          | otherwise -> go lo ro (Head i dL : uni) is
        (Just dL, Nothing) ->
          let h = Head i dL in go (h:lo) ro (h:uni) is
        (Nothing, Just dR) ->
          let h = Head i dR in go lo (h:ro) (h:uni) is
        (Nothing, Nothing) -> go lo ro uni is

unionPreservingOk :: StateSummary -> StateSummary -> Bool
unionPreservingOk left right =
  case reconcileHeads left right of
    Left _ -> False
    Right d ->
      let ids = map headId (summaryHeads left ++ summaryHeads right)
          u = map headId (unionH d)
      in all (`elem` u) ids

contentConflictRefused :: StateSummary -> StateSummary -> Bool
contentConflictRefused left right =
  case reconcileHeads left right of
    Left (ContentConflict _) -> True
    _ -> False

fixtureLeft :: StateSummary
fixtureLeft = StateSummary [Head 1 10, Head 2 20]

fixtureRight :: StateSummary
fixtureRight = StateSummary [Head 2 20, Head 3 30]

fixtureConflictL :: StateSummary
fixtureConflictL = StateSummary [Head 1 1]

fixtureConflictR :: StateSummary
fixtureConflictR = StateSummary [Head 1 9]

-- Aggregate honesty probe — must stay True; not physics GREEN.
reconcileFixturesHonest :: Bool
reconcileFixturesHonest =
  unionPreservingOk fixtureLeft fixtureRight
    && contentConflictRefused fixtureConflictL fixtureConflictR
    && not reconcilePhysicsGreen

reconcilePhysicsGreen :: Bool
reconcilePhysicsGreen = False

reconcilePhysicsGreenFalse :: Bool
reconcilePhysicsGreenFalse = not reconcilePhysicsGreen
