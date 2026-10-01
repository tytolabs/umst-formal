-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The contract a coordination runtime honours, executable: twin of @Lean/CoordinationContract.lean@,
-- @Coq/CoordinationContract.v@ and @Agda/CoordinationContract.agda@, and the reference model the umst-ucrs Rust
-- runtime is tested against. Arithmetic is exact ('Rational'); the Landauer bit energy is an argument
-- (@k_B T ln 2@ is irrational, so the laws are stated for any nonnegative bit energy, as in Agda and Coq).
module UMST.CoordinationContract
  ( -- * Landauer cost
    cost
    -- * Admission
  , ClockThermState (..)
  , admits
    -- * Clock drift
  , ClockState (..)
  , clockStep
  , clockRun
    -- * Byzantine isolation
  , Participant (..)
  , honestCredits
    -- * Wire order
  , WireStamp (..)
  , wireNext
  , wireIter
    -- * Peer credit (runtime model)
  , PeerCredit (..)
  , bestPeer
  , recordSync
  ) where

import qualified Data.List as L

-- | Landauer cost of @bits@ at bit energy @e@.
cost :: Rational -> Rational -> Rational
cost e bits = e * bits

-- | Thermal state of a clock sync.
data ClockThermState = ClockThermState
  { desyncEnergy :: Rational
  , budget :: Rational
  }
  deriving (Eq, Show)

-- | A sync of @bits@ is admitted when its cost fits the budget and there is desync to resolve.
admits :: Rational -> ClockThermState -> Rational -> Bool
admits e s bits = cost e bits <= budget s && desyncEnergy s > 0

-- | Clock state: tick count and accumulated drift.
data ClockState = ClockState
  { tick :: Int
  , drift :: Rational
  }
  deriving (Eq, Show)

clockStep :: ClockState -> Rational -> ClockState
clockStep c d = ClockState (tick c + 1) (drift c + d)

-- | Run a trace of increments (a left fold of 'clockStep').
clockRun :: ClockState -> [Rational] -> ClockState
clockRun = L.foldl' clockStep

-- | A participant of a sync mesh.
data Participant = Participant
  { participantId :: Int
  , credit :: Rational
  , faulty :: Bool
  }
  deriving (Eq, Show)

-- | The honest credit projection.
honestCredits :: [Participant] -> [Rational]
honestCredits = map credit . filter (not . faulty)

newtype WireStamp = WireStamp {wireSeq :: Integer}
  deriving (Eq, Show)

wireNext :: WireStamp -> WireStamp
wireNext (WireStamp n) = WireStamp (n + 1)

-- | @n@ advances of the wire.
wireIter :: Int -> WireStamp -> WireStamp
wireIter n w = iterate wireNext w !! max 0 n

-- | A peer's credit record in the runtime's greedy routing.
data PeerCredit = PeerCredit
  { peerId :: Int
  , creditBits :: Rational
  , accuracyScore :: Rational
  , syncCount :: Int
  }
  deriving (Eq, Show)

-- | The healthy peer (accuracy above one tenth) with the most credit; 'Nothing' when no peer is healthy.
bestPeer :: [PeerCredit] -> Maybe Int
bestPeer peers = case filter ((> 1 / 10) . accuracyScore) peers of
  [] -> Nothing
  p : ps -> Just (peerId (L.foldl' (\a b -> if creditBits b > creditBits a then b else a) p ps))

-- | Record a sync: an improving sync earns its bits, a failing one pays twice its bits.
recordSync :: PeerCredit -> Rational -> Bool -> PeerCredit
recordSync p bits improved
  | improved = p {creditBits = creditBits p + bits, accuracyScore = 9 / 10 * accuracyScore p + 1 / 10, syncCount = n}
  | otherwise = p {creditBits = creditBits p - 2 * bits, accuracyScore = 9 / 10 * accuracyScore p, syncCount = n}
  where
    n = syncCount p + 1
