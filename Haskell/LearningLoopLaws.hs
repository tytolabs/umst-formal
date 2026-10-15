-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- The laws the learning-loop kernel of umst-adk relies on; twin of Lean/LearningLoopLaws.lean,
-- Coq/LearningLoopLaws.v and Agda/LearningLoopLaws.agda. The definitions follow what the runtime computes
-- (umst-adk outcome.rs, steer/learn.rs, liquid_ppo_bind.rs; umst-algebra ppo_clipped_step.rs) on exact rationals;
-- test/LearningLoopProps.hs decides the laws on random inputs.
module LearningLoopLaws
  ( Level (..)
  , levelRank
  , ClaimStatus (..)
  , Outcome (..)
  , Evidence (..)
  , evidenceLe
  , completeLevel
  , levelOf
  , outcomeLe
  , Counts
  , countsZero
  , combine
  , foldCounts
  , posterior
  , barrierHolds
  , barrierFloor
  , clamp
  , scaledW
  , ppoStep
  , armsOk
  , bump
  , apportioned
  , floorsOk
  , bumpsPositive
  , countedBits
  , landauerBitEnergy
  ) where

-- | A rung of the evidence lattice (outcome.rs OutcomeLevel).
data Level = Unclaimed | Claimed | GuardPassed | Verified | Landed | MeterMoved
  deriving (Eq, Show, Enum, Bounded)

-- | The rung's height; the lattice order is the order of heights.
levelRank :: Level -> Int
levelRank = fromEnum

-- | What a receipt claims.
data ClaimStatus = Open | Complete | Refused
  deriving (Eq, Show, Enum, Bounded)

-- | A rung, or refused (REWORK or REFUSED), outside the lattice.
data Outcome = OutcomeRefused | OutcomeLevel Level
  deriving (Eq, Show)

-- | The evidence beneath a COMPLETE claim: guard, verified, landed, moved.
data Evidence = Evidence { evGuard :: Bool, evVerified :: Bool, evLanded :: Bool, evMoved :: Bool }
  deriving (Eq, Show)

-- | More evidence: every piece the first holds, the second holds too.
evidenceLe :: Evidence -> Evidence -> Bool
evidenceLe e f =
  imp (evGuard e) (evGuard f) && imp (evVerified e) (evVerified f) && imp (evLanded e) (evLanded f)
    && imp (evMoved e) (evMoved f)
  where imp a b = not a || b

-- | The highest rung a COMPLETE claim's evidence holds (outcome.rs level_of).
completeLevel :: Evidence -> Level
completeLevel e
  | evVerified e = if evLanded e then (if evMoved e then MeterMoved else Landed) else Verified
  | evGuard e = GuardPassed
  | otherwise = Claimed

-- | The outcome of a receipt.
levelOf :: ClaimStatus -> Evidence -> Outcome
levelOf Refused _ = OutcomeRefused
levelOf Open _ = OutcomeLevel Unclaimed
levelOf Complete e = OutcomeLevel (completeLevel e)

-- | Refused only below itself; rungs by height.
outcomeLe :: Outcome -> Outcome -> Bool
outcomeLe OutcomeRefused OutcomeRefused = True
outcomeLe (OutcomeLevel a) (OutcomeLevel b) = levelRank a <= levelRank b
outcomeLe _ _ = False

-- | Counts of outcomes by key; an absent key counts zero.
type Counts k = k -> Integer

countsZero :: Counts k
countsZero _ = 0

-- | The pointwise sum (OutcomeCounts::combine).
combine :: Counts k -> Counts k -> Counts k
combine a b k = a k + b k

-- | The fold from the identity, left to right (OutcomeCounts::fold).
foldCounts :: [Counts k] -> Counts k
foldCounts = foldl combine countsZero

-- | The Beta(V+1, R+1) posterior mean (V+1)/(V+R+2), V under the verified keys and R under the failure keys.
posterior :: [k] -> [k] -> Counts k -> Rational
posterior vKeys rKeys c = fromIntegral (v + 1) / fromIntegral (v + r + 2)
  where
    v = sum (map c vKeys)
    r = sum (map c rKeys)

-- | Whether a barrier history meets h_{k+1} >= (1 - gamma) h_k at every step.
barrierHolds :: Rational -> [Rational] -> Bool
barrierHolds gamma hs = and (zipWith (\x y -> (1 - gamma) * x <= y) hs (drop 1 hs))

-- | The geometric floor (1 - gamma)^k h_0.
barrierFloor :: Rational -> Rational -> Int -> Rational
barrierFloor gamma h0 k = (1 - gamma) ^ k * h0

-- | The clamp of the runtime (ppo_clipped_step.rs clamp).
clamp :: Rational -> Rational -> Rational -> Rational
clamp lo hi v
  | v < lo = lo
  | hi < v = hi
  | otherwise = v

-- | An arm's weight scaled by 1 + its clamped change.
scaledW :: (Rational, Rational) -> Rational
scaledW (w, c) = w * (1 + c)

-- | The step: each scaled weight over the sum of the scaled weights.
ppoStep :: [(Rational, Rational)] -> [Rational]
ppoStep arms = map (\a -> scaledW a / s) arms
  where s = sum (map scaledW arms)

-- | Every weight non-negative and every change within the clip.
armsOk :: Rational -> [(Rational, Rational)] -> Bool
armsOk clip = all (\(w, c) -> 0 <= w && negate clip <= c && c <= clip)

bump :: Bool -> Integer
bump b = if b then 1 else 0

-- | The apportioned count of a part (scaled weight, floor, bump): the floor plus the bump.
apportioned :: (Rational, Integer, Bool) -> Integer
apportioned (_, f, b) = f + bump b

-- | Each floor is the floor of its scaled weight.
floorsOk :: [(Rational, Integer, Bool)] -> Bool
floorsOk = all (\(x, f, _) -> fromIntegral f <= x && x < fromIntegral f + 1)

-- | A bump goes only to a positive remainder.
bumpsPositive :: [(Rational, Integer, Bool)] -> Bool
bumpsPositive = all (\(x, f, b) -> not b || fromIntegral f < x)

-- | The bits a close counts as evidence: its claimed bits from the Verified level up.
countedBits :: ClaimStatus -> Evidence -> Integer -> Integer
countedBits s e bits = case levelOf s e of
  OutcomeLevel l | levelRank l >= 3 -> bits
  _ -> 0

-- | The Landauer bit energy k_B T h, with h a rational stand-in for ln 2 (the Agda carriage).
landauerBitEnergy :: Rational -> Rational -> Rational
landauerBitEnergy kT h = kT * h
