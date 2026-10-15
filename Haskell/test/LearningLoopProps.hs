-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "LearningLoopLaws" (FORMAL-LEARNING-LOOP-LAWS): the six laws the learning-loop kernel relies on,
-- decided on random evidence, counts, barrier histories, arms and apportionments over exact rationals.
module LearningLoopProps
  ( prop_completeLevel_monotone
  , prop_levelOf_monotone
  , prop_combine_comm_monoid
  , prop_fold_append
  , prop_fold_perm
  , prop_posterior_perm
  , prop_posterior_mean_mem
  , prop_barrier_forward_invariant
  , prop_ppoStep_simplex
  , prop_scaled_move
  , prop_ppoStep_ratio
  , prop_apportion_sum
  , prop_apportion_close
  , prop_apportion_missing_lt
  , prop_countedBits_cost
  , prop_verified_bit_costs_landauer
  , learningLoopProps
  ) where

import Test.QuickCheck
import LearningLoopLaws

genEvidence :: Gen Evidence
genEvidence = Evidence <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

-- | Evidence f holding at least what e holds.
genMore :: Evidence -> Gen Evidence
genMore e = Evidence <$> up (evGuard e) <*> up (evVerified e) <*> up (evLanded e) <*> up (evMoved e)
  where up b = if b then pure True else arbitrary

genStatus :: Gen ClaimStatus
genStatus = elements [minBound .. maxBound]

-- | Counts over keys 0..4 by their table (shown on failure).
genTable :: Gen [Integer]
genTable = vectorOf 5 (choose (0, 9))

asCounts :: [Integer] -> Counts Int
asCounts t k = if k >= 0 && k < length t then t !! k else 0

tableOf :: Counts Int -> [Integer]
tableOf c = map c [0 .. 4]

-- | Twin of completeLevel_monotone.
prop_completeLevel_monotone :: Property
prop_completeLevel_monotone = forAll genEvidence $ \e -> forAll (genMore e) $ \f ->
  evidenceLe e f && levelRank (completeLevel e) <= levelRank (completeLevel f)

-- | Twin of levelOf_monotone.
prop_levelOf_monotone :: Property
prop_levelOf_monotone = forAll genStatus $ \s -> forAll genEvidence $ \e -> forAll (genMore e) $ \f ->
  outcomeLe (levelOf s e) (levelOf s f)

-- | Twin of combine_assoc, combine_comm, zero_combine and combine_zero.
prop_combine_comm_monoid :: Property
prop_combine_comm_monoid = forAll genTable $ \ta -> forAll genTable $ \tb -> forAll genTable $ \tc ->
  let (a, b, c) = (asCounts ta, asCounts tb, asCounts tc)
  in tableOf (combine (combine a b) c) == tableOf (combine a (combine b c))
       && tableOf (combine a b) == tableOf (combine b a)
       && tableOf (combine countsZero a) == ta && tableOf (combine a countsZero) == ta

-- | Twin of fold_append.
prop_fold_append :: Property
prop_fold_append = forAll (listOf genTable) $ \xs -> forAll (listOf genTable) $ \ys ->
  let (cx, cy) = (map asCounts xs, map asCounts ys)
  in tableOf (foldCounts (cx ++ cy)) == tableOf (combine (foldCounts cx) (foldCounts cy))

-- | Twin of fold_perm.
prop_fold_perm :: Property
prop_fold_perm = forAll (listOf genTable) $ \xs -> forAll (shuffle xs) $ \ys ->
  tableOf (foldCounts (map asCounts xs)) == tableOf (foldCounts (map asCounts ys))

-- | Twin of posterior_perm (verified keys 0 and 1, failure keys 2 and 3, as outcome.rs reads two keys each).
prop_posterior_perm :: Property
prop_posterior_perm = forAll (listOf genTable) $ \xs -> forAll (shuffle xs) $ \ys ->
  posterior [0, 1] [2, 3] (foldCounts (map asCounts xs)) == posterior [0, 1] [2, 3] (foldCounts (map asCounts ys))

-- | Twin of posterior_mean_mem.
prop_posterior_mean_mem :: Property
prop_posterior_mean_mem = forAll genTable $ \t ->
  let m = posterior [0, 1] [2, 3] (asCounts t) in 0 < m && m < 1

genUnit :: Gen Rational
genUnit = do
  d <- choose (1, 20)
  n <- choose (0, d)
  pure (fromIntegral n / fromIntegral (d :: Integer))

-- | A barrier history from h_0 >= 0 meeting the condition, each step at least (1 - gamma) times the last.
genBarrier :: Rational -> Gen [Rational]
genBarrier gamma = do
  h0 <- genUnit
  steps <- listOf genUnit
  pure (scanl (\x s -> (1 - gamma) * x + s) h0 steps)

-- | Twin of barrier_floor and barrier_forward_invariant.
prop_barrier_forward_invariant :: Property
prop_barrier_forward_invariant = forAll genUnit $ \gamma -> forAll (genBarrier gamma) $ \hs ->
  case hs of
    [] -> property False
    h0 : _ -> property (barrierHolds gamma hs && and [barrierFloor gamma h0 k <= h && 0 <= h | (k, h) <- zip [0 ..] hs])

-- | Arms of a distribution with changes within the clip.
genArms :: Rational -> Gen [(Rational, Rational)]
genArms clip = do
  n <- choose (1, 6)
  raw <- vectorOf n (choose (0, 9 :: Integer))
  let raw' = if sum raw == 0 then 1 : drop 1 raw else raw
      weightSum = fromIntegral (sum raw') :: Rational
  cs <- vectorOf n (genUnit >>= \u -> elements [u * clip, negate (u * clip)])
  pure (zip [fromIntegral r / weightSum | r <- raw'] cs)

genClip :: Gen Rational
genClip = do
  d <- choose (2, 20)
  n <- choose (0, d - 1)
  pure (fromIntegral n / fromIntegral (d :: Integer))

-- | Twin of ppoStep_simplex.
prop_ppoStep_simplex :: Property
prop_ppoStep_simplex = forAll genClip $ \clip -> forAll (genArms clip) $ \arms ->
  armsOk clip arms && all (>= 0) (ppoStep arms) && sum (ppoStep arms) == 1

-- | Twin of scaled_move and clamp_mem.
prop_scaled_move :: Property
prop_scaled_move = forAll genClip $ \clip -> forAll (genArms clip) $ \arms -> forAll genUnit $ \v ->
  all (\(w, c) -> abs (scaledW (w, c) - w) <= clip * w) arms
    && let k = clamp (negate clip) clip (4 * v - 2) in negate clip <= k && k <= clip

-- | Twin of ppoStep_ratio.
prop_ppoStep_ratio :: Property
prop_ppoStep_ratio = forAll genClip $ \clip -> forAll (genArms clip) $ \arms ->
  and [ (1 - clip) * w <= (1 + clip) * w' && (1 - clip) * w' <= (1 + clip) * w
      | ((w, _), w') <- zip arms (ppoStep arms) ]

-- | Parts of a largest-remainder apportionment of a distribution at 2^bits units.
genParts :: Gen [(Rational, Integer, Bool)]
genParts = do
  (ws, _) <- unzip <$> genArms 0
  bits <- choose (0, 6 :: Int)
  let units = 2 ^ bits :: Integer
      xs = map (* fromIntegral units) ws
      fs = map floor xs :: [Integer]
      missing = units - sum fs
      order = map snd (sortDesc [(x - fromIntegral f, i) | (i, x, f) <- zip3 [0 :: Int ..] xs fs])
      chosen = take (fromIntegral missing) order
  pure [(x, f, i `elem` chosen) | (i, x, f) <- zip3 [0 ..] xs fs]
  where
    sortDesc = foldr insertDesc []
    insertDesc p [] = [p]
    insertDesc p (q : qs) = if fst p > fst q || (fst p == fst q && snd p < snd q) then p : q : qs else q : insertDesc p qs

-- | Twin of apportion_sum.
prop_apportion_sum :: Property
prop_apportion_sum = forAll genParts $ \ps ->
  sum (map apportioned ps) == sum [f | (_, f, _) <- ps] + sum [bump b | (_, _, b) <- ps]

-- | Twin of apportion_close, on the largest-remainder selection.
prop_apportion_close :: Property
prop_apportion_close = forAll genParts $ \ps ->
  floorsOk ps && bumpsPositive ps
    && all (\p@(x, _, _) -> x - 1 < fromIntegral (apportioned p) && fromIntegral (apportioned p) < x + 1) ps

-- | Twin of apportion_missing_lt.
prop_apportion_missing_lt :: Property
prop_apportion_missing_lt = forAll genParts $ \ps ->
  sum [x | (x, _, _) <- ps] - fromIntegral (sum [f | (_, f, _) <- ps]) < fromIntegral (length ps)

-- | Twin of countedBits_cost: an erasure of `bits` bits obeying the predicate (energy at least bits · L) pays the
-- counted bits.
prop_countedBits_cost :: Property
prop_countedBits_cost = forAll genStatus $ \s -> forAll genEvidence $ \e -> forAll (choose (0, 8)) $ \bits ->
  forAll genUnit $ \kT -> forAll genUnit $ \h -> forAll genUnit $ \extra ->
    let energy = fromIntegral bits * landauerBitEnergy kT h + extra
    in fromIntegral (countedBits s e bits) * landauerBitEnergy kT h <= energy

-- | Twin of verified_bit_costs_landauer.
prop_verified_bit_costs_landauer :: Property
prop_verified_bit_costs_landauer = forAll genEvidence $ \e0 -> forAll (choose (1, 8)) $ \bits ->
  forAll genUnit $ \kT -> forAll genUnit $ \h -> forAll genUnit $ \extra ->
    let e = e0 { evVerified = True }
        energy = fromIntegral bits * landauerBitEnergy kT h + extra
    in countedBits Complete e bits == bits && landauerBitEnergy kT h <= energy

learningLoopProps :: [(String, Property)]
learningLoopProps =
  [ ("prop_completeLevel_monotone", prop_completeLevel_monotone)
  , ("prop_levelOf_monotone", prop_levelOf_monotone)
  , ("prop_combine_comm_monoid", prop_combine_comm_monoid)
  , ("prop_fold_append", prop_fold_append)
  , ("prop_fold_perm", prop_fold_perm)
  , ("prop_posterior_perm", prop_posterior_perm)
  , ("prop_posterior_mean_mem", prop_posterior_mean_mem)
  , ("prop_barrier_forward_invariant", prop_barrier_forward_invariant)
  , ("prop_ppoStep_simplex", prop_ppoStep_simplex)
  , ("prop_scaled_move", prop_scaled_move)
  , ("prop_ppoStep_ratio", prop_ppoStep_ratio)
  , ("prop_apportion_sum", prop_apportion_sum)
  , ("prop_apportion_close", prop_apportion_close)
  , ("prop_apportion_missing_lt", prop_apportion_missing_lt)
  , ("prop_countedBits_cost", prop_countedBits_cost)
  , ("prop_verified_bit_costs_landauer", prop_verified_bit_costs_landauer)
  ]
