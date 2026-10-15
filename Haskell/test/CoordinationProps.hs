-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "UMST.Coordination.AgentColimit" (H-COLIMIT-1, W-30): the gluing laws on random agents over a
-- finite world of eight points.
module CoordinationProps
  ( prop_glue_knows
  , prop_knows_glue_iff
  , prop_knows_trans
  , prop_ker_glue
  , agentColimitProps
  ) where

import Test.QuickCheck
import UMST.Coordination.AgentColimit

-- | A world of eight points and an agent reading it into a small alphabet.
world :: [Int]
world = [0 .. 7]

-- | An agent by its table of readings (shown on failure); 'at' reads it as a map.
genAgent :: Gen [Int]
genAgent = do
  k <- choose (1, 4)
  vectorOf (length world) (choose (0, k - 1))

at :: [Int] -> Int -> Int
at = (!!)

-- | The glued agent knows both agents (twin of glue_knows_left and glue_knows_right).
prop_glue_knows :: Property
prop_glue_knows = forAll genAgent $ \ta -> forAll genAgent $ \tb ->
  let (a, b) = (at ta, at tb) in property (knows world (glue a b) a && knows world (glue a b) b)

-- | c knows the glued agent iff c knows both: the join in the information order (twin of knows_glue_iff).
prop_knows_glue_iff :: Property
prop_knows_glue_iff = forAll genAgent $ \tc -> forAll genAgent $ \ta -> forAll genAgent $ \tb ->
  let (c, a, b) = (at tc, at ta, at tb) in knows world c (glue a b) === (knows world c a && knows world c b)

-- | Knowing is transitive (twin of knows_trans).
prop_knows_trans :: Property
prop_knows_trans = forAll genAgent $ \tc -> forAll genAgent $ \tb -> forAll genAgent $ \ta ->
  let (c, b, a) = (at tc, at tb, at ta) in property (not (knows world c b && knows world b a) || knows world c a)

-- | The kernel of the glued agent is the meet of the two kernels, at every pair of worlds (twin of ker_glue).
prop_ker_glue :: Property
prop_ker_glue = forAll genAgent $ \ta -> forAll genAgent $ \tb ->
  let (a, b) = (at ta, at tb)
   in property (and [sameReading (glue a b) x y == (sameReading a x y && sameReading b x y) | x <- world, y <- world])

-- | The properties with their names, for the runner.
agentColimitProps :: [(String, Property)]
agentColimitProps =
  [ ("agent_glue_knows", prop_glue_knows)
  , ("agent_knows_glue_iff", prop_knows_glue_iff)
  , ("agent_knows_trans", prop_knows_trans)
  , ("agent_ker_glue", prop_ker_glue)
  ]
