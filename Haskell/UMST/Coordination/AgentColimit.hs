-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Agents as observation maps on a finite world, and the gluing of two agents (H-COLIMIT-1, W-30). Twin of
-- Lean/Coordination/AgentColimit.lean, Coq/Coordination/AgentColimit.v and Agda/Coordination/AgentColimit.agda.
--
-- Agent @c@ knows agent @a@ on the world @ws@ when equal @c@-readings give equal @a@-readings. The glued agent
-- observes the pair; it knows both agents, and every agent that knows both knows it: the join in the information
-- order. The kernel of the glued agent is the meet of the two kernels. On a finite world 'knows' is decidable, so
-- the laws run as QuickCheck properties (test/CoordinationProps.hs).
module UMST.Coordination.AgentColimit
  ( knows
  , glue
  , sameReading
  ) where

-- | Agent @c@ knows agent @a@ on the world @ws@.
knows :: (Eq c, Eq a) => [w] -> (w -> c) -> (w -> a) -> Bool
knows ws c a = and [a x == a y | x <- ws, y <- ws, c x == c y]

-- | The glued agent observes both readings at once.
glue :: (w -> a) -> (w -> b) -> w -> (a, b)
glue a b x = (a x, b x)

-- | The kernel of an agent: whether it reads two worlds alike.
sameReading :: Eq a => (w -> a) -> w -> w -> Bool
sameReading a x y = a x == a y
