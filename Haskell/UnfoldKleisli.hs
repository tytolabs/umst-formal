-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- The laws nested-solve composition relies on, on exact rationals; twin of Lean/UnfoldKleisli.lean,
-- Coq/UnfoldKleisli.v and Agda/UnfoldKleisli.agda. A nested solve is refused or done with a value and a spend (measured
-- energy, Landauer floor); bind threads refusals and adds spends. test/UnfoldKleisliProps.hs decides the statements on
-- random solves and Kleisli arrows.
module UnfoldKleisli
  ( Spend (..)
  , szero
  , sadd
  , honest
  , Thermo
  , unit
  , bind
  , kcomp
  , Interval (..)
  , mem
  , iadd
  , symI
  ) where

-- | The spend a solve posts: the measured energy and the Landauer floor of the bits it erased.
data Spend = Spend { measured :: Rational, floorJ :: Rational }
  deriving (Eq, Show)

-- | The empty spend.
szero :: Spend
szero = Spend 0 0

-- | Spends add componentwise.
sadd :: Spend -> Spend -> Spend
sadd (Spend a b) (Spend c d) = Spend (a + c) (b + d)

-- | A spend is honest when its measured energy is at least its floor.
honest :: Spend -> Bool
honest s = floorJ s <= measured s

-- | A nested solve: a refusal, or a value with the spend that produced it.
type Thermo e a = Either e (a, Spend)

-- | The monad unit: a value at no spend.
unit :: a -> Thermo e a
unit a = Right (a, szero)

-- | Kleisli bind: a refusal stops the chain, spends add.
bind :: Thermo e a -> (a -> Thermo e b) -> Thermo e b
bind (Left e) _ = Left e
bind (Right (a, s)) f = case f a of
  Left e -> Left e
  Right (b, t) -> Right (b, sadd s t)

-- | Kleisli composition of nested solves.
kcomp :: (a -> Thermo e b) -> (b -> Thermo e c) -> a -> Thermo e c
kcomp f g a = bind (f a) g

-- | A closed rational interval.
data Interval = Interval { lo :: Rational, hi :: Rational }
  deriving (Eq, Show)

-- | Membership in an interval.
mem :: Interval -> Rational -> Bool
mem i x = lo i <= x && x <= hi i

-- | Interval addition.
iadd :: Interval -> Interval -> Interval
iadd i j = Interval (lo i + lo j) (hi i + hi j)

-- | The symmetric tolerance interval [-tau, tau].
symI :: Rational -> Interval
symI t = Interval (negate t) t
