-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "UnfoldKleisli" (FORMAL-UNFOLD-KLEISLI-LAWS): random nested solves and Kleisli arrows, honest spends
-- and interval errors, on exact rationals.
module UnfoldKleisliProps
  ( prop_unit_bind
  , prop_bind_unit
  , prop_bind_assoc
  , prop_bind_inner_refusal
  , prop_bind_spend
  , prop_spend_monoid
  , prop_bind_honest
  , prop_honest_sum
  , prop_mem_add
  , prop_mem_sum_sym
  , prop_error_chain
  , unfoldKleisliProps
  ) where

import Test.QuickCheck
import UnfoldKleisli

type Raw = Either Int (Int, (Integer, Integer))

toSpend :: (Integer, Integer) -> Spend
toSpend (m, f) = Spend (fromInteger m / 7) (fromInteger f / 7)

toThermo :: Raw -> Thermo Int Int
toThermo = fmap (\(a, s) -> (a, toSpend s))

arrow :: Fun Int Raw -> Int -> Thermo Int Int
arrow f = toThermo . applyFun f

-- | An honest spend: the floor lowered below the measured energy.
honestOf :: (Integer, Integer) -> Spend
honestOf (m, d) = Spend (fromInteger m / 7) (fromInteger m / 7 - fromInteger (abs d) / 11)

honestArrow :: Fun Int (Either Int (Int, (Integer, Integer))) -> Int -> Thermo Int Int
honestArrow f = fmap (\(a, s) -> (a, honestOf s)) . applyFun f

prop_unit_bind :: Int -> Fun Int Raw -> Bool
prop_unit_bind a f = bind (unit a) (arrow f) == arrow f a

prop_bind_unit :: Raw -> Bool
prop_bind_unit m = bind (toThermo m) unit == toThermo m

prop_bind_assoc :: Raw -> Fun Int Raw -> Fun Int Raw -> Bool
prop_bind_assoc m f g =
  bind (bind (toThermo m) (arrow f)) (arrow g) == bind (toThermo m) (\a -> bind (arrow f a) (arrow g))

prop_bind_inner_refusal :: Int -> (Integer, Integer) -> Int -> Bool
prop_bind_inner_refusal a s e = bind (Right (a, toSpend s)) (\_ -> Left e :: Thermo Int Int) == Left e

prop_bind_spend :: Raw -> Fun Int Raw -> Bool
prop_bind_spend m f = case (toThermo m, bind (toThermo m) (arrow f)) of
  (Right (a, s), Right (b, u)) -> case arrow f a of
    Right (b', t) -> b == b' && u == sadd s t
    Left _ -> False
  (Left e, r) -> r == Left e
  (Right (a, _), Left e) -> arrow f a == Left e

prop_spend_monoid :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) -> Bool
prop_spend_monoid x y z =
  let (s, t, u) = (toSpend x, toSpend y, toSpend z)
  in sadd (sadd s t) u == sadd s (sadd t u) && sadd szero s == s && sadd s szero == s && sadd s t == sadd t s

prop_bind_honest :: Either Int (Int, (Integer, Integer)) -> Fun Int (Either Int (Int, (Integer, Integer))) -> Bool
prop_bind_honest m f = case bind (fmap (\(a, s) -> (a, honestOf s)) m) (honestArrow f) of
  Right (_, u) -> honest u
  Left _ -> True

prop_honest_sum :: [(Integer, Integer)] -> Bool
prop_honest_sum xs = honest (foldr (sadd . honestOf) szero xs)

genQ :: Gen Rational
genQ = do
  d <- choose (1, 12 :: Integer)
  n <- choose (-60, 60)
  pure (fromInteger n / fromInteger d)

genIn :: Interval -> Gen Rational
genIn i = do
  u <- choose (0, 12 :: Integer)
  pure (lo i + (hi i - lo i) * fromInteger u / 12)

genInterval :: Gen Interval
genInterval = do
  a <- genQ
  w <- abs <$> genQ
  pure (Interval a (a + w))

prop_mem_add :: Property
prop_mem_add = forAll genInterval $ \i -> forAll genInterval $ \j -> forAll (genIn i) $ \x -> forAll (genIn j) $ \y ->
  mem (iadd i j) (x + y)

prop_mem_sum_sym :: Property
prop_mem_sum_sym = forAll (listOf (abs <$> genQ)) $ \taus ->
  forAll (mapM (genIn . symI) taus) $ \errs -> mem (symI (sum taus)) (sum errs)

-- | An L-Lipschitz affine map g x = L x + c, an inner error within tau_in and an outer error within tau_out.
prop_error_chain :: Property
prop_error_chain = forAll (abs <$> genQ) $ \l -> forAll genQ $ \c -> forAll (abs <$> genQ) $ \tin ->
  forAll (abs <$> genQ) $ \tout -> forAll genQ $ \ystar -> forAll (genIn (symI tin)) $ \ein ->
  forAll (genIn (symI tout)) $ \eout ->
    let g x = l * x + c
        yhat = ystar + ein
        z = g yhat + eout
    in mem (symI (tout + l * tin)) (z - g ystar)

unfoldKleisliProps :: [(String, Property)]
unfoldKleisliProps =
  [ ("prop_unit_bind", property prop_unit_bind)
  , ("prop_bind_unit", property prop_bind_unit)
  , ("prop_bind_assoc", property prop_bind_assoc)
  , ("prop_bind_inner_refusal", property prop_bind_inner_refusal)
  , ("prop_bind_spend", property prop_bind_spend)
  , ("prop_spend_monoid", property prop_spend_monoid)
  , ("prop_bind_honest", property prop_bind_honest)
  , ("prop_honest_sum", property prop_honest_sum)
  , ("prop_mem_add", prop_mem_add)
  , ("prop_mem_sum_sym", prop_mem_sum_sym)
  , ("prop_error_chain", prop_error_chain)
  ]
