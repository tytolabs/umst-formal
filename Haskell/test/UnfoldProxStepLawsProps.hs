-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "UnfoldProxStepLaws" (UNFOLD-PROX-STEP-LAWS): random scalar proximal steps with convex quadratic
-- free energy and dissipation potential, on exact rationals.
module UnfoldProxStepLawsProps
  ( prop_prox_step_le
  , prop_prox_step_deltaF_le
  , prop_prox_step_refused
  , prop_prox_step_stationary_le
  , prop_prox_dissipation_rate_nonneg
  , unfoldProxStepLawsProps
  ) where

import Test.QuickCheck
import UnfoldProxStepLaws

genQ :: Integer -> Gen Rational
genQ hi = do
  d <- choose (1, 12)
  n <- choose (-hi * d, hi * d)
  pure (fromIntegral n / fromIntegral (d :: Integer))

genPos :: Gen Rational
genPos = do
  d <- choose (1, 12)
  n <- choose (1, 10 * d)
  pure (fromIntegral n / fromIntegral (d :: Integer))

genStep :: Gen QuadStep
genStep = QuadStep <$> genPos <*> genQ 10 <*> genPos <*> genPos <*> genQ 10 <*> genQ 10

-- | The minimiser is no worse than any candidate (the hypothesis of the laws holds on the generated steps).
isMin :: QuadStep -> Rational -> Bool
isMin s y = incrementalQ s (proxMinimiser s) <= incrementalQ s y

-- | Twin of prox_step_le.
prop_prox_step_le :: Property
prop_prox_step_le = forAll genStep $ \s -> forAll (genQ 20) $ \y ->
  let xp = proxMinimiser s
      x0 = qx0 s
      v = (xp - x0) / qtau s
  in isMin s y && psiQ s xp - psiQ s x0 + qtau s * phiQ s v <= qf s * xp - qf s * x0

-- | Twin of prox_step_deltaF_le.
prop_prox_step_deltaF_le :: Property
prop_prox_step_deltaF_le = forAll genStep $ \s ->
  let xp = proxMinimiser s
  in psiQ s xp - psiQ s (qx0 s) <= qf s * (xp - qx0 s)

-- | Twin of prox_step_refused: a candidate breaking the inequality has a larger incremental potential than x0.
prop_prox_step_refused :: Property
prop_prox_step_refused = forAll genStep $ \s -> forAll (genQ 20) $ \y ->
  let x0 = qx0 s
      v = (y - x0) / qtau s
      anti = qf s * (y - x0) < psiQ s y - psiQ s x0 + qtau s * phiQ s v
  in anti ==> incrementalQ s y > incrementalQ s x0

-- | Twin of prox_step_stationary_le: the slopes a = k (x+ - c) and b = eta v meet the load, a + b = f, and their
-- supporting lines bound psi and phi.
prop_prox_step_stationary_le :: Property
prop_prox_step_stationary_le = forAll genStep $ \s ->
  let xp = proxMinimiser s
      x0 = qx0 s
      v = (xp - x0) / qtau s
      a = qk s * (xp - qc s)
      b = qeta s * v
  in a + b == qf s
     && psiQ s x0 >= psiQ s xp + a * (x0 - xp)
     && phiQ s 0 >= phiQ s v + b * (0 - v)
     && psiQ s xp - psiQ s x0 + qtau s * phiQ s v <= qf s * (xp - x0)

-- | Twin of prox_dissipation_rate_nonneg.
prop_prox_dissipation_rate_nonneg :: Property
prop_prox_dissipation_rate_nonneg = forAll genStep $ \s -> forAll (genQ 20) $ \v ->
  let b = qeta s * v
  in phiQ s v <= b * v && 0 <= b * v

unfoldProxStepLawsProps :: [(String, Property)]
unfoldProxStepLawsProps =
  [ ("prop_prox_step_le", prop_prox_step_le)
  , ("prop_prox_step_deltaF_le", prop_prox_step_deltaF_le)
  , ("prop_prox_step_refused", prop_prox_step_refused)
  , ("prop_prox_step_stationary_le", prop_prox_step_stationary_le)
  , ("prop_prox_dissipation_rate_nonneg", prop_prox_dissipation_rate_nonneg)
  ]
