-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- Properties of "PredictionFeedback" (FORMAL-PREDICTION-AS-MEASURE-FEEDBACK) on random turns over exact rationals.
module PredictionFeedbackProps
  ( prop_turn_cyclic_work_le
  , prop_turn_pair_work_le
  , prop_summary_admitted_receipts
  , prop_gated_error_le
  , prop_gated_error_sum_le
  , predictionFeedbackProps
  ) where

import Test.QuickCheck
import PredictionFeedback

genQ :: Gen Rational
genQ = do
  d <- choose (1, 12)
  n <- choose (-24, 24)
  pure (fromIntegral (n :: Integer) / fromIntegral (d :: Integer))

genNonNeg :: Gen Rational
genNonNeg = abs <$> genQ

-- | An admissible turn: its work at most the Sagawa–Ueda bound, less a non-negative slack.
genAdmissible :: Rational -> Gen Turn
genAdmissible k = do
  f <- genQ
  i <- genNonNeg
  slack <- genNonNeg
  pure (Turn (negate f + k * i - slack) f k i)

-- | Twin of turn_cyclic_work_le.
prop_turn_cyclic_work_le :: Property
prop_turn_cyclic_work_le = forAll genNonNeg $ \k -> forAll (genAdmissible k) $ \t0 ->
  let t = t0 { turnDeltaF = 0, turnWork = turnWork t0 + turnDeltaF t0 }
  in turnAdmissible t && turnWork t <= turnKBT t * turnInfo t

-- | Twin of turn_pair_work_le.
prop_turn_pair_work_le :: Property
prop_turn_pair_work_le = forAll genNonNeg $ \k -> forAll (genAdmissible k) $ \s -> forAll (genAdmissible k) $ \t ->
  turnWork s + turnWork t <= negate (turnDeltaF s + turnDeltaF t) + k * (turnInfo s + turnInfo t)

-- | Twin of summary_admitted_receipts and receipts_refused_summary.
prop_summary_admitted_receipts :: Property
prop_summary_admitted_receipts = forAll genNonNeg $ \k -> forAll (genAdmissible k) $ \t -> forAll genNonNeg $ \extra ->
  let (iS, iR) = (turnInfo t, turnInfo t + extra)
  in turnAdmissible (against t iS) && turnAdmissible (against t iR)
       && (turnAdmissible (against t iR) || not (turnAdmissible (against t iS)))

-- | Twin of gated_error_le.
prop_gated_error_le :: Property
prop_gated_error_le = forAll genQ $ \p -> forAll genQ $ \g -> forAll genQ $ \y -> forAll genNonNeg $ \extra ->
  let delta = abs (g - p) + extra in gatedError g y <= gatedError p y + delta

-- | Twin of gated_error_sum_le: decisions whose gate moves stay within their bounds.
prop_gated_error_sum_le :: Property
prop_gated_error_sum_le = forAll (listOf genDecision) $ \ds ->
  sum [gatedError g y | (_, g, y, _) <- ds] <= sum [gatedError p y | (p, _, y, _) <- ds] + sum [d | (_, _, _, d) <- ds]
  where
    genDecision = do
      p <- genQ
      g <- genQ
      y <- genQ
      extra <- genNonNeg
      pure (p, g, y, abs (g - p) + extra)

predictionFeedbackProps :: [(String, Property)]
predictionFeedbackProps =
  [ ("prop_turn_cyclic_work_le", prop_turn_cyclic_work_le)
  , ("prop_turn_pair_work_le", prop_turn_pair_work_le)
  , ("prop_summary_admitted_receipts", prop_summary_admitted_receipts)
  , ("prop_gated_error_le", prop_gated_error_le)
  , ("prop_gated_error_sum_le", prop_gated_error_sum_le)
  ]
