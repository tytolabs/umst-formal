-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- | Property tests of the Jarzynski fluctuation theorem and the thermodynamic uncertainty relation (twins of
-- Lean/FluctuationTheorem.lean, Lean/UncertaintyRelation.lean and their Coq and Agda twins).
--
-- Protocols are drawn with random positive rational weights per stage and Metropolis kernels, which satisfy detailed
-- balance with the weight they relax under; the Jarzynski identity is then checked exactly, in transfer form and as
-- a sum over every trajectory. The Jensen bridge, the SecondLaw consequence and the TUR run on 'Double' with the real
-- exponential and logarithm; their margins are relative to the size of the terms.
module FluctuationProps
  ( fluctuationProps
  ) where

import Test.QuickCheck

import UMST.FluctuationTheorem
import UMST.UncertaintyRelation
import qualified UMST.Process as P

-- | A positive rational with numerator in [1, 50] and denominator in [1, 20].
genPos :: Gen Rational
genPos = (\a b -> fromIntegral a / fromIntegral b) <$> choose (1 :: Integer, 50) <*> choose (1 :: Integer, 20)

-- | Weights of a protocol on n states with K stages: K + 1 rows of n positive rationals.
genWeights :: Gen [[Rational]]
genWeights = do
  n <- choose (1, 4)
  kmax <- choose (0, 3)
  vectorOf (kmax + 1) (vectorOf n genPos)

-- | The protocol with these weights and Metropolis kernels for the weight of each next stage, and its stage count.
mkProtocol :: [[Rational]] -> (Protocol, Int)
mkProtocol ws = (p, length ws - 1)
  where
    n = case ws of { (row : _) -> length row; [] -> 0 }
    w k x = (ws !! k) !! x
    p = Protocol { states = n, weight = w, kernel = \k -> metropolisKernel n (w (k + 1)) }

genProtocol :: Gen [[Rational]]
genProtocol = genWeights

-- | One stage: tilting by the work of the switch and relaxing gives the next weight (exact).
prop_ft_gibbs_tilt_stage :: Property
prop_ft_gibbs_tilt_stage = forAll genProtocol $ \ws -> let (p, kmax) = mkProtocol ws in
  kernelBalanced p kmax &&
  and [ sum [weight p k x * tilt p k x * kernel p k x y | x <- [0 .. states p - 1]] == weight p (k + 1) y
      | k <- [0 .. kmax - 1], y <- [0 .. states p - 1] ]

-- | Transfer form: the tilted forward vector after K stages is the weight of stage K (exact).
prop_ft_tilted_forward_eq :: Property
prop_ft_tilted_forward_eq = forAll genProtocol $ \ws -> let (p, kmax) = mkProtocol ws in
  all (\y -> tiltedForward p kmax y == weight p kmax y) [0 .. states p - 1]

-- | Jarzynski over every trajectory: <exp(-beta W)> = Z K / Z 0 (exact).
prop_ft_jarzynski_paths :: Property
prop_ft_jarzynski_paths = forAll genProtocol $ \ws -> let (p, kmax) = mkProtocol ws in
  pathAverage p kmax == partition p kmax / partition p 0

-- | A finite ensemble: positive probabilities summing to one and works in units of 1/beta.
genEnsemble :: Gen [(Double, Double)]
genEnsemble = do
  m <- choose (1, 8)
  raw <- vectorOf m (choose (0.01, 1))
  ws <- vectorOf m (choose (-5, 5))
  let s = sum raw
  pure (zip (map (/ s) raw) ws)

-- | Jensen bridge: the free-energy change fixed by the integral fluctuation theorem is at most the mean work.
prop_ft_jensen_bridge :: Property
prop_ft_jensen_bridge = forAll (choose (0.1, 10)) $ \beta -> forAll genEnsemble $ \ens ->
  let dF = jarzynskiFreeEnergy beta ens
  in abs (ensembleIFT beta dF ens - 1) < 1e-9 && dF <= ensembleMean ens + 1e-9 * (1 + abs dF)

-- | The measureFeedback case of SecondLaw from the fluctuation theorem, at beta = 1 / (k_B T), works in joules.
prop_ft_secondLaw_feedback :: Property
prop_ft_secondLaw_feedback = forAll (choose (1, 1000)) $ \t -> forAll genEnsemble $ \ens0 ->
  forAll (choose (0, 3)) $ \mi ->
  let kT = P.kB * t
      ens = [(pr, w * kT) | (pr, w) <- ens0]
      dF = jarzynskiFreeEnergy (1 / kT) ens
      -- shift by a margin of 1e-9 k_B T against rounding in the logarithm
      f = asFeedback (P.HeatBath t) (dF - 1e-9 * kT) ens
  in P.secondLaw (P.MeasureFeedback f) (P.Feedback mi)

-- | Logarithmic-mean bound 2 (a - b)^2 <= (a + b)(a - b)(ln a - ln b).
prop_tur_log_mean_bound :: Property
prop_tur_log_mean_bound = forAll (choose (0.01, 100)) $ \a -> forAll (choose (0.01, 100)) $ \b ->
  logMeanGap a b >= -1e-9 * (a + b) * (a + b)

-- | TUR for the biased walk: Var(J_t) sigma_t >= 2 <J_t>^2.
prop_tur_biased_walk :: Property
prop_tur_biased_walk = forAll (choose (0.01, 100)) $ \kp -> forAll (choose (0.01, 100)) $ \km ->
  forAll (choose (0, 50)) $ \t ->
  let w = BiasedWalk kp km
  in turGap w t >= -1e-9 * ((kp + km) * t) * ((kp + km) * t)

fluctuationProps :: [(String, Property)]
fluctuationProps =
  [ ("ft_gibbs_tilt_stage", prop_ft_gibbs_tilt_stage)
  , ("ft_tilted_forward_eq", prop_ft_tilted_forward_eq)
  , ("ft_jarzynski_paths", prop_ft_jarzynski_paths)
  , ("ft_jensen_bridge", prop_ft_jensen_bridge)
  , ("ft_secondLaw_feedback", prop_ft_secondLaw_feedback)
  , ("tur_log_mean_bound", prop_tur_log_mean_bound)
  , ("tur_biased_walk", prop_tur_biased_walk)
  ]
