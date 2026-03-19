-- | Engineering consistency check for `Lean/LandauerEinsteinBridge.lean` tight bracket.
-- Not a proof layer: exact arithmetic in 'Rational' mirrors the rational endpoints
-- used after propagating Mathlib's @log_two_near_10@ bound on ln 2.
module Main (main) where

import Data.Ratio ((%))
import System.Exit (exitFailure)

kB, c, r, eps :: Rational
kB = 1380649 % (10 ^ (29 :: Integer))
c = 299792458 % 1
r = 287209 % 414355
eps = 1 % (10 ^ (10 :: Integer))

-- Endpoints from |ln 2 - r| ≤ eps (conservative mass bounds at T = 300 K).
massLower, massUpper :: Rational
massLower = kB * 300 * (r - eps) / (c * c)
massUpper = kB * 300 * (r + eps) / (c * c)

-- Lean theorems @massEquivalent_three_hundred_gt_tight@ / @lt_tight@.
nLo, nHi :: Rational
nLo = 319439481694054 % (10 ^ (52 :: Integer))
nHi = 319439481786228 % (10 ^ (52 :: Integer))

main :: IO ()
main = do
  putStrLn "LandauerEinsteinSanity: Rational endpoints vs Lean tight bracket numerators"
  if nLo < massLower && massUpper < nHi
    then putStrLn "PASS"
    else do
      putStrLn "FAIL: expected nLo < massLower && massUpper < nHi"
      print ("nLo", nLo, "massLower", massLower, "massUpper", massUpper, "nHi", nHi)
      exitFailure
