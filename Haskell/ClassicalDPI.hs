-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- The classical data-processing inequality for a deterministic summary; twin of Lean/ClassicalDPI.lean,
-- Coq/ClassicalDPI.v and Agda/ClassicalDPI.agda. A joint distribution is a table of rows (X) by columns (Y); the
-- summary merges the columns of each fibre of f. Mutual information is computed in Double at this test edge, so the
-- property in test/ClassicalDPIProps.hs allows a stated rounding tolerance.
module ClassicalDPI
  ( Joint
  , mutualInformation
  , summary
  , logSumGap
  , colFun
  ) where

-- | Rows indexed by X, columns by Y; non-negative masses summing to 1.
type Joint = [[Double]]

xlogx :: Double -> Double
xlogx x = if x <= 0 then 0 else x * log x

entropy :: [Double] -> Double
entropy = negate . sum . map xlogx

-- | I(X; Y) = H(X) + H(Y) - H(X, Y).
mutualInformation :: Joint -> Double
mutualInformation j = entropy (map sum j) + entropy (foldr (zipWith (+)) (map (const 0) (headOr j)) j) - entropy (concat j)
  where headOr (r : _) = r
        headOr [] = []

-- | The joint of X and f(Y) on k summary values: column c is the sum of the columns j with f j = c.
summary :: Int -> (Int -> Int) -> Joint -> Joint
summary k f = map (\row -> [sum [p | (jIdx, p) <- zip [0 ..] row, f jIdx == c] | c <- [0 .. k - 1]])

-- | The two-term log-sum gap a ln(a/s) + b ln(b/t) - (a+b) ln((a+b)/(s+t)), non-negative for a, b >= 0, s, t > 0.
logSumGap :: Double -> Double -> Double -> Double -> Double
logSumGap a b s t = term a s + term b t - term (a + b) (s + t)
  where term x y = if x <= 0 then 0 else x * log (x / y)

-- | The column functional G(v) = sum v_i ln v_i - (sum v_i) ln(sum v_i).
colFun :: [Double] -> Double
colFun v = sum (map xlogx v) - xlogx (sum v)
