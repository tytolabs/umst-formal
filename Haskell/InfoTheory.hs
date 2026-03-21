-- |
-- Module      : InfoTheory
-- Description : Finite discrete joint laws (engineering mirror of @Lean/InfoTheory.lean@)
--
-- Provides product joint and marginals on lists of masses (no dependent @Fin n@).
-- QuickCheck in @test/Test.hs@ checks the same algebraic facts proved in Lean:
-- @marginalX_product@, @marginalY_product@ (sum-normalized case).
module InfoTheory
  ( productJoint
  , marginalFirst
  , marginalSecond
  , jointMassesSum
  ) where

-- | Outer index = first marginal (row); inner = second (column).
--   @productJoint p q@ has shape @length p@ rows, each of length @length q@.
productJoint :: [Double] -> [Double] -> [[Double]]
productJoint p q = [ [ px * qk | qk <- q ] | px <- p ]

-- | Sum of all entries in a rectangular joint table.
jointMassesSum :: [[Double]] -> Double
jointMassesSum = sum . map sum

-- | First marginal: row sums @\\sum_k J[i][k]@.
marginalFirst :: [[Double]] -> [Double]
marginalFirst = map sum

-- | Second marginal: column sums @\\sum_i J[i][k]@.
marginalSecond :: [[Double]] -> [Double]
marginalSecond [] = []
marginalSecond (r : rs) = foldl (zipWith (+)) r rs
