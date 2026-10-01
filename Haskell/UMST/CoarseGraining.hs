-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Coarse graining on the process family; twin of Lean/CoarseGraining.lean, Coq/CoarseGraining.v and
-- Agda/CoarseGraining.agda. Under the Esposito conditions (work preserved, coarse entropy drop at most the fine
-- one) fine admissibility implies coarse admissibility; for a product joint H(X,Y) = H(X) + H(Y) >= H(X).
module UMST.CoarseGraining
  ( CoarseGrainMap (..)
  , idCoarseGrainMap
  , comp
  , eraseEntropyDrop
  , sharpenMap
  , productJoint2
  ) where

import UMST.Process

data CoarseGrainMap = CoarseGrainMap { mapProcess :: Process -> Process, mapPrior :: Prior -> Prior }

idCoarseGrainMap :: CoarseGrainMap
idCoarseGrainMap = CoarseGrainMap id id

comp :: CoarseGrainMap -> CoarseGrainMap -> CoarseGrainMap
comp g f = CoarseGrainMap (mapProcess g . mapProcess f) (mapPrior g . mapPrior f)

eraseEntropyDrop :: ProbDist2 -> Double
eraseEntropyDrop p = shannon2 p - shannon2 dirac0

-- | An Esposito-admissible map for tests: erasures unchanged, each erasure prior moved a fraction @s@ toward the
-- nearer pure state, which lowers its entropy.
sharpenMap :: Double -> CoarseGrainMap
sharpenMap s = CoarseGrainMap id prior
  where
    prior (Erasure (ProbDist2 x)) = Erasure (ProbDist2 (if x >= 0.5 then x + s * (1 - x) else x - s * x))
    prior pr = pr

productJoint2 :: ProbDist2 -> ProbDist2 -> JointDist2
productJoint2 (ProbDist2 a) (ProbDist2 b) = JointDist2 (a * b) (a * (1 - b)) ((1 - a) * b) ((1 - a) * (1 - b))
