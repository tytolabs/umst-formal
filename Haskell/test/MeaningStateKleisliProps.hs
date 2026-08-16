-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- QuickCheck stub for HCOM-002 Kleisli dialogue composition.
-- Run: cabal test meaning-state-kleisli-props
module Main where

import Test.QuickCheck
import MeaningStateKleisli

instance Arbitrary MeaningState where
  arbitrary = do
    dId <- arbitrary
    tIdx <- arbitrary
    ts <- arbitrary
    defect <- choose (0, 1) >>= \k -> if k == (0 :: Int) then pure 0 else arbitrary
    pure MeaningState
      { context = MeaningContext dId tIdx
      , timestamp = abs ts
      , consistencyDefect = defect
      }

prop_kleisli_compose_preserves_structural_gate :: MeaningState -> Bool
prop_kleisli_compose_preserves_structural_gate s =
  case meaningKleisliCompose (makeMeaningGateArrow id) (makeMeaningGateArrow id) s of
    Just s' -> structurallyConsistent s'
    Nothing -> True

main :: IO ()
main =
  quickCheck prop_kleisli_compose_preserves_structural_gate
