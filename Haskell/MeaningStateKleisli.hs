-- |
-- Module      : MeaningStateKleisli
-- Description : HCOM-002 Haskell QuickCheck stub — Kleisli dialogue composition
--               mirrors `Lean/MeaningState.lean` structural gate leg.
module MeaningStateKleisli
  ( MeaningContext (..)
  , MeaningState (..)
  , MeaningKleisliArrow
  , structurallyConsistent
  , meaningStructuralGateCheck
  , makeMeaningGateArrow
  , meaningKleisliCompose
  ) where

data MeaningContext = MeaningContext
  { dialogueId :: !Int
  , turnIndex  :: !Int
  } deriving (Show, Eq)

data MeaningState = MeaningState
  { context           :: !MeaningContext
  , timestamp         :: !Int
  , consistencyDefect :: !Double
  } deriving (Show, Eq)

type MeaningKleisliArrow = MeaningState -> Maybe MeaningState

structurallyConsistent :: MeaningState -> Bool
structurallyConsistent ms = consistencyDefect ms == 0

meaningStructuralGateCheck :: MeaningState -> Bool
meaningStructuralGateCheck = structurallyConsistent

makeMeaningGateArrow :: (MeaningState -> MeaningState) -> MeaningKleisliArrow
makeMeaningGateArrow propose prior =
  let post = propose prior
   in if meaningStructuralGateCheck post then Just post else Nothing

meaningKleisliCompose :: MeaningKleisliArrow -> MeaningKleisliArrow -> MeaningKleisliArrow
meaningKleisliCompose f g s =
  case f s of
    Nothing -> Nothing
    Just s' -> g s'
