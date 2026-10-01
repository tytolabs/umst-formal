-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The semantic second law; twin of Lean/SemanticSecondLaw.lean, Coq/SemanticSecondLaw.v and
-- Agda/SemanticSecondLaw.agda. A communicative transition obeys the one predicate on its shared model (its entropy
-- clause is the erase instance on the model's transformation), with structural consistency and mutual information
-- preserved above a threshold.
module UMST.Semantic
  ( CommunicativeTransition (..)
  , structurallyConsistent
  , modelUncertaintyDrop
  , miPreserved
  , semanticSecondLaw
  , consistentP0Transition
  ) where

import UMST.Process

data CommunicativeTransition = CommunicativeTransition
  { ctBath :: HeatBath, ctPrior :: ProbDist, ctPost :: ProbDist, ctWork :: Double, ctDefect :: Double }
  deriving (Show)

structurallyConsistent :: CommunicativeTransition -> Bool
structurallyConsistent t = ctDefect t == 0

modelUncertaintyDrop :: CommunicativeTransition -> Double
modelUncertaintyDrop t = shannon (ctPrior t) - shannon (ctPost t)

miPreserved :: Double -> JointDist2 -> Bool
miPreserved threshold j = threshold <= mutualInformation2 j

semanticSecondLaw :: Double -> CommunicativeTransition -> JointDist2 -> Bool
semanticSecondLaw threshold t j =
  structurallyConsistent t && modelUncertaintyDrop t <= ctWork t / bathTemp (ctBath t) && miPreserved threshold j

consistentP0Transition :: CommunicativeTransition
consistentP0Transition = CommunicativeTransition (HeatBath 300) (asProbDist uniform2) (asProbDist uniform2) 0 0
