-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The second law as one free-energy inequality, dF <= W_in + k_B T I (joules; I in nats); twin of
-- Lean/OneInequalitySecondLaw.lean, Coq/OneInequalitySecondLaw.v and Agda/OneInequalitySecondLaw.agda. Each
-- process kind fixes which terms vanish; one chaining rule composes mixed sequences at a common bath.
module UMST.OneInequality
  ( Step (..)
  , oneInequality
  , chain
  , eraseStep
  , feedbackStep
  , transitionStepAt
  , stepOf
  ) where

import UMST.Concrete (ThermodynamicState (..))
import UMST.Process

-- | One thermodynamic step: its bath, free-energy change, work in and information.
data Step = Step { stepBath :: HeatBath, deltaF :: Double, wIn :: Double, infoI :: Double }
  deriving (Show)

oneInequality :: Step -> Bool
oneInequality s = deltaF s <= wIn s + kB * bathTemp (stepBath s) * infoI s

-- | Sequential composition at the first step's bath.
chain :: Step -> Step -> Step
chain s1 s2 = Step (stepBath s1) (deltaF s1 + deltaF s2) (wIn s1 + wIn s2) (infoI s1 + infoI s2)

-- | Erase (joules): I = 0, dF = k_B T (S(prior) - S(post)), W_in = k_B W.
eraseStep :: ErasureProcess -> ProbDist -> ProbDist -> Step
eraseStep e p q = Step (erasureBath e) (kB * bathTemp (erasureBath e) * (shannon p - shannon q)) (kB * work e) 0

-- | Measurement with feedback: W_in = -W_ext.
feedbackStep :: FeedbackProcess -> Double -> Step
feedbackStep f mi = Step (feedbackBath f) (deltaFreeEnergy f) (negate (extWork f)) mi

-- | Passive transition at a bath: W_in = 0, I = 0.
transitionStepAt :: HeatBath -> ThermodynamicState -> ThermodynamicState -> Step
transitionStepAt b old new = Step b (freeEnergy new - freeEnergy old) 0 0

-- | Any process with a prior of its kind packages as a step.
stepOf :: Process -> Prior -> Maybe Step
stepOf (Erase e) (Erasure p) = Just (eraseStep e (asProbDist p) (asProbDist dirac0))
stepOf (MeasureFeedback f) (Feedback mi) = Just (feedbackStep f mi)
stepOf Transition (Thermodynamic old new) = Just (transitionStepAt (HeatBath 1) old new)
stepOf (Erase e) (Transformation p q) = Just (eraseStep e p q)
stepOf _ _ = Nothing
