-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The one second law as an executable predicate, twin of Lean/Process.lean, Coq/Process.v and Agda/Process.agda:
-- a process family (erasure, measurement with feedback, gate transition) and one predicate 'secondLaw'. A prior of
-- the wrong kind for its process is refused ('False').
--
--   erase            S(prior) - S(Dirac) <= W / T   (entropy in nats, work in units of k_B times kelvin)
--   measureFeedback  W_ext <= -dF + k_B T I         (joules; I in nats)
--   transition       the gate's admissibility of the state move
module UMST.Process
  ( HeatBath (..)
  , ErasureProcess (..)
  , FeedbackProcess (..)
  , ProbDist2 (..)
  , Process (..)
  , Prior (..)
  , shannon2
  , dirac0
  , uniform2
  , kB
  , secondLaw
  , landauerTightErasure
  , eraseSecondLawSI
  ) where

import UMST.Concrete (ThermodynamicState, AdmissibilityResult (..), gateCheck)
import qualified UMST.Constants.SI as SI

-- | A heat bath at a temperature in kelvin (positive for a physical bath).
newtype HeatBath = HeatBath { bathTemp :: Double }
  deriving (Show)

-- | An erasure: its bath and the work it dissipates (units of k_B times kelvin).
data ErasureProcess = ErasureProcess { erasureBath :: HeatBath, work :: Double }
  deriving (Show)

-- | Measurement and feedback: bath, external work and free-energy change (joules).
data FeedbackProcess = FeedbackProcess
  { feedbackBath :: HeatBath, extWork :: Double, deltaFreeEnergy :: Double }
  deriving (Show)

-- | A distribution on two states, by the probability of the first (in [0, 1]).
newtype ProbDist2 = ProbDist2 { p0 :: Double }
  deriving (Show)

data Process = Erase ErasureProcess | MeasureFeedback FeedbackProcess | Transition
  deriving (Show)

-- | The prior a process is judged against: a distribution to erase, the mutual information (nats) a measurement
-- acquired, or the two states of a gate move.
data Prior = Erasure ProbDist2 | Feedback Double | Thermodynamic ThermodynamicState ThermodynamicState

-- | x ln x with the continuous extension 0 ln 0 = 0.
xlnx :: Double -> Double
xlnx x = if x <= 0 then 0 else x * log x

-- | Shannon entropy in nats.
shannon2 :: ProbDist2 -> Double
shannon2 (ProbDist2 p) = negate (xlnx p + xlnx (1 - p))

dirac0, uniform2 :: ProbDist2
dirac0 = ProbDist2 1
uniform2 = ProbDist2 0.5

-- | The exact SI Boltzmann constant of "UMST.Constants.SI", as a 'Double'.
kB :: Double
kB = fromRational SI.boltzmann

-- | The second law: one predicate over the process family.
secondLaw :: Process -> Prior -> Bool
secondLaw (Erase e) (Erasure p) =
  shannon2 p - shannon2 dirac0 <= work e / bathTemp (erasureBath e)
secondLaw (MeasureFeedback f) (Feedback mi) =
  extWork f <= negate (deltaFreeEnergy f) + kB * bathTemp (feedbackBath f) * mi
secondLaw Transition (Thermodynamic old new) = accepted (gateCheck old new 1)  -- a unit step; the verdict's
                                                                             -- sign conditions do not depend on it
secondLaw _ _ = False

-- | The erasure that dissipates exactly T ln 2: it attains the Landauer bound.
landauerTightErasure :: HeatBath -> ErasureProcess
landauerTightErasure b = ErasureProcess b (bathTemp b * log 2)

-- | SI Clausius form: an entropy drop dS (nats) with work W in joules at T obeys dS <= W / (k_B T).
eraseSecondLawSI :: Double -> Double -> Double -> Bool
eraseSecondLawSI t dS w = dS <= w / (kB * t)
