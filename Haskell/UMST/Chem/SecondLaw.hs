-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The chemical second law as an instance of the one predicate ("UMST.Process"): a structurally coherent update of
-- an assemblage obeys the law when its erasure obeys 'secondLaw' on the transformation of its state distribution.
-- Twin of Lean/Chem/SecondLaw.lean, Coq/Chem/SecondLaw.v and Agda/Chem/SecondLaw.agda.
module UMST.Chem.SecondLaw
  ( ThermochemicalTransition (..)
  , structurallyCoherent
  , erasureOf
  , chemSecondLaw
  , assemblageEntropyDrop
  , refinementWorkFloor
  , refinementWorkAccounted
  , PhysicalChemBridge (..)
  , physicalChemBridge
  , coherentP0Transition
  ) where

import UMST.Process
  (ErasureProcess (..), HeatBath (..), Prior (..), ProbDist, Process (..), asProbDist, dirac0, secondLaw, shannon, uniform2)

-- | A thermochemical update: bath, state distributions before and after, the work it dissipates (units of k_B
-- times kelvin) and a structural defect scalar.
data ThermochemicalTransition = ThermochemicalTransition
  { tcBath :: HeatBath
  , tcPrior :: ProbDist
  , tcPost :: ProbDist
  , tcWork :: Double
  , tcDefect :: Double
  }
  deriving (Show)

structurallyCoherent :: ThermochemicalTransition -> Bool
structurallyCoherent t = tcDefect t == 0

-- | The erasure that pays for a transition.
erasureOf :: ThermochemicalTransition -> ErasureProcess
erasureOf t = ErasureProcess (tcBath t) (tcWork t)

chemSecondLaw :: ThermochemicalTransition -> Bool
chemSecondLaw t = structurallyCoherent t && secondLaw (Erase (erasureOf t)) (Transformation (tcPrior t) (tcPost t))

-- | The entropy drop of an update's state distribution (nats).
assemblageEntropyDrop :: ThermochemicalTransition -> Double
assemblageEntropyDrop t = shannon (tcPrior t) - shannon (tcPost t)

-- | Landauer work floor for an entropy drop at bath temperature @T@.
refinementWorkFloor :: Double -> Double -> Double
refinementWorkFloor entropyDrop temp = temp * entropyDrop

-- | Dissipated work meets the floor for the update's entropy drop.
refinementWorkAccounted :: ThermochemicalTransition -> Bool
refinementWorkAccounted t = refinementWorkFloor (assemblageEntropyDrop t) (bathTemp (tcBath t)) <= tcWork t

-- | Physical realisation of a binary assemblage erasure (uniform to Dirac): the erasure and the update it realises.
data PhysicalChemBridge = PhysicalChemBridge
  { pcProc :: ErasureProcess
  , pcTransition :: ThermochemicalTransition
  }
  deriving (Show)

-- | The bridge an erasure determines: the coherent update of the uniform binary assemblage to the Dirac state at the
-- erasure's bath and work (the equations of the Lean structure hold by construction).
physicalChemBridge :: ErasureProcess -> PhysicalChemBridge
physicalChemBridge e =
  PhysicalChemBridge e (ThermochemicalTransition (erasureBath e) (asProbDist uniform2) (asProbDist dirac0) (work e) 0)

-- | A coherent update of the uniform binary assemblage to itself at 300 K, dissipating nothing.
coherentP0Transition :: ThermochemicalTransition
coherentP0Transition = ThermochemicalTransition (HeatBath 300) (asProbDist uniform2) (asProbDist uniform2) 0 0
