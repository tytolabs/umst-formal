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
  ) where

import UMST.Process (ErasureProcess (..), HeatBath, Prior (..), ProbDist, Process (..), secondLaw)

-- | A thermochemical update: bath, state distributions before and after, the work it dissipates (units of k_B
-- times kelvin) and a structural defect scalar.
data ThermochemicalTransition = ThermochemicalTransition
  { tcBath :: HeatBath
  , tcPrior :: ProbDist
  , tcPost :: ProbDist
  , tcWork :: Double
  , tcDefect :: Double
  }

structurallyCoherent :: ThermochemicalTransition -> Bool
structurallyCoherent t = tcDefect t == 0

-- | The erasure that pays for a transition.
erasureOf :: ThermochemicalTransition -> ErasureProcess
erasureOf t = ErasureProcess (tcBath t) (tcWork t)

chemSecondLaw :: ThermochemicalTransition -> Bool
chemSecondLaw t = structurallyCoherent t && secondLaw (Erase (erasureOf t)) (Transformation (tcPrior t) (tcPost t))
