-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Chemistry as an instance of the one predicate ("UMST.Process"): an update is sent to the erasure that pays for it,
-- judged against the transformation of its state distribution. Updates form a category (the identity update, the
-- composite update) and the map is a functor that preserves admissibility. Twin of Lean/Chem/ProcessFunctor.lean,
-- Coq/Chem/ProcessFunctor.v and Agda/Chem/ProcessFunctor.agda.
module UMST.Chem.ProcessFunctor
  ( processOf
  , transformationOf
  , idAt
  , composite
  , bridgeSecondLaw
  , realisedSecondLaw
  ) where

import UMST.Chem.SecondLaw (PhysicalChemBridge (..), ThermochemicalTransition (..), erasureOf)
import UMST.Process (HeatBath, Prior (..), ProbDist, Process (..), secondLaw, uniform2)

-- | The process an update is: the erasure that pays for it.
processOf :: ThermochemicalTransition -> Process
processOf = Erase . erasureOf

-- | The prior an update is judged against: the transformation of its state distribution.
transformationOf :: ThermochemicalTransition -> Prior
transformationOf t = Transformation (tcPrior t) (tcPost t)

-- | The identity update of distribution @p@ at bath @b@: no change, no work, no defect.
idAt :: HeatBath -> ProbDist -> ThermochemicalTransition
idAt b p = ThermochemicalTransition b p p 0 0

-- | The composite of @t1@ then @t2@ at the bath of @t1@: works and defects added.
composite :: ThermochemicalTransition -> ThermochemicalTransition -> ThermochemicalTransition
composite t1 t2 =
  ThermochemicalTransition (tcBath t1) (tcPrior t1) (tcPost t2) (tcWork t1 + tcWork t2) (tcDefect t1 + tcDefect t2)

-- | The erase case of the bridge's erasure on the uniform bit.
bridgeSecondLaw :: PhysicalChemBridge -> Bool
bridgeSecondLaw b = secondLaw (Erase (pcProc b)) (Erasure uniform2)

-- | The second law of the image of the update the bridge realises.
realisedSecondLaw :: PhysicalChemBridge -> Bool
realisedSecondLaw b = secondLaw (processOf (pcTransition b)) (transformationOf (pcTransition b))
