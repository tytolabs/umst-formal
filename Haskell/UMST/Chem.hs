-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem
-- Description : Chemistry meso/acting axiom spine — second law + conservation only.
--
-- Lifts existing UMST gate meaning ('UMST.Core', 'SDFGate', 'UMST.Concrete');
-- no new physics axiom.  Tables, patterns, and cartridges are presentations
-- under this spine — not additional laws.
module UMST.Chem
  ( -- * Axiom spine (meso/acting)
    ChemAxiom (..)
  , chemAxiomMarker
    -- * Conservation (mass-density ball)
  , ConservationWitness (..)
  , conservationDensityOk
  , conservationSDF
  , conservationFromGate
    -- * Second law (Clausius–Duhem dissipation sign)
  , SecondLawWitness (..)
  , secondLawDissipationOk
  , secondLawSDF
  , secondLawFromGate
    -- * Combined transition check
  , ChemTransition (..)
  , chemAxiomOk
  , chemAxiomSDF
  ) where

import SDFGate (clausiusDuhemSDF, massConservationSDF)
import UMST.Concrete
  ( AdmissibilityResult (..)
  , ThermodynamicState (..)
  , gateCheck
  , tolerance
  )
import UMST.Core (coreDissipationOk, coreMassOk)

-- | Machine-readable marker — single axiom: second law + conservation.
chemAxiomMarker :: String
chemAxiomMarker = "chem_axiom_second_law_conservation_v1"

-- | Chemistry admits only the thermodynamic spine (no parallel laws).
data ChemAxiom = SecondLawConservationOnly
  deriving (Show, Eq)

-- | Witness for mass-density conservation (lifts 'coreMassOk').
data ConservationWitness = ConservationWitness
  { densityDelta :: !Double
  , massOk       :: !Bool
  } deriving (Show, Eq)

conservationDensityOk :: Double -> Double -> Bool
conservationDensityOk = coreMassOk tolerance

conservationSDF :: ThermodynamicState -> ThermodynamicState -> Double
conservationSDF = massConservationSDF

conservationFromGate
  :: ThermodynamicState -> ThermodynamicState -> Double -> ConservationWitness
conservationFromGate old new dt =
  let AdmissibilityResult{massConserved = ok} = gateCheck old new dt
  in ConservationWitness
      { densityDelta = density new - density old
      , massOk = ok
      }

-- | Witness for Clausius–Duhem dissipation (lifts 'coreDissipationOk').
data SecondLawWitness = SecondLawWitness
  { freeEnergyDelta :: !Double
  , dissipationJoule  :: !Double
  , secondLawOk       :: !Bool
  } deriving (Show, Eq)

secondLawSDF :: ThermodynamicState -> ThermodynamicState -> Double
secondLawSDF = clausiusDuhemSDF

secondLawDissipationOk
  :: ThermodynamicState -> ThermodynamicState -> Double -> Bool
secondLawDissipationOk old new dt =
  let psiDot = (freeEnergy new - freeEnergy old) / (dt + 1e-10)
      rhoAvg = (density old + density new) / 2.0
      diss   = negate (rhoAvg * psiDot)
  in coreDissipationOk tolerance diss

secondLawFromGate
  :: ThermodynamicState -> ThermodynamicState -> Double -> SecondLawWitness
secondLawFromGate old new dt =
  let AdmissibilityResult{dissipation = diss, energyPositive = ok} =
        gateCheck old new dt
  in SecondLawWitness
      { freeEnergyDelta = freeEnergy new - freeEnergy old
      , dissipationJoule = diss
      , secondLawOk = ok
      }

-- | A chemistry transition under the single axiom.
data ChemTransition = ChemTransition
  { chemFromState :: !ThermodynamicState
  , chemToState   :: !ThermodynamicState
  , chemDt        :: !Double
  } deriving (Show, Eq)

chemAxiomOk :: ChemTransition -> Bool
chemAxiomOk (ChemTransition fs ts dt) =
  conservationDensityOk (density fs) (density ts)
  && secondLawDissipationOk fs ts dt

chemAxiomSDF :: ThermodynamicState -> ThermodynamicState -> Double
chemAxiomSDF old new =
  max (conservationSDF old new) (secondLawSDF old new)
