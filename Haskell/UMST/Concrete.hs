-- |
-- Module      : UMST.Concrete
-- Description : OPC cement cartridge — state types and gate logic.
module UMST.Concrete
  ( -- * Types
    ThermodynamicState (..)
  , AdmissibilityResult (..)
  , MaterialType (..)
    -- * Constants
  , qHydration
  , tolerance
  , massTolerance
  , intrinsicStrength
    -- * Gate
  , gateCheck
    -- * Constructors
  , fromMix
  ) where

import UMST.Core (coreDissipationOk, coreMassOk, massTolerance)

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

qHydration :: Double
qHydration = 450.0

tolerance :: Double
tolerance = 1e-6

intrinsicStrength :: Double
intrinsicStrength = 230.0

------------------------------------------------------------------------
-- ThermodynamicState
------------------------------------------------------------------------

data ThermodynamicState = ThermodynamicState
  { density     :: !Double
  , freeEnergy  :: !Double
  , hydration   :: !Double
  , strength    :: !Double
  , maxStrength :: !Double
  } deriving (Show, Eq)

------------------------------------------------------------------------
-- AdmissibilityResult
------------------------------------------------------------------------

data AdmissibilityResult = AdmissibilityResult
  { accepted       :: !Bool
  , dissipation    :: !Double
  , massConserved  :: !Bool
  , energyPositive :: !Bool
  , hydrationOk    :: !Bool
  , strengthOk     :: !Bool
  } deriving (Show, Eq)

------------------------------------------------------------------------
-- MaterialType
------------------------------------------------------------------------

data MaterialType
  = Cement
  | Aggregate
  | Water
  | Admixture
  | Air
  | SCM
  | Fiber
  | Nanomaterial
  | Activator
  | Lightweight
  | Heavyweight
  | Accelerator
  | Retarder
  | AirEntrainer
  | Polymer
  | Pigment
  | Filler
  deriving (Show, Eq, Ord, Enum, Bounded)

------------------------------------------------------------------------
-- Pure Gate Check
------------------------------------------------------------------------

gateCheck
  :: ThermodynamicState
  -> ThermodynamicState
  -> Double
  -> AdmissibilityResult
gateCheck old new dt =
  let
    massOk = coreMassOk tolerance (density old) (density new)

    psiDot = (freeEnergy new - freeEnergy old) / (dt + 1e-10)
    rhoAvg = (density old + density new) / 2.0
    diss   = negate (rhoAvg * psiDot)
    dissOk = coreDissipationOk tolerance diss

    hydOk = hydration new >= hydration old - tolerance
    strOk = strength new >= strength old - tolerance

    allOk = massOk && dissOk && hydOk && strOk
  in AdmissibilityResult
    { accepted       = allOk
    , dissipation    = diss
    , massConserved  = massOk
    , energyPositive = dissOk
    , hydrationOk    = hydOk
    , strengthOk     = strOk
    }

------------------------------------------------------------------------
-- Pure fromMix
------------------------------------------------------------------------

fromMix
  :: Double
  -> Double
  -> Double
  -> ThermodynamicState
fromMix wc alpha temp =
  let
    rho    = 1000.0 + 500.0 * (1.0 - wc) - 0.5 * (temp - 20.0)
    psi    = negate (qHydration * alpha)
    gel    = powersGelSpaceRatio wc alpha
    fc     = intrinsicStrength * gel ** 3
    gelMax = powersGelSpaceRatio wc 1.0
    fcMax  = intrinsicStrength * gelMax ** 3
  in ThermodynamicState
    { density     = rho
    , freeEnergy  = psi
    , hydration   = alpha
    , strength    = fc
    , maxStrength = fcMax
    }

powersGelSpaceRatio :: Double -> Double -> Double
powersGelSpaceRatio wc alpha
  | denom < tolerance = 0.0
  | otherwise         = (0.68 * alpha) / denom
  where
    denom = 0.32 * alpha + wc
