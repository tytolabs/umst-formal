-- |
-- Module      : UMST
-- Description : Compat shim — re-exports the legacy UMST API unchanged.
module UMST
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

import UMST.Compat
