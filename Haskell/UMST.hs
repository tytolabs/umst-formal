-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
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
