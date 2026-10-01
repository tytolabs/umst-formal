-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: MaterialClass.agda
--
-- The five binder families the cartridges model; twin of Lean/MaterialClass.lean. The gate takes two states and no
-- material, so its verdict never depends on the binder. Activation indexes its engines by this type.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module MaterialClass where

data MaterialClass : Set where
  OPC        : MaterialClass  -- Ordinary Portland Cement
  RAC        : MaterialClass  -- Recycled-Aggregate Concrete
  Geopolymer : MaterialClass  -- Alkali-activated alumino-silicate
  Lime       : MaterialClass  -- Air lime or hydraulic lime
  Earth      : MaterialClass  -- Raw or stabilised earth
