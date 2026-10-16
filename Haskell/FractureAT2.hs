-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- AT2 fracture at a material point on exact rationals; twin of Lean/Concrete/FractureAT2.lean, Coq/FractureAT2.v and
-- Agda/FractureAT2.agda. The stored energy is g(phi) psi_e with g(phi) = (1 - phi)^2; the crack energy
-- (c/2)(phi'^2 - phi^2), c = G_c / l, is spent as dissipation; the damage step is phi' = max phi phi*,
-- phi* = 2 psi_e / (2 psi_e + c). test/FractureAT2Props.hs decides the statements on random inputs.
module FractureAT2
  ( degradation
  , stored
  , crackSpent
  , totalEnergy
  , damageTarget
  , damageUpdate
  ) where

degradation :: Rational -> Rational
degradation phi = (1 - phi) * (1 - phi)

stored :: Rational -> Rational -> Rational
stored psie phi = degradation phi * psie

crackSpent :: Rational -> Rational -> Rational -> Rational
crackSpent c phi phi' = c / 2 * (phi' * phi' - phi * phi)

totalEnergy :: Rational -> Rational -> Rational -> Rational
totalEnergy c psie phi = stored psie phi + c / 2 * (phi * phi)

damageTarget :: Rational -> Rational -> Rational
damageTarget c psie = 2 * psie / (2 * psie + c)

damageUpdate :: Rational -> Rational -> Rational -> Rational
damageUpdate c psie phi = max phi (damageTarget c psie)
