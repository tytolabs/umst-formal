-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.Chem.Constants.EgoffHarnessAdversarial
-- Description : Meso acting — adversarial egoff harness drift refusal witness.
module UMST.Chem.Constants.EgoffHarnessAdversarial
  ( soleAxiomCount
  , physicsGreen
  , sidecarModelPin
  , harnessDriftForbidden
  , refuseSecondAxiom
  ) where

soleAxiomCount :: Int
soleAxiomCount = 1

physicsGreen :: Bool
physicsGreen = False

sidecarModelPin :: String
sidecarModelPin = "EGOFF_SIDECAR_MODEL"

harnessDriftForbidden :: Bool
harnessDriftForbidden = True

refuseSecondAxiom :: Bool
refuseSecondAxiom = soleAxiomCount /= 2
