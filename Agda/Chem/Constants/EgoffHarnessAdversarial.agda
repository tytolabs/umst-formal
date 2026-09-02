-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
module Chem.Constants.EgoffHarnessAdversarial where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; false; true)
open import Data.String using (String)

soleAxiomCount : ℕ
soleAxiomCount = suc zero

physicsGreen : Bool
physicsGreen = false

sidecarModelPin : String
sidecarModelPin = "EGOFF_SIDECAR_MODEL"

harnessDriftForbidden : Bool
harnessDriftForbidden = true
