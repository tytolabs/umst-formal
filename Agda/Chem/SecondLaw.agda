-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.SecondLaw — meso/acting chemistry second-law anchor.
--
-- CHEM-L0-FORMAL-01 / CHEM-NS-W0-AXIOM (umst-formal acting fiber only).
-- Sole project physics postulate mirrors:
--   • Lean  @Lean/LandauerLaw.lean@  `physicalSecondLaw`
--   • Haskell / Coq Shannon+log bounds remain authority for numeric ln 2.
--
-- physics_green: false — this module does not duplicate Mathlib analysis.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Chem.SecondLaw where

open import Data.Rational as ℚ using (ℚ; _≤_)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Clausius interface (k_B = 1 convention; W/T bundled as entropy units)
------------------------------------------------------------------------

record HeatBath : Set where
  field
    temperature : ℚ

record ErasureProcess : Set where
  field
    bath : HeatBath
    dissipatedEntropy : ℚ  -- W/T in nats (Lean `proc.work / proc.bath.bathTemp.val`)

PhysicalSecondLaw : ErasureProcess → ℚ → Set
PhysicalSecondLaw proc entropyDecrease =
  entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc

------------------------------------------------------------------------
-- Physical axiom — mirrors LandauerLaw.physicalSecondLaw (honesty fence)
------------------------------------------------------------------------

postulate
  physicalSecondLaw : ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
    PhysicalSecondLaw proc entropyDecrease

------------------------------------------------------------------------
-- Derived witnesses (zero new physics postulates)
------------------------------------------------------------------------

landauerBound :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc
landauerBound proc ΔS h = h

physicalSecondLawUniformBinary :
  ∀ (proc : ErasureProcess) (uniformBinaryDrop : ℚ) →
  PhysicalSecondLaw proc uniformBinaryDrop →
  uniformBinaryDrop ≤ ErasureProcess.dissipatedEntropy proc
physicalSecondLawUniformBinary proc ΔS h = h

secondLawModuleWitness : ErasureProcess → ℚ → Set
secondLawModuleWitness proc ΔS = PhysicalSecondLaw proc ΔS
