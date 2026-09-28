-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.SecondLaw — meso/acting chemistry second-law anchor.
--
-- CHEM-L0-FORMAL-01 / CHEM-NS-W0-AXIOM (umst-formal acting fiber only).
-- Physical hypothesis mirrors Lean @Lean/LandauerLaw.lean@ `physicalSecondLaw`,
-- but is threaded as a `SecondLawPhysics` record field (zero postulates).
--
-- Importers: `open Chem.SecondLaw.Anchored Φ` after supplying `Φ : SecondLawPhysics`.
--
-- physics_green: false — this module does not duplicate Mathlib analysis.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split --safe #-}

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
-- Physical hypothesis — record field (P0-13b / W-04; no postulate block)
------------------------------------------------------------------------

record SecondLawPhysics : Set where
  field
    physicalSecondLaw :
      ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
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

------------------------------------------------------------------------
-- Parameterized anchor for importers (thread `Φ : SecondLawPhysics`)
------------------------------------------------------------------------

module Anchored (Φ : SecondLawPhysics) where

  open SecondLawPhysics Φ public using (physicalSecondLaw)
