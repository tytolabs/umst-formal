-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-|
  The Landauer–Einstein mass equivalent, algebraically: with the Landauer energy E(T) = k_B · T · ln 2 and the
  mass equivalence E = m · c², energy scales linearly in temperature (E-linear-scaling) and a mass equivalent at T
  scales to one at a · T (mass-equivalent-scaling). The constants are parameters of a commutative semiring (ℕ
  here); the real-valued bounds with the exact SI k_B and c are Lean LandauerEinsteinBridge and Constants.SIBridge.
-}

{-# OPTIONS --without-K --exact-split --safe #-}

module LandauerEinsteinTrace where

open import Data.Nat using (ℕ; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Nat.Properties using (*-assoc; *-comm)

-- | We formulate the Landauer-Einstein bridge over a commutative semiring (ℕ) 
-- | to provide a structurally guaranteed, zero-postulate machine-checked proof
-- | of the energy-mass algebraic equivalence without relying on floating point.

module Bridge (kB c² ln2 : ℕ) where

  -- | Landauer information cost: E = kB * T * ln2
  E-Landauer-bit : ℕ → ℕ
  E-Landauer-bit T = (kB * T) * ln2

  -- | Special relativity equivalence: E = m * c²
  -- | A mass `m` is information-equivalent at temperature `T` if it satisfies this.
  record MassEquivalent (T m : ℕ) : Set where
    constructor mkMassEq
    field
      energy-match : E-Landauer-bit T ≡ m * c²

  -- | Theorem: The Landauer energy scales linearly with Temperature.
  -- | E(a * T) = a * E(T)
  E-linear-scaling : ∀ (T a : ℕ) → E-Landauer-bit (a * T) ≡ a * E-Landauer-bit T
  E-linear-scaling T a =
    let 
      step1 : (kB * (a * T)) * ln2 ≡ ((kB * a) * T) * ln2
      step1 = cong (λ x → x * ln2) (sym (*-assoc kB a T))
      
      step2 : ((kB * a) * T) * ln2 ≡ ((a * kB) * T) * ln2
      step2 = cong (λ x → (x * T) * ln2) (*-comm kB a)
      
      step3 : ((a * kB) * T) * ln2 ≡ (a * (kB * T)) * ln2
      step3 = cong (λ x → x * ln2) (*-assoc a kB T)
      
      step4 : (a * (kB * T)) * ln2 ≡ a * ((kB * T) * ln2)
      step4 = *-assoc a (kB * T) ln2
    in trans step1 (trans step2 (trans step3 step4))

  -- | Theorem: If an information mass scales its temperature by `a`, 
  -- | its equivalent mass scales by `a` perfectly.
  mass-equivalent-scaling : ∀ (T m a : ℕ) → MassEquivalent T m → MassEquivalent (a * T) (a * m)
  mass-equivalent-scaling T m a (mkMassEq eq) = mkMassEq proof
    where
      -- We know: E(T) = m * c²
      -- We want: E(a * T) = (a * m) * c²
      
      p1 : E-Landauer-bit (a * T) ≡ a * E-Landauer-bit T
      p1 = E-linear-scaling T a
      
      p2 : a * E-Landauer-bit T ≡ a * (m * c²)
      p2 = cong (λ x → a * x) eq
      
      p3 : a * (m * c²) ≡ (a * m) * c²
      p3 = sym (*-assoc a m c²)
      
      proof : E-Landauer-bit (a * T) ≡ (a * m) * c²
      proof = trans p1 (trans p2 p3)

