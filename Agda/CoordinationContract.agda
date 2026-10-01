-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-|
  The contract a coordination runtime honours (umst-ucrs implements it in Rust); twin of
  `Lean/CoordinationContract.lean` and `Coq/CoordinationContract.v`.

  The Landauer bit energy enters as a parameter `e` with `0 ≤ e` (Lean instantiates it with
  `landauerBitEnergy T`, positive through the second law); the laws are exact over ℚ.
-}
{-# OPTIONS --without-K --exact-split --safe #-}

open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)

module CoordinationContract (e : ℚ) (0≤e : 0ℚ ≤ e) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; foldl; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕ-Props
open import Data.Product using (_×_; _,_)
import Data.Rational.Properties as ℚ-Props
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)

------------------------------------------------------------------------
-- Landauer cost

cost : ℚ → ℚ
cost bits = e * bits

cost-nonneg : ∀ {bits} → 0ℚ ≤ bits → 0ℚ ≤ cost bits
cost-nonneg {bits} 0≤b =
  subst (_≤ e * bits) (ℚ-Props.*-zeroʳ e) (ℚ-Props.*-monoˡ-≤-nonNeg e {{nonNegative 0≤e}} 0≤b)

cost-add : ∀ a b → cost (a + b) ≡ cost a + cost b
cost-add a b = ℚ-Props.*-distribˡ-+ e a b

private
  ≤-+-nonneg : ∀ p {δ} → 0ℚ ≤ δ → p ≤ p + δ
  ≤-+-nonneg p 0≤δ = subst (_≤ p + _) (ℚ-Props.+-identityʳ p) (ℚ-Props.+-mono-≤ (ℚ-Props.≤-refl {p}) 0≤δ)

------------------------------------------------------------------------
-- Admission

record ClockThermState : Set where
  constructor thermal
  field
    desyncEnergy  : ℚ
    budget        : ℚ
    totalSyncCost : ℚ

open ClockThermState

-- Admitted when the cost fits the budget and does not exceed the desync energy it resolves (Clausius–Duhem).
Admits : ClockThermState → ℚ → Set
Admits s bits = (cost bits ≤ budget s) × (cost bits ≤ desyncEnergy s)

-- The admitted step: desync is resolved to zero and the cost is added to the total.
gatedSync : ClockThermState → ℚ → ClockThermState
gatedSync (thermal d b t) bits = thermal 0ℚ b (t + cost bits)

admitted-cost-bounded : ∀ s {bits} → 0ℚ ≤ bits → Admits s bits →
  (0ℚ ≤ cost bits) × (cost bits ≤ budget s) × (cost bits ≤ desyncEnergy s)
admitted-cost-bounded s 0≤b (fits , resolves) = cost-nonneg 0≤b , fits , resolves

admitted-budget-nonneg : ∀ s {bits} → 0ℚ ≤ bits → Admits s bits → 0ℚ ≤ budget s
admitted-budget-nonneg s 0≤b (fits , _) = ℚ-Props.≤-trans (cost-nonneg 0≤b) fits

------------------------------------------------------------------------
-- Clock drift

record ClockState : Set where
  constructor clock
  field
    tick  : ℕ
    drift : ℚ

open ClockState

clockStep : ClockState → ℚ → ClockState
clockStep (clock t d) δ = clock (suc t) (d + δ)

clockRun : ClockState → List ℚ → ClockState
clockRun = foldl clockStep

clockRun-monotone : ∀ c δs → All (0ℚ ≤_) δs →
  (drift c ≤ drift (clockRun c δs)) × (tick (clockRun c δs) ≡ tick c ℕ.+ length δs)
clockRun-monotone c [] [] = ℚ-Props.≤-refl , sym (ℕ-Props.+-identityʳ (tick c))
clockRun-monotone (clock t d) (δ ∷ δs) (0≤δ ∷ rest) with clockRun-monotone (clock (suc t) (d + δ)) δs rest
... | d≤ , t≡ = ℚ-Props.≤-trans (≤-+-nonneg d 0≤δ) d≤ , trans t≡ (sym (ℕ-Props.+-suc t (length δs)))

------------------------------------------------------------------------
-- Byzantine isolation

record Participant : Set where
  constructor participant
  field
    pid    : ℕ
    credit : ℚ
    faulty : Bool

open Participant

honestCredits : List Participant → List ℚ
honestCredits [] = []
honestCredits (p ∷ ps) with faulty p
... | true  = honestCredits ps
... | false = credit p ∷ honestCredits ps

Faulty : Participant → Set
Faulty p = faulty p ≡ true

honestCredits-faulty-only : ∀ fs → All Faulty fs → honestCredits fs ≡ []
honestCredits-faulty-only [] [] = refl
honestCredits-faulty-only (p ∷ fs) (fp ∷ rest) with faulty p | fp
... | true | refl = honestCredits-faulty-only fs rest

honestCredits-append-faulty : ∀ ps fs → All Faulty fs → honestCredits (ps ++ fs) ≡ honestCredits ps
honestCredits-append-faulty [] fs all = honestCredits-faulty-only fs all
honestCredits-append-faulty (p ∷ ps) fs all with faulty p
... | true  = honestCredits-append-faulty ps fs all
... | false = cong (credit p ∷_) (honestCredits-append-faulty ps fs all)

------------------------------------------------------------------------
-- Wire order

record WireStamp : Set where
  constructor stamp
  field
    seq : ℕ

open WireStamp

wireNext : WireStamp → WireStamp
wireNext (stamp n) = stamp (suc n)

wireIter : ℕ → WireStamp → WireStamp
wireIter ℕ.zero    w = w
wireIter (suc k) w = wireIter k (wireNext w)

wireIter-seq : ∀ n w → seq (wireIter n w) ≡ seq w ℕ.+ n
wireIter-seq ℕ.zero    w = sym (ℕ-Props.+-identityʳ (seq w))
wireIter-seq (suc k) (stamp m) = trans (wireIter-seq k (stamp (suc m))) (sym (ℕ-Props.+-suc m k))
