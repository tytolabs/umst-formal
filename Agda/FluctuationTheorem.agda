-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: FluctuationTheorem.agda
--
-- Twin of Lean/FluctuationTheorem.lean and Coq/FluctuationTheorem.v: the Jarzynski integral fluctuation theorem on
-- a finite state space Fin n, exact over the rationals, and the measureFeedback case of SecondLaw derived from it.
--
-- Rational Boltzmann weights. Stage k + 1 switches the energy at the current state x; its exponentiated work is the
-- ratio of the two weights, carried as `tilt k x` with weight k x * tilt k x ≡ weight (suc k) x (with real weights
-- exp(−β E k x) this is exp(−β (E (k+1) x − E k x)), as Lean and Coq compute it). The kernel of stage k + 1 leaves
-- the weight of that stage invariant. The work-tilted forward vector then equals the weight of each stage, so the
-- identity ⟨e^{−βW}⟩ = Z K / Z 0 holds exactly in ℚ (C. Jarzynski, Phys. Rev. Lett. 78, 2690 (1997); finite Markov
-- form after G. E. Crooks, J. Stat. Phys. 90, 1481 (1998)).
--
-- The standard library has no real exponential, so the Jensen bridge takes the exponential as a parameter, as
-- NaturalLog.agda takes the logarithm: a function on ℚ with the tangent-line bound 1 + t ≤ exp t. The bridge holds
-- for every such function and is the Lean and Coq statement at the real exponential. The record is a parameter of
-- each statement, never a postulate.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FluctuationTheorem where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _≤_; Positive; NonNegative; nonNegative)
open import Data.Rational.Properties
  using (+-mono-≤; ≤-refl; ≤-trans; *-monoˡ-≤-nonNeg; *-cancelˡ-≤-pos; pos⇒nonNeg; nonNeg*nonNeg⇒nonNeg)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst₂)

open import Process using (SecondLaw; measureFeedback; feedback; FeedbackProcess)

open +-*-Solver

------------------------------------------------------------------------
-- Sums over a finite state space

sumFin : ∀ {n} → (Fin n → ℚ) → ℚ
sumFin {zero}  f = 0ℚ
sumFin {suc n} f = f zero + sumFin (λ i → f (suc i))

sumFin-cong : ∀ {n} {f g : Fin n → ℚ} → (∀ i → f i ≡ g i) → sumFin f ≡ sumFin g
sumFin-cong {zero}  h = refl
sumFin-cong {suc n} h = cong₂ _+_ (h zero) (sumFin-cong (λ i → h (suc i)))

sumFin-mono : ∀ {n} {f g : Fin n → ℚ} → (∀ i → f i ≤ g i) → sumFin f ≤ sumFin g
sumFin-mono {zero}  h = ≤-refl
sumFin-mono {suc n} h = +-mono-≤ (h zero) (sumFin-mono (λ i → h (suc i)))

------------------------------------------------------------------------
-- The protocol

record Protocol (n : ℕ) : Set where
  field
    weight         : ℕ → Fin n → ℚ
    tilt           : ℕ → Fin n → ℚ
    kernel         : ℕ → Fin n → Fin n → ℚ
    weight-tilt    : ∀ k x → weight k x * tilt k x ≡ weight (suc k) x
    kernel-balance : ∀ k y → sumFin (λ x → weight (suc k) x * kernel k x y) ≡ weight (suc k) y

module _ {n : ℕ} (P : Protocol n) where
  open Protocol P

  -- One stage: tilting the weight of stage k by the work of the switch and relaxing gives the weight of stage k + 1.
  gibbs-tilt-stage : ∀ k y → sumFin (λ x → weight k x * tilt k x * kernel k x y) ≡ weight (suc k) y
  gibbs-tilt-stage k y =
    trans (sumFin-cong (λ x → cong (_* kernel k x y) (weight-tilt k x))) (kernel-balance k y)

  -- Unnormalised work-tilted forward vector.
  tiltedForward : ℕ → Fin n → ℚ
  tiltedForward zero    y = weight zero y
  tiltedForward (suc k) y = sumFin (λ x → tiltedForward k x * tilt k x * kernel k x y)

  -- Transfer form of the Jarzynski identity: after k stages the tilted forward vector is the weight of stage k.
  tiltedForward-eq : ∀ k y → tiltedForward k y ≡ weight k y
  tiltedForward-eq zero    y = refl
  tiltedForward-eq (suc k) y =
    trans (sumFin-cong (λ x → cong (λ u → u * tilt k x * kernel k x y) (tiltedForward-eq k x)))
          (gibbs-tilt-stage k y)

  partition : ℕ → ℚ
  partition k = sumFin (weight k)

  -- Jarzynski equality, unnormalised: Σ_y u K y = Z K.
  jarzynski-transfer : ∀ K → sumFin (tiltedForward K) ≡ partition K
  jarzynski-transfer K = sumFin-cong (tiltedForward-eq K)

------------------------------------------------------------------------
-- Jensen bridge

-- An exponential on the rationals, by its tangent-line bound at zero.
record Exponential : Set where
  field
    exp      : ℚ → ℚ
    exp-ineq : ∀ t → 1ℚ + t ≤ exp t

open Exponential

private
  affine : ∀ {m} (P W : Fin m → ℚ) (b dF : ℚ) →
    sumFin (λ i → P i * (1ℚ + - (b * (W i - dF)))) ≡
      (sumFin P - b * sumFin (λ i → P i * W i)) + b * dF * sumFin P
  affine {zero}  P W b dF = solve 2 (λ b dF → con 0ℚ := (con 0ℚ :- b :* con 0ℚ) :+ b :* dF :* con 0ℚ) refl b dF
  affine {suc m} P W b dF =
    trans (cong (P zero * (1ℚ + - (b * (W zero - dF))) +_) (affine (λ i → P (suc i)) (λ i → W (suc i)) b dF))
          (solve 6 (λ p w s₁ s₂ b dF →
                      p :* (con 1ℚ :+ :- (b :* (w :- dF))) :+ ((s₁ :- b :* s₂) :+ b :* dF :* s₁)
                      := ((p :+ s₁) :- b :* (p :* w :+ s₂)) :+ b :* dF :* (p :+ s₁))
                   refl (P zero) (W zero) (sumFin (λ i → P (suc i))) (sumFin (λ i → P (suc i) * W (suc i))) b dF)

-- On a finite ensemble with weights P ≥ 0 summing to one, the integral fluctuation theorem ⟨e^{−β(W − ΔF)}⟩ = 1 at
-- β > 0 forces ⟨W⟩ ≥ ΔF.
jensen-bridge : ∀ (X : Exponential) {m} (P W : Fin m → ℚ) (b dF : ℚ) .{{_ : Positive b}} →
  (∀ i → 0ℚ ≤ P i) → sumFin P ≡ 1ℚ →
  sumFin (λ i → P i * exp X (- (b * (W i - dF)))) ≡ 1ℚ →
  dF ≤ sumFin (λ i → P i * W i)
jensen-bridge X P W b dF hP hsum hift = *-cancelˡ-≤-pos b step₃
  where
  w = sumFin (λ i → P i * W i)
  step₁ : sumFin (λ i → P i * (1ℚ + - (b * (W i - dF)))) ≤ sumFin (λ i → P i * exp X (- (b * (W i - dF))))
  step₁ = sumFin-mono (λ i → *-monoˡ-≤-nonNeg (P i) {{nonNegative (hP i)}} (exp-ineq X (- (b * (W i - dF)))))
  step₂ : (1ℚ - b * w) + b * dF ≤ 1ℚ
  step₂ = subst₂ _≤_ (trans (affine P W b dF) (trans (cong (λ s → (s - b * w) + b * dF * s) hsum)
                       (solve 3 (λ w b dF → (con 1ℚ :- b :* w) :+ b :* dF :* con 1ℚ := (con 1ℚ :- b :* w) :+ b :* dF)
                              refl w b dF)))
                     hift step₁
  step₃ : b * dF ≤ b * w
  step₃ = subst₂ _≤_ (solve 3 (λ w b dF → ((con 1ℚ :- b :* w) :+ b :* dF) :+ (b :* w :- con 1ℚ) := b :* dF) refl w b dF)
                     (solve 2 (λ w b → con 1ℚ :+ (b :* w :- con 1ℚ) := b :* w) refl w b)
                     (+-mono-≤ step₂ (≤-refl {b * w - 1ℚ}))

-- The measureFeedback case of SecondLaw from the fluctuation theorem: the ensemble of a protocol, read as a feedback
-- process extracting −⟨W⟩, obeys the second law against any measurement whose mutual information is non-negative.
jarzynski-secondLaw-feedback : ∀ (X : Exponential) {m} (P W : Fin m → ℚ) (b dF kBT I : ℚ) .{{_ : Positive b}} →
  (∀ i → 0ℚ ≤ P i) → sumFin P ≡ 1ℚ →
  sumFin (λ i → P i * exp X (- (b * (W i - dF)))) ≡ 1ℚ →
  0ℚ ≤ kBT → 0ℚ ≤ I →
  SecondLaw (measureFeedback (record { extWork = - sumFin (λ i → P i * W i) ; deltaFreeEnergy = dF ; kBT = kBT }))
            (feedback I)
jarzynski-secondLaw-feedback X P W b dF kBT I hP hsum hift hk hI =
  subst₂ _≤_ (solve 2 (λ w dF → (dF :+ con 0ℚ) :+ ((:- w) :- dF) := :- w) refl w dF)
             (solve 3 (λ w dF c → (w :+ c) :+ ((:- w) :- dF) := (:- dF) :+ c) refl w dF (kBT * I))
             (+-mono-≤ (+-mono-≤ hj hc) (≤-refl {(- w) - dF}))
  where
  w = sumFin (λ i → P i * W i)
  hj : dF ≤ w
  hj = jensen-bridge X P W b dF hP hsum hift
  hc : 0ℚ ≤ kBT * I
  hc = subst₂ _≤_ (solve 1 (λ k → k :* con 0ℚ := con 0ℚ) refl kBT) refl
         (*-monoˡ-≤-nonNeg kBT {{nonNegative hk}} hI)
