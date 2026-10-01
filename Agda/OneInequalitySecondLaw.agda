-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: OneInequalitySecondLaw.agda
--
-- Twin of Lean/OneInequalitySecondLaw.lean and Coq/OneInequalitySecondLaw.v: the second law as one free-energy
-- inequality ΔF ≤ W_in + k_B T · I over the rationals. Each process kind fixes which terms vanish; one chaining
-- lemma composes mixed sequences at a common k_B T; every account is equivalent to the one predicate SecondLaw of
-- Process.agda. An Agda erasure carries its dissipated entropy σ = W / T, so its account takes the bath's k_B T.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module OneInequalitySecondLaw where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; Positive; NonNegative)
open import Data.Rational.Properties using (+-mono-≤; ≤-refl; ≤-reflexive; *-monoˡ-≤-nonNeg; *-cancelˡ-≤-pos; pos⇒nonNeg)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)

open import Core.Gate using (CoreAdmissible; CoreMassCond)
open import Concrete.Gate using (ThermodynamicState; concrete-thermodynamic-system)
open import Process
open ThermodynamicState

open +-*-Solver

-- One thermodynamic step: k_B T of its bath, free-energy change, work in and information (nats).
record Step : Set where
  field
    kBT    : ℚ
    deltaF : ℚ
    wIn    : ℚ
    infoI  : ℚ

open Step

-- The second law as one inequality.
oneInequality : Step → Set
oneInequality s = deltaF s ≤ wIn s + kBT s * infoI s

-- Sequential composition at the first step's bath: free energy, work and information add.
chain : Step → Step → Step
chain s₁ s₂ = record { kBT = kBT s₁ ; deltaF = deltaF s₁ + deltaF s₂ ; wIn = wIn s₁ + wIn s₂ ; infoI = infoI s₁ + infoI s₂ }

-- Chaining: admissible steps at a common k_B T compose.
oneInequality-chain : ∀ s₁ s₂ → kBT s₁ ≡ kBT s₂ → oneInequality s₁ → oneInequality s₂ → oneInequality (chain s₁ s₂)
oneInequality-chain s₁ s₂ e h₁ h₂ =
  subst₂ _≤_ refl (sym (solve 5 (λ w₁ w₂ k i₁ i₂ → (w₁ :+ w₂) :+ k :* (i₁ :+ i₂) := (w₁ :+ k :* i₁) :+ (w₂ :+ k :* i₂))
                          refl (wIn s₁) (wIn s₂) (kBT s₁) (infoI s₁) (infoI s₂)))
    (+-mono-≤ h₁ (subst₂ _≤_ refl (sym (cong-k e)) h₂))
  where
  cong-k : kBT s₁ ≡ kBT s₂ → wIn s₂ + kBT s₁ * infoI s₂ ≡ wIn s₂ + kBT s₂ * infoI s₂
  cong-k refl = refl

private
  -- x ≤ y + k · 0 exactly when x ≤ y.
  plus-zero : ∀ y k → y + k * 0ℚ ≡ y
  plus-zero = solve 2 (λ y k → y :+ k :* con 0ℚ := y) refl

-- Erase (natural units scaled by the bath's k_B T): I = 0, ΔF = k_B T (H(prior) − H(post)), W_in = k_B T σ.
eraseStep : ℚ → ErasureProcess → (Hp Hq : ℚ) → Step
eraseStep kT e Hp Hq = record { kBT = kT ; deltaF = kT * (Hp - Hq) ; wIn = kT * ErasureProcess.dissipatedEntropy e ; infoI = 0ℚ }

eraseStep-oneInequality-iff : ∀ kT .{{_ : Positive kT}} e Hp Hq →
  SecondLaw (erase e) (transformation Hp Hq) ⇔ oneInequality (eraseStep kT e Hp Hq)
eraseStep-oneInequality-iff kT e Hp Hq = mk⇔
  (λ h → subst₂ _≤_ refl (sym (plus-zero _ kT)) (*-monoˡ-≤-nonNeg kT {{pos⇒nonNeg kT}} h))
  (λ h → *-cancelˡ-≤-pos kT (subst₂ _≤_ refl (plus-zero _ kT) h))

-- Measurement with feedback: W_in = −W_ext, I the information acquired.
feedbackStep : FeedbackProcess → ℚ → Step
feedbackStep f I = record { kBT = FeedbackProcess.kBT f ; deltaF = FeedbackProcess.deltaFreeEnergy f
                          ; wIn = - FeedbackProcess.extWork f ; infoI = I }

private
  -- W ≤ −ΔF + c exactly when ΔF ≤ −W + c.
  swap-sides : ∀ W ΔF c → W ≤ (- ΔF) + c → ΔF ≤ (- W) + c
  swap-sides W ΔF c h = subst₂ _≤_ (solve 3 (λ W ΔF c → W :+ (ΔF :- W) := ΔF) refl W ΔF c)
                                   (solve 3 (λ W ΔF c → ((:- ΔF) :+ c) :+ (ΔF :- W) := (:- W) :+ c) refl W ΔF c)
                                   (+-mono-≤ h (≤-refl {ΔF - W}))

SecondLaw-measureFeedback-oneInequality-iff : ∀ f I →
  SecondLaw (measureFeedback f) (feedback I) ⇔ oneInequality (feedbackStep f I)
SecondLaw-measureFeedback-oneInequality-iff f I = mk⇔
  (swap-sides (FeedbackProcess.extWork f) (FeedbackProcess.deltaFreeEnergy f) _)
  (swap-sides (FeedbackProcess.deltaFreeEnergy f) (FeedbackProcess.extWork f) _)

-- Passive transition at a bath: W_in = 0 and I = 0, so ΔF ≤ 0.
transitionStepAt : ℚ → ThermodynamicState → ThermodynamicState → Step
transitionStepAt kT old new = record { kBT = kT ; deltaF = free-energy new - free-energy old ; wIn = 0ℚ ; infoI = 0ℚ }

private
  diff≤0⇔ : ∀ x y k → (x - y ≤ 0ℚ + k * 0ℚ) ⇔ (x ≤ y)
  diff≤0⇔ x y k = mk⇔
    (λ h → subst₂ _≤_ (solve 2 (λ x y → (x :- y) :+ y := x) refl x y) (solve 2 (λ y k → (con 0ℚ :+ k :* con 0ℚ) :+ y := y) refl y k)
             (+-mono-≤ h (≤-refl {y})))
    (λ h → subst₂ _≤_ refl (solve 2 (λ y k → y :- y := con 0ℚ :+ k :* con 0ℚ) refl y k) (+-mono-≤ h (≤-refl { - y})))

SecondLaw-transition-oneInequality-iff : ∀ kT old new →
  SecondLaw transition (thermodynamic old new) ⇔
    (oneInequality (transitionStepAt kT old new) × CoreMassCond concrete-thermodynamic-system old new)
SecondLaw-transition-oneInequality-iff kT old new = mk⇔
  (λ c → Equivalence.from (diff≤0⇔ (free-energy new) (free-energy old) kT) (CoreAdmissible.dissipation-nonneg c)
       , CoreAdmissible.mass-conserved c)
  (λ (h , m) → record { mass-conserved = m ; dissipation-nonneg = Equivalence.to (diff≤0⇔ (free-energy new) (free-energy old) kT) h })

-- An admissible transition followed by an admissible erase composes at the erase's bath.
transition-erase-chain-oneInequality : ∀ kT .{{_ : Positive kT}} old new e Hp Hq →
  SecondLaw transition (thermodynamic old new) → SecondLaw (erase e) (transformation Hp Hq) →
  oneInequality (chain (transitionStepAt kT old new) (eraseStep kT e Hp Hq))
transition-erase-chain-oneInequality kT old new e Hp Hq hTr hEr =
  oneInequality-chain (transitionStepAt kT old new) (eraseStep kT e Hp Hq) refl
    (proj₁ (Equivalence.to (SecondLaw-transition-oneInequality-iff kT old new) hTr))
    (Equivalence.to (eraseStep-oneInequality-iff kT e Hp Hq) hEr)
  where open import Data.Product using (proj₁)

-- Any process with a prior of its kind packages as a step (at a bath k_B T for those that do not carry one).
stepOf : ℚ → Process → Prior → Maybe Step
stepOf kT (erase e) (erasure ΔS) = just (eraseStep kT e ΔS 0ℚ)
stepOf kT (measureFeedback f) (feedback I) = just (feedbackStep f I)
stepOf kT transition (thermodynamic old new) = just (transitionStepAt kT old new)
stepOf kT (erase e) (transformation Hp Hq) = just (eraseStep kT e Hp Hq)
stepOf kT _ _ = nothing

-- Every member of the one predicate packages as a step obeying the one inequality.
secondLaw-implies-oneInequality : ∀ kT .{{_ : Positive kT}} p pr → SecondLaw p pr →
  ∃[ s ] (stepOf kT p pr ≡ just s × oneInequality s)
secondLaw-implies-oneInequality kT (erase e) (erasure ΔS) h =
  _ , refl , Equivalence.to (eraseStep-oneInequality-iff kT e ΔS 0ℚ) (erasure-is-transformation e ΔS h)
secondLaw-implies-oneInequality kT (measureFeedback f) (feedback I) h =
  _ , refl , Equivalence.to (SecondLaw-measureFeedback-oneInequality-iff f I) h
secondLaw-implies-oneInequality kT transition (thermodynamic old new) h =
  _ , refl , proj₁ (Equivalence.to (SecondLaw-transition-oneInequality-iff kT old new) h)
  where open import Data.Product using (proj₁)
secondLaw-implies-oneInequality kT (erase e) (transformation Hp Hq) h =
  _ , refl , Equivalence.to (eraseStep-oneInequality-iff kT e Hp Hq) h

-- The Szilard cycle with the information H of one bit carried as data: measuring it (W_ext = k_B T H, ΔF = 0) then
-- erasing it (dissipated entropy H) composes at the bath.
szilardMixedChain-oneInequality : ∀ kT .{{_ : Positive kT}} H →
  oneInequality (chain (feedbackStep (record { extWork = kT * H ; deltaFreeEnergy = 0ℚ ; kBT = kT }) H)
                       (eraseStep kT (record { dissipatedEntropy = H }) H 0ℚ))
szilardMixedChain-oneInequality kT H =
  oneInequality-chain (feedbackStep f H) (eraseStep kT e H 0ℚ) refl
    (Equivalence.to (SecondLaw-measureFeedback-oneInequality-iff f H)
      (≤-reflexive (solve 2 (λ k H → k :* H := (:- con 0ℚ) :+ k :* H) refl kT H)))
    (Equivalence.to (eraseStep-oneInequality-iff kT e H 0ℚ) (≤-reflexive (solve 1 (λ H → H :- con 0ℚ := H) refl H)))
  where
  f : FeedbackProcess
  f = record { extWork = kT * H ; deltaFreeEnergy = 0ℚ ; kBT = kT }
  e : ErasureProcess
  e = record { dissipatedEntropy = H }
