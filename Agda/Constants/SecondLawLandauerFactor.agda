-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawLandauerFactor — the Landauer factor fixed by the second law (twin of
-- Lean/Constants/SecondLawLandauerFactor.lean and Coq/Constants/SecondLawLandauerFactor.v).
--
-- An erasure at a bath of positive temperature T dissipating T·r (work per kelvin r, in nats) obeys the erase case
-- of SecondLaw against a prior whose erasure removes ΔS nats exactly when ΔS ≤ r, so ΔS is the least admitted work
-- per kelvin. The standard library has no real logarithm, so the prior carries its entropy drop (Process.agda); the
-- uniform bit is ΔS = ln 2, which Lean and Coq compute from the distribution, and the least work per kelvin is then
-- ln 2, the Landauer factor.
------------------------------------------------------------------------

module Constants.SecondLawLandauerFactor where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; _≤_; _*_; _÷_; 1/_; NonZero; Positive)
open import Data.Rational.Properties using (*-inverseʳ; *-identityʳ; ≤-refl; pos⇒nonZero)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; sym)

open import Process using (SecondLaw; erase; erasure; atBath)

open +-*-Solver

private
  ÷-cancel : ∀ a .{{_ : NonZero a}} r → _÷_ (a * r) a ≡ r
  ÷-cancel a r = trans (solve 3 (λ a r i → (a :* r) :* i := r :* (a :* i)) refl a r (1/ a))
                       (trans (cong (r *_) (*-inverseʳ a)) (*-identityʳ r))

-- Erasing a prior of entropy drop ΔS with work per kelvin r obeys the second law exactly when ΔS ≤ r.
secondLaw-uniformBit-⇔ : ∀ T .{{_ : Positive T}} r ΔS → SecondLaw (erase (atBath T (T * r))) (erasure ΔS) ⇔ (ΔS ≤ r)
secondLaw-uniformBit-⇔ T r ΔS = mk⇔ (λ h → subst (ΔS ≤_) (÷-cancel T {{pos⇒nonZero T}} r) h)
                                     (λ h → subst (ΔS ≤_) (sym (÷-cancel T {{pos⇒nonZero T}} r)) h)

-- The Landauer factor: the work per kelvin ΔS is admitted, and every admitted work per kelvin is at least ΔS.
landauerFactor-isLeast : ∀ T .{{_ : Positive T}} ΔS →
  SecondLaw (erase (atBath T (T * ΔS))) (erasure ΔS) × (∀ r → SecondLaw (erase (atBath T (T * r))) (erasure ΔS) → ΔS ≤ r)
landauerFactor-isLeast T ΔS =
  Equivalence.from (secondLaw-uniformBit-⇔ T ΔS ΔS) ≤-refl , λ r h → Equivalence.to (secondLaw-uniformBit-⇔ T r ΔS) h
  where open import Function.Bundles using (Equivalence)
