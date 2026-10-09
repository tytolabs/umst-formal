-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawRestitution — the coefficient of restitution bounded by the second law (twin of
-- ConvexPhiChannels.restitution_le_one and restitution_energy_loss_nonneg in Lean and of
-- Coq/Constants/SecondLawRestitution.v).
--
-- A passive impact has free energy ½·m before and ½·m·e² after, with m = μ·v² > 0 the impact's kinetic measure
-- (Agda carries it as a positive rational); as a transition case of SecondLaw it forces e ≤ 1 for e ≥ 0, and the
-- kinetic energy lost is nonnegative. The result is a bound, never a value.
------------------------------------------------------------------------

module Constants.SecondLawRestitution where

open import Data.Empty using (⊥-elim)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _<_; _+_; _*_; _-_; -_; Positive; positive)
open import Data.Rational.Properties using (*-cancelˡ-≤-pos; *-identityʳ; *-identityˡ; *-monoˡ-<-pos; +-inverseʳ;
  +-monoˡ-≤; <-cmp; <-trans; <-≤-trans; <-irrefl; ≤-reflexive; <⇒≤; positive⁻¹; pos*pos⇒pos)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Concrete.Gate using (mkState)
open import Core.Gate using (CoreAdmissible)
open import Process using (Prior; SecondLaw; transition; thermodynamic)

open +-*-Solver

-- A passive impact with kinetic measure m = μ·v² and restitution e.
impact : ℚ → ℚ → ℚ → ℚ → Prior
impact ρ ρ' m e = thermodynamic (mkState ρ (½ * m) 0ℚ 0ℚ) (mkState ρ' (½ * m * (e * e)) 0ℚ 0ℚ)

-- Passive restitution: the impact obeys the second law only with e ≤ 1 (for e ≥ 0 and m > 0).
restitution-le-one : ∀ ρ ρ' m e .{{_ : Positive m}} → 0ℚ ≤ e → SecondLaw transition (impact ρ ρ' m e) → e ≤ 1ℚ
restitution-le-one ρ ρ' m e e≥0 h with <-cmp e 1ℚ
... | tri< e<1 _ _ = <⇒≤ e<1
... | tri≈ _ e≡1 _ = ≤-reflexive e≡1
... | tri> _ _ e>1 = ⊥-elim (<-irrefl refl (<-≤-trans (<-trans e>1 (e<ee)) ee≤1))
  where
    instance
      pe : Positive e
      pe = positive (<-trans (positive⁻¹ 1ℚ) e>1)
      phm : Positive (½ * m)
      phm = pos*pos⇒pos ½ m
    -- e > 1 > 0 gives e = 1·e < e·e.
    e<ee : e < e * e
    e<ee = subst (_< e * e) (*-identityˡ e) (*-monoˡ-<-pos e e>1)
    -- ½·m·(e·e) ≤ ½·m = ½·m·1 gives e·e ≤ 1.
    ee≤1 : e * e ≤ 1ℚ
    ee≤1 = *-cancelˡ-≤-pos (½ * m) (subst (½ * m * (e * e) ≤_) (sym (*-identityʳ (½ * m)))
             (CoreAdmissible.dissipation-nonneg h))

-- The kinetic energy lost in a passive impact, ½·m·(1 − e²), is nonnegative under the second law.
restitution-energy-loss-nonneg : ∀ ρ ρ' m e → SecondLaw transition (impact ρ ρ' m e) → 0ℚ ≤ ½ * m * (1ℚ - e * e)
restitution-energy-loss-nonneg ρ ρ' m e h =
  subst (_≤ ½ * m * (1ℚ - e * e)) (+-inverseʳ (½ * m * (e * e)))
    (subst (½ * m * (e * e) - ½ * m * (e * e) ≤_) (split ½ m e)
      (+-monoˡ-≤ (- (½ * m * (e * e))) (CoreAdmissible.dissipation-nonneg h)))
  where
    split : ∀ h m e → h * m + - (h * m * (e * e)) ≡ h * m * (1ℚ - e * e)
    split = solve 3 (λ h m e → h :* m :+ :- (h :* m :* (e :* e)) := h :* m :* (con 1ℚ :- e :* e)) refl
