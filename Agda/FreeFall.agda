-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: FreeFall.agda
--
-- Twin of Lean/FreeFall.lean and Coq/FreeFall.v over the rationals: a body dropped from rest, an instance of the
-- passive transition case of SecondLaw. Gravity is the gradient of a scalar potential Φ on the configuration
-- manifold and free fall is the flow along −∇Φ; ψ(z) = m·Φ(z) = m·g·z is linear, hence convex, in z, so the
-- passive route of ConvexPhiDissipation applies. The SDF, MSDF, TESDF and FRep framing is left out: it does not
-- reduce any proof below. The kinetic measure K = m·v² enters as a rational with K ≡ m·v², as in
-- Constants.SecondLawRestitution, which this module reuses for e ≤ 1; the divisions of the Lean statements enter in
-- their division-free form. Typed absence: the k_B·T·ln 2 cost per extracted frame bit is the measureFeedback case;
-- follow-up cell FORMAL-FREEFALL-MEASURE-FEEDBACK.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module FreeFall where

open import Data.Product using (_×_; _,_; proj₁)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _+_; _*_; _-_; -_; Positive; NonNegative; nonNegative)
open import Data.Rational.Properties using (+-monoˡ-≤; +-inverseʳ; ≤-refl; ≤-reflexive; ≤-antisym; *-monoˡ-≤-nonNeg;
  *-cancelˡ-≤-pos; pos*pos⇒pos)
open import Data.Rational.Solver using (module +-*-Solver)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import Concrete.Gate using (mkState)
open import Core.Gate using (CoreAdmissible; CoreMassCond)
open import Process using (Prior; SecondLaw; transition; thermodynamic)
open import OneInequalitySecondLaw using (Step; oneInequality; chain; transitionStepAt; SecondLaw-transition-oneInequality-iff;
  oneInequality-chain)
open import Constants.SecondLawRestitution using (impact; restitution-le-one)
open +-*-Solver

two : ℚ
two = 1ℚ + 1ℚ

instance
  two-nonNeg : NonNegative two
  two-nonNeg = _

-- The work the gravitational potential supplies to mass m dropped through h in the field g.
fallWork : ℚ → ℚ → ℚ → ℚ
fallWork m g h = m * g * h

-- The dissipation of a fall: the work supplied less the kinetic energy ½·K at the ground.
fallDissipation : ℚ → ℚ → ℚ → ℚ → ℚ
fallDissipation m g h K = fallWork m g h - ½ * K

-- The fall: free energy m·g·h at rest on top, ½·K at the ground.
fall : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → Prior
fall ρ ρ' m g h K = thermodynamic (mkState ρ (fallWork m g h) 0ℚ 0ℚ) (mkState ρ' (½ * K) 0ℚ 0ℚ)

private
  sub≤0⇒≤ : ∀ x y → x - y ≤ 0ℚ → x ≤ y
  sub≤0⇒≤ x y h = subst₂ _≤_ (solve 2 (λ x y → (x :- y) :+ y := x) refl x y) (solve 1 (λ y → con 0ℚ :+ y := y) refl y)
                    (+-monoˡ-≤ y h)

-- Free fall as a passive transition: D ≥ 0, ½·K = W_in − D ≤ W_in, and v² ≤ 2·g·h (K = m·v², m > 0).
freeFall-gravity-lower-bound : ∀ ρ ρ' m g h v K .{{_ : Positive m}} → K ≡ m * (v * v) → SecondLaw transition (fall ρ ρ' m g h K) →
  0ℚ ≤ fallDissipation m g h K × ½ * K ≡ fallWork m g h - fallDissipation m g h K × ½ * K ≤ fallWork m g h × v * v ≤ two * g * h
freeFall-gravity-lower-bound ρ ρ' m g h v K hK s =
  nonneg , solve 4 (λ m g h K → (con ½) :* K := (m :* g :* h) :- ((m :* g :* h) :- (con ½) :* K)) refl m g h K , hd , vv
  where
  hd : ½ * K ≤ fallWork m g h
  hd = CoreAdmissible.dissipation-nonneg s
  nonneg : 0ℚ ≤ fallDissipation m g h K
  nonneg = subst (_≤ fallDissipation m g h K) (+-inverseʳ (½ * K)) (+-monoˡ-≤ (- (½ * K)) hd)
  -- 2·(½·K) ≤ 2·(m·g·h), with K = m·v²; cancel m.
  eqL : two * (½ * K) ≡ K
  eqL = solve 1 (λ K → con two :* (con ½ :* K) := K) refl K
  eqR : two * (m * g * h) ≡ m * (two * g * h)
  eqR = solve 3 (λ m g h → con two :* (m :* g :* h) := m :* (con two :* g :* h)) refl m g h
  scaled : m * (v * v) ≤ m * (two * g * h)
  scaled = subst₂ _≤_ (trans eqL hK) eqR (*-monoˡ-≤-nonNeg two hd)
  vv : v * v ≤ two * g * h
  vv = *-cancelˡ-≤-pos m scaled

-- Fall, impact and rebound steps of the chain, at one k_B·T.
fallStep : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → Step
fallStep kT ρ ρ' m g h K = transitionStepAt kT (mkState ρ (fallWork m g h) 0ℚ 0ℚ) (mkState ρ' (½ * K) 0ℚ 0ℚ)

impactStep : ℚ → ℚ → ℚ → ℚ → ℚ → Step
impactStep kT ρ ρ' K e = transitionStepAt kT (mkState ρ (½ * K) 0ℚ 0ℚ) (mkState ρ' (½ * K * (e * e)) 0ℚ 0ℚ)

reboundStep : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → Step
reboundStep kT ρ ρ' K e m g h = transitionStepAt kT (mkState ρ (½ * K * (e * e)) 0ℚ 0ℚ) (mkState ρ' (fallWork m g h) 0ℚ 0ℚ)

-- Fall, impact, rebound as one mixed chain of the one inequality (I = 0).
freeFallRebound-chain-oneInequality : ∀ kT ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr K e →
  SecondLaw transition (fall ρ₀ ρ₁ m g hd K) → SecondLaw transition (impact ρ₁ ρ₂ K e) →
  SecondLaw transition (thermodynamic (mkState ρ₂ (½ * K * (e * e)) 0ℚ 0ℚ) (mkState ρ₃ (fallWork m g hr) 0ℚ 0ℚ)) →
  oneInequality (chain (chain (fallStep kT ρ₀ ρ₁ m g hd K) (impactStep kT ρ₁ ρ₂ K e)) (reboundStep kT ρ₂ ρ₃ K e m g hr))
freeFallRebound-chain-oneInequality kT ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr K e hF hI hR =
  oneInequality-chain (chain (fallStep kT ρ₀ ρ₁ m g hd K) (impactStep kT ρ₁ ρ₂ K e)) (reboundStep kT ρ₂ ρ₃ K e m g hr) refl
    (oneInequality-chain (fallStep kT ρ₀ ρ₁ m g hd K) (impactStep kT ρ₁ ρ₂ K e) refl
      (proj₁ (Equivalence.to (SecondLaw-transition-oneInequality-iff kT _ _) hF))
      (proj₁ (Equivalence.to (SecondLaw-transition-oneInequality-iff kT _ _) hI)))
    (proj₁ (Equivalence.to (SecondLaw-transition-oneInequality-iff kT _ _) hR))

-- The rebound never rises above the drop: the chain's free-energy change m·g·(h_r − h_d) is at most zero.
freeFallRebound-height-le : ∀ kT ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr K e .{{_ : Positive m}} .{{_ : Positive g}} →
  SecondLaw transition (fall ρ₀ ρ₁ m g hd K) → SecondLaw transition (impact ρ₁ ρ₂ K e) →
  SecondLaw transition (thermodynamic (mkState ρ₂ (½ * K * (e * e)) 0ℚ 0ℚ) (mkState ρ₃ (fallWork m g hr) 0ℚ 0ℚ)) →
  hr ≤ hd
freeFallRebound-height-le kT ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr K e hF hI hR =
  *-cancelˡ-≤-pos (m * g) (sub≤0⇒≤ (m * g * hr) (m * g * hd) tot)
  where
  instance
    mg : Positive (m * g)
    mg = pos*pos⇒pos m g
  h = freeFallRebound-chain-oneInequality kT ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr K e hF hI hR
  tot : m * g * hr - m * g * hd ≤ 0ℚ
  tot = subst₂ _≤_
    (solve 4 (λ f₀ f₁ f₂ f₃ → ((f₁ :- f₀) :+ (f₂ :- f₁)) :+ (f₃ :- f₂) := f₃ :- f₀) refl (m * g * hd) (½ * K) (½ * K * (e * e)) (m * g * hr))
    (solve 1 (λ k → ((con 0ℚ :+ con 0ℚ) :+ con 0ℚ) :+ k :* ((con 0ℚ :+ con 0ℚ) :+ con 0ℚ) := con 0ℚ) refl kT) h

-- Restitution from the heights (g cancels): with no dissipation in flight, e²·h_d = h_r, and e ≤ 1 by the passive
-- restitution of Constants.SecondLawRestitution.
freeFallRebound-restitution : ∀ ρ₁ ρ₂ m g hd hr K e .{{_ : Positive m}} .{{_ : Positive g}} .{{_ : Positive K}} →
  0ℚ ≤ e → ½ * K ≡ fallWork m g hd → ½ * K * (e * e) ≡ fallWork m g hr → SecondLaw transition (impact ρ₁ ρ₂ K e) →
  e * e * hd ≡ hr × e ≤ 1ℚ
freeFallRebound-restitution ρ₁ ρ₂ m g hd hr K e e≥0 hFall hRise hI =
  ≤-antisym (*-cancelˡ-≤-pos (m * g) (≤-reflexive eq)) (*-cancelˡ-≤-pos (m * g) (≤-reflexive (sym eq)))
  , restitution-le-one ρ₁ ρ₂ K e e≥0 hI
  where
  instance
    mg : Positive (m * g)
    mg = pos*pos⇒pos m g
  eq : m * g * (e * e * hd) ≡ m * g * hr
  eq = trans (solve 4 (λ m g e hd → m :* g :* (e :* e :* hd) := (e :* e) :* (m :* g :* hd)) refl m g e hd)
         (trans (cong ((e * e) *_) (sym hFall))
           (trans (solve 2 (λ K e → (e :* e) :* (con ½ :* K) := con ½ :* K :* (e :* e)) refl K e) hRise))
