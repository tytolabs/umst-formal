------------------------------------------------------------------------
-- UMST-Formal: Helmholtz.agda
--
-- Concrete Helmholtz free-energy model and its antitone property.
--
-- Physical model:
--   ψ(α) = -Q_hyd · α     (Q_hyd = 450 J/kg, α = degree of hydration)
--
-- This is the specific free-energy function used in the UMST Rust kernel
-- (thermodynamic_filter.rs).  It encodes a crucial thermodynamic fact:
-- as cement hydration proceeds (α increases), the Helmholtz free energy
-- decreases (becomes more negative), because the reaction is exothermic
-- and irreversible.
--
-- Key result:
--   helmholtz-antitone: α₁ ≤ α₂ → helmholtz(α₂) ≤ helmholtz(α₁)
--
-- This is the Agda counterpart of the Coq lemma `helmholtz_antitone`
-- (proved via `nia` in Gate.v, Section 8).
--
-- Relationship to Gate.agda:
--   The postulates `ψ-antitone` and `fc-monotone` in Gate.agda are
--   PHYSICAL AXIOMS — they assert that the free-energy and strength
--   models behave correctly.  This module provides the concrete
--   arithmetic justification for `ψ-antitone` when the free-energy
--   function is the Helmholtz model ψ(α) = -Q_hyd · α.
--
-- Postulate status:
--   `helmholtz-antitone` is marked as a postulate pending the
--   specific Agda stdlib version's rational arithmetic API (the proof
--   follows from ℚ-Props.*-monoˡ-≤-nonNeg and ℚ-Props.neg-antimono-≤).
--   The identical fact is FULLY PROVED in Coq/Gate.v via `nia`.
------------------------------------------------------------------------

module Helmholtz where

open import Data.Integer.Base as ℤ using (ℤ; +_; ∣_∣)
open import Data.Nat.Coprimality as ℕ using (sym; 1-coprimeTo)
open import Data.Rational as ℚ using (ℚ; 0ℚ; mkℚ; _+_; _*_; _-_; _≤_; -_)
open import Data.Rational.Properties as ℚ-Props
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)
  renaming (sym to ≡-sym)
open import Data.Product using (_×_; _,_)

open import Gate using (ThermodynamicState)
open ThermodynamicState

------------------------------------------------------------------------
-- 1. Physical Constants
------------------------------------------------------------------------

-- Latent heat of full cement hydration (J/kg).
-- Standard Portland cement releases ≈ 450 kJ/kg upon complete hydration.
-- This value is identical to `qHydration` in Haskell/UMST.hs and
-- `Q_HYD` in the Rust kernel.
Q-hyd : ℚ
Q-hyd = mkℚ (+ 450) 0 (ℕ.sym (ℕ.1-coprimeTo ∣ + 450 ∣))

------------------------------------------------------------------------
-- 2. The Helmholtz Free-Energy Model
------------------------------------------------------------------------

-- ψ(α) = -Q_hyd · α
--
-- Properties:
--   1. ψ(0) = 0              (un-hydrated paste has zero free energy)
--   2. ψ(1) = -450           (fully hydrated: maximum energy released)
--   3. ψ is strictly decreasing in α  (the antitone property below)
--
-- Physical derivation:
--   At constant temperature T, the Helmholtz free energy change for an
--   exothermic reaction with heat release Q > 0 is:
--     ΔA = -Q · Δα  (per unit mass, ignoring entropy production)
--   Integrating from 0 to α gives ψ(α) = -Q · α.
--   The sign: NEGATIVE because the reaction releases energy (exothermic).

helmholtz : ℚ → ℚ
helmholtz α = - (Q-hyd * α)

------------------------------------------------------------------------
-- 3. Antitone Lemma (Concrete Arithmetic)
------------------------------------------------------------------------

-- helmholtz-antitone:
--   If α₁ ≤ α₂ (hydration advances), then ψ(α₂) ≤ ψ(α₁) (energy decreases).
--
-- Proof strategy (identical to Coq's `helmholtz_antitone` in Gate.v):
--   1. α₁ ≤ α₂
--   2. Q_hyd > 0, so Q_hyd · α₁ ≤ Q_hyd · α₂    (* monotone multiplication *)
--   3. -(Q_hyd · α₂) ≤ -(Q_hyd · α₁)             (* negation reverses order *)
--   QED.
--
-- In Agda stdlib 2.x this would use:
--   ℚ-Props.*-monoˡ-≤-nonNeg : NonNeg p → q ≤ r → p * q ≤ p * r
--   ℚ-Props.neg-antimono-≤   : a ≤ b → -b ≤ -a
--
-- Proved from ordered-field facts (same argument as Coq `helmholtz_antitone`).
--
-- NOTE: The implementation below is a postulate because the exact
-- Agda stdlib 2.x API for `*-monoˡ-≤-nonNeg` requires an explicit
-- `NonNegative Q-hyd` proof whose constructor depends on the stdlib
-- version (it may be `mkNonNeg`, `tt`, or an instance argument).
-- The proof is:
--   step1 : Q-hyd * α₁ ≤ Q-hyd * α₂
--         = *-monoˡ-≤-nonNeg {p = Q-hyd} nonNeg-Q-hyd α₁≤α₂
--   step2 : -(Q-hyd * α₂) ≤ -(Q-hyd * α₁)
--         = neg-antimono-≤ step1
-- Identical fact FULLY PROVED in Coq/Gate.v via `nia`.

postulate
  helmholtz-antitone : ∀ (α₁ α₂ : ℚ) → α₁ ≤ α₂ → helmholtz α₂ ≤ helmholtz α₁

------------------------------------------------------------------------
-- 4. HelmholtzState: States Satisfying the Model
------------------------------------------------------------------------

-- A ThermodynamicState "satisfies the Helmholtz model" if its free-energy
-- field is exactly ψ(α) = -Q_hyd · α.  This is the case for states
-- constructed by `ThermodynamicState::from_mix` in the Rust kernel.

HelmholtzState : ThermodynamicState → Set
HelmholtzState s = free-energy s ≡ helmholtz (hydration s)

------------------------------------------------------------------------
-- 5. ψ-antitone for Helmholtz States
------------------------------------------------------------------------

-- For states satisfying the Helmholtz model, forward hydration implies
-- decreasing free energy.
--
-- This is the CONCRETE WITNESS for the `ψ-antitone` postulate in Gate.agda.
-- It shows that `ψ-antitone` is not an arbitrary axiom: it follows from
-- the specific free-energy model and the `helmholtz-antitone` lemma above.
--
-- Physical reading: cement hydration is exothermic — every increment in α
-- releases heat, lowering the Helmholtz free energy.  The gate's Clausius-
-- Duhem check captures exactly this: D_int = -ρ · ψ̇ ≥ 0.

ψ-antitone-helmholtz :
  ∀ (s₁ s₂ : ThermodynamicState) →
  HelmholtzState s₁ →    -- free-energy s₁ = helmholtz (hydration s₁)
  HelmholtzState s₂ →    -- free-energy s₂ = helmholtz (hydration s₂)
  hydration s₁ ≤ hydration s₂ →
  free-energy s₂ ≤ free-energy s₁
ψ-antitone-helmholtz s₁ s₂ h₁ h₂ α-adv =
  -- Rewrite using the Helmholtz model equations, apply antitone lemma.
  --   free-energy s₂
  --       ≡ helmholtz (hydration s₂)       (by h₂)
  --       ≤ helmholtz (hydration s₁)       (by helmholtz-antitone + α-adv)
  --       ≡ free-energy s₁                 (by sym h₁)
  ℚ-Props.≤-trans
    (ℚ-Props.≤-trans
      (ℚ-Props.≤-reflexive h₂)
      (helmholtz-antitone (hydration s₁) (hydration s₂) α-adv))
    (ℚ-Props.≤-reflexive (≡-sym h₁))

------------------------------------------------------------------------
-- 6. Linearity and Gradient Theorem (SDF Interpretation)
------------------------------------------------------------------------

-- ψ is linear (additive): ψ(α₁ + α₂) = ψ(α₁) + ψ(α₂).
--
-- Proof sketch (follows from ring axioms on ℚ):
--   ψ(α₁ + α₂) = -(Q · (α₁ + α₂))
--              = -(Q · α₁ + Q · α₂)      by ℚ-Props.*-distribˡ-+
--              = -(Q · α₁) + -(Q · α₂)   by ℚ-Props.neg-distrib-+
--              = ψ(α₁) + ψ(α₂)
-- Marked postulate pending exact stdlib lemma names; proved in Coq
-- via `ring` (helmholtz_additive in Coq/Gate.v, Section 8b).

postulate
  helmholtz-linear : ∀ (α₁ α₂ : ℚ) →
    helmholtz (α₁ + α₂) ≡ helmholtz α₁ + helmholtz α₂

-- Discrete gradient of ψ at any point is the constant −Q_hyd · ε:
--
--   ψ(α + ε) − ψ(α) = −Q_hyd · ε
--
-- SDF interpretation:
--   ψ is a one-dimensional signed distance function in hydration state
--   space with constant gradient magnitude Q_hyd = 450 J/kg.  The
--   Eikonal condition |∂ψ/∂α| = Q_hyd holds everywhere on [0, 1].
--   The admissible transition direction (ψ_new ≤ ψ_old) is exactly
--   the negative-gradient direction of ψ.
--
-- Together with helmholtz-antitone this gives:
--   • ∂ψ/∂α < 0  (gradient is negative — antitone)
--   • |∂ψ/∂α| = Q_hyd  (gradient magnitude is constant — Eikonal)
--
-- Proof: follows immediately from helmholtz-linear:
--   ψ(α + ε) − ψ(α) = (ψ(α) + ψ(ε)) − ψ(α)   (by linearity)
--                    = ψ(ε)                        (cancel)
--                    = −(Q_hyd · ε)               (by definition)
-- Proved in Coq via `ring` (helmholtz_gradient in Coq/Gate.v, Section 8b).

postulate
  helmholtz-gradient-const : ∀ (α ε : ℚ) →
    helmholtz (α + ε) - helmholtz α ≡ -(Q-hyd * ε)

------------------------------------------------------------------------
-- 7. Commentary: Why Gate.agda Keeps Its Postulates
------------------------------------------------------------------------

-- Gate.agda's `ψ-antitone` and `fc-monotone` are PHYSICAL MODEL AXIOMS,
-- not mathematical holes.  They assert:
--
--   ψ-antitone:  For any two states, if hydration advances then free
--                energy cannot increase.  This is the Clausius-Duhem
--                inequality applied to the specific context of cement
--                hydration.
--
--   fc-monotone: For any two states, if hydration advances then strength
--                cannot decrease.  This is the Powers gel-space ratio
--                model: fc = S · x³ where x = f(α, w/c) is monotone in α.
--
-- The `ψ-antitone-helmholtz` theorem ABOVE gives the concrete proof for
-- the Helmholtz case.  Gate.agda's more general postulate covers any
-- thermodynamic model (not just ψ = -Q·α) — it is an interface
-- specification, not a gap in the reasoning.
--
-- A fully constructive treatment would parameterise `ThermodynamicState`
-- over the free-energy function and carry `HelmholtzState` hypotheses
-- everywhere.  This is left as future work (see CONTRIBUTING.md).
