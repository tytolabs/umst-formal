-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: AdaptiveSeamLensLaws.agda
--
-- Twin of Lean/AdaptiveSeamLensLaws.lean and Coq/AdaptiveSeamLensLaws.v. L-A: the transfer lens get = R,
-- put s v = (s − P (R s)) + P v satisfies GetPut, and PutGet when R P = id, with s − P (R s) in ker R. L-D: two
-- subsystems each satisfying ΔF ≤ W + c I (c = k_B T), joined by a power-preserving seam (W₁ + W₂ = 0), satisfy
-- ΔF₁ + ΔF₂ ≤ c (I₁ + I₂); without information the composite free energy does not rise. L-I: for L antisymmetric,
-- M symmetric positive semidefinite, L ∇S = 0 and M ∇E = 0 under a symmetric pairing, ∇E · ż = 0 and ∇S · ż ≥ 0.
-- The group and pairing laws are module parameters, not postulates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module AdaptiveSeamLensLaws where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; ½; _+_; _*_; _-_; -_; _≤_; _<_)
open import Data.Rational.Properties
  using (≤-reflexive; ≤-trans; +-mono-≤; *-zeroʳ; <-irrefl; <-≤-trans; +-identityˡ)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open +-*-Solver

------------------------------------------------------------------------
-- L-A: the transfer lens

module Lens {S V : Set} (_⊕_ _⊖_ : S → S → S) (_⊞_ _⊟_ : V → V → V) (vzero : V) (R : S → V) (P : V → S)
  (sub-add-cancel : ∀ x y → (x ⊖ y) ⊕ y ≡ x)
  (R-add : ∀ a b → R (a ⊕ b) ≡ R a ⊞ R b)
  (R-sub : ∀ a b → R (a ⊖ b) ≡ R a ⊟ R b)
  (vsub-self : ∀ u → u ⊟ u ≡ vzero)
  (vzero-add : ∀ v → vzero ⊞ v ≡ v) where

  lensGet : S → V
  lensGet = R

  lensPut : S → V → S
  lensPut s v = (s ⊖ P (R s)) ⊕ P v

  -- L-A GetPut.
  lens-getPut : ∀ s → lensPut s (lensGet s) ≡ s
  lens-getPut s = sub-add-cancel s (P (R s))

  -- L-A PutGet, when R P = id.
  lens-putGet : (∀ v → R (P v) ≡ v) → ∀ s v → lensGet (lensPut s v) ≡ v
  lens-putGet RP s v =
    trans (R-add (s ⊖ P (R s)) (P v))
      (trans (cong (_⊞ R (P v)) (trans (R-sub s (P (R s))) (trans (cong (R s ⊟_) (RP (R s))) (vsub-self (R s)))))
        (trans (cong (vzero ⊞_) (RP v)) (vzero-add v)))

  -- With R P = id, s − P (R s) lies in ker R.
  proj-mem-ker : (∀ v → R (P v) ≡ v) → ∀ s → R (s ⊖ P (R s)) ≡ vzero
  proj-mem-ker RP s = trans (R-sub s (P (R s))) (trans (cong (R s ⊟_) (RP (R s))) (vsub-self (R s)))

------------------------------------------------------------------------
-- L-D: a power-preserving seam creates no energy

record Step : Set where
  constructor step
  field
    dF    : ℚ
    wIn   : ℚ
    infoI : ℚ
open Step

OneIneq : ℚ → Step → Set
OneIneq c s = dF s ≤ wIn s + c * infoI s

seam-oneInequality : ∀ c s₁ s₂ → OneIneq c s₁ → OneIneq c s₂ → wIn s₁ + wIn s₂ ≡ 0ℚ →
  dF s₁ + dF s₂ ≤ c * (infoI s₁ + infoI s₂)
seam-oneInequality c s₁ s₂ h₁ h₂ hw =
  ≤-trans (+-mono-≤ h₁ h₂)
    (≤-reflexive (trans (solve 5 (λ a b c i j → (a :+ c :* i) :+ (b :+ c :* j) := (a :+ b) :+ c :* (i :+ j)) refl
                          (wIn s₁) (wIn s₂) c (infoI s₁) (infoI s₂))
                   (trans (cong (_+ c * (infoI s₁ + infoI s₂)) hw) (+-identityˡ _))))

seam-creates-no-energy : ∀ c s₁ s₂ → OneIneq c s₁ → OneIneq c s₂ → wIn s₁ + wIn s₂ ≡ 0ℚ →
  infoI s₁ + infoI s₂ ≡ 0ℚ → dF s₁ + dF s₂ ≤ 0ℚ
seam-creates-no-energy c s₁ s₂ h₁ h₂ hw hi =
  ≤-trans (seam-oneInequality c s₁ s₂ h₁ h₂ hw) (≤-reflexive (trans (cong (c *_) hi) (*-zeroʳ c)))

seam-refused : ∀ c s₁ s₂ → wIn s₁ + wIn s₂ ≡ 0ℚ → infoI s₁ + infoI s₂ ≡ 0ℚ → 0ℚ < dF s₁ + dF s₂ →
  ¬ (OneIneq c s₁ × OneIneq c s₂)
seam-refused c s₁ s₂ hw hi hr (h₁ , h₂) = <-irrefl refl (<-≤-trans hr (seam-creates-no-energy c s₁ s₂ h₁ h₂ hw hi))

------------------------------------------------------------------------
-- L-I: GENERIC degeneracy

module Generic {W : Set} (_⊞_ : W → W → W) (vzero : W) (⟪_,_⟫ : W → W → ℚ) (L M : W → W)
  (pair-add-r : ∀ x y z → ⟪ x , y ⊞ z ⟫ ≡ ⟪ x , y ⟫ + ⟪ x , z ⟫)
  (pair-comm : ∀ x y → ⟪ x , y ⟫ ≡ ⟪ y , x ⟫)
  (pair-zero-l : ∀ y → ⟪ vzero , y ⟫ ≡ 0ℚ)
  (L-antisym : ∀ x y → ⟪ x , L y ⟫ ≡ - ⟪ L x , y ⟫)
  (M-sym : ∀ x y → ⟪ x , M y ⟫ ≡ ⟪ M x , y ⟫)
  (M-psd : ∀ x → 0ℚ ≤ ⟪ x , M x ⟫) where

  -- q = − q forces q = 0 over ℚ.
  private
    self-neg-zero : ∀ q → q ≡ - q → q ≡ 0ℚ
    self-neg-zero q h =
      trans (solve 1 (λ q → q := (q :+ q) :* con ½) refl q)
        (trans (cong (λ r → (q + r) * ½) h) (solve 1 (λ q → (q :+ (:- q)) :* con ½ := con 0ℚ) refl q))

  quad-antisymm-zero : ∀ g → ⟪ g , L g ⟫ ≡ 0ℚ
  quad-antisymm-zero g = self-neg-zero ⟪ g , L g ⟫ (trans (L-antisym g g) (cong -_ (pair-comm (L g) g)))

  -- L-I, energy conserved.
  generic-energy-rate : ∀ gE gS → M gE ≡ vzero → ⟪ gE , L gE ⊞ M gS ⟫ ≡ 0ℚ
  generic-energy-rate gE gS hME =
    trans (pair-add-r gE (L gE) (M gS))
      (trans (cong₂' (quad-antisymm-zero gE) (trans (M-sym gE gS) (trans (cong (λ w → ⟪ w , gS ⟫) hME) (pair-zero-l gS))))
        (+-identityˡ 0ℚ))
    where
      cong₂' : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
      cong₂' refl refl = refl

  -- L-I, entropy produced.
  generic-entropy-rate-nonneg : ∀ gE gS → L gS ≡ vzero → 0ℚ ≤ ⟪ gS , L gE ⊞ M gS ⟫
  generic-entropy-rate-nonneg gE gS hLS =
    ≤-trans (M-psd gS) (≤-reflexive (sym (trans (pair-add-r gS (L gE) (M gS)) (trans (cong (_+ ⟪ gS , M gS ⟫) h0) (+-identityˡ _)))))
    where
      h0 : ⟪ gS , L gE ⟫ ≡ 0ℚ
      h0 = trans (L-antisym gS gE) (trans (cong (λ w → - ⟪ w , gE ⟫) hLS) (cong -_ (pair-zero-l gE)))
