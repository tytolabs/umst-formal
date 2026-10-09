-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawElastic — elastic moduli bounded by the second law (twin of
-- Lean/Constants/SecondLawElastic.lean and Coq/Constants/SecondLawElastic.v).
--
-- A linear-elastic body loaded away from its natural state stores free energy; released, it relaxes passively to
-- the natural state (free energy zero). Each theorem takes that relaxation as the transition case of SecondLaw and
-- concludes a bound on a modulus. Agda carries quantities as rationals, so a squared strain or stress enters as a
-- positive rational q (q = s² for s ≠ 0), the Poisson and Young bounds are stated with their positive denominator
-- cleared, and the orthotropic bound is stated on the compliance entries (S₁₁ = 1/E₁, S₂₂ = 1/E₂,
-- S₁₂ = −ν₁₂/E₁, so S₁₂² ≤ S₁₁·S₂₂ is ν₁₂² ≤ E₁/E₂). Each result is a bound, never a value.
------------------------------------------------------------------------

module Constants.SecondLawElastic where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _/_; _≤_; _<_; _+_; _*_; _-_; -_; Positive; nonNegative)
open import Data.Rational.Properties using (*-cancelʳ-≤-pos; *-cancelˡ-≤-pos; *-zeroˡ; *-zeroʳ; *-comm;
  *-identityʳ; +-identityʳ; +-identityˡ; +-mono-≤; +-monoʳ-≤; pos⇒nonNeg; <-≤-trans; <-irrefl; <-cmp; <⇒≤;
  positive⁻¹; *-monoˡ-≤-nonNeg; pos*pos⇒pos; nonNeg*nonNeg⇒nonNeg; nonNegative⁻¹)
open import Data.Integer using (+_)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Concrete.Gate using (mkState)
open import Core.Gate using (CoreAdmissible)
open import Process using (Prior; SecondLaw; transition; thermodynamic)

open +-*-Solver

-- The rational constants of the isotropic formulas.
two three nine : ℚ
two = + 2 / 1
three = + 3 / 1
nine = + 9 / 1

-- The relaxation of a state of free energy ψ to the natural state.
relaxation : ℚ → ℚ → ℚ → Prior
relaxation ρ ρ' ψ = thermodynamic (mkState ρ ψ 0ℚ 0ℚ) (mkState ρ' 0ℚ 0ℚ 0ℚ)

relaxation-nonneg : ∀ ρ ρ' ψ → SecondLaw transition (relaxation ρ ρ' ψ) → 0ℚ ≤ ψ
relaxation-nonneg ρ ρ' ψ h = CoreAdmissible.dissipation-nonneg h

private
  -- A nonnegative product with a positive right factor has a nonnegative left factor.
  cancelʳ : ∀ c r .{{_ : Positive r}} → 0ℚ ≤ c * r → 0ℚ ≤ c
  cancelʳ c r h = *-cancelʳ-≤-pos r (subst (_≤ c * r) (sym (*-zeroˡ r)) h)

  -- A nonnegative product with a positive left factor has a nonnegative right factor.
  cancelˡ : ∀ r .{{_ : Positive r}} d → 0ℚ ≤ r * d → 0ℚ ≤ d
  cancelˡ r d h = *-cancelˡ-≤-pos r (subst (_≤ r * d) (sym (*-zeroʳ r)) h)

  -- a ≤ b when b is a plus a nonnegative d.
  le-by : ∀ a b d → 0ℚ ≤ d → b ≡ a + d → a ≤ b
  le-by a b d h eq = subst (a ≤_) (sym eq) (subst (_≤ a + d) (+-identityʳ a) (+-monoʳ-≤ a h))

  -- A nonnegative quantity scaled by a positive constant stays nonnegative.
  scale : ∀ c .{{_ : Positive c}} {x} → 0ℚ ≤ x → 0ℚ ≤ c * x
  scale c {x} h = subst (_≤ c * x) (*-zeroʳ c) (*-monoˡ-≤-nonNeg c {{pos⇒nonNeg c}} h)

  nonneg-sum : ∀ x y → 0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ x + y
  nonneg-sum x y hx hy = +-mono-≤ hx hy

  half-nonneg : ∀ k → 0ℚ ≤ ½ * k → 0ℚ ≤ k
  half-nonneg k h = cancelʳ k ½ (subst (0ℚ ≤_) (*-comm ½ k) h)

-- Stiffness: a mode storing ½·k·q (q = s² > 0) that relaxes passively has k ≥ 0.
relaxation-stiffness-nonneg : ∀ ρ ρ' k q .{{_ : Positive q}} →
  SecondLaw transition (relaxation ρ ρ' (½ * k * q)) → 0ℚ ≤ k
relaxation-stiffness-nonneg ρ ρ' k q h = half-nonneg k (cancelʳ (½ * k) q (relaxation-nonneg ρ ρ' _ h))

-- Modulus: a body held at a stress with σ² = q > 0 by a modulus E stores the free energy ψ with 2·E·ψ = q (ψ = q/(2E));
-- its relaxation forces E > 0.
relaxation-modulus-pos : ∀ ρ ρ' E q ψ .{{_ : Positive q}} → ψ * E ≡ ½ * q →
  SecondLaw transition (relaxation ρ ρ' ψ) → 0ℚ < E
relaxation-modulus-pos ρ ρ' E q ψ eq h with <-cmp E 0ℚ
... | tri< E<0 _ _ = ⊥-elim (<-irrefl refl (<-≤-trans half>0 (subst (_≤ 0ℚ) eq ψE≤0)))
  where
    instance _ = nonNegative (relaxation-nonneg ρ ρ' ψ h)
    ψE≤0 : ψ * E ≤ 0ℚ
    ψE≤0 = subst (ψ * E ≤_) (*-zeroʳ ψ) (*-monoˡ-≤-nonNeg ψ (<⇒≤ E<0))
    half>0 : 0ℚ < ½ * q
    half>0 = positive⁻¹ (½ * q) {{pos*pos⇒pos ½ q}}
... | tri≈ _ E≡0 _ = ⊥-elim (<-irrefl refl (subst (0ℚ <_) (trans (sym eq) (trans (cong (ψ *_) E≡0) (*-zeroʳ ψ)))
                                             (positive⁻¹ (½ * q) {{pos*pos⇒pos ½ q}})))
... | tri> _ _ E>0 = E>0

-- Two modes: ½·a·x² + ½·b·y² relaxing passively from every (x, y) gives a ≥ 0 and b ≥ 0.
twoMode-stiffness-nonneg : ∀ ρ ρ' a b →
  (∀ x y → SecondLaw transition (relaxation ρ ρ' (½ * a * (x * x) + ½ * b * (y * y)))) → (0ℚ ≤ a) × (0ℚ ≤ b)
twoMode-stiffness-nonneg ρ ρ' a b h =
  half-nonneg a (subst (0ℚ ≤_) (ea a b) (relaxation-nonneg ρ ρ' _ (h 1ℚ 0ℚ))) ,
  half-nonneg b (subst (0ℚ ≤_) (eb a b) (relaxation-nonneg ρ ρ' _ (h 0ℚ 1ℚ)))
  where
    -- ½·a·(1·1) + ½·b·(0·0) = ½·a and its mirror, by the identity and zero laws (1ℚ * 1ℚ and 0ℚ * 0ℚ compute).
    ea : ∀ a b → ½ * a * (1ℚ * 1ℚ) + ½ * b * (0ℚ * 0ℚ) ≡ ½ * a
    ea a b = trans (cong₂ _+_ (*-identityʳ (½ * a)) (*-zeroʳ (½ * b))) (+-identityʳ (½ * a))
    eb : ∀ a b → ½ * a * (0ℚ * 0ℚ) + ½ * b * (1ℚ * 1ℚ) ≡ ½ * b
    eb a b = trans (cong₂ _+_ (*-zeroʳ (½ * a)) (*-identityʳ (½ * b))) (+-identityˡ (½ * b))

-- Poisson ratio, denominator cleared: an isotropic solid storing ½·K·e² + ½·G·γ² that relaxes passively from every
-- volumetric strain e and shear γ has −2(3K + G) ≤ 3K − 2G ≤ 3K + G, which for 3K + G > 0 is −1 ≤ ν ≤ 1/2 with
-- ν = (3K − 2G)/(2(3K + G)).
isotropic-poisson-bounds : ∀ ρ ρ' K G →
  (∀ e γ → SecondLaw transition (relaxation ρ ρ' (½ * K * (e * e) + ½ * G * (γ * γ)))) →
  (- (two * (three * K + G)) ≤ three * K - two * G) × (three * K - two * G ≤ three * K + G)
isotropic-poisson-bounds ρ ρ' K G h with twoMode-stiffness-nonneg ρ ρ' K G h
... | K≥0 , G≥0 =
  le-by _ _ (three * K + two * (three * K)) (nonneg-sum (three * K) (two * (three * K)) 3K≥0 (scale two 3K≥0))
    (lo two three K G) ,
  le-by _ _ (G + two * G) (nonneg-sum G (two * G) G≥0 (scale two G≥0)) (hi two three K G)
  where
    3K≥0 : 0ℚ ≤ three * K
    3K≥0 = scale three K≥0
    -- The identities hold for every value of the constants (they are polynomial in two and three).
    lo : ∀ t2 t3 K G → t3 * K - t2 * G ≡ - (t2 * (t3 * K + G)) + (t3 * K + t2 * (t3 * K))
    lo = solve 4 (λ t2 t3 K G → t3 :* K :- t2 :* G := :- (t2 :* (t3 :* K :+ G)) :+ (t3 :* K :+ t2 :* (t3 :* K))) refl
    hi : ∀ t2 t3 K G → t3 * K + G ≡ (t3 * K - t2 * G) + (G + t2 * G)
    hi = solve 4 (λ t2 t3 K G → t3 :* K :+ G := (t3 :* K :- t2 :* G) :+ (G :+ t2 :* G)) refl

-- Young's modulus, denominator cleared: under the same relaxation 9·K·G ≥ 0, which for 3K + G > 0 is
-- E = 9KG/(3K + G) ≥ 0.
isotropic-young-nonneg : ∀ ρ ρ' K G →
  (∀ e γ → SecondLaw transition (relaxation ρ ρ' (½ * K * (e * e) + ½ * G * (γ * γ)))) → 0ℚ ≤ nine * K * G
isotropic-young-nonneg ρ ρ' K G h with twoMode-stiffness-nonneg ρ ρ' K G h
... | K≥0 , G≥0 = nonNegative⁻¹ _ {{nonNeg*nonNeg⇒nonNeg (nine * K) {{nonNegative (scale nine K≥0)}} G
  {{nonNegative G≥0}}}}

-- Standard linear solid: storing ½·G∞·ε² + ½·G₁·ξ² and relaxing passively from every total strain and arm strain,
-- 0 ≤ G∞ ≤ G∞ + G₁, the instantaneous modulus.
sls-relaxed-le-instantaneous : ∀ ρ ρ' Ginf G1 →
  (∀ ε ξ → SecondLaw transition (relaxation ρ ρ' (½ * Ginf * (ε * ε) + ½ * G1 * (ξ * ξ)))) →
  (0ℚ ≤ Ginf) × (Ginf ≤ Ginf + G1)
sls-relaxed-le-instantaneous ρ ρ' Ginf G1 h with twoMode-stiffness-nonneg ρ ρ' Ginf G1 h
... | Ginf≥0 , G1≥0 = Ginf≥0 , le-by Ginf (Ginf + G1) G1 G1≥0 refl

-- Orthotropic lamina, compliance form: storing ½·(S₁₁·σ₁² + 2·S₁₂·σ₁·σ₂ + S₂₂·σ₂²) (the cross term written as a sum) with S₂₂ > 0 and relaxing
-- passively from every plane stress state gives S₁₂² ≤ S₁₁·S₂₂ (ν₁₂² ≤ E₁/E₂ for S₁₁ = 1/E₁, S₂₂ = 1/E₂,
-- S₁₂ = −ν₁₂/E₁).
orthotropic-compliance-sq-le : ∀ ρ ρ' S11 S22 S12 .{{_ : Positive S22}} →
  (∀ s1 s2 → SecondLaw transition
    (relaxation ρ ρ' (½ * (S11 * (s1 * s1) + (S12 * s1 * s2 + S12 * s1 * s2) + S22 * (s2 * s2))))) →
  S12 * S12 ≤ S11 * S22
orthotropic-compliance-sq-le ρ ρ' S11 S22 S12 h =
  le-by _ _ (S11 * S22 - S12 * S12) d≥0 (split S11 S22 S12)
  where
    instance _ = pos*pos⇒pos ½ S22
    at : ∀ h S11 S22 S12 → h * (S11 * (S22 * S22) + (S12 * S22 * (- S12) + S12 * S22 * (- S12)) + S22 * ((- S12) * (- S12)))
                           ≡ h * S22 * (S11 * S22 - S12 * S12)
    at = solve 4 (λ h a b c → h :* (a :* (b :* b) :+ (c :* b :* (:- c) :+ c :* b :* (:- c)) :+ b :* ((:- c) :* (:- c)))
                                := h :* b :* (a :* b :- c :* c)) refl
    d≥0 : 0ℚ ≤ S11 * S22 - S12 * S12
    d≥0 = cancelˡ (½ * S22) _ (subst (0ℚ ≤_) (at ½ S11 S22 S12) (relaxation-nonneg ρ ρ' _ (h S22 (- S12))))
    split : ∀ S11 S22 S12 → S11 * S22 ≡ S12 * S12 + (S11 * S22 - S12 * S12)
    split = solve 3 (λ a b c → a :* b := c :* c :+ (a :* b :- c :* c)) refl
