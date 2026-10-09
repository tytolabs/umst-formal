-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Constants.SecondLawPoroContinuum — transport, reaction and poroelastic constants bounded by the second law (twin
-- of Lean/Constants/SecondLawPoroContinuum.lean and Coq/Constants/SecondLawPoroContinuum.v).
--
-- Each theorem takes a passive step as the transition case of SecondLaw: a step whose dissipation leaves the free
-- energy (`dissipates`) or the relaxation of a loaded state to the natural state (`relaxation`). Agda carries
-- quantities as rationals: a squared gradient or strain enters as a positive rational q, the Darcy mobility 1/μ as a
-- positive rational f (the fluidity), the Biot storage bound is stated on the storage coefficient m = 1/M and the
-- Poisson bounds with their positive denominator cleared. The Biot relations enter as hypotheses on the constants.
-- Each result is a bound, never a value.
------------------------------------------------------------------------

module Constants.SecondLawPoroContinuum where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _<_; _+_; _*_; _-_; -_; Positive; positive; nonNegative)
open import Data.Rational.Properties using (*-cancelˡ-≤-pos; *-zeroʳ; +-identityʳ; +-monoʳ-≤; +-mono-≤-<;
  +-monoʳ-<; *-monoˡ-≤-nonNeg; pos⇒nonNeg; pos*pos⇒pos; positive⁻¹; <-cmp; <-irrefl; <⇒≤; ≤-<-trans; <-≤-trans;
  ≤-reflexive)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Process using (SecondLaw; transition)
open import Constants.SecondLawDissipation using (dissipates; dissipation-coefficient-nonneg)
open import Constants.SecondLawElastic using (relaxation; relaxation-stiffness-nonneg; twoMode-stiffness-nonneg;
  two; three)

open +-*-Solver

private
  -- a ≤ b when b is a plus a nonnegative d.
  le-by : ∀ a b d → 0ℚ ≤ d → b ≡ a + d → a ≤ b
  le-by a b d h eq = subst (a ≤_) (sym eq) (subst (_≤ a + d) (+-identityʳ a) (+-monoʳ-≤ a h))

  -- a < b when b is a plus a positive d.
  lt-by : ∀ a b d → 0ℚ < d → b ≡ a + d → a < b
  lt-by a b d h eq = subst (a <_) (sym eq) (subst (_< a + d) (+-identityʳ a) (+-monoʳ-< a h))

  -- A nonnegative product with a positive left factor has a nonnegative right factor.
  cancelˡ : ∀ r .{{_ : Positive r}} d → 0ℚ ≤ r * d → 0ℚ ≤ d
  cancelˡ r d h = *-cancelˡ-≤-pos r (subst (_≤ r * d) (sym (*-zeroʳ r)) h)

  -- A nonnegative quantity scaled by a positive constant stays nonnegative.
  scale : ∀ c .{{_ : Positive c}} {x} → 0ℚ ≤ x → 0ℚ ≤ c * x
  scale c {x} h = subst (_≤ c * x) (*-zeroʳ c) (*-monoˡ-≤-nonNeg c {{pos⇒nonNeg c}} h)

  -- A nonnegative quantity that is not zero is positive.
  nonneg-nonzero-pos : ∀ x → 0ℚ ≤ x → x ≢ 0ℚ → 0ℚ < x
  nonneg-nonzero-pos x h nz with <-cmp x 0ℚ
  ... | tri< x<0 _ _ = ⊥-elim (<-irrefl refl (≤-<-trans h x<0))
  ... | tri≈ _ x≡0 _ = ⊥-elim (nz x≡0)
  ... | tri> _ _ x>0 = x>0

  -- A positive quantity scaled by a positive constant stays positive.
  scale-pos : ∀ c .{{_ : Positive c}} x → 0ℚ < x → 0ℚ < c * x
  scale-pos c x h = positive⁻¹ (c * x) {{pos*pos⇒pos c x {{positive h}}}}

-- Reaction rate: a reaction with affinity A > 0 advancing at rate r over dt > 0 dissipates A·r·dt; the second law
-- gives r ≥ 0.
reaction-rate-nonneg : ∀ ρ ρ' ψ A r dt .{{_ : Positive A}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (A * r * dt)) → 0ℚ ≤ r
reaction-rate-nonneg ρ ρ' ψ A r dt h =
  dissipation-coefficient-nonneg ρ ρ' ψ r (A * dt) {{pos*pos⇒pos A dt}} (subst (λ d → SecondLaw transition (dissipates ρ ρ' ψ d)) (e A r dt) h)
  where
    e : ∀ A r dt → A * r * dt ≡ r * (A * dt)
    e = solve 3 (λ A r dt → A :* r :* dt := r :* (A :* dt)) refl

-- Rate constant: with affinity A > 0 and rate law r = k·g, g > 0, the step dissipates A·(k·g)·dt; the second law
-- gives k ≥ 0.
reaction-rate-constant-nonneg : ∀ ρ ρ' ψ A k g dt .{{_ : Positive A}} .{{_ : Positive g}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (A * (k * g) * dt)) → 0ℚ ≤ k
reaction-rate-constant-nonneg ρ ρ' ψ A k g dt h =
  dissipation-coefficient-nonneg ρ ρ' ψ k (A * g * dt) {{pos*pos⇒pos (A * g) {{pos*pos⇒pos A g}} dt}}
    (subst (λ d → SecondLaw transition (dissipates ρ ρ' ψ d)) (e A k g dt) h)
  where
    e : ∀ A k g dt → A * (k * g) * dt ≡ k * (A * g * dt)
    e = solve 4 (λ A k g dt → A :* (k :* g) :* dt := k :* (A :* g :* dt)) refl

-- Diffusivity: Fickian diffusion at a gradient with g² = q > 0 and thermodynamic factor χ > 0 over dt > 0
-- dissipates D·χ·q·dt; the second law gives D ≥ 0.
fick-diffusivity-nonneg : ∀ ρ ρ' ψ D χ q dt .{{_ : Positive χ}} .{{_ : Positive q}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (D * χ * q * dt)) → 0ℚ ≤ D
fick-diffusivity-nonneg ρ ρ' ψ D χ q dt h =
  dissipation-coefficient-nonneg ρ ρ' ψ D (χ * q * dt) {{pos*pos⇒pos (χ * q) {{pos*pos⇒pos χ q}} dt}}
    (subst (λ d → SecondLaw transition (dissipates ρ ρ' ψ d)) (e D χ q dt) h)
  where
    e : ∀ D χ q dt → D * χ * q * dt ≡ D * (χ * q * dt)
    e = solve 4 (λ D χ q dt → D :* χ :* q :* dt := D :* (χ :* q :* dt)) refl

-- Permeability: Darcy flow at a pressure gradient with g² = q > 0 through a fluid of fluidity f = 1/μ > 0 over
-- dt > 0 dissipates κ·f·q·dt; the second law gives κ ≥ 0.
darcy-permeability-nonneg : ∀ ρ ρ' ψ κ f q dt .{{_ : Positive f}} .{{_ : Positive q}} .{{_ : Positive dt}} →
  SecondLaw transition (dissipates ρ ρ' ψ (κ * f * q * dt)) → 0ℚ ≤ κ
darcy-permeability-nonneg ρ ρ' ψ κ f q dt h = fick-diffusivity-nonneg ρ ρ' ψ κ f q dt h

-- Biot coefficient: with K = K_s·(1 − b) and b − φ = K_s·n (K_s > 0), a drained mode storing ½·K·q and a pore mode
-- storing ½·n·q (q = s² > 0) that relax passively give φ ≤ b ≤ 1.
biot-coefficient-bounds : ∀ ρ ρ' K Ks n φ b q .{{_ : Positive q}} .{{_ : Positive Ks}} →
  K ≡ Ks * (1ℚ - b) → b - φ ≡ Ks * n →
  SecondLaw transition (relaxation ρ ρ' (½ * K * q)) → SecondLaw transition (relaxation ρ ρ' (½ * n * q)) →
  (φ ≤ b) × (b ≤ 1ℚ)
biot-coefficient-bounds ρ ρ' K Ks n φ b q hK hn hdrained hpore =
  le-by φ b (Ks * n) (scale Ks n≥0) (trans (eφ φ b) (cong (φ +_) hn)) ,
  le-by b 1ℚ (1ℚ - b) (cancelˡ Ks (1ℚ - b) (subst (0ℚ ≤_) hK K≥0)) (eb b)
  where
    K≥0 : 0ℚ ≤ K
    K≥0 = relaxation-stiffness-nonneg ρ ρ' K q hdrained
    n≥0 : 0ℚ ≤ n
    n≥0 = relaxation-stiffness-nonneg ρ ρ' n q hpore
    eφ : ∀ φ b → b ≡ φ + (b - φ)
    eφ = solve 2 (λ φ b → b := φ :+ (b :- φ)) refl
    eb : ∀ b → 1ℚ ≡ b + (1ℚ - b)
    eb = solve 1 (λ b → con 1ℚ := b :+ (con 1ℚ :- b)) refl

-- Biot storage: with m = n + φ·c_f, φ > 0, a pore mode storing ½·n·q and a fluid mode storing ½·c_f·q (c_f ≠ 0,
-- q = s² > 0) that relax passively, the storage coefficient m = 1/M is positive.
biot-storage-pos : ∀ ρ ρ' n cf φ m q .{{_ : Positive q}} .{{_ : Positive φ}} → cf ≢ 0ℚ → m ≡ n + φ * cf →
  SecondLaw transition (relaxation ρ ρ' (½ * n * q)) → SecondLaw transition (relaxation ρ ρ' (½ * cf * q)) →
  0ℚ < m
biot-storage-pos ρ ρ' n cf φ m q cf≢0 hm hpore hfluid =
  subst (0ℚ <_) (sym hm) (subst (_< n + φ * cf) (+-identityʳ 0ℚ) (+-mono-≤-< n≥0 (scale-pos φ cf cf>0)))
  where
    n≥0 : 0ℚ ≤ n
    n≥0 = relaxation-stiffness-nonneg ρ ρ' n q hpore
    cf>0 : 0ℚ < cf
    cf>0 = nonneg-nonzero-pos cf (relaxation-stiffness-nonneg ρ ρ' cf q hfluid) cf≢0

-- Isotropic moduli, denominator cleared: an isotropic solid storing ½·K·e² + ½·G·γ² with K ≠ 0 and G ≠ 0 that
-- relaxes passively from every (e, γ) has K > 0, G > 0 and −2(3K + G) < 3K − 2G < 3K + G, which is −1 < ν < 1/2
-- with ν = (3K − 2G)/(2(3K + G)).
isotropic-moduli-pos : ∀ ρ ρ' K G → K ≢ 0ℚ → G ≢ 0ℚ →
  (∀ e γ → SecondLaw transition (relaxation ρ ρ' (½ * K * (e * e) + ½ * G * (γ * γ)))) →
  (0ℚ < K) × (0ℚ < G) × (- (two * (three * K + G)) < three * K - two * G) × (three * K - two * G < three * K + G)
isotropic-moduli-pos ρ ρ' K G K≢0 G≢0 h with twoMode-stiffness-nonneg ρ ρ' K G h
... | K≥0 , G≥0 =
  K>0 , G>0 ,
  lt-by _ _ (three * K + two * (three * K)) (+-mono-<-pos 3K>0 (scale-pos two (three * K) 3K>0)) (lo two three K G) ,
  lt-by _ _ (G + two * G) (+-mono-<-pos G>0 (scale-pos two G G>0)) (hi two three K G)
  where
    K>0 : 0ℚ < K
    K>0 = nonneg-nonzero-pos K K≥0 K≢0
    G>0 : 0ℚ < G
    G>0 = nonneg-nonzero-pos G G≥0 G≢0
    instance
      p2 : Positive two
      p2 = positive (positive⁻¹ two)
      p3 : Positive three
      p3 = positive (positive⁻¹ three)
    3K>0 : 0ℚ < three * K
    3K>0 = scale-pos three K K>0
    +-mono-<-pos : ∀ {x y} → 0ℚ < x → 0ℚ < y → 0ℚ < x + y
    +-mono-<-pos {x} {y} hx hy = subst (_< x + y) (+-identityʳ 0ℚ) (+-mono-≤-< (<⇒≤ hx) hy)
    lo : ∀ t2 t3 K G → t3 * K - t2 * G ≡ - (t2 * (t3 * K + G)) + (t3 * K + t2 * (t3 * K))
    lo = solve 4 (λ t2 t3 K G → t3 :* K :- t2 :* G := :- (t2 :* (t3 :* K :+ G)) :+ (t3 :* K :+ t2 :* (t3 :* K))) refl
    hi : ∀ t2 t3 K G → t3 * K + G ≡ (t3 * K - t2 * G) + (G + t2 * G)
    hi = solve 4 (λ t2 t3 K G → t3 :* K :+ G := (t3 :* K :- t2 :* G) :+ (G :+ t2 :* G)) refl
