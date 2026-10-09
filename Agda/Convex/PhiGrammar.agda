-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Convex.PhiGrammar — a grammar of dissipation potentials that are convex, nonnegative and zero at zero by
-- construction (twin of Lean/Convex/PhiGrammar.lean and Coq/Convex/PhiGrammar.v).
--
-- Agda states the grammar over one exact rational rate: the linear maps of ℚ are the scalings x ↦ k·x, a
-- positive-semidefinite form is a·x² with a ≥ 0, and the power and Norton exponents are p + 1 and m + 1 for natural
-- p and m. Every expression denotes a potential that is zero at zero, nonnegative and convex along every chord; a
-- subgradient of it pairs with the rate to a nonnegative dissipation, so a passive step is a transition case of
-- SecondLaw.
------------------------------------------------------------------------

module Convex.PhiGrammar where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _<_; _+_; _*_; _-_; -_; ∣_∣; _⊔_; _⊓_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-total; ≤-<-trans; <-irrefl; _<?_;
  +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-identityʳ; +-inverseʳ; *-zeroˡ; *-zeroʳ; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg;
  nonNeg*nonNeg⇒nonNeg; nonNegative⁻¹; 0≤∣p∣; 0≤p⇒∣p∣≡p; ∣p∣≡p∨∣p∣≡-p; ∣p+q∣≤∣p∣+∣q∣; ∣p*q∣≡∣p∣*∣q∣;
  p≤p⊔q; p≤q⊔p; ⊔-lub)
open import Data.Rational.Base using (nonNegative)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)

open import Concrete.Gate using (ThermodynamicState; mkState)
open import Core.Gate using (CoreAdmissible; δ-mass)
open import Process using (Prior; SecondLaw; transition; thermodynamic)

open +-*-Solver

------------------------------------------------------------------------
-- Order helpers over ℚ

-- p ≤ q from a nonnegative gap q − p.
gap : ∀ p q → 0ℚ ≤ q - p → p ≤ q
gap p q h = subst₂ _≤_ (+-identityʳ p) (eq p q) (+-monoʳ-≤ p h)
  where
    eq : ∀ p q → p + (q - p) ≡ q
    eq = solve 2 (λ p q → p :+ (q :- p) := q) refl

-- A nonnegative gap from p ≤ q.
gap⁻¹ : ∀ p q → p ≤ q → 0ℚ ≤ q - p
gap⁻¹ p q h = subst (_≤ q - p) (+-inverseʳ p) (+-monoˡ-≤ (- p) h)

mul-nonneg : ∀ {p q} → 0ℚ ≤ p → 0ℚ ≤ q → 0ℚ ≤ p * q
mul-nonneg {p} {q} hp hq = nonNegative⁻¹ (p * q) {{nonNeg*nonNeg⇒nonNeg p {{nonNegative hp}} q {{nonNegative hq}}}}

mul-monoˡ : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → r * p ≤ r * q
mul-monoˡ {r} hr h = *-monoˡ-≤-nonNeg r {{nonNegative hr}} h

mul-monoʳ : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → p * r ≤ q * r
mul-monoʳ {r} hr h = *-monoʳ-≤-nonNeg r {{nonNegative hr}} h

add-nonneg : ∀ {p q} → 0ℚ ≤ p → 0ℚ ≤ q → 0ℚ ≤ p + q
add-nonneg hp hq = +-mono-≤ hp hq

sq-nonneg : ∀ z → 0ℚ ≤ z * z
sq-nonneg z with ∣p∣≡p∨∣p∣≡-p z
... | inj₁ e = subst (λ w → 0ℚ ≤ w * w) e (mul-nonneg (0≤∣p∣ z) (0≤∣p∣ z))
... | inj₂ e = subst (0ℚ ≤_) (trans (cong (λ w → w * w) e) (neg-sq z)) (mul-nonneg (0≤∣p∣ z) (0≤∣p∣ z))
  where
    neg-sq : ∀ z → (- z) * (- z) ≡ z * z
    neg-sq = solve 1 (λ z → (:- z) :* (:- z) := z :* z) refl

------------------------------------------------------------------------
-- Powers

qpow : ℚ → ℕ → ℚ
qpow z zero    = 1ℚ
qpow z (suc k) = z * qpow z k

qpow-nonneg : ∀ {z} k → 0ℚ ≤ z → 0ℚ ≤ qpow z k
qpow-nonneg zero    hz = toWitness {a? = 0ℚ Data.Rational.Properties.≤? 1ℚ} tt
qpow-nonneg (suc k) hz = mul-nonneg hz (qpow-nonneg k hz)

qpow-mono : ∀ {a b} k → 0ℚ ≤ a → a ≤ b → qpow a k ≤ qpow b k
qpow-mono zero    ha hab = ≤-refl
qpow-mono {a} {b} (suc k) ha hab =
  ≤-trans (mul-monoˡ ha (qpow-mono k ha hab)) (mul-monoʳ (qpow-nonneg k (≤-trans ha hab)) hab)

-- (a − b)·(aᵏ − bᵏ) ≥ 0 for a, b ≥ 0.
qpow-sorted : ∀ a b k → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ (a - b) * (qpow a k - qpow b k)
qpow-sorted a b k ha hb with ≤-total a b
... | inj₁ a≤b = subst (0ℚ ≤_) (flip a b (qpow a k) (qpow b k))
                   (mul-nonneg (gap⁻¹ a b a≤b) (gap⁻¹ (qpow a k) (qpow b k) (qpow-mono k ha a≤b)))
  where
    flip : ∀ a b A B → (b - a) * (B - A) ≡ (a - b) * (A - B)
    flip = solve 4 (λ a b A B → (b :- a) :* (B :- A) := (a :- b) :* (A :- B)) refl
... | inj₂ b≤a = mul-nonneg (gap⁻¹ b a b≤a) (gap⁻¹ (qpow b k) (qpow a k) (qpow-mono k hb b≤a))

chord : ℚ → ℚ → ℚ → ℚ
chord t x y = t * x + (1ℚ - t) * y

chord-nonneg : ∀ {t a b} → 0ℚ ≤ t → t ≤ 1ℚ → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ chord t a b
chord-nonneg {t} ht0 ht1 ha hb = add-nonneg (mul-nonneg ht0 ha) (mul-nonneg (gap⁻¹ t 1ℚ ht1) hb)

-- z ↦ z^(k+1) is convex along every chord of [0, ∞).
qpow-convex : ∀ t a b k → 0ℚ ≤ t → t ≤ 1ℚ → 0ℚ ≤ a → 0ℚ ≤ b →
  qpow (chord t a b) (suc k) ≤ t * qpow a (suc k) + (1ℚ - t) * qpow b (suc k)
qpow-convex t a b zero ht0 ht1 ha hb = ≤-reflexive (base t a b)
  where
    base : ∀ t a b → (t * a + (1ℚ - t) * b) * 1ℚ ≡ t * (a * 1ℚ) + (1ℚ - t) * (b * 1ℚ)
    base = solve 3 (λ t a b → (t :* a :+ (con 1ℚ :- t) :* b) :* con 1ℚ
                     := t :* (a :* con 1ℚ) :+ (con 1ℚ :- t) :* (b :* con 1ℚ)) refl
qpow-convex t a b (suc k) ht0 ht1 ha hb =
  ≤-trans (mul-monoˡ hm (qpow-convex t a b k ht0 ht1 ha hb))
    (gap _ _ (subst (0ℚ ≤_) (sym (key t a b A B))
      (mul-nonneg (mul-nonneg ht0 (gap⁻¹ t 1ℚ ht1)) (qpow-sorted a b (suc k) ha hb))))
  where
    A = qpow a (suc k)
    B = qpow b (suc k)
    hm = chord-nonneg ht0 ht1 ha hb
    key : ∀ t a b A B → (t * (a * A) + (1ℚ - t) * (b * B)) - (t * a + (1ℚ - t) * b) * (t * A + (1ℚ - t) * B)
                       ≡ t * (1ℚ - t) * ((a - b) * (A - B))
    key = solve 5 (λ t a b A B →
      (t :* (a :* A) :+ (con 1ℚ :- t) :* (b :* B)) :- (t :* a :+ (con 1ℚ :- t) :* b) :* (t :* A :+ (con 1ℚ :- t) :* B)
      := t :* (con 1ℚ :- t) :* ((a :- b) :* (A :- B))) refl

abs-chord : ∀ t x y → 0ℚ ≤ t → t ≤ 1ℚ → ∣ chord t x y ∣ ≤ chord t (∣ x ∣) (∣ y ∣)
abs-chord t x y ht0 ht1 = subst (∣ chord t x y ∣ ≤_) eq (∣p+q∣≤∣p∣+∣q∣ (t * x) ((1ℚ - t) * y))
  where
    eq : ∣ t * x ∣ + ∣ (1ℚ - t) * y ∣ ≡ chord t (∣ x ∣) (∣ y ∣)
    eq rewrite ∣p*q∣≡∣p∣*∣q∣ t x | ∣p*q∣≡∣p∣*∣q∣ (1ℚ - t) y | 0≤p⇒∣p∣≡p ht0 | 0≤p⇒∣p∣≡p (gap⁻¹ t 1ℚ ht1) = refl

abspow-chord : ∀ t x y k → 0ℚ ≤ t → t ≤ 1ℚ →
  qpow (∣ chord t x y ∣) (suc k) ≤ t * qpow (∣ x ∣) (suc k) + (1ℚ - t) * qpow (∣ y ∣) (suc k)
abspow-chord t x y k ht0 ht1 =
  ≤-trans (qpow-mono (suc k) (0≤∣p∣ _) (abs-chord t x y ht0 ht1))
          (qpow-convex t (∣ x ∣) (∣ y ∣) k ht0 ht1 (0≤∣p∣ x) (0≤∣p∣ y))

------------------------------------------------------------------------
-- The grammar

data PhiExpr : Set where
  quad    : (a : ℚ) → 0ℚ ≤ a → PhiExpr                  -- a·x², a ≥ 0
  abs     : PhiExpr                                     -- |x|
  pow     : ℕ → PhiExpr                                 -- |x|^(p+1)
  norton  : (a : ℚ) → 0ℚ ≤ a → ℕ → PhiExpr              -- a·|x|^(m+1), a ≥ 0
  scale   : (c : ℚ) → 0ℚ ≤ c → PhiExpr → PhiExpr        -- c·φ, c ≥ 0
  add     : PhiExpr → PhiExpr → PhiExpr                 -- φ₁ + φ₂
  max     : PhiExpr → PhiExpr → PhiExpr                 -- max(φ₁, φ₂)
  precomp : ℚ → PhiExpr → PhiExpr                       -- φ(k·x)

denote : PhiExpr → ℚ → ℚ
denote (quad a _)     x = a * (x * x)
denote abs            x = ∣ x ∣
denote (pow p)        x = qpow (∣ x ∣) (suc p)
denote (norton a _ m) x = a * qpow (∣ x ∣) (suc m)
denote (scale c _ e)  x = c * denote e x
denote (add e₁ e₂)    x = denote e₁ x + denote e₂ x
denote (max e₁ e₂)    x = denote e₁ x ⊔ denote e₂ x
denote (precomp k e)  x = denote e (k * x)

-- Zero at zero: φ(0) = 0.
denote-zero : ∀ e → denote e 0ℚ ≡ 0ℚ
denote-zero (quad a _)     = trans (cong (a *_) (*-zeroˡ 0ℚ)) (*-zeroʳ a)
denote-zero abs            = refl
denote-zero (pow p)        = *-zeroˡ (qpow 0ℚ p)
denote-zero (norton a _ m) = trans (cong (a *_) (*-zeroˡ (qpow 0ℚ m))) (*-zeroʳ a)
denote-zero (scale c _ e)  = trans (cong (c *_) (denote-zero e)) (*-zeroʳ c)
denote-zero (add e₁ e₂)    = cong₂ _+_ (denote-zero e₁) (denote-zero e₂)
denote-zero (max e₁ e₂)    = cong₂ _⊔_ (denote-zero e₁) (denote-zero e₂)
denote-zero (precomp k e)  = trans (cong (denote e) (*-zeroʳ k)) (denote-zero e)

-- Nonnegative: φ ≥ 0.
denote-nonneg : ∀ e x → 0ℚ ≤ denote e x
denote-nonneg (quad a ha)     x = mul-nonneg ha (sq-nonneg x)
denote-nonneg abs             x = 0≤∣p∣ x
denote-nonneg (pow p)         x = qpow-nonneg (suc p) (0≤∣p∣ x)
denote-nonneg (norton a ha m) x = mul-nonneg ha (qpow-nonneg (suc m) (0≤∣p∣ x))
denote-nonneg (scale c hc e)  x = mul-nonneg hc (denote-nonneg e x)
denote-nonneg (add e₁ e₂)     x = add-nonneg (denote-nonneg e₁ x) (denote-nonneg e₂ x)
denote-nonneg (max e₁ e₂)     x = ≤-trans (denote-nonneg e₁ x) (p≤p⊔q _ _)
denote-nonneg (precomp k e)   x = denote-nonneg e (k * x)

-- c·(t·p + (1 − t)·q) = t·(c·p) + (1 − t)·(c·q)
scale-chord : ∀ c t p q → c * chord t p q ≡ chord t (c * p) (c * q)
scale-chord = solve 4 (λ c t p q → c :* (t :* p :+ (con 1ℚ :- t) :* q)
                         := t :* (c :* p) :+ (con 1ℚ :- t) :* (c :* q)) refl

-- Convex: φ(t·x + (1 − t)·y) ≤ t·φ(x) + (1 − t)·φ(y) for t ∈ [0, 1].
denote-convex : ∀ e t x y → 0ℚ ≤ t → t ≤ 1ℚ → denote e (chord t x y) ≤ chord t (denote e x) (denote e y)
denote-convex (quad a ha) t x y ht0 ht1 =
  gap _ _ (subst (0ℚ ≤_) (sym (key a t x y))
    (mul-nonneg (mul-nonneg ha (mul-nonneg ht0 (gap⁻¹ t 1ℚ ht1))) (sq-nonneg (x - y))))
  where
    key : ∀ a t x y → (t * (a * (x * x)) + (1ℚ - t) * (a * (y * y)))
                       - a * ((t * x + (1ℚ - t) * y) * (t * x + (1ℚ - t) * y))
                     ≡ a * (t * (1ℚ - t)) * ((x - y) * (x - y))
    key = solve 4 (λ a t x y →
      (t :* (a :* (x :* x)) :+ (con 1ℚ :- t) :* (a :* (y :* y)))
        :- a :* ((t :* x :+ (con 1ℚ :- t) :* y) :* (t :* x :+ (con 1ℚ :- t) :* y))
      := a :* (t :* (con 1ℚ :- t)) :* ((x :- y) :* (x :- y))) refl
denote-convex abs t x y ht0 ht1 = abs-chord t x y ht0 ht1
denote-convex (pow p) t x y ht0 ht1 = abspow-chord t x y p ht0 ht1
denote-convex (norton a ha m) t x y ht0 ht1 =
  subst (denote (norton a ha m) (chord t x y) ≤_) (scale-chord a t _ _) (mul-monoˡ ha (abspow-chord t x y m ht0 ht1))
denote-convex (scale c hc e) t x y ht0 ht1 =
  subst (denote (scale c hc e) (chord t x y) ≤_) (scale-chord c t _ _) (mul-monoˡ hc (denote-convex e t x y ht0 ht1))
denote-convex (add e₁ e₂) t x y ht0 ht1 =
  subst (denote (add e₁ e₂) (chord t x y) ≤_) (sum-chord t _ _ _ _)
    (+-mono-≤ (denote-convex e₁ t x y ht0 ht1) (denote-convex e₂ t x y ht0 ht1))
  where
    sum-chord : ∀ t p q r s → chord t p q + chord t r s ≡ chord t (p + r) (q + s)
    sum-chord = solve 5 (λ t p q r s → (t :* p :+ (con 1ℚ :- t) :* q) :+ (t :* r :+ (con 1ℚ :- t) :* s)
                           := t :* (p :+ r) :+ (con 1ℚ :- t) :* (q :+ s)) refl
denote-convex (max e₁ e₂) t x y ht0 ht1 =
  ⊔-lub (≤-trans (denote-convex e₁ t x y ht0 ht1) (bound (p≤p⊔q _ _) (p≤p⊔q _ _)))
        (≤-trans (denote-convex e₂ t x y ht0 ht1) (bound (p≤q⊔p (denote e₁ x) _) (p≤q⊔p (denote e₁ y) _)))
  where
    bound : ∀ {p q r s} → p ≤ r → q ≤ s → chord t p q ≤ chord t r s
    bound hpr hqs = +-mono-≤ (mul-monoˡ ht0 hpr) (mul-monoˡ (gap⁻¹ t 1ℚ ht1) hqs)
denote-convex (precomp k e) t x y ht0 ht1 =
  subst (λ z → denote e z ≤ chord t (denote e (k * x)) (denote e (k * y))) (sym (lin k t x y))
    (denote-convex e t (k * x) (k * y) ht0 ht1)
  where
    lin : ∀ k t x y → k * (t * x + (1ℚ - t) * y) ≡ t * (k * x) + (1ℚ - t) * (k * y)
    lin = solve 4 (λ k t x y → k :* (t :* x :+ (con 1ℚ :- t) :* y)
                    := t :* (k :* x) :+ (con 1ℚ :- t) :* (k :* y)) refl

------------------------------------------------------------------------
-- The passive second law

-- g is a subgradient of φ at x: φ(x) + g·(y − x) ≤ φ(y) for every y.
IsSubgradient : PhiExpr → ℚ → ℚ → Set
IsSubgradient e x g = ∀ y → denote e x + g * (y - x) ≤ denote e y

-- The dissipation g·x dominates the potential.
phi-le-subgradient-power : ∀ e x g → IsSubgradient e x g → denote e x ≤ g * x
phi-le-subgradient-power e x g hg =
  gap _ _ (subst (0ℚ ≤_) (eq (denote e x) g x)
    (gap⁻¹ _ _ (subst (denote e x + g * (0ℚ - x) ≤_) (denote-zero e) (hg 0ℚ))))
  where
    eq : ∀ f g x → 0ℚ - (f + g * (0ℚ - x)) ≡ g * x - f
    eq = solve 3 (λ f g x → con 0ℚ :- (f :+ g :* (con 0ℚ :- x)) := g :* x :- f) refl

-- Nonnegative dissipation for every expression and subgradient.
subgradient-power-nonneg : ∀ e x g → IsSubgradient e x g → 0ℚ ≤ g * x
subgradient-power-nonneg e x g hg = ≤-trans (denote-nonneg e x) (phi-le-subgradient-power e x g hg)

-- Passive second law: a step that dissipates g·x (g a subgradient of a grammar potential at the rate x), under the
-- passive balance (ψ_new − ψ_old) + g·x ≤ 0 and the mass condition, is a transition case of SecondLaw.
phi-expr-passive-second-law : ∀ e x g (old new : ThermodynamicState) → IsSubgradient e x g →
  (ThermodynamicState.density new - ThermodynamicState.density old ≤ δ-mass) →
  (ThermodynamicState.density old - ThermodynamicState.density new ≤ δ-mass) →
  (ThermodynamicState.free-energy new - ThermodynamicState.free-energy old) + g * x ≤ 0ℚ →
  SecondLaw transition (thermodynamic old new)
phi-expr-passive-second-law e x g old new hg hm₁ hm₂ hb =
  record { mass-conserved = hm₁ , hm₂ ; dissipation-nonneg = descent }
  where
    ψo = ThermodynamicState.free-energy old
    ψn = ThermodynamicState.free-energy new
    -- ψn − ψo ≤ (ψn − ψo) + g·x ≤ 0
    step : ψn - ψo ≤ 0ℚ
    step = ≤-trans (subst (_≤ (ψn - ψo) + g * x) (+-identityʳ (ψn - ψo))
                     (+-monoʳ-≤ (ψn - ψo) (subgradient-power-nonneg e x g hg))) hb
    descent : ψn ≤ ψo
    descent = gap _ _ (subst (0ℚ ≤_) (eq ψn ψo) (gap⁻¹ _ _ step))
      where
        eq : ∀ n o → 0ℚ - (n - o) ≡ o - n
        eq = solve 2 (λ n o → con 0ℚ :- (n :- o) := o :- n) refl

------------------------------------------------------------------------
-- A nonconvex potential has no expression: min(|x|, 1) is nonnegative and zero at zero but not convex.

two : ℚ
two = 1ℚ + 1ℚ

no-expr-denotes-capped : ¬ (Σ PhiExpr (λ e → ∀ x → denote e x ≡ ∣ x ∣ ⊓ 1ℚ))
no-expr-denotes-capped (e , he) = <-irrefl refl (≤-<-trans one≤half half<one)
  where
    hc : denote e (chord ½ 0ℚ two) ≤ chord ½ (denote e 0ℚ) (denote e two)
    hc = denote-convex e ½ 0ℚ two (toWitness {a? = 0ℚ Data.Rational.Properties.≤? ½} tt)
                                   (toWitness {a? = ½ Data.Rational.Properties.≤? 1ℚ} tt)
    one≤half : 1ℚ ≤ ½
    one≤half = subst₂ _≤_ (he (chord ½ 0ℚ two)) (cong₂ (chord ½) (he 0ℚ) (he two)) hc
    half<one : ½ < 1ℚ
    half<one = toWitness {a? = ½ <? 1ℚ} tt
