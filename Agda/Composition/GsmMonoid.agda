-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Composition.GsmMonoid — the composition law of GSM atoms and the glue fraction (twin of
-- Lean/Composition/GsmMonoid.lean and Coq/Composition/GsmMonoid.v, W-44).
--
-- Agda carries a GSM potential over the rationals in supporting-line form: φ with a slope dφ such that
-- φ x + dφ x · (y − x) ≤ φ y for all x, y (convexity with a subgradient), φ ≥ 0 and φ 0 = 0. The power at rate x
-- is D = x · dφ x, and the supporting line at x through 0 gives D ≥ φ x ≥ 0.
--
-- Potentials and atoms (a convex ψ with a potential) form commutative monoids under pointwise sum and cones under
-- non-negative scaling, up to pointwise equality; the power is additive and homogeneous (a monoid homomorphism to
-- the non-negative rationals); the atoms passing one passive step are closed under sum, scaling and the empty
-- composite, and the composite step is a transition case of SecondLaw. A convex glue term keeps admissibility; an
-- arbitrary glue term needs its own witness. The standard library divides only by a value with a NonZero instance,
-- so the glue-fraction bounds are stated cross-multiplied: |D_glue| ≤ D_total is the fraction ≤ 1 for D_total > 0.
------------------------------------------------------------------------

module Composition.GsmMonoid where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; foldr)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_; _-_; -_; ∣_∣; NonNegative; nonNegative; _<?_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans; <-≤-trans; <-irrefl; ≮⇒≥;
  +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-mono-≤-<; +-identityˡ; +-identityʳ; +-inverseʳ; +-assoc; +-comm;
  *-zeroʳ; *-distribˡ-+; *-monoˡ-≤-nonNeg; neg-antimono-≤; 0≤p⇒∣p∣≡p; ∣p∣≡0⇒p≡0; 0≤∣p∣)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (toWitness)

open import Concrete.Gate using (mkState)
open import Core.Gate using (δ-mass; CoreAdmissible)
open import Process using (SecondLaw; transition; thermodynamic)

open +-*-Solver

------------------------------------------------------------------------
-- Supporting lines (convexity with a subgradient) are closed under sum and non-negative scaling.
------------------------------------------------------------------------

Supports : (ℚ → ℚ) → (ℚ → ℚ) → Set
Supports f df = ∀ x y → f x + df x * (y - x) ≤ f y

supports-zero : Supports (λ _ → 0ℚ) (λ _ → 0ℚ)
supports-zero x y = ≤-reflexive (solve 2 (λ x y → con 0ℚ :+ con 0ℚ :* (y :- x) := con 0ℚ) refl x y)

supports-add : ∀ {f df g dg} → Supports f df → Supports g dg → Supports (λ x → f x + g x) (λ x → df x + dg x)
supports-add {f} {df} {g} {dg} sf sg x y =
  subst (_≤ f y + g y) (sym (split (f x) (g x) (df x) (dg x) x y)) (+-mono-≤ (sf x y) (sg x y))
  where
    split : ∀ a b c d x y → a + b + (c + d) * (y - x) ≡ (a + c * (y - x)) + (b + d * (y - x))
    split = solve 6 (λ a b c d x y → a :+ b :+ (c :+ d) :* (y :- x) := (a :+ c :* (y :- x)) :+ (b :+ d :* (y :- x)))
              refl

supports-scale : ∀ c → 0ℚ ≤ c → ∀ {f df} → Supports f df → Supports (λ x → c * f x) (λ x → c * df x)
supports-scale c hc {f} {df} sf x y =
  subst (_≤ c * f y) (sym (factor c (f x) (df x) x y)) (*-monoˡ-≤-nonNeg c (sf x y))
  where
    instance
      nn : NonNegative c
      nn = nonNegative hc
    factor : ∀ c a d x y → c * a + c * d * (y - x) ≡ c * (a + d * (y - x))
    factor = solve 5 (λ c a d x y → c :* a :+ c :* d :* (y :- x) := c :* (a :+ d :* (y :- x))) refl

-- Scaling by c ≥ 0 keeps a non-negative value non-negative.
scale-nonneg : ∀ c → 0ℚ ≤ c → ∀ {a} → 0ℚ ≤ a → 0ℚ ≤ c * a
scale-nonneg c hc {a} ha = subst (_≤ c * a) (*-zeroʳ c) (*-monoˡ-≤-nonNeg c ha)
  where
    instance
      nn : NonNegative c
      nn = nonNegative hc

------------------------------------------------------------------------
-- Potentials
------------------------------------------------------------------------

record GsmPotential : Set where
  field
    φ        : ℚ → ℚ
    dφ       : ℚ → ℚ
    support  : Supports φ dφ
    φ-nonneg : ∀ x → 0ℚ ≤ φ x
    φ-zero   : φ 0ℚ ≡ 0ℚ

open GsmPotential

-- Dissipation power at rate x.
power : GsmPotential → ℚ → ℚ
power P x = x * dφ P x

-- The supporting line at x through 0: φ x ≤ x · dφ x.
φ≤power : ∀ P x → φ P x ≤ power P x
φ≤power P x = subst₂ _≤_ (e₁ (φ P x) (dφ P x) x) (+-identityˡ (x * dφ P x)) (+-monoˡ-≤ (x * dφ P x) h)
  where
    h : φ P x + dφ P x * (0ℚ - x) ≤ 0ℚ
    h = subst (φ P x + dφ P x * (0ℚ - x) ≤_) (φ-zero P) (support P x 0ℚ)
    e₁ : ∀ a d x → a + d * (0ℚ - x) + x * d ≡ a
    e₁ = solve 3 (λ a d x → a :+ d :* (con 0ℚ :- x) :+ x :* d := a) refl

-- Non-negative dissipation from a convex, non-negative potential pinned at zero.
power-nonneg : ∀ P x → 0ℚ ≤ power P x
power-nonneg P x = ≤-trans (φ-nonneg P x) (φ≤power P x)

pot-zero : GsmPotential
pot-zero = record
  { φ = λ _ → 0ℚ ; dφ = λ _ → 0ℚ ; support = supports-zero ; φ-nonneg = λ _ → ≤-refl ; φ-zero = refl }

pot-add : GsmPotential → GsmPotential → GsmPotential
pot-add P R = record
  { φ        = λ x → φ P x + φ R x
  ; dφ       = λ x → dφ P x + dφ R x
  ; support  = supports-add {φ P} {dφ P} {φ R} {dφ R} (support P) (support R)
  ; φ-nonneg = λ x → subst (_≤ φ P x + φ R x) (+-identityʳ 0ℚ) (+-mono-≤ (φ-nonneg P x) (φ-nonneg R x))
  ; φ-zero   = trans (cong₂ _+_ (φ-zero P) (φ-zero R)) (+-identityʳ 0ℚ)
  }

pot-scale : ∀ c → 0ℚ ≤ c → GsmPotential → GsmPotential
pot-scale c hc P = record
  { φ        = λ x → c * φ P x
  ; dφ       = λ x → c * dφ P x
  ; support  = supports-scale c hc (support P)
  ; φ-nonneg = λ x → scale-nonneg c hc (φ-nonneg P x)
  ; φ-zero   = trans (cong (c *_) (φ-zero P)) (*-zeroʳ c)
  }

-- Pointwise equality of potentials.
PotEq : GsmPotential → GsmPotential → Set
PotEq P R = ∀ x → φ P x ≡ φ R x × dφ P x ≡ dφ R x

pot-add-assoc : ∀ P R S → PotEq (pot-add (pot-add P R) S) (pot-add P (pot-add R S))
pot-add-assoc P R S x = +-assoc (φ P x) (φ R x) (φ S x) , +-assoc (dφ P x) (dφ R x) (dφ S x)

pot-add-comm : ∀ P R → PotEq (pot-add P R) (pot-add R P)
pot-add-comm P R x = +-comm (φ P x) (φ R x) , +-comm (dφ P x) (dφ R x)

pot-zero-add : ∀ P → PotEq (pot-add pot-zero P) P
pot-zero-add P x = +-identityˡ (φ P x) , +-identityˡ (dφ P x)

pot-scale-add : ∀ c (hc : 0ℚ ≤ c) P R → PotEq (pot-scale c hc (pot-add P R)) (pot-add (pot-scale c hc P) (pot-scale c hc R))
pot-scale-add c hc P R x = *-distribˡ-+ c (φ P x) (φ R x) , *-distribˡ-+ c (dφ P x) (dφ R x)

-- The power is a monoid homomorphism into the non-negative rationals: zero, additive, homogeneous.
power-zero : ∀ x → power pot-zero x ≡ 0ℚ
power-zero x = *-zeroʳ x

power-add : ∀ P R x → power (pot-add P R) x ≡ power P x + power R x
power-add P R x = *-distribˡ-+ x (dφ P x) (dφ R x)

power-scale : ∀ c (hc : 0ℚ ≤ c) P x → power (pot-scale c hc P) x ≡ c * power P x
power-scale c hc P x = solve 3 (λ x c d → x :* (c :* d) := c :* (x :* d)) refl x c (dφ P x)

------------------------------------------------------------------------
-- Atoms and the admissible cone
------------------------------------------------------------------------

record GsmAtom : Set where
  field
    ψ         : ℚ → ℚ
    dψ        : ℚ → ℚ
    ψ-support : Supports ψ dψ
    pot       : GsmPotential

open GsmAtom

atom-zero : GsmAtom
atom-zero = record { ψ = λ _ → 0ℚ ; dψ = λ _ → 0ℚ ; ψ-support = supports-zero ; pot = pot-zero }

atom-add : GsmAtom → GsmAtom → GsmAtom
atom-add A B = record
  { ψ = λ x → ψ A x + ψ B x ; dψ = λ x → dψ A x + dψ B x
  ; ψ-support = supports-add {ψ A} {dψ A} {ψ B} {dψ B} (ψ-support A) (ψ-support B) ; pot = pot-add (pot A) (pot B) }

atom-scale : ∀ c → 0ℚ ≤ c → GsmAtom → GsmAtom
atom-scale c hc A = record
  { ψ = λ x → c * ψ A x ; dψ = λ x → c * dψ A x
  ; ψ-support = supports-scale c hc (ψ-support A) ; pot = pot-scale c hc (pot A) }

-- A passive step of an atom: internal variable s → s′ at rate r with Δψ + D ≤ 0.
PassiveStep : ℚ → ℚ → ℚ → GsmAtom → Set
PassiveStep s s' r A = (ψ A s' - ψ A s) + power (pot A) r ≤ 0ℚ

passive-zero : ∀ s s' r → PassiveStep s s' r atom-zero
passive-zero s s' r = ≤-reflexive (solve 1 (λ r → (con 0ℚ :- con 0ℚ) :+ r :* con 0ℚ := con 0ℚ) refl r)

passive-add : ∀ s s' r A B → PassiveStep s s' r A → PassiveStep s s' r B → PassiveStep s s' r (atom-add A B)
passive-add s s' r A B hA hB =
  subst (_≤ 0ℚ) (sym (split (ψ A s') (ψ A s) (ψ B s') (ψ B s) r (dφ (pot A) r) (dφ (pot B) r)))
    (subst ((ψ A s' - ψ A s) + power (pot A) r + ((ψ B s' - ψ B s) + power (pot B) r) ≤_) (+-identityʳ 0ℚ)
      (+-mono-≤ hA hB))
  where
    split : ∀ a₁ a₀ b₁ b₀ r d e →
      (a₁ + b₁ - (a₀ + b₀)) + r * (d + e) ≡ ((a₁ - a₀) + r * d) + ((b₁ - b₀) + r * e)
    split = solve 7 (λ a₁ a₀ b₁ b₀ r d e →
      (a₁ :+ b₁ :- (a₀ :+ b₀)) :+ r :* (d :+ e) := ((a₁ :- a₀) :+ r :* d) :+ ((b₁ :- b₀) :+ r :* e)) refl

passive-scale : ∀ s s' r c (hc : 0ℚ ≤ c) A → PassiveStep s s' r A → PassiveStep s s' r (atom-scale c hc A)
passive-scale s s' r c hc A hA =
  subst₂ _≤_ (sym (factor c (ψ A s') (ψ A s) r (dφ (pot A) r))) (*-zeroʳ c) (*-monoˡ-≤-nonNeg c hA)
  where
    instance
      nn : NonNegative c
      nn = nonNegative hc
    factor : ∀ c a₁ a₀ r d → (c * a₁ - c * a₀) + r * (c * d) ≡ c * ((a₁ - a₀) + r * d)
    factor = solve 5 (λ c a₁ a₀ r d → (c :* a₁ :- c :* a₀) :+ r :* (c :* d) := c :* ((a₁ :- a₀) :+ r :* d)) refl

-- The composite of a list of atoms (each already scaled by its non-negative coefficient).
atom-sum : List GsmAtom → GsmAtom
atom-sum = foldr atom-add atom-zero

-- Composition law (W-44): a composite of atoms that each pass the step passes it.
passive-sum : ∀ s s' r (As : List GsmAtom) → All (PassiveStep s s' r) As → PassiveStep s s' r (atom-sum As)
passive-sum s s' r []       []         = passive-zero s s' r
passive-sum s s' r (A ∷ As) (hA ∷ hAs) = passive-add s s' r A (atom-sum As) hA (passive-sum s s' r As hAs)

-- The composite's dissipation is the sum of the atoms' dissipations.
power-sum : ∀ (As : List GsmAtom) r → power (pot (atom-sum As)) r ≡ foldr (λ A acc → power (pot A) r + acc) 0ℚ As
power-sum []       r = *-zeroʳ r
power-sum (A ∷ As) r = trans (power-add (pot A) (pot (atom-sum As)) r) (cong (power (pot A) r +_) (power-sum As r))

------------------------------------------------------------------------
-- The bridge to SecondLaw
------------------------------------------------------------------------

-- Δψ + D ≤ 0 with D ≥ 0 gives descent: b ≤ a.
descent : ∀ {a b d} → 0ℚ ≤ d → (b - a) + d ≤ 0ℚ → b ≤ a
descent {a} {b} {d} hd h =
  ≤-trans (subst₂ _≤_ (e₁ a b d) (+-identityˡ (a - d)) (+-monoˡ-≤ (a - d) h))
          (subst (a - d ≤_) (+-identityʳ a) (+-monoʳ-≤ a (neg-antimono-≤ hd)))
  where
    e₁ : ∀ a b d → (b - a) + d + (a - d) ≡ b
    e₁ = solve 3 (λ a b d → (b :- a) :+ d :+ (a :- d) := b) refl

MassBall : ℚ → ℚ → Set
MassBall ρ ρ' = (ρ' - ρ ≤ δ-mass) × (ρ - ρ' ≤ δ-mass)

passiveStep-secondLaw : ∀ A {s s' r ρ ρ'} → MassBall ρ ρ' → PassiveStep s s' r A →
  SecondLaw transition (thermodynamic (mkState ρ (ψ A s) 0ℚ 0ℚ) (mkState ρ' (ψ A s') 0ℚ 0ℚ))
passiveStep-secondLaw A {r = r} m h = record
  { mass-conserved = m ; dissipation-nonneg = descent (power-nonneg (pot A) r) h }

-- The composite step of passing atoms satisfies the second law.
combination-secondLaw : ∀ (As : List GsmAtom) {s s' r ρ ρ'} → MassBall ρ ρ' → All (PassiveStep s s' r) As →
  SecondLaw transition
    (thermodynamic (mkState ρ (ψ (atom-sum As) s) 0ℚ 0ℚ) (mkState ρ' (ψ (atom-sum As) s') 0ℚ 0ℚ))
combination-secondLaw As {s} {s'} {r} m h = passiveStep-secondLaw (atom-sum As) {s} {s'} {r} m (passive-sum s s' r As h)

------------------------------------------------------------------------
-- Glue
------------------------------------------------------------------------

-- A convex glue term is an atom with zero free energy.
glue-atom : GsmPotential → GsmAtom
glue-atom G = record { ψ = λ _ → 0ℚ ; dψ = λ _ → 0ℚ ; ψ-support = supports-zero ; pot = G }

-- Convex glue keeps admissibility: D_glue ≥ 0 and the composite with the glue atom passes the step.
convexGlue-secondLaw : ∀ A G {s s' r ρ ρ'} → MassBall ρ ρ' →
  (ψ A s' - ψ A s) + (power (pot A) r + power G r) ≤ 0ℚ →
  0ℚ ≤ power G r ×
  SecondLaw transition
    (thermodynamic (mkState ρ (ψ (atom-add A (glue-atom G)) s) 0ℚ 0ℚ)
                   (mkState ρ' (ψ (atom-add A (glue-atom G)) s') 0ℚ 0ℚ))
convexGlue-secondLaw A G {s} {s'} {r} m hb =
  power-nonneg G r ,
  passiveStep-secondLaw (atom-add A (glue-atom G)) {s} {s'} {r} m
    (subst (_≤ 0ℚ) (sym (split (ψ A s') (ψ A s) r (dφ (pot A) r) (dφ G r))) hb)
  where
    split : ∀ a₁ a₀ r d e → (a₁ + 0ℚ - (a₀ + 0ℚ)) + r * (d + e) ≡ (a₁ - a₀) + (r * d + r * e)
    split = solve 5 (λ a₁ a₀ r d e →
      (a₁ :+ con 0ℚ :- (a₀ :+ con 0ℚ)) :+ r :* (d :+ e) := (a₁ :- a₀) :+ (r :* d :+ r :* e)) refl

-- An arbitrary glue term with a witness 0 ≤ D_total is admissible.
glued-secondLaw-of-witness : ∀ {dA dG ρ ρ' ψ₀ ψ₁} → MassBall ρ ρ' → 0ℚ ≤ dA + dG → (ψ₁ - ψ₀) + (dA + dG) ≤ 0ℚ →
  SecondLaw transition (thermodynamic (mkState ρ ψ₀ 0ℚ 0ℚ) (mkState ρ' ψ₁ 0ℚ 0ℚ))
glued-secondLaw-of-witness m hw hb = record { mass-conserved = m ; dissipation-nonneg = descent hw hb }

-- Without a witness, a negative total under the passive equality balance is refused.
glued-refused-of-negative-total : ∀ {dA dG ρ ρ' ψ₀ ψ₁} → dA + dG < 0ℚ → (ψ₁ - ψ₀) + (dA + dG) ≡ 0ℚ →
  ¬ SecondLaw transition (thermodynamic (mkState ρ ψ₀ 0ℚ 0ℚ) (mkState ρ' ψ₁ 0ℚ 0ℚ))
glued-refused-of-negative-total {dA} {dG} {ψ₀ = ψ₀} {ψ₁} hn hb h = <-irrefl refl (subst₂ _<_ hb (+-identityʳ 0ℚ) lt)
  where
    Δ≤0 : ψ₁ - ψ₀ ≤ 0ℚ
    Δ≤0 = subst (ψ₁ - ψ₀ ≤_) (+-inverseʳ ψ₀) (+-monoˡ-≤ (- ψ₀) (CoreAdmissible.dissipation-nonneg h))
    lt : (ψ₁ - ψ₀) + (dA + dG) < 0ℚ + 0ℚ
    lt = +-mono-≤-< Δ≤0 hn

-- An arbitrary glue term is not closed under the law.
arbitrary-glue-not-closed : ∃[ dA ] ∃[ dG ] ∃[ ψ₀ ] ∃[ ψ₁ ]
  (0ℚ ≤ dA × (ψ₁ - ψ₀) + (dA + dG) ≡ 0ℚ × ¬ SecondLaw transition (thermodynamic (mkState 0ℚ ψ₀ 0ℚ 0ℚ) (mkState 0ℚ ψ₁ 0ℚ 0ℚ)))
arbitrary-glue-not-closed =
  0ℚ , - 1ℚ , 0ℚ , 1ℚ , ≤-refl , refl ,
  glued-refused-of-negative-total {0ℚ} { - 1ℚ} (toWitness {a? = 0ℚ + - 1ℚ <? 0ℚ} _) refl

-- Glue within the total: |D_glue| ≤ D_total, the glue fraction ≤ 1 cross-multiplied. A convex glue term satisfies it.
glue-within-total : ∀ {dA dG} → 0ℚ ≤ dA → 0ℚ ≤ dG → 0ℚ ≤ ∣ dG ∣ × ∣ dG ∣ ≤ dA + dG
glue-within-total {dA} {dG} hA hG =
  0≤∣p∣ dG , subst (_≤ dA + dG) (trans (+-identityˡ dG) (sym (0≤p⇒∣p∣≡p hG))) (+-monoˡ-≤ dG hA)

-- The glue fraction vanishes exactly when the glue dissipation does.
glue-free-iff : ∀ dG → (∣ dG ∣ ≡ 0ℚ → dG ≡ 0ℚ) × (dG ≡ 0ℚ → ∣ dG ∣ ≡ 0ℚ)
glue-free-iff dG = ∣p∣≡0⇒p≡0 dG , λ { refl → refl }

-- A glue term exceeding the total signals a negative glue term (with non-negative atom dissipation).
glue-neg-of-exceeds-total : ∀ {dA dG} → 0ℚ ≤ dA → dA + dG < ∣ dG ∣ → dG < 0ℚ
glue-neg-of-exceeds-total {dA} {dG} hA h with dG <? 0ℚ
... | yes neg = neg
... | no ¬neg =
  ⊥-elim (<-irrefl refl (<-≤-trans h (proj₂ (glue-within-total {dA} {dG} hA (≮⇒≥ ¬neg)))))
