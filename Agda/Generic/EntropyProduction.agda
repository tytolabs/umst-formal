-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- Generic.EntropyProduction — the GENERIC form and its entropy-production theorem over exact rationals (twin of
-- Lean/Generic/EntropyProduction.lean and Coq/Generic/EntropyProduction.v).
--
-- GENERIC (Grmela and Öttinger, Phys. Rev. E 56, 6620 and 6633 (1997)) writes the rate of an n-coordinate state as
-- L·∇E + M·∇S with L antisymmetric, M symmetric positive semidefinite, L·∇S = 0 and M·∇E = 0. At one state the
-- energy rate ∇E·(L∇E + M∇S) is zero and the entropy rate ∇S·(L∇E + M∇S) = ∇S·M∇S is nonnegative. The bridge to
-- SecondLaw takes a reservoir temperature T ≥ 0 (free energy E − T·S), a step of length h ≥ 0 whose free energy
-- changes by h times the free-energy rate, and the mass condition, which GENERIC does not supply.
------------------------------------------------------------------------

module Generic.EntropyProduction where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _≤_; _+_; _*_; _-_; -_)
open import Data.Rational.Properties using (≤-trans; +-identityʳ; +-inverseʳ; *-zeroˡ; *-zeroʳ; +-monoʳ-≤)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Concrete.Gate using (ThermodynamicState)
open import Core.Gate using (δ-mass)
open import Process using (SecondLaw; transition; thermodynamic)
open import Convex.PhiGrammar using (gap; gap⁻¹; mul-nonneg)

open +-*-Solver

------------------------------------------------------------------------
-- Finite sums, pairings and matrices on n coordinates

Vec : ℕ → Set
Vec n = Fin n → ℚ

Mat : ℕ → Set
Mat n = Fin n → Fin n → ℚ

sum : ∀ {n} → Vec n → ℚ
sum {zero}  f = 0ℚ
sum {suc n} f = f zero + sum (λ i → f (suc i))

dot : ∀ {n} → Vec n → Vec n → ℚ
dot u v = sum (λ i → u i * v i)

mulVec : ∀ {n} → Mat n → Vec n → Vec n
mulVec A v i = sum (λ j → A i j * v j)

transpose : ∀ {n} → Mat n → Mat n
transpose A i j = A j i

sum-cong : ∀ {n} {f g : Vec n} → (∀ i → f i ≡ g i) → sum f ≡ sum g
sum-cong {zero}  h = refl
sum-cong {suc n} h = cong₂ _+_ (h zero) (sum-cong (λ i → h (suc i)))

sum-add : ∀ {n} (f g : Vec n) → sum (λ i → f i + g i) ≡ sum f + sum g
sum-add {zero}  f g = refl
sum-add {suc n} f g = trans (cong (f zero + g zero +_) (sum-add (λ i → f (suc i)) (λ i → g (suc i))))
                            (shuffle (f zero) (g zero) _ _)
  where
    shuffle : ∀ a b c d → a + b + (c + d) ≡ a + c + (b + d)
    shuffle = solve 4 (λ a b c d → a :+ b :+ (c :+ d) := a :+ c :+ (b :+ d)) refl

sum-scal : ∀ {n} (c : ℚ) (f : Vec n) → sum (λ i → c * f i) ≡ c * sum f
sum-scal {zero}  c f = sym (*-zeroʳ c)
sum-scal {suc n} c f = trans (cong (c * f zero +_) (sum-scal c (λ i → f (suc i)))) (distr c (f zero) _)
  where
    distr : ∀ c a b → c * a + c * b ≡ c * (a + b)
    distr = solve 3 (λ c a b → c :* a :+ c :* b := c :* (a :+ b)) refl

sum-zero : ∀ {n} (f : Vec n) → (∀ i → f i ≡ 0ℚ) → sum f ≡ 0ℚ
sum-zero {zero}  f h = refl
sum-zero {suc n} f h = trans (cong₂ _+_ (h zero) (sum-zero (λ i → f (suc i)) (λ i → h (suc i)))) refl

sum-swap : ∀ {n m} (f : Fin n → Fin m → ℚ) → sum (λ i → sum (λ j → f i j)) ≡ sum (λ j → sum (λ i → f i j))
sum-swap {zero}  {m} f = sym (sum-zero {m} (λ j → 0ℚ) (λ j → refl))
sum-swap {suc n} {m} f =
  trans (cong (sum (λ j → f zero j) +_) (sum-swap (λ i j → f (suc i) j)))
        (sym (sum-add (λ j → f zero j) (λ j → sum (λ i → f (suc i) j))))

-- u·(A·w) = (Aᵀ·u)·w
pair-transpose : ∀ {n} (A : Mat n) (u w : Vec n) → dot u (mulVec A w) ≡ dot (mulVec (transpose A) u) w
pair-transpose A u w =
  trans (sum-cong (λ i → trans (sym (sum-scal (u i) (λ j → A i j * w j))) (sum-cong (λ j → assoc₁ (u i) (A i j) (w j)))))
    (trans (sum-swap (λ i j → u i * A i j * w j))
      (sym (sum-cong (λ j → trans (*-comm' (sum (λ i → A i j * u i)) (w j))
        (trans (sym (sum-scal (w j) (λ i → A i j * u i))) (sum-cong (λ i → assoc₂ (w j) (A i j) (u i))))))))
  where
    assoc₁ : ∀ a b c → a * (b * c) ≡ a * b * c
    assoc₁ = solve 3 (λ a b c → a :* (b :* c) := a :* b :* c) refl
    assoc₂ : ∀ c b a → c * (b * a) ≡ a * b * c
    assoc₂ = solve 3 (λ c b a → c :* (b :* a) := a :* b :* c) refl
    *-comm' : ∀ a b → a * b ≡ b * a
    *-comm' = solve 2 (λ a b → a :* b := b :* a) refl

dot-comm : ∀ {n} (u v : Vec n) → dot u v ≡ dot v u
dot-comm u v = sum-cong (λ i → comm (u i) (v i))
  where
    comm : ∀ a b → a * b ≡ b * a
    comm = solve 2 (λ a b → a :* b := b :* a) refl

dot-add : ∀ {n} (u v w : Vec n) → dot u (λ i → v i + w i) ≡ dot u v + dot u w
dot-add u v w = trans (sum-cong (λ i → distr (u i) (v i) (w i))) (sum-add (λ i → u i * v i) (λ i → u i * w i))
  where
    distr : ∀ a b c → a * (b + c) ≡ a * b + a * c
    distr = solve 3 (λ a b c → a :* (b :+ c) := a :* b :+ a :* c) refl

dot-zeroˡ : ∀ {n} (u v : Vec n) → (∀ i → u i ≡ 0ℚ) → dot u v ≡ 0ℚ
dot-zeroˡ u v h = sum-zero _ (λ i → trans (cong (_* v i) (h i)) (*-zeroˡ (v i)))

------------------------------------------------------------------------
-- The GENERIC conditions at one state

record GenericAt {n} (L M : Mat n) (dE dS : Vec n) : Set where
  field
    antisymm : ∀ i j → L j i ≡ - L i j
    symm     : ∀ i j → M j i ≡ M i j
    psd      : ∀ v → 0ℚ ≤ dot v (mulVec M v)
    degenL   : ∀ i → mulVec L dS i ≡ 0ℚ
    degenM   : ∀ i → mulVec M dE i ≡ 0ℚ

open GenericAt

genericField : ∀ {n} → Mat n → Mat n → Vec n → Vec n → Vec n
genericField L M dE dS i = mulVec L dE i + mulVec M dS i

transpose-antisymm : ∀ {n} (L : Mat n) (v : Vec n) → (∀ i j → L j i ≡ - L i j) →
  ∀ i → mulVec (transpose L) v i ≡ - mulVec L v i
transpose-antisymm L v hL i =
  trans (sum-cong (λ j → trans (cong (_* v j) (hL i j)) (neg (L i j) (v j))))
        (trans (sum-scal (- 1ℚ) (λ j → L i j * v j)) (neg1 (mulVec L v i)))
  where
    neg : ∀ a b → (- a) * b ≡ (- 1ℚ) * (a * b)
    neg = solve 2 (λ a b → (:- a) :* b := (:- con 1ℚ) :* (a :* b)) refl
    neg1 : ∀ a → (- 1ℚ) * a ≡ - a
    neg1 = solve 1 (λ a → (:- con 1ℚ) :* a := :- a) refl

transpose-symm : ∀ {n} (M : Mat n) (v : Vec n) → (∀ i j → M j i ≡ M i j) → ∀ i → mulVec (transpose M) v i ≡ mulVec M v i
transpose-symm M v hM i = sum-cong (λ j → cong (_* v j) (hM i j))

-- x ≡ − x gives x ≡ 0.
self-neg-zero : ∀ x → x ≡ - x → x ≡ 0ℚ
self-neg-zero x h = trans (half x) (trans (cong (λ z → ½ * (x + z)) h) (trans (cong (½ *_) (+-inverseʳ x)) (*-zeroʳ ½)))
  where
    half : ∀ x → x ≡ ½ * (x + x)
    half = solve 1 (λ x → x := con ½ :* (x :+ x)) refl

-- An antisymmetric operator pairs every vector with itself to zero.
antisymm-pair-self : ∀ {n} (L : Mat n) (v : Vec n) → (∀ i j → L j i ≡ - L i j) → dot v (mulVec L v) ≡ 0ℚ
antisymm-pair-self L v hL = self-neg-zero _ (trans (pair-transpose L v v) (trans (sum-cong (λ i →
  trans (cong (_* v i) (transpose-antisymm L v hL i)) (negmul (mulVec L v i) (v i))))
  (trans (sum-scal (- 1ℚ) (λ i → mulVec L v i * v i)) (trans (neg1 _) (cong -_ (dot-comm (mulVec L v) v))))))
  where
    negmul : ∀ a b → (- a) * b ≡ (- 1ℚ) * (a * b)
    negmul = solve 2 (λ a b → (:- a) :* b := (:- con 1ℚ) :* (a :* b)) refl
    neg1 : ∀ a → (- 1ℚ) * a ≡ - a
    neg1 = solve 1 (λ a → (:- con 1ℚ) :* a := :- a) refl

-- Energy conservation: ∇E·(L∇E + M∇S) = 0.
energy-rate-zero : ∀ {n} {L M : Mat n} {dE dS : Vec n} → GenericAt L M dE dS → dot dE (genericField L M dE dS) ≡ 0ℚ
energy-rate-zero {L = L} {M} {dE} {dS} h =
  trans (dot-add dE (mulVec L dE) (mulVec M dS))
    (trans (cong₂ _+_ (antisymm-pair-self L dE (antisymm h))
             (trans (pair-transpose M dE dS)
               (dot-zeroˡ _ dS (λ i → trans (transpose-symm M dE (symm h) i) (degenM h i)))))
      refl)

-- The entropy rate is the friction pairing ∇S·M∇S.
entropy-rate-eq : ∀ {n} {L M : Mat n} {dE dS : Vec n} → GenericAt L M dE dS →
  dot dS (genericField L M dE dS) ≡ dot dS (mulVec M dS)
entropy-rate-eq {L = L} {M} {dE} {dS} h =
  trans (dot-add dS (mulVec L dE) (mulVec M dS))
    (trans (cong (_+ dot dS (mulVec M dS))
             (trans (pair-transpose L dS dE)
               (dot-zeroˡ _ dE (λ i → trans (transpose-antisymm L dS (antisymm h) i) (cong -_ (degenL h i))))))
      (zero-add (dot dS (mulVec M dS))))
  where
    zero-add : ∀ p → 0ℚ + p ≡ p
    zero-add = solve 1 (λ p → con 0ℚ :+ p := p) refl

-- Entropy production: ∇S·(L∇E + M∇S) ≥ 0.
entropy-rate-nonneg : ∀ {n} {L M : Mat n} {dE dS : Vec n} → GenericAt L M dE dS → 0ℚ ≤ dot dS (genericField L M dE dS)
entropy-rate-nonneg {M = M} {dS = dS} h = subst (0ℚ ≤_) (sym (entropy-rate-eq h)) (psd h dS)

-- At a reservoir temperature T ≥ 0 the free-energy rate Ė − T·Ṡ is not positive.
free-energy-rate-nonpos : ∀ {n} {L M : Mat n} {dE dS : Vec n} (T : ℚ) → GenericAt L M dE dS → 0ℚ ≤ T →
  0ℚ ≤ T * dot dS (genericField L M dE dS) - dot dE (genericField L M dE dS)
free-energy-rate-nonpos {L = L} {M} {dE} {dS} T h hT =
  subst (0ℚ ≤_) (sym (trans (cong (λ z → T * dot dS (genericField L M dE dS) - z) (energy-rate-zero h)) (sub0 _)))
    (mul-nonneg hT (entropy-rate-nonneg h))
  where
    sub0 : ∀ p → p - 0ℚ ≡ p
    sub0 = solve 1 (λ p → p :- con 0ℚ := p) refl

-- Bridge to the second law: a step of length h ≥ 0 whose free energy changes by h times the GENERIC free-energy
-- rate at reservoir temperature T ≥ 0, with the mass condition, is a transition case of SecondLaw. The temperature,
-- the step and the mass condition are the hypotheses GENERIC does not supply.
generic-second-law : ∀ {n} {L M : Mat n} {dE dS : Vec n} (T step : ℚ) (old new : ThermodynamicState) →
  GenericAt L M dE dS → 0ℚ ≤ T → 0ℚ ≤ step →
  (ThermodynamicState.density new - ThermodynamicState.density old ≤ δ-mass) →
  (ThermodynamicState.density old - ThermodynamicState.density new ≤ δ-mass) →
  ThermodynamicState.free-energy new ≡
    ThermodynamicState.free-energy old - step * (T * dot dS (genericField L M dE dS) - dot dE (genericField L M dE dS)) →
  SecondLaw transition (thermodynamic old new)
generic-second-law {L = L} {M} {dE} {dS} T step old new h hT hstep hm₁ hm₂ hψ =
  record { mass-conserved = hm₁ , hm₂ ; dissipation-nonneg = descent }
  where
    ψo = ThermodynamicState.free-energy old
    r = T * dot dS (genericField L M dE dS) - dot dE (genericField L M dE dS)
    hd : 0ℚ ≤ step * r
    hd = mul-nonneg hstep (free-energy-rate-nonpos T h hT)
    descent : ThermodynamicState.free-energy new ≤ ψo
    descent = subst (_≤ ψo) (sym hψ) (gap _ _ (subst (0ℚ ≤_) (eq ψo (step * r)) hd))
      where
        eq : ∀ o d → d ≡ o - (o - d)
        eq = solve 2 (λ o d → d := o :- (o :- d)) refl
