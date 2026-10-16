-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: UnfoldKleisli.agda
--
-- Twin of Lean/UnfoldKleisli.lean and Coq/UnfoldKleisli.v over exact rationals: a nested solve is refused or done
-- with a value and a spend (measured energy, Landauer floor). L1: bind has unit as left and right identity and is
-- associative, an inner refusal is the outer refusal, an outer spend is the sum of the inner ones. L2: spends form a
-- commutative monoid and honesty (floor ≤ measured) is closed under addition and binding. Error propagation over
-- rational intervals: interval addition encloses sums, tolerances add along a chain, and an inner error within τ_in
-- through an L-Lipschitz map with an outer error within τ_out stays within τ_out + L τ_in.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module UnfoldKleisli where

open import Data.List using (List; []; _∷_; foldr; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_)
open import Data.Rational.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-assoc; +-comm; +-identityˡ; +-identityʳ; neg-distrib-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

------------------------------------------------------------------------
-- Spends

record Spend : Set where
  constructor spend
  field
    measured : ℚ
    floor    : ℚ
open Spend

szero : Spend
szero = spend 0ℚ 0ℚ

sadd : Spend → Spend → Spend
sadd s t = spend (measured s + measured t) (floor s + floor t)

sadd-assoc : ∀ s t u → sadd (sadd s t) u ≡ sadd s (sadd t u)
sadd-assoc (spend a b) (spend c d) (spend e f) = cong₂ spend (+-assoc a c e) (+-assoc b d f)

szero-add : ∀ s → sadd szero s ≡ s
szero-add (spend a b) = cong₂ spend (+-identityˡ a) (+-identityˡ b)

sadd-zero : ∀ s → sadd s szero ≡ s
sadd-zero (spend a b) = cong₂ spend (+-identityʳ a) (+-identityʳ b)

sadd-comm : ∀ s t → sadd s t ≡ sadd t s
sadd-comm (spend a b) (spend c d) = cong₂ spend (+-comm a c) (+-comm b d)

-- A spend is honest when its measured energy is at least its floor.
Honest : Spend → Set
Honest s = floor s ≤ measured s

-- L2: honesty is closed under addition.
honest-add : ∀ {s t} → Honest s → Honest t → Honest (sadd s t)
honest-add hs ht = +-mono-≤ hs ht

honest-zero : Honest szero
honest-zero = ≤-refl

-- L2 for any list of spends: the sum of measured energies is at least the sum of floors.
honest-sum : ∀ l → All Honest l → Honest (foldr sadd szero l)
honest-sum []      []       = honest-zero
honest-sum (s ∷ l) (h ∷ hs) = honest-add h (honest-sum l hs)

------------------------------------------------------------------------
-- Nested solves and Kleisli bind

data Thermo (E A : Set) : Set where
  refused : E → Thermo E A
  done    : A → Spend → Thermo E A

module _ {E : Set} where

  unit : ∀ {A : Set} → A → Thermo E A
  unit a = done a szero

  bind : ∀ {A B : Set} → Thermo E A → (A → Thermo E B) → Thermo E B
  bind (refused e) f = refused e
  bind (done a s)  f with f a
  ... | refused e = refused e
  ... | done b t  = done b (sadd s t)

  kcomp : ∀ {A B C : Set} → (A → Thermo E B) → (B → Thermo E C) → A → Thermo E C
  kcomp f g a = bind (f a) g

  -- L1 left identity.
  unit-bind : ∀ {A B : Set} (a : A) (f : A → Thermo E B) → bind (unit a) f ≡ f a
  unit-bind a f with f a
  ... | refused e = refl
  ... | done b t  = cong (done b) (szero-add t)

  -- L1 right identity.
  bind-unit : ∀ {A : Set} (m : Thermo E A) → bind m unit ≡ m
  bind-unit (refused e) = refl
  bind-unit (done a s)  = cong (done a) (sadd-zero s)

  -- L1 associativity.
  bind-assoc : ∀ {A B C : Set} (m : Thermo E A) (f : A → Thermo E B) (g : B → Thermo E C) →
    bind (bind m f) g ≡ bind m (λ a → bind (f a) g)
  bind-assoc (refused e) f g = refl
  bind-assoc (done a s)  f g with f a
  ... | refused e = refl
  ... | done b t with g b
  ...   | refused e = refl
  ...   | done c u  = cong (done c) (sadd-assoc s t u)

  -- L1 Kleisli composition is associative (pointwise).
  kcomp-assoc : ∀ {A B C D : Set} (f : A → Thermo E B) (g : B → Thermo E C) (h : C → Thermo E D) (a : A) →
    kcomp (kcomp f g) h a ≡ kcomp f (kcomp g h) a
  kcomp-assoc f g h a = bind-assoc (f a) g h

  -- A refusal of an inner solve is the outer solve's refusal.
  bind-inner-refusal : ∀ {A B : Set} (a : A) (s : Spend) (f : A → Thermo E B) (e : E) →
    f a ≡ refused e → bind (done a s) f ≡ refused e
  bind-inner-refusal a s f e h with f a
  bind-inner-refusal a s f e refl | .(refused e) = refl

  -- An outer solve's spend is the sum of its inner spends.
  bind-spend : ∀ {A B : Set} (m : Thermo E A) (f : A → Thermo E B) (b : B) (u : Spend) → bind m f ≡ done b u →
    Σ[ a ∈ A ] Σ[ s ∈ Spend ] Σ[ t ∈ Spend ] (m ≡ done a s × f a ≡ done b t × u ≡ sadd s t)
  bind-spend (refused e) f b u ()
  bind-spend (done a s)  f b u h with f a in eq
  bind-spend (done a s)  f b u () | refused e
  bind-spend (done a s)  f b .(sadd s t) refl | done .b t = a , s , t , refl , eq , refl

  -- Every spend a solve can post is honest.
  HonestT : ∀ {A : Set} → Thermo E A → Set
  HonestT {A} m = ∀ (a : A) s → m ≡ done a s → Honest s

  -- L2 under nesting: honest inner solves bind to an honest outer solve.
  bind-honest : ∀ {A B : Set} (m : Thermo E A) (f : A → Thermo E B) → HonestT m → (∀ a → HonestT (f a)) →
    HonestT (bind m f)
  bind-honest (refused e) f hm hf b u ()
  bind-honest (done a s)  f hm hf b u h with f a | hf a
  bind-honest (done a s)  f hm hf b u () | refused e | _
  bind-honest (done a s)  f hm hf b .(sadd s t) refl | done .b t | hfa =
    honest-add (hm a s refl) (hfa b t refl)

------------------------------------------------------------------------
-- Error propagation over rational intervals

record Interval : Set where
  constructor interval
  field
    lo : ℚ
    hi : ℚ
open Interval

Mem : Interval → ℚ → Set
Mem I x = (lo I ≤ x) × (x ≤ hi I)

iadd : Interval → Interval → Interval
iadd I J = interval (lo I + lo J) (hi I + hi J)

symI : ℚ → Interval
symI τ = interval (- τ) τ

-- Interval addition encloses sums.
mem-add : ∀ {I J x y} → Mem I x → Mem J y → Mem (iadd I J) (x + y)
mem-add (h1 , h2) (h3 , h4) = +-mono-≤ h1 h3 , +-mono-≤ h2 h4

qsum : List ℚ → ℚ
qsum = foldr _+_ 0ℚ

-- −(a + b) = −a + −b, so the sum of two symmetric intervals is symmetric.
private
  symI-add : ∀ a b → iadd (symI a) (symI b) ≡ symI (a + b)
  symI-add a b = cong₂ interval (sym (neg-distrib-+ a b)) refl

  mem-cast : ∀ {I J x} → I ≡ J → Mem I x → Mem J x
  mem-cast refl h = h

-- Tolerance chain: errors each within their tolerance sum within the summed tolerance.
mem-sum-sym : ∀ (l : List (ℚ × ℚ)) → All (λ p → Mem (symI (proj₂ p)) (proj₁ p)) l →
  Mem (symI (qsum (map proj₂ l))) (qsum (map proj₁ l))
mem-sum-sym []            []       = ≤-reflexive refl , ≤-refl
mem-sum-sym ((e , τ) ∷ l) (h ∷ hs) = mem-cast (symI-add τ (qsum (map proj₂ l))) (mem-add h (mem-sum-sym l hs))

-- Error propagation: within τ_out + L τ_in.
error-chain : ∀ (L τin τout ystar yhat z : ℚ) (g : ℚ → ℚ) → Mem (symI τin) (yhat - ystar) →
  (∀ x y → Mem (symI τin) (x - y) → Mem (symI (L * τin)) (g x - g y)) →
  Mem (symI τout) (z - g yhat) → Mem (symI (τout + L * τin)) (z - g ystar)
error-chain L τin τout ystar yhat z g hin hlip hout =
  mem-cast (symI-add τout (L * τin))
    (subst-x (mem-add hout (hlip yhat ystar hin)))
  where
    open import Data.Rational.Solver using (module +-*-Solver)
    open +-*-Solver
    telescope : (z - g yhat) + (g yhat - g ystar) ≡ z - g ystar
    telescope = solve 3 (λ z a b → (z :- a) :+ (a :- b) := z :- b) refl z (g yhat) (g ystar)
    subst-x : ∀ {I} → Mem I ((z - g yhat) + (g yhat - g ystar)) → Mem I (z - g ystar)
    subst-x (h1 , h2) = ≤-trans h1 (≤-reflexive telescope) , ≤-trans (≤-reflexive (sym telescope)) h2
