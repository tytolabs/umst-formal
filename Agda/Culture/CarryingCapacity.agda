-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: Culture/CarryingCapacity.agda
--
-- Twin of Lean/Culture/CarryingCapacity.lean and Coq/Culture/CarryingCapacity.v over exact rationals, with ln 2 a
-- parameter l and bounds with a division stated with cleared denominators: an age cap τ bounds the live ticks of a
-- window by τ (D_T + N_T); erasing D bits at a cost of at least D l, with at most i D l recovered and the net paid by
-- T W, gives D l (1 − i) ≤ T W; so l (1 − i) Σ_t N_t ≤ τ (T W + l (1 − i) N_T), and with a lower enclosure
-- l_lo ≤ l of ln 2 the same bound holds with l_lo.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Culture.CarryingCapacity where

open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _≤_; _<_; nonNegative)
open import Data.Rational.Properties
  using ( ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; neg-antimono-≤; neg-antimono-<
        ; +-inverseʳ; +-mono-≤-<; ≤-<-trans; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; *-zeroʳ; nonNegative⁻¹; +-identityˡ )
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open +-*-Solver

qsum : List ℚ → ℚ
qsum = foldr _+_ 0ℚ

-- The number of lives, as a rational.
count : List ℚ → ℚ
count = foldr (λ _ n → 1ℚ + n) 0ℚ

private
  sub-nonneg : ∀ {p q} → p ≤ q → 0ℚ ≤ q - p
  sub-nonneg {p} {q} h = ≤-trans (≤-reflexive (sym (+-inverseʳ q))) (+-monoʳ-≤ q (neg-antimono-≤ h))

  sub-pos : ∀ {p q} → p < q → 0ℚ < q - p
  sub-pos {p} {q} h = ≤-<-trans (≤-reflexive (sym (+-inverseʳ q))) (+-mono-≤-< (≤-refl {q}) (neg-antimono-< h))

  mul-nonneg : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
  mul-nonneg {a} ha hb = ≤-trans (≤-reflexive (sym (*-zeroʳ a))) (*-monoˡ-≤-nonNeg a {{nonNegative ha}} hb)

  mul-le-left : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → r * p ≤ r * q
  mul-le-left {r} hr h = *-monoˡ-≤-nonNeg r {{nonNegative hr}} h

  count-nonneg : ∀ xs → 0ℚ ≤ count xs
  count-nonneg []       = ≤-refl
  count-nonneg (_ ∷ xs) = ≤-trans (count-nonneg xs)
    (≤-trans (≤-reflexive (sym (+-identityˡ (count xs)))) (+-monoˡ-≤ (count xs) (nonNegative⁻¹ 1ℚ)))

  qsum-++ : ∀ xs ys → qsum (xs ++ ys) ≡ qsum xs + qsum ys
  qsum-++ []       ys = sym (+-identityˡ (qsum ys))
  qsum-++ (x ∷ xs) ys = trans (cong (x +_) (qsum-++ xs ys)) (solve 3 (λ x a b → x :+ (a :+ b) := (x :+ a) :+ b) refl x (qsum xs) (qsum ys))

  count-++ : ∀ xs ys → count (xs ++ ys) ≡ count xs + count ys
  count-++ []       ys = sym (+-identityˡ (count ys))
  count-++ (x ∷ xs) ys = trans (cong (1ℚ +_) (count-++ xs ys)) (solve 2 (λ a b → con 1ℚ :+ (a :+ b) := (con 1ℚ :+ a) :+ b) refl (count xs) (count ys))

-- Age cap: lives of at most τ ticks give at most τ live ticks each.
liveTicks-le-length : ∀ τ ds → All (_≤ τ) ds → qsum ds ≤ τ * count ds
liveTicks-le-length τ []       []        = ≤-reflexive (sym (*-zeroʳ τ))
liveTicks-le-length τ (d ∷ ds) (hd ∷ hs) =
  ≤-trans (+-mono-≤ hd (liveTicks-le-length τ ds hs)) (≤-reflexive (solve 2 (λ t n → t :+ t :* n := t :* (con 1ℚ :+ n)) refl τ (count ds)))

-- Age cap over a window: Σ_t N_t ≤ τ (D_T + N_T).
liveTicks-le : ∀ τ dead alive → All (_≤ τ) (dead ++ alive) → qsum (dead ++ alive) ≤ τ * (count dead + count alive)
liveTicks-le τ dead alive h = ≤-trans (liveTicks-le-length τ (dead ++ alive) h) (≤-reflexive (cong (τ *_) (count-++ dead alive)))

-- Death cost: D l (1 − i) ≤ T W.
deathCost-le : ∀ D l i TW Werase Wrec → D * l ≤ Werase → Wrec ≤ i * (D * l) → Werase - Wrec ≤ TW → D * l * (1ℚ - i) ≤ TW
deathCost-le D l i TW We Wr h1 h2 h3 =
  ≤-trans (≤-reflexive (solve 3 (λ D l i → D :* l :* (con 1ℚ :- i) := D :* l :- i :* (D :* l)) refl D l i))
    (≤-trans (+-mono-≤ h1 (neg-antimono-≤ h2)) h3)

-- The carrying capacity, with denominators cleared: l (1 − i) Σ_t N_t ≤ τ (T W + l (1 − i) N_T).
meanLive-le : ∀ τ TW l i dead alive → 0ℚ ≤ τ → 0ℚ ≤ l → i < 1ℚ → All (_≤ τ) (dead ++ alive) →
  count dead * l * (1ℚ - i) ≤ TW → l * (1ℚ - i) * qsum (dead ++ alive) ≤ τ * (TW + l * (1ℚ - i) * count alive)
meanLive-le τ TW l i dead alive hτ hl hi hage hcost =
  ≤-trans (mul-le-left hk (liveTicks-le τ dead alive hage))
    (≤-trans (≤-reflexive (solve 5 (λ k t d a x → k :* (t :* (d :+ a)) := t :* (d :* k) :+ t :* (k :* a)) refl
               (l * (1ℚ - i)) τ (count dead) (count alive) TW))
      (≤-trans (+-mono-≤ (mul-le-left hτ (≤-trans (≤-reflexive (solve 3 (λ d l j → d :* (l :* j) := d :* l :* j) refl (count dead) l (1ℚ - i))) hcost)) ≤-refl)
        (≤-reflexive (solve 3 (λ t x y → t :* x :+ t :* y := t :* (x :+ y)) refl τ TW (l * (1ℚ - i) * count alive)))))
  where hk = mul-nonneg hl (<⇒≤ (sub-pos hi))

-- With a lower enclosure l_lo ≤ l of ln 2 the bound holds with l_lo.
meanLive-le-of-enclosure : ∀ τ TW l llo i dead alive → 0ℚ ≤ τ → 0ℚ ≤ llo → llo ≤ l → i < 1ℚ →
  All (_≤ τ) (dead ++ alive) → count dead * l * (1ℚ - i) ≤ TW →
  llo * (1ℚ - i) * qsum (dead ++ alive) ≤ τ * (TW + llo * (1ℚ - i) * count alive)
meanLive-le-of-enclosure τ TW l llo i dead alive hτ hlo hl hi hage hcost =
  meanLive-le τ TW llo i dead alive hτ hlo hi hage
    (≤-trans (≤-reflexive (solve 3 (λ d m j → d :* m :* j := d :* j :* m) refl (count dead) llo (1ℚ - i)))
      (≤-trans (mul-le-left (mul-nonneg (count-nonneg dead) (<⇒≤ (sub-pos hi))) hl)
        (≤-trans (≤-reflexive (solve 3 (λ d m j → d :* j :* m := d :* m :* j) refl (count dead) l (1ℚ - i))) hcost)))
