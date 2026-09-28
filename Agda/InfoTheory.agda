-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: InfoTheory.agda
--
-- Finite product joint on lists of rationals, mirroring:
--   • Lean  @Lean/InfoTheory.lean@
--   • Coq   @Coq/InfoTheory.v@  (Qeq / Forall2 proofs)
--   • Haskell @Haskell/InfoTheory.hs@ (QC)
--
-- Product joint mass + both marginals: machine-checked (zero postulate).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module InfoTheory where

open import Data.List.Base as List using (List; []; _∷_; map; length; foldl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Binary.Pointwise.Base as Pw
  using (Pointwise)
  renaming ([] to pw-[]; _∷_ to _pw∷_)
open import Data.List.Relation.Binary.Pointwise.Properties using (Pointwise-length)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties using (+-0; +-suc; suc-injective)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Properties
  using (*-distribʳ-+; *-distribˡ-+; *-comm; *-cong; +-cong; *-zeroˡ; *-zeroʳ; +-assoc; +-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Relation.Binary.Reasoning.Setoid (setoid ℚ)

pw-sym : ∀ {l₁ l₂} → Pointwise _≡_ l₁ l₂ → Pointwise _≡_ l₂ l₁
pw-sym pw-[] = pw-[]
pw-sym (eq pw∷ rest) = sym eq pw∷ pw-sym rest

pw-trans : ∀ {l₁ l₂ l₃} → Pointwise _≡_ l₁ l₂ → Pointwise _≡_ l₂ l₃ → Pointwise _≡_ l₁ l₃
pw-trans pw-[] pw-[] = pw-[]
pw-trans (eq₁ pw∷ rest₁) (eq₂ pw∷ rest₂) = trans eq₁ eq₂ pw∷ pw-trans rest₁ rest₂

pw-refl : ∀ (xs : List ℚ) → Pointwise _≡_ xs xs
pw-refl [] = pw-[]
pw-refl (x ∷ xs) = refl pw∷ pw-refl xs

------------------------------------------------------------------------
-- Sums and tensor row
------------------------------------------------------------------------

sumList : List ℚ → ℚ
sumList []       = 0ℚ
sumList (x ∷ xs) = x + sumList xs

mapMulRow : ℚ → List ℚ → List ℚ
mapMulRow p []       = []
mapMulRow p (x ∷ xs) = (p * x) ∷ mapMulRow p xs

productJoint : List ℚ → List ℚ → List (List ℚ)
productJoint []       q = []
productJoint (p ∷ ps) q = mapMulRow p q ∷ productJoint ps q

------------------------------------------------------------------------
-- Marginals (same layout as Coq/Haskell)
------------------------------------------------------------------------

marginalFirst : List (List ℚ) → List ℚ
marginalFirst []         = []
marginalFirst (r ∷ rows) = sumList r ∷ marginalFirst rows

pointwiseAdd : List ℚ → List ℚ → List ℚ
pointwiseAdd []         ys = ys
pointwiseAdd xs         [] = xs
pointwiseAdd (x ∷ xs) (y ∷ ys) = (x + y) ∷ pointwiseAdd xs ys

marginalSecond : List (List ℚ) → List ℚ
marginalSecond []         = []
marginalSecond (r ∷ rows) = foldl pointwiseAdd r rows

sumFlat : List (List ℚ) → ℚ
sumFlat []           = 0ℚ
sumFlat (row ∷ rows) = sumList row + sumFlat rows

------------------------------------------------------------------------
-- Small structural lemmas
------------------------------------------------------------------------

mapMulRow-length : ∀ (p : ℚ) (q : List ℚ) → length (mapMulRow p q) ≡ length q
mapMulRow-length p []       = refl
mapMulRow-length p (x ∷ xs) = cong suc (mapMulRow-length p xs)

productJoint-first-row-length :
  ∀ (p : ℚ) (ps : List ℚ) (q : List ℚ) →
  length (mapMulRow p q) ≡ length q
productJoint-first-row-length p ps q = mapMulRow-length p q

sumList-mapMulRow-distribˡ :
  ∀ (x : ℚ) (l : List ℚ) → sumList (mapMulRow x l) ≡ x * sumList l
sumList-mapMulRow-distribˡ x [] =
  begin
    sumList []        ≈⟨ refl ⟩
    0ℚ                ≈⟨ sym (*-zeroʳ x) ⟩
    x * 0ℚ            ≈⟨ refl ⟩
    x * sumList []    ∎
sumList-mapMulRow-distribˡ x (a ∷ la) =
  begin
    sumList (mapMulRow x (a ∷ la))
      ≈⟨ refl ⟩
    x * a + sumList (mapMulRow x la)
      ≈⟨ cong (x * a +_) (sumList-mapMulRow-distribˡ x la) ⟩
    x * a + x * sumList la
      ≈⟨ sym (*-distribˡ-+ x a (sumList la)) ⟩
    x * (a + sumList la)
      ≈⟨ refl ⟩
    x * sumList (a ∷ la) ∎

jointMassProduct :
  ∀ (p q : List ℚ) → sumFlat (productJoint p q) ≡ sumList p * sumList q
jointMassProduct [] q =
  begin
    sumFlat (productJoint [] q) ≈⟨ refl ⟩
    0ℚ                        ≈⟨ sym (*-zeroˡ (sumList q)) ⟩
    0ℚ * sumList q            ≈⟨ refl ⟩
    sumList [] * sumList q    ∎
jointMassProduct (ph ∷ pt) q =
  begin
    sumFlat (productJoint (ph ∷ pt) q)
      ≈⟨ refl ⟩
    sumList (mapMulRow ph q) + sumFlat (productJoint pt q)
      ≈⟨ cong₂ _+_ (sumList-mapMulRow-distribˡ ph q) (jointMassProduct pt q) ⟩
    ph * sumList q + sumList pt * sumList q
      ≈⟨ sym (*-distribʳ-+ (sumList q) ph (sumList pt)) ⟩
    (ph + sumList pt) * sumList q
      ≈⟨ refl ⟩
    sumList (ph ∷ pt) * sumList q ∎

marginalFirstProduct :
  ∀ (p q : List ℚ) →
  Pointwise _≡_ (marginalFirst (productJoint p q))
    (map (λ pi → pi * sumList q) p)
marginalFirstProduct [] q = pw-[]
marginalFirstProduct (ph ∷ pt) q =
  sumList-mapMulRow-distribˡ ph q pw∷ marginalFirstProduct pt q

------------------------------------------------------------------------
-- Second marginal helpers (Coq InfoTheory.v port)
------------------------------------------------------------------------

pointwiseAdd-length :
  ∀ (a b : List ℚ) → length a ≡ length b →
  length (pointwiseAdd a b) ≡ length a
pointwiseAdd-length [] [] refl = refl
pointwiseAdd-length (ha ∷ ta) (hb ∷ tb) eq =
  cong suc (pointwiseAdd-length ta tb (suc-injective eq))

pointwiseAdd-assoc :
  ∀ (a b c : List ℚ) →
  length a ≡ length b → length b ≡ length c →
  Pointwise _≡_ (pointwiseAdd (pointwiseAdd a b) c)
    (pointwiseAdd a (pointwiseAdd b c))
pointwiseAdd-assoc [] [] [] refl refl = pw-[]
pointwiseAdd-assoc (ha ∷ ta) (hb ∷ tb) (hc ∷ tc) eq₁ eq₂ =
  +-assoc ha hb hc pw∷ pointwiseAdd-assoc ta tb tc (suc-injective eq₁) (suc-injective eq₂)

pointwiseAdd-compatˡ :
  ∀ (R0 l1 l2 : List ℚ) → Pointwise _≡_ l1 l2 →
  Pointwise _≡_ (pointwiseAdd R0 l1) (pointwiseAdd R0 l2)
pointwiseAdd-compatˡ [] [] [] pw-[] = pw-[]
pointwiseAdd-compatˡ (hr ∷ rt) [] [] pw-[] = pw-refl (hr ∷ rt)
pointwiseAdd-compatˡ [] (y ∷ ys) (y' ∷ ys') (Hxy pw∷ Hys) = Hxy pw∷ Hys
pointwiseAdd-compatˡ (hr ∷ rt) (y ∷ ys) (y' ∷ ys') (Hxy pw∷ Hys) =
  cong₂ _+_ refl Hxy pw∷ pointwiseAdd-compatˡ rt ys ys' Hys

productJoint-row-length :
  ∀ (p q row : List ℚ) → row ∈ productJoint p q → length row ≡ length q
productJoint-row-length [] q row ()
productJoint-row-length (ph ∷ pt) q row (here row≡) =
  subst (λ r → length r ≡ length q) (sym row≡) (mapMulRow-length ph q)
productJoint-row-length (ph ∷ pt) q row (there Hin) =
  productJoint-row-length pt q row Hin

length-foldl-pointwiseAdd :
  ∀ (acc : List ℚ) (rows : List (List ℚ)) →
  (∀ row → row ∈ rows → length row ≡ length acc) →
  length (foldl pointwiseAdd acc rows) ≡ length acc
length-foldl-pointwiseAdd acc [] H = refl
length-foldl-pointwiseAdd acc (r ∷ rs) H =
  let Hr0 = H r (here refl)
      Hlen = pointwiseAdd-length acc r (sym Hr0)
      Hdim' row Hin = trans (H row (there Hin)) (sym Hlen)
  in trans (length-foldl-pointwiseAdd (pointwiseAdd acc r) rs Hdim') Hlen

foldl-pointwiseAdd-commute :
  ∀ (rs : List (List ℚ)) (Racc racc : List ℚ) →
  length Racc ≡ length racc →
  (∀ row → row ∈ rs → length row ≡ length Racc) →
  Pointwise _≡_ (foldl pointwiseAdd (pointwiseAdd Racc racc) rs)
    (pointwiseAdd Racc (foldl pointwiseAdd racc rs))
foldl-pointwiseAdd-commute [] Racc racc Hlen Hdim =
  pw-refl (pointwiseAdd Racc racc)
foldl-pointwiseAdd-commute (r₁ ∷ rs) Racc racc Hlen Hdim =
  let Hr1 = Hdim r₁ (here refl)
      Hlen-pr = trans (pointwiseAdd-length Racc racc Hlen) (sym Hr1)
      Hdim' row Hin =
        trans (Hdim row (there Hin)) (sym (pointwiseAdd-length Racc racc Hlen))
      IH1 = foldl-pointwiseAdd-commute rs (pointwiseAdd Racc racc) r₁ Hlen-pr Hdim'
      Hlen2 = trans (sym Hlen) (sym Hr1)
      Hdim2 row Hin = trans (Hdim row (there Hin)) Hlen
      IH2 = foldl-pointwiseAdd-commute rs racc r₁ Hlen2 Hdim2
      Hfl = length-foldl-pointwiseAdd r₁ rs (λ row Hin → trans (Hdim row (there Hin)) (sym Hr1))
      Hassoc = pointwiseAdd-assoc Racc racc (foldl pointwiseAdd r₁ rs) Hlen (trans Hlen2 (sym Hfl))
  in pw-trans IH1
    (pw-trans Hassoc
      (pointwiseAdd-compatˡ Racc
        (pointwiseAdd racc (foldl pointwiseAdd r₁ rs))
        (foldl pointwiseAdd (pointwiseAdd racc r₁) rs)
        (pw-sym IH2)))

pointwiseAdd-right-empty : ∀ (xs : List ℚ) → pointwiseAdd xs [] ≡ xs
pointwiseAdd-right-empty [] = refl
pointwiseAdd-right-empty (x ∷ xs) = refl

marginalSecond-fold :
  ∀ (R : List ℚ) (rows : List (List ℚ)) →
  (∀ row → row ∈ rows → length row ≡ length R) →
  Pointwise _≡_ (foldl pointwiseAdd R rows)
    (pointwiseAdd R (marginalSecond rows))
marginalSecond-empty : marginalSecond [] ≡ []
marginalSecond-empty = refl

marginalSecond-fold R [] Hdim =
  let list-eq = trans (cong (pointwiseAdd R) marginalSecond-empty) (pointwiseAdd-right-empty R)
  in subst (λ l → Pointwise _≡_ (foldl pointwiseAdd R []) l) (sym list-eq)
    (pw-refl (foldl pointwiseAdd R []))
marginalSecond-fold R (r ∷ rs) Hdim =
  foldl-pointwiseAdd-commute rs R r (sym (Hdim r (here refl))) (λ row Hin → Hdim row (there Hin))

mapMulRow-as-map :
  ∀ (ph : ℚ) (q : List ℚ) →
  Pointwise _≡_ (mapMulRow ph q) (map (λ qk → qk * ph) q)
mapMulRow-as-map ph [] = pw-[]
mapMulRow-as-map ph (qh ∷ qt) =
  *-comm ph qh pw∷ mapMulRow-as-map ph qt

pointwiseAdd-mapMul :
  ∀ (ph S : ℚ) (q : List ℚ) →
  Pointwise _≡_
    (pointwiseAdd (mapMulRow ph q) (map (λ qk → qk * S) q))
    (map (λ qk → qk * (ph + S)) q)
pointwiseAdd-mapMul ph S [] = pw-[]
pointwiseAdd-mapMul ph S (qh ∷ qt) =
  trans (cong₂ _+_ (*-comm ph qh) refl) (sym (*-distribˡ-+ qh ph S))
    pw∷ pointwiseAdd-mapMul ph S qt

map-scale-pointwise :
  ∀ (l : List ℚ) (c₁ c₂ : ℚ) → c₁ ≡ c₂ →
  Pointwise _≡_ (map (λ qk → qk * c₁) l) (map (λ qk → qk * c₂) l)
map-scale-pointwise [] c₁ c₂ Hc = pw-[]
map-scale-pointwise (qh ∷ qt) c₁ c₂ Hc =
  cong (qh *_) Hc pw∷ map-scale-pointwise qt c₁ c₂ Hc

map-mul-comm-pointwise :
  ∀ (c : ℚ) (l : List ℚ) →
  Pointwise _≡_ (map (λ qk → qk * c) l) (map (λ qk → c * qk) l)
map-mul-comm-pointwise c [] = pw-[]
map-mul-comm-pointwise c (qh ∷ qt) =
  sym (*-comm qh c) pw∷ map-mul-comm-pointwise c qt

marginalSecondProduct :
  ∀ (ph : ℚ) (pt q : List ℚ) →
  Pointwise _≡_ (marginalSecond (productJoint (ph ∷ pt) q))
    (map (λ qk → sumList (ph ∷ pt) * qk) q)
sumList-singleton : ∀ (ph : ℚ) → sumList (ph ∷ []) ≡ ph
sumList-singleton ph =
  trans (cong (ph +_) (refl {x = sumList []})) (+-identityʳ ph)

marginalSecondProduct ph [] q =
  pw-trans (mapMulRow-as-map ph q)
    (pw-trans (map-mul-comm-pointwise ph q)
      (pw-trans (map-scale-pointwise q ph (sumList (ph ∷ [])) (sym (sumList-singleton ph)))
        (pw-sym (map-mul-comm-pointwise (sumList (ph ∷ [])) q))))
marginalSecondProduct ph (a ∷ pt') q =
  let Hrows row Hin = productJoint-row-length (a ∷ pt') q row Hin
      Hdim row Hin = trans (Hrows row Hin) (mapMulRow-length ph q)
      step₁ = marginalSecond-fold (mapMulRow ph q) (productJoint (a ∷ pt') q) Hdim
      step₂ = pointwiseAdd-compatˡ (mapMulRow ph q)
        (marginalSecond (productJoint (a ∷ pt') q))
        (map (λ qk → sumList (a ∷ pt') * qk) q)
        (marginalSecondProduct a pt' q)
      step₃ = pointwiseAdd-mapMul ph (sumList (a ∷ pt')) q
      step₄ = map-scale-pointwise q (ph + sumList (a ∷ pt')) (sumList (ph ∷ a ∷ pt')) refl
  in pw-trans step₁ (pw-trans (pw-sym step₂) (pw-trans step₃ step₄))
