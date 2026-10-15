-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: LearningLoopLaws.agda
--
-- Twin of Lean/LearningLoopLaws.lean and Coq/LearningLoopLaws.v: the laws the learning-loop kernel of umst-adk
-- relies on, over exact rationals.
--   (1) the evidence map onto Unclaimed < Claimed < GuardPassed < Verified < Landed < MeterMoved is monotone;
--   (2) outcome counts form a commutative monoid and the fold is a homomorphism, so every reordering folds to the
--       same counts (compared pointwise, so no extensionality enters);
--   (3) the Beta(V+1, R+1) posterior depends on the counts alone, and 0 < V+1 < V+R+2;
--   (4) the barrier h_{k+1} ≥ (1 − γ) h_k with γ ≤ 1 keeps h above (1 − γ)^k h_0 and h ≥ 0;
--   (5) the clipped multiplicative step keeps a distribution and moves each weight within the clip; the
--       normalised weight v of an arm is carried with its defining equation v · S = w (1 + c), S the sum of the
--       scaled weights; the largest-remainder apportionment carries its floors as rationals and keeps each count
--       within one of its scaled weight;
--   (6) a verified evidence bit paid by an erasure obeying SecondLaw costs at least k_B T h, h the information of
--       one bit carried as data as in CostOfInformation.agda.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module LearningLoopLaws where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; foldl; foldr)
open import Data.List.Properties using (foldl-++)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
  renaming (refl to ↭-refl; prep to ↭-prep; swap to ↭-swap; trans to ↭-trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Rational
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _≤_; _<_; NonNegative; Positive; nonNegative; positive)
open import Data.Rational.Properties
  using ( ≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; <-trans; <-≤-trans; ≤-<-trans; <⇒≤; ≮⇒≥; _<?_
        ; +-mono-≤; +-monoʳ-≤; +-mono-≤-<; +-mono-<-≤; neg-antimono-≤; neg-antimono-<; +-inverseʳ
        ; *-monoˡ-≤-nonNeg; *-cancelʳ-≤-pos; *-zeroʳ; *-zeroˡ; *-identityʳ; *-identityˡ; *-assoc; *-comm
        ; *-distribˡ-+; *-distribʳ-+; nonNegative⁻¹; positive⁻¹; nonNeg*nonNeg⇒nonNeg )
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
  renaming (trans to ≡-trans)
open import Relation.Nullary using (yes; no)

open import Process
open import CostOfInformation using (honestSpend; honest-spend-of-secondLaw)
open +-*-Solver

------------------------------------------------------------------------
-- 1. The evidence lattice

data Level : Set where
  unclaimed claimed guardPassed verified landed meterMoved : Level

rank : Level → ℕ
rank unclaimed   = 0
rank claimed     = 1
rank guardPassed = 2
rank verified    = 3
rank landed      = 4
rank meterMoved  = 5

data ClaimStatus : Set where
  openClaim complete refusedClaim : ClaimStatus

data Outcome : Set where
  refused : Outcome
  atLevel : Level → Outcome

record Evidence : Set where
  constructor evidence
  field
    guard verified landed moved : Bool
open Evidence

_⇒ᵇ_ : Bool → Bool → Set
a ⇒ᵇ b = a ≡ true → b ≡ true

-- More evidence: every piece e holds, f holds too.
EvidenceLe : Evidence → Evidence → Set
EvidenceLe e f =
  (guard e ⇒ᵇ guard f) × (verified e ⇒ᵇ verified f) × (landed e ⇒ᵇ landed f) × (moved e ⇒ᵇ moved f)

-- The highest rung a COMPLETE claim's evidence holds (outcome.rs level_of).
completeLevel : Evidence → Level
completeLevel (evidence _     true  true  true)  = meterMoved
completeLevel (evidence _     true  true  false) = landed
completeLevel (evidence _     true  false _)     = verified
completeLevel (evidence true  false _     _)     = guardPassed
completeLevel (evidence false false _     _)     = claimed

levelOf : ClaimStatus → Evidence → Outcome
levelOf refusedClaim _ = refused
levelOf openClaim    _ = atLevel unclaimed
levelOf complete     e = atLevel (completeLevel e)

OutcomeLe : Outcome → Outcome → Set
OutcomeLe refused     refused     = ⊤
OutcomeLe (atLevel a) (atLevel b) = rank a ℕ.≤ rank b
OutcomeLe refused     (atLevel _) = ⊥
OutcomeLe (atLevel _) refused     = ⊥

private
  false≢true : false ≡ true → ⊥
  false≢true ()

  low≤2 : ∀ g l m → rank (completeLevel (evidence g false l m)) ℕ.≤ 2
  low≤2 true  _ _ = s≤s (s≤s z≤n)
  low≤2 false _ _ = s≤s z≤n

  3≤high : ∀ g l m → 3 ℕ.≤ rank (completeLevel (evidence g true l m))
  3≤high _ true  true  = s≤s (s≤s (s≤s z≤n))
  3≤high _ true  false = s≤s (s≤s (s≤s z≤n))
  3≤high _ false _     = s≤s (s≤s (s≤s z≤n))

-- Law 1: more evidence never lowers the level of a COMPLETE claim.
completeLevel-monotone : ∀ e f → EvidenceLe e f → rank (completeLevel e) ℕ.≤ rank (completeLevel f)
completeLevel-monotone (evidence g false l m) (evidence g' true l' m') _ =
  ℕP.≤-trans (low≤2 g l m) (ℕP.≤-trans (s≤s (s≤s z≤n)) (3≤high g' l' m'))
completeLevel-monotone (evidence _ true _ _) (evidence _ false _ _) (_ , hv , _) = ⊥-elim (false≢true (hv refl))
completeLevel-monotone (evidence false false _ _) (evidence false false _ _) _ = s≤s z≤n
completeLevel-monotone (evidence false false _ _) (evidence true  false _ _) _ = s≤s z≤n
completeLevel-monotone (evidence true  false _ _) (evidence true  false _ _) _ = ℕP.≤-refl
completeLevel-monotone (evidence true  false _ _) (evidence false false _ _) (hg , _) = ⊥-elim (false≢true (hg refl))
completeLevel-monotone (evidence _ true false _) (evidence g' true l' m') _ = 3≤high g' l' m'
completeLevel-monotone (evidence _ true true _) (evidence _ true false _) (_ , _ , hl , _) =
  ⊥-elim (false≢true (hl refl))
completeLevel-monotone (evidence _ true true false) (evidence _ true true false) _ = ℕP.≤-refl
completeLevel-monotone (evidence _ true true false) (evidence _ true true true)  _ = s≤s (s≤s (s≤s (s≤s z≤n)))
completeLevel-monotone (evidence _ true true true)  (evidence _ true true true)  _ = ℕP.≤-refl
completeLevel-monotone (evidence _ true true true)  (evidence _ true true false) (_ , _ , _ , hm) =
  ⊥-elim (false≢true (hm refl))

-- Law 1, for every claim status.
levelOf-monotone : ∀ s e f → EvidenceLe e f → OutcomeLe (levelOf s e) (levelOf s f)
levelOf-monotone openClaim    _ _ _ = z≤n
levelOf-monotone complete     e f h = completeLevel-monotone e f h
levelOf-monotone refusedClaim _ _ _ = tt

------------------------------------------------------------------------
-- 2. Outcome counts and 3. the Beta posterior

module Counting {k} (K : Set k) where

  Counts : Set k
  Counts = K → ℕ

  czero : Counts
  czero _ = 0

  combine : Counts → Counts → Counts
  combine a b x = a x ℕ.+ b x

  combine-assoc : ∀ a b c x → combine (combine a b) c x ≡ combine a (combine b c) x
  combine-assoc a b c x = ℕP.+-assoc (a x) (b x) (c x)

  combine-comm : ∀ a b x → combine a b x ≡ combine b a x
  combine-comm a b x = ℕP.+-comm (a x) (b x)

  zero-combine : ∀ a x → combine czero a x ≡ a x
  zero-combine a x = refl

  combine-zero : ∀ a x → combine a czero x ≡ a x
  combine-zero a x = ℕP.+-identityʳ (a x)

  -- The fold from the identity, left to right (OutcomeCounts::fold).
  cfold : List Counts → Counts
  cfold xs = foldl combine czero xs

  foldl-combine : ∀ xs acc x → foldl combine acc xs x ≡ acc x ℕ.+ cfold xs x
  foldl-combine []       acc x = sym (ℕP.+-identityʳ (acc x))
  foldl-combine (y ∷ ys) acc x =
    ≡-trans (foldl-combine ys (combine acc y) x)
      (≡-trans (ℕP.+-assoc (acc x) (y x) (cfold ys x))
        (cong (acc x ℕ.+_) (sym (foldl-combine ys (combine czero y) x))))

  fold-cons : ∀ y ys x → cfold (y ∷ ys) x ≡ y x ℕ.+ cfold ys x
  fold-cons y ys x = foldl-combine ys (combine czero y) x

  -- Law 2: the fold is a monoid homomorphism from lists under append.
  fold-append : ∀ xs ys x → cfold (xs ++ ys) x ≡ cfold xs x ℕ.+ cfold ys x
  fold-append xs ys x = ≡-trans (cong (λ f → f x) (foldl-++ combine czero xs ys)) (foldl-combine ys (cfold xs) x)

  private
    swap-sum : ∀ a b c d → c ≡ d → a ℕ.+ (b ℕ.+ c) ≡ b ℕ.+ (a ℕ.+ d)
    swap-sum a b c .c refl =
      ≡-trans (sym (ℕP.+-assoc a b c)) (≡-trans (cong (ℕ._+ c) (ℕP.+-comm a b)) (ℕP.+-assoc b a c))

  -- Law 2: every reordering of the rows folds to the same counts.
  fold-perm : ∀ {xs ys} → xs ↭ ys → ∀ x → cfold xs x ≡ cfold ys x
  fold-perm ↭-refl x = refl
  fold-perm (↭-prep y p) x =
    ≡-trans (fold-cons y _ x) (≡-trans (cong (y x ℕ.+_) (fold-perm p x)) (sym (fold-cons y _ x)))
  fold-perm (↭-swap y z p) x =
    ≡-trans (fold-cons y _ x)
      (≡-trans (cong (y x ℕ.+_) (fold-cons z _ x))
        (≡-trans (swap-sum (y x) (z x) _ _ (fold-perm p x))
          (≡-trans (cong (z x ℕ.+_) (sym (fold-cons y _ x))) (sym (fold-cons z _ x)))))
  fold-perm (↭-trans p q) x = ≡-trans (fold-perm p x) (fold-perm q x)

  keySum : List K → Counts → ℕ
  keySum keys c = foldr (λ x acc → c x ℕ.+ acc) 0 keys

  keySum-ext : ∀ keys c d → (∀ x → c x ≡ d x) → keySum keys c ≡ keySum keys d
  keySum-ext []       c d h = refl
  keySum-ext (x ∷ xs) c d h = cong₂ ℕ._+_ (h x) (keySum-ext xs c d h)

  -- The Beta(V+1, R+1) posterior mean as numerator and denominator (outcome.rs posterior).
  posterior : List K → List K → Counts → ℕ × ℕ
  posterior vKeys rKeys c = keySum vKeys c ℕ.+ 1 , keySum vKeys c ℕ.+ keySum rKeys c ℕ.+ 2

  -- Law 3: the posterior of a lane is the same for every order of its rows.
  posterior-perm : ∀ vKeys rKeys {xs ys} → xs ↭ ys → posterior vKeys rKeys (cfold xs) ≡ posterior vKeys rKeys (cfold ys)
  posterior-perm vKeys rKeys p =
    cong₂ (λ v r → v ℕ.+ 1 , v ℕ.+ r ℕ.+ 2) (keySum-ext vKeys _ _ (fold-perm p)) (keySum-ext rKeys _ _ (fold-perm p))

  -- Law 3: the posterior mean lies strictly between 0 and 1: 0 < V+1 < V+R+2.
  posterior-mean-mem : ∀ vKeys rKeys c →
    0 ℕ.< proj₁ (posterior vKeys rKeys c) × proj₁ (posterior vKeys rKeys c) ℕ.< proj₂ (posterior vKeys rKeys c)
  posterior-mean-mem vKeys rKeys c =
    ℕP.m≤n+m 1 v , subst (v ℕ.+ 1 ℕ.<_) (sym (ℕP.+-assoc v r 2)) (ℕP.+-monoʳ-< v (ℕP.m≤n+m 2 r))
    where
      v = keySum vKeys c
      r = keySum rKeys c

------------------------------------------------------------------------
-- Rational helpers

private
  sub-nonneg : ∀ {p q} → p ≤ q → 0ℚ ≤ q - p
  sub-nonneg {p} {q} h = ≤-trans (≤-reflexive (sym (+-inverseʳ q))) (+-monoʳ-≤ q (neg-antimono-≤ h))

  sub-pos : ∀ {p q} → p < q → 0ℚ < q - p
  sub-pos {p} {q} h = ≤-<-trans (≤-reflexive (sym (+-inverseʳ q))) (+-mono-≤-< (≤-refl {q}) (neg-antimono-< h))

  mul-nonneg : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
  mul-nonneg {a} ha hb = ≤-trans (≤-reflexive (sym (*-zeroʳ a))) (*-monoˡ-≤-nonNeg a {{nonNegative ha}} hb)

  mul-le-left : ∀ {r p q} → 0ℚ ≤ r → p ≤ q → r * p ≤ r * q
  mul-le-left {r} hr h = *-monoˡ-≤-nonNeg r {{nonNegative hr}} h

  0≤1 : 0ℚ ≤ 1ℚ
  0≤1 = nonNegative⁻¹ 1ℚ

  0<1 : 0ℚ < 1ℚ
  0<1 = positive⁻¹ 1ℚ

------------------------------------------------------------------------
-- 4. The control barrier

pow : ℚ → ℕ → ℚ
pow x zero    = 1ℚ
pow x (suc n) = x * pow x n

barrier-step-nonneg : ∀ γ x y → γ ≤ 1ℚ → 0ℚ ≤ x → (1ℚ - γ) * x ≤ y → 0ℚ ≤ y
barrier-step-nonneg γ x y hγ hx hs = ≤-trans (mul-nonneg (sub-nonneg hγ) hx) hs

-- Law 4: under h (k+1) ≥ (1 − γ) h k, h stays above the geometric floor.
barrier-floor : ∀ (h : ℕ → ℚ) γ → γ ≤ 1ℚ → (∀ k → (1ℚ - γ) * h k ≤ h (suc k)) → ∀ k → pow (1ℚ - γ) k * h 0 ≤ h k
barrier-floor h γ hγ hs zero    = ≤-reflexive (*-identityˡ (h 0))
barrier-floor h γ hγ hs (suc k) =
  ≤-trans (≤-reflexive (*-assoc (1ℚ - γ) (pow (1ℚ - γ) k) (h 0)))
    (≤-trans (mul-le-left (sub-nonneg hγ) (barrier-floor h γ hγ hs k)) (hs k))

pow-nonneg : ∀ {x} → 0ℚ ≤ x → ∀ n → 0ℚ ≤ pow x n
pow-nonneg hx zero    = 0≤1
pow-nonneg hx (suc n) = mul-nonneg hx (pow-nonneg hx n)

-- Law 4: the safe set h ≥ 0 is forward invariant.
barrier-forward-invariant : ∀ (h : ℕ → ℚ) γ → γ ≤ 1ℚ → (∀ k → (1ℚ - γ) * h k ≤ h (suc k)) → 0ℚ ≤ h 0 →
  ∀ k → 0ℚ ≤ h k
barrier-forward-invariant h γ hγ hs h0 k =
  ≤-trans (mul-nonneg (pow-nonneg (sub-nonneg hγ) k) h0) (barrier-floor h γ hγ hs k)

------------------------------------------------------------------------
-- 5. The clipped multiplicative step and the largest-remainder apportionment

-- The clamp of the runtime (ppo_clipped_step.rs clamp).
clamp : ℚ → ℚ → ℚ → ℚ
clamp lo hi v with v <? lo
... | yes _ = lo
... | no _ with hi <? v
...   | yes _ = hi
...   | no _  = v

clamp-mem : ∀ lo hi v → lo ≤ hi → lo ≤ clamp lo hi v × clamp lo hi v ≤ hi
clamp-mem lo hi v h with v <? lo
... | yes _ = ≤-refl , h
... | no v≮lo with hi <? v
...   | yes _    = h , ≤-refl
...   | no hi≮v  = ≮⇒≥ v≮lo , ≮⇒≥ hi≮v

-- An arm: its weight w, its clamped change c and its normalised weight v.
Arm : Set
Arm = ℚ × ℚ × ℚ

wt : Arm → ℚ
wt = proj₁

chg : Arm → ℚ
chg t = proj₁ (proj₂ t)

nw : Arm → ℚ
nw t = proj₂ (proj₂ t)

scaledW : Arm → ℚ
scaledW t = wt t * (1ℚ + chg t)

sumW sumScaled sumV : List Arm → ℚ
sumW      = foldr (λ t acc → wt t + acc) 0ℚ
sumScaled = foldr (λ t acc → scaledW t + acc) 0ℚ
sumV      = foldr (λ t acc → nw t + acc) 0ℚ

ArmOk : ℚ → Arm → Set
ArmOk clip t = 0ℚ ≤ wt t × - clip ≤ chg t × chg t ≤ clip

-- The normalised weight is the scaled weight over S: v · S = w (1 + c).
Normalised : ℚ → Arm → Set
Normalised S t = nw t * S ≡ scaledW t

-- Law 5: before renormalisation each weight moves by at most the clip times itself.
scaled-move : ∀ clip t → ArmOk clip t → - (clip * wt t) ≤ scaledW t - wt t × scaledW t - wt t ≤ clip * wt t
scaled-move clip (w , c , _) (hw , hlo , hhi) =
  ≤-trans (≤-reflexive (solve 2 (λ cl w → :- (cl :* w) := w :* (:- cl)) refl clip w))
    (≤-trans (mul-le-left hw hlo) (≤-reflexive (solve 2 (λ w c → w :* c := w :* (con 1ℚ :+ c) :- w) refl w c))) ,
  ≤-trans (≤-reflexive (solve 2 (λ w c → w :* (con 1ℚ :+ c) :- w := w :* c) refl w c))
    (≤-trans (mul-le-left hw hhi) (≤-reflexive (*-comm w clip)))

scaled-mem : ∀ clip t → ArmOk clip t → (1ℚ - clip) * wt t ≤ scaledW t × scaledW t ≤ (1ℚ + clip) * wt t
scaled-mem clip (w , c , _) (hw , hlo , hhi) =
  ≤-trans (≤-reflexive (solve 2 (λ cl w → (con 1ℚ :- cl) :* w := w :* (con 1ℚ :+ (:- cl))) refl clip w))
    (mul-le-left hw (+-monoʳ-≤ 1ℚ hlo)) ,
  ≤-trans (mul-le-left hw (+-monoʳ-≤ 1ℚ hhi)) (≤-reflexive (*-comm w (1ℚ + clip)))

sumScaled-mem : ∀ clip l → All (ArmOk clip) l →
  (1ℚ - clip) * sumW l ≤ sumScaled l × sumScaled l ≤ (1ℚ + clip) * sumW l
sumScaled-mem clip [] [] = ≤-reflexive (*-zeroʳ (1ℚ - clip)) , ≤-reflexive (sym (*-zeroʳ (1ℚ + clip)))
sumScaled-mem clip (t ∷ l) (ht ∷ hl) =
  ≤-trans (≤-reflexive (*-distribˡ-+ (1ℚ - clip) (wt t) (sumW l))) (+-mono-≤ (proj₁ hs) (proj₁ ih)) ,
  ≤-trans (+-mono-≤ (proj₂ hs) (proj₂ ih)) (≤-reflexive (sym (*-distribˡ-+ (1ℚ + clip) (wt t) (sumW l))))
  where
    hs = scaled-mem clip t ht
    ih = sumScaled-mem clip l hl

private
  sumV-mul : ∀ S l → All (Normalised S) l → sumV l * S ≡ sumScaled l
  sumV-mul S []      []        = *-zeroˡ S
  sumV-mul S (t ∷ l) (ht ∷ hl) = ≡-trans (*-distribʳ-+ S (nw t) (sumV l)) (cong₂ _+_ ht (sumV-mul S l hl))

  S-bounds : ∀ clip l → All (ArmOk clip) l → sumW l ≡ 1ℚ → 1ℚ - clip ≤ sumScaled l × sumScaled l ≤ 1ℚ + clip
  S-bounds clip l h hsum =
    ≤-trans (≤-reflexive (sym (*-identityʳ (1ℚ - clip)))) (subst (λ s → (1ℚ - clip) * s ≤ sumScaled l) hsum (proj₁ b)) ,
    ≤-trans (subst (λ s → sumScaled l ≤ (1ℚ + clip) * s) hsum (proj₂ b)) (≤-reflexive (*-identityʳ (1ℚ + clip)))
    where b = sumScaled-mem clip l h

  nw-nonneg : ∀ clip S t → 0ℚ < S → clip < 1ℚ → ArmOk clip t → Normalised S t → 0ℚ ≤ nw t
  nw-nonneg clip S t hS hc ht hn =
    *-cancelʳ-≤-pos S {{positive hS}}
      (≤-trans (≤-reflexive (*-zeroˡ S))
        (≤-trans (≤-trans (mul-nonneg (sub-nonneg (<⇒≤ hc)) (proj₁ ht)) (proj₁ (scaled-mem clip t ht)))
          (≤-reflexive (sym hn))))

  all-nonneg : ∀ clip S l → 0ℚ < S → clip < 1ℚ → All (ArmOk clip) l → All (Normalised S) l → All (λ t → 0ℚ ≤ nw t) l
  all-nonneg clip S []      hS hc []        []        = []
  all-nonneg clip S (t ∷ l) hS hc (ht ∷ hl) (hn ∷ hns) = nw-nonneg clip S t hS hc ht hn ∷ all-nonneg clip S l hS hc hl hns

-- Law 5: the step of a distribution is a distribution: non-negative weights summing to 1.
ppoStep-simplex : ∀ clip l → clip < 1ℚ → All (ArmOk clip) l → sumW l ≡ 1ℚ → All (Normalised (sumScaled l)) l →
  All (λ t → 0ℚ ≤ nw t) l × sumV l ≡ 1ℚ
ppoStep-simplex clip l hc h hsum hn =
  all-nonneg clip S l hS hc h hn ,
  ≤-antisym (*-cancelʳ-≤-pos S {{positive hS}} (≤-reflexive eq))
            (*-cancelʳ-≤-pos S {{positive hS}} (≤-reflexive (sym eq)))
  where
    S = sumScaled l
    hS : 0ℚ < S
    hS = <-≤-trans (sub-pos hc) (proj₁ (S-bounds clip l h hsum))
    eq : sumV l * S ≡ 1ℚ * S
    eq = ≡-trans (sumV-mul S l hn) (sym (*-identityˡ S))

private
  ratio-one : ∀ clip S t → 0ℚ < S → clip < 1ℚ → 1ℚ - clip ≤ S → S ≤ 1ℚ + clip → ArmOk clip t → Normalised S t →
    (1ℚ - clip) * wt t ≤ (1ℚ + clip) * nw t × (1ℚ - clip) * nw t ≤ (1ℚ + clip) * wt t
  ratio-one clip S t hS hc hlo hhi ht hn =
    ≤-trans (proj₁ hm) (≤-trans (≤-reflexive (sym hn)) (≤-trans (mul-le-left hv hhi) (≤-reflexive (*-comm (nw t) (1ℚ + clip))))) ,
    ≤-trans (≤-reflexive (*-comm (1ℚ - clip) (nw t))) (≤-trans (mul-le-left hv hlo) (≤-trans (≤-reflexive hn) (proj₂ hm)))
    where
      hm = scaled-mem clip t ht
      hv = nw-nonneg clip S t hS hc ht hn
      -- v · S ≤ v · (1 + clip) and v · (1 − clip) ≤ v · S, with v ≥ 0 and S between 1 − clip and 1 + clip

  all-ratio : ∀ clip S l → 0ℚ < S → clip < 1ℚ → 1ℚ - clip ≤ S → S ≤ 1ℚ + clip →
    All (ArmOk clip) l → All (Normalised S) l →
    All (λ t → (1ℚ - clip) * wt t ≤ (1ℚ + clip) * nw t × (1ℚ - clip) * nw t ≤ (1ℚ + clip) * wt t) l
  all-ratio clip S []      _  _  _   _   []        []        = []
  all-ratio clip S (t ∷ l) hS hc hlo hhi (ht ∷ hl) (hn ∷ hns) =
    ratio-one clip S t hS hc hlo hhi ht hn ∷ all-ratio clip S l hS hc hlo hhi hl hns

-- Law 5: each normalised weight stays within the ratio (1 + clip)/(1 − clip) of its predecessor.
ppoStep-ratio : ∀ clip l → clip < 1ℚ → All (ArmOk clip) l → sumW l ≡ 1ℚ → All (Normalised (sumScaled l)) l →
  All (λ t → (1ℚ - clip) * wt t ≤ (1ℚ + clip) * nw t × (1ℚ - clip) * nw t ≤ (1ℚ + clip) * wt t) l
ppoStep-ratio clip l hc h hsum hn =
  all-ratio clip (sumScaled l) l (<-≤-trans (sub-pos hc) (proj₁ b)) hc (proj₁ b) (proj₂ b) h hn
  where b = S-bounds clip l h hsum

-- A part of the apportionment: the scaled weight x, its floor f (carried as a rational) and its bump.
Part : Set
Part = ℚ × ℚ × Bool

bumpQ : Bool → ℚ
bumpQ true  = 1ℚ
bumpQ false = 0ℚ

apportioned : Part → ℚ
apportioned (_ , f , b) = f + bumpQ b

sumX sumF sumB sumA countQ : List Part → ℚ
sumX   = foldr (λ p acc → proj₁ p + acc) 0ℚ
sumF   = foldr (λ p acc → proj₁ (proj₂ p) + acc) 0ℚ
sumB   = foldr (λ p acc → bumpQ (proj₂ (proj₂ p)) + acc) 0ℚ
sumA   = foldr (λ p acc → apportioned p + acc) 0ℚ
countQ = foldr (λ _ acc → 1ℚ + acc) 0ℚ

FloorOk : Part → Set
FloorOk (x , f , _) = f ≤ x × x < f + 1ℚ

-- A bump goes only to a positive remainder (the largest-remainder order gives one).
BumpPositive : Part → Set
BumpPositive (x , f , b) = b ≡ true → f < x

-- Law 5: the apportioned total is the floors' total plus the bumps.
apportion-sum : ∀ l → sumA l ≡ sumF l + sumB l
apportion-sum []                = refl
apportion-sum ((x , f , b) ∷ l) =
  ≡-trans (cong (apportioned (x , f , b) +_) (apportion-sum l))
    (solve 4 (λ f b F B → (f :+ b) :+ (F :+ B) := (f :+ F) :+ (b :+ B)) refl f (bumpQ b) (sumF l) (sumB l))

private
  below-one : ∀ {x f} → x < f + 1ℚ → x - f < 1ℚ
  below-one {x} {f} h =
    <-≤-trans (+-mono-<-≤ h (≤-refl { - f})) (≤-reflexive (solve 1 (λ f → f :+ con 1ℚ :- f := con 1ℚ) refl f))

  sub-one-below : ∀ {x f} → x < f + 1ℚ → x - 1ℚ < f
  sub-one-below {x} {f} h =
    <-≤-trans (+-mono-<-≤ h (≤-refl { - 1ℚ})) (≤-reflexive (solve 1 (λ f → f :+ con 1ℚ :- con 1ℚ := f) refl f))

  close-one : ∀ p → FloorOk p → BumpPositive p → proj₁ p - 1ℚ < apportioned p × apportioned p < proj₁ p + 1ℚ
  close-one (x , f , false) (h1 , h2) _ =
    <-≤-trans (sub-one-below h2) (≤-reflexive (sym (+-identityʳ′ f))) ,
    ≤-<-trans (≤-reflexive (+-identityʳ′ f)) (≤-<-trans h1 (≤-<-trans (≤-reflexive (sym (+-identityʳ′ x))) (+-mono-≤-< (≤-refl {x}) 0<1)))
    where
      +-identityʳ′ : ∀ q → q + 0ℚ ≡ q
      +-identityʳ′ q = solve 1 (λ q → q :+ con 0ℚ := q) refl q
  close-one (x , f , true) (h1 , h2) hpos =
    <-trans (sub-one-below h2) (≤-<-trans (≤-reflexive (sym (solve 1 (λ f → f :+ con 0ℚ := f) refl f))) (+-mono-≤-< (≤-refl {f}) 0<1)) ,
    +-mono-<-≤ (hpos refl) (≤-refl {1ℚ})

  all-close : ∀ l → All FloorOk l → All BumpPositive l →
    All (λ p → proj₁ p - 1ℚ < apportioned p × apportioned p < proj₁ p + 1ℚ) l
  all-close []      []        []        = []
  all-close (p ∷ l) (h ∷ hs) (b ∷ bs) = close-one p h b ∷ all-close l hs bs

-- Law 5: each apportioned count is within one of its scaled weight.
apportion-close : ∀ l → All FloorOk l → All BumpPositive l →
  All (λ p → proj₁ p - 1ℚ < apportioned p × apportioned p < proj₁ p + 1ℚ) l
apportion-close = all-close

private
  missing-le : ∀ l → All FloorOk l → sumX l - sumF l ≤ countQ l
  missing-le [] [] = ≤-refl
  missing-le ((x , f , b) ∷ l) ((h1 , h2) ∷ hl) =
    ≤-trans (≤-reflexive (solve 4 (λ x X f F → (x :+ X) :- (f :+ F) := (x :- f) :+ (X :- F)) refl x (sumX l) f (sumF l)))
      (+-mono-≤ (<⇒≤ (below-one h2)) (missing-le l hl))

-- Law 5: the missing units are fewer than the arms.
apportion-missing-lt : ∀ p l → All FloorOk (p ∷ l) → sumX (p ∷ l) - sumF (p ∷ l) < countQ (p ∷ l)
apportion-missing-lt (x , f , b) l ((h1 , h2) ∷ hl) =
  ≤-<-trans (≤-reflexive (solve 4 (λ x X f F → (x :+ X) :- (f :+ F) := (x :- f) :+ (X :- F)) refl x (sumX l) f (sumF l)))
    (+-mono-<-≤ (below-one h2) (missing-le l hl))

------------------------------------------------------------------------
-- 6. One verified evidence bit costs at least k_B T h

-- The bits a close counts as evidence: its claimed bits from the Verified level up.
countedOutcome : Outcome → ℚ → ℚ
countedOutcome (atLevel verified)   b = b
countedOutcome (atLevel landed)     b = b
countedOutcome (atLevel meterMoved) b = b
countedOutcome (atLevel _)          _ = 0ℚ
countedOutcome refused              _ = 0ℚ

countedBits : ClaimStatus → Evidence → ℚ → ℚ
countedBits s e b = countedOutcome (levelOf s e) b

private
  counted-cases : ∀ o b → countedOutcome o b ≡ b ⊎ countedOutcome o b ≡ 0ℚ
  counted-cases (atLevel unclaimed)   _ = inj₂ refl
  counted-cases (atLevel claimed)     _ = inj₂ refl
  counted-cases (atLevel guardPassed) _ = inj₂ refl
  counted-cases (atLevel verified)    _ = inj₁ refl
  counted-cases (atLevel landed)      _ = inj₁ refl
  counted-cases (atLevel meterMoved)  _ = inj₁ refl
  counted-cases refused               _ = inj₂ refl

  verified-counts : ∀ g l m b → countedBits complete (evidence g true l m) b ≡ b
  verified-counts _ true  true  _ = refl
  verified-counts _ true  false _ = refl
  verified-counts _ false _     _ = refl

-- Law 6: the counted evidence bits of a close paid by an erasure of its bits obeying SecondLaw cost at least
-- k_B T h each.
countedBits-cost : ∀ s e kT .{{_ : NonNegative kT}} h .{{_ : NonNegative h}} bits er → 0ℚ ≤ bits →
  SecondLaw (erase er) (transformation (bits * h) 0ℚ) →
  countedBits s e bits * (kT * h) ≤ kT * ErasureProcess.dissipatedEntropy er
countedBits-cost s e kT h bits er hb hs with counted-cases (levelOf s e) bits
... | inj₁ eq = ≤-trans (≤-reflexive (≡-trans (cong (_* (kT * h)) eq) (*-comm bits (kT * h))))
                  (honest-spend-of-secondLaw kT h bits er hs)
... | inj₂ eq = ≤-trans (≤-reflexive (≡-trans (cong (_* (kT * h)) eq) (*-zeroˡ (kT * h))))
                  (≤-trans (mul-nonneg (nonNegative⁻¹ (kT * h) {{nonNeg*nonNeg⇒nonNeg kT h}}) hb)
                    (honest-spend-of-secondLaw kT h bits er hs))

-- Law 6: a verified close of at least one evidence bit, paid by an erasure of its bits obeying SecondLaw, spends
-- honestly (honest-spend-of-secondLaw) and pays at least one Landauer bit energy k_B T h.
verified-bit-costs-landauer : ∀ g l m kT .{{_ : NonNegative kT}} h .{{_ : NonNegative h}} bits er → 1ℚ ≤ bits →
  SecondLaw (erase er) (transformation (bits * h) 0ℚ) →
  countedBits complete (evidence g true l m) bits ≡ bits ×
  honestSpend (kT * h) bits (kT * ErasureProcess.dissipatedEntropy er) ×
  kT * h ≤ kT * ErasureProcess.dissipatedEntropy er
verified-bit-costs-landauer g l m kT h bits er h1 hs =
  verified-counts g l m bits , hh ,
  ≤-trans (≤-reflexive (sym (*-identityʳ (kT * h))))
    (≤-trans (mul-le-left (nonNegative⁻¹ (kT * h) {{nonNeg*nonNeg⇒nonNeg kT h}}) h1) hh)
  where hh = honest-spend-of-secondLaw kT h bits er hs
