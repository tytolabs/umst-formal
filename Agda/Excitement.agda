-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Excitement.agda
--
-- Twin of Lean/Excitement.lean, Lean/ExcitementProofs.lean and the selection theorems of
-- Lean/Concrete/SecondLaw.lean: selection under cost over cement candidates. Each candidate carries the admissibility
-- of its move; selection returns the evidence-tagged candidate of least global free energy (ties by id) when it
-- lowers the source's free energy, and a residue otherwise. The joint free energy is a module parameter (a class
-- parameter, JointThermo, in Lean).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Excitement where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; filterᵇ; foldl; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Rational using (ℚ; _+_; _≤_; _<_; _<?_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; ≤-reflexive; <⇒≤; ≮⇒≥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; cong; subst) renaming (refl to ≡-refl; trans to ≡-trans)
open import Relation.Nullary using (yes; no; ¬_; does)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
import Data.Rational.Properties as ℚP
import Data.Nat.Properties as ℕP
open import Data.Nat using () renaming (_<_ to _<ℕ_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; refl; prep; swap; trans; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; ¬x∷xs↭[])
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)

open import Concrete.Gate using (ThermodynamicState; Admissible)
open import Concrete.SecondLaw using (admissible⇔secondLaw)
open import Process using (SecondLaw; transition; thermodynamic)

-- Why selection returns no candidate.
data Residue : Set where
  noCandidates allInadmissible allExcludedByCBF allExcludedByDEC untaggedConstant noStrictImprovement : Residue

anyᵇ : {A : Set} → (A → Bool) → List A → Bool
anyᵇ p = foldr (λ x acc → if p x then true else acc) false

∈-filterᵇ⁻ : {A : Set} (p : A → Bool) (xs : List A) {v : A} → v ∈ filterᵇ p xs → v ∈ xs × p v ≡ true
∈-filterᵇ⁻ p (x ∷ xs) v∈ with p x in eq
... | true with v∈
...   | here ≡-refl = here ≡-refl , eq
...   | there v∈′ = let (m , q) = ∈-filterᵇ⁻ p xs v∈′ in there m , q
∈-filterᵇ⁻ p (x ∷ xs) v∈ | false = let (m , q) = ∈-filterᵇ⁻ p xs v∈ in there m , q

∈-filterᵇ⁺ : {A : Set} (p : A → Bool) (xs : List A) {v : A} → v ∈ xs → p v ≡ true → v ∈ filterᵇ p xs
∈-filterᵇ⁺ p (x ∷ xs) (here ≡-refl) pv with p x
∈-filterᵇ⁺ p (x ∷ xs) (here ≡-refl) ≡-refl | true = here ≡-refl
∈-filterᵇ⁺ p (x ∷ xs) (there v∈) pv with p x
... | true = there (∈-filterᵇ⁺ p xs v∈ pv)
... | false = ∈-filterᵇ⁺ p xs v∈ pv

module Select (jointFreeEnergy : ThermodynamicState → ℚ) (src : ThermodynamicState) where

  -- A candidate move from src: its id, target, the admissibility of the move, its ledger total and whether it
  -- carries evidence.
  record Cand : Set where
    field
      cid            : ℕ
      tgt            : ThermodynamicState
      step           : Admissible src tgt
      ledger         : ℚ
      evidenceTagged : Bool

  open Cand public

  candEnergy : Cand → ℚ
  candEnergy c = jointFreeEnergy (tgt c) + ledger c

  pickMin : Maybe Cand → Cand → Maybe Cand
  pickMin nothing c = just c
  pickMin (just b) c with candEnergy c <? candEnergy b
  ... | yes _ = just c
  ... | no _ with candEnergy b <? candEnergy c
  ...   | yes _ = just b
  ...   | no _ = if cid c <ᵇ cid b then just c else just b

  decide : Cand → Cand ⊎ Residue
  decide c with candEnergy c <? jointFreeEnergy src
  ... | yes _ = inj₁ c
  ... | no _ = inj₂ noStrictImprovement

  onFold : Maybe Cand → Cand ⊎ Residue
  onFold nothing = inj₂ allInadmissible
  onFold (just c) = decide c

  untagged : List Cand → Cand ⊎ Residue
  untagged cands = if anyᵇ (λ c → not (evidenceTagged c)) cands then inj₂ allInadmissible else inj₂ untaggedConstant

  onTagged : List Cand → List Cand → Cand ⊎ Residue
  onTagged cands [] = untagged cands
  onTagged cands (t ∷ ts) = onFold (foldl pickMin nothing (t ∷ ts))

  select : List Cand → Cand ⊎ Residue
  select [] = inj₂ noCandidates
  select (c ∷ cs) = onTagged (c ∷ cs) (filterᵇ evidenceTagged (c ∷ cs))

  select-empty : select [] ≡ inj₂ noCandidates
  select-empty = ≡-refl

  pickMin-spec : ∀ acc x → ∃[ r ] (pickMin acc x ≡ just r × (r ≡ x ⊎ acc ≡ just r) × candEnergy r ≤ candEnergy x ×
    (∀ a → acc ≡ just a → candEnergy r ≤ candEnergy a))
  pickMin-spec nothing x = x , ≡-refl , inj₁ ≡-refl , ≤-refl , λ a ()
  pickMin-spec (just b) x with candEnergy x <? candEnergy b
  ... | yes p = x , ≡-refl , inj₁ ≡-refl , ≤-refl , λ { a ≡-refl → <⇒≤ p }
  ... | no ¬p with candEnergy b <? candEnergy x
  ...   | yes q = b , ≡-refl , inj₂ ≡-refl , <⇒≤ q , λ { a ≡-refl → ≤-refl }
  ...   | no ¬q with cid x <ᵇ cid b
  ...     | true = x , ≡-refl , inj₁ ≡-refl , ≤-refl , λ { a ≡-refl → ≮⇒≥ ¬q }
  ...     | false = b , ≡-refl , inj₂ ≡-refl , ≮⇒≥ ¬p , λ { a ≡-refl → ≤-refl }

  fold-spec : ∀ l acc m → foldl pickMin acc l ≡ just m →
    (m ∈ l ⊎ acc ≡ just m) × (∀ {x} → x ∈ l → candEnergy m ≤ candEnergy x) × (∀ a → acc ≡ just a → candEnergy m ≤ candEnergy a)
  fold-spec [] acc m h = inj₂ h , (λ ()) , λ a eq → ≤-reflexive (cong candEnergy (just-injective (≡-trans (sym h) eq)))
  fold-spec (x ∷ xs) acc m h with pickMin-spec acc x
  ... | r , hr , hrmem , hrx , hracc with fold-spec xs (just r) m (subst (λ z → foldl pickMin z xs ≡ just m) hr h)
  ...   | hmem , hle , hseed = mem hmem hrmem , le , λ a eq → ≤-trans hmr (hracc a eq)
    where
    hmr : candEnergy m ≤ candEnergy r
    hmr = hseed r ≡-refl
    mem : (m ∈ xs ⊎ just r ≡ just m) → (r ≡ x ⊎ acc ≡ just r) → (m ∈ x ∷ xs ⊎ acc ≡ just m)
    mem (inj₁ m∈) _ = inj₁ (there m∈)
    mem (inj₂ eq) (inj₁ ≡-refl) with just-injective eq
    ... | ≡-refl = inj₁ (here ≡-refl)
    mem (inj₂ eq) (inj₂ acc≡) with just-injective eq
    ... | ≡-refl = inj₂ acc≡
    le : ∀ {y} → y ∈ x ∷ xs → candEnergy m ≤ candEnergy y
    le (here ≡-refl) = ≤-trans hmr hrx
    le (there y∈) = hle y∈

  decide-inl : ∀ c c′ → decide c ≡ inj₁ c′ → c ≡ c′ × candEnergy c < jointFreeEnergy src
  decide-inl c c′ h with candEnergy c <? jointFreeEnergy src
  decide-inl c .c ≡-refl | yes p = ≡-refl , p
  decide-inl c c′ () | no _

  onTagged-inl : ∀ cands tagged c → onTagged cands tagged ≡ inj₁ c →
    foldl pickMin nothing tagged ≡ just c × candEnergy c < jointFreeEnergy src
  onTagged-inl cands [] c h with anyᵇ (λ c → not (evidenceTagged c)) cands
  onTagged-inl cands [] c () | true
  onTagged-inl cands [] c () | false
  onTagged-inl cands (t ∷ ts) c h with foldl pickMin nothing (t ∷ ts)
  onTagged-inl cands (t ∷ ts) c () | nothing
  onTagged-inl cands (t ∷ ts) c h | just m with decide-inl m c h
  ... | ≡-refl , lt = ≡-refl , lt

  select-inl-spec : ∀ cands c → select cands ≡ inj₁ c →
    foldl pickMin nothing (filterᵇ evidenceTagged cands) ≡ just c × candEnergy c < jointFreeEnergy src
  select-inl-spec [] c ()
  select-inl-spec (x ∷ xs) c h = onTagged-inl (x ∷ xs) (filterᵇ evidenceTagged (x ∷ xs)) c h

  -- Selection is a minimum: the selected candidate is an evidence-tagged member and no evidence-tagged candidate has
  -- lower global free energy.
  select-minimal : ∀ cands c → select cands ≡ inj₁ c →
    c ∈ cands × evidenceTagged c ≡ true × (∀ {c′} → c′ ∈ cands → evidenceTagged c′ ≡ true → candEnergy c ≤ candEnergy c′)
  select-minimal cands c h with fold-spec (filterᵇ evidenceTagged cands) nothing c (proj₁ (select-inl-spec cands c h))
  ... | inj₂ () , _ , _
  ... | inj₁ c∈ , hle , _ =
    proj₁ (∈-filterᵇ⁻ evidenceTagged cands c∈) , proj₂ (∈-filterᵇ⁻ evidenceTagged cands c∈) ,
    λ c′∈ t → hle (∈-filterᵇ⁺ evidenceTagged cands c′∈ t)

  -- Selection descends: the selected candidate's global free energy is strictly below the source's.
  select-descent : ∀ cands c → select cands ≡ inj₁ c → candEnergy c < jointFreeEnergy src
  select-descent cands c h = proj₂ (select-inl-spec cands c h)

  -- Every candidate move is a member of the second-law predicate.
  cand-secondLaw : ∀ c → SecondLaw transition (thermodynamic src (tgt c))
  cand-secondLaw c = proj₁ (Equivalence.to (admissible⇔secondLaw src (tgt c)) (step c))

  ------------------------------------------------------------------------
  -- Order independence: the lexicographic order on (energy, id), its minimum, and the fold over a permutation.

  -- c comes before b: lower energy, or equal energy and lower id.
  data _≺_ (c b : Cand) : Set where
    lt  : candEnergy c < candEnergy b → c ≺ b
    tie : candEnergy c ≡ candEnergy b → cid c <ℕ cid b → c ≺ b

  ≺-trans : ∀ {a b c} → c ≺ b → b ≺ a → c ≺ a
  ≺-trans (lt p) (lt q) = lt (ℚP.<-trans p q)
  ≺-trans {a} {b} {c} (lt p) (tie e _) = lt (subst (candEnergy c <_) e p)
  ≺-trans {a} {b} {c} (tie e _) (lt q) = lt (subst (_< candEnergy a) (sym e) q)
  ≺-trans (tie e i) (tie e′ i′) = tie (≡-trans e e′) (ℕP.<-trans i i′)

  ≺-asym : ∀ {b c} → c ≺ b → ¬ b ≺ c
  ≺-asym (lt p) (lt q) = ℚP.<-asym p q
  ≺-asym (lt p) (tie e _) = ℚP.<-irrefl (sym e) p
  ≺-asym (tie e _) (lt q) = ℚP.<-irrefl (sym e) q
  ≺-asym (tie _ i) (tie _ i′) = ℕP.<-asym i i′

  ≺-irr : ∀ {b c} → candEnergy c ≡ candEnergy b → cid c ≡ cid b → ¬ c ≺ b
  ≺-irr e ie (lt q) = ℚP.<-irrefl e q
  ≺-irr e ie (tie _ i) = ℕP.<-irrefl ie i

  ≺-total : ∀ b c → cid c ≢ cid b → ¬ c ≺ b → b ≺ c
  ≺-total b c ne n with ℚP.<-cmp (candEnergy c) (candEnergy b)
  ... | tri< p _ _ = ⊥-elim (n (lt p))
  ... | tri> _ _ p = lt p
  ... | tri≈ _ e _ with ℕP.<-cmp (cid c) (cid b)
  ...   | tri< i _ _ = ⊥-elim (n (tie e i))
  ...   | tri≈ _ ie _ = ⊥-elim (ne ie)
  ...   | tri> _ _ i = tie (sym e) i

  -- c before a, and b not before a: c before b.
  ≺-≼-trans : ∀ {a b c} → c ≺ a → ¬ b ≺ a → c ≺ b
  ≺-≼-trans {a} {b} {c} h n with ℚP.<-cmp (candEnergy a) (candEnergy b)
  ... | tri> _ _ p = ⊥-elim (n (lt p))
  ≺-≼-trans {a} {b} {c} (lt q) n | tri< p _ _ = lt (ℚP.<-trans q p)
  ≺-≼-trans {a} {b} {c} (tie e _) n | tri< p _ _ = lt (subst (_< candEnergy b) (sym e) p)
  ≺-≼-trans {a} {b} {c} (lt q) n | tri≈ _ e _ = lt (subst (candEnergy c <_) e q)
  ≺-≼-trans {a} {b} {c} (tie e′ i) n | tri≈ _ e _ =
    tie (≡-trans e′ e) (ℕP.<-≤-trans i (ℕP.≮⇒≥ (λ j → n (tie (sym e) j))))

  ≺? : ∀ c b → (c ≺ b) ⊎ (¬ c ≺ b)
  ≺? c b with ℚP.<-cmp (candEnergy c) (candEnergy b)
  ... | tri< p _ _ = inj₁ (lt p)
  ... | tri> _ _ p = inj₂ (≺-asym (lt p))
  ... | tri≈ _ e _ with ℕP.<-cmp (cid c) (cid b)
  ...   | tri< i _ _ = inj₁ (tie e i)
  ...   | tri≈ _ ie _ = inj₂ (≺-irr e ie)
  ...   | tri> _ _ i = inj₂ (≺-asym (tie (sym e) i))

  -- The minimum: the challenger c replaces b exactly when it comes before b.
  minK : Cand → Cand → Cand
  minK b c with ≺? c b
  ... | inj₁ _ = c
  ... | inj₂ _ = b

  minK-≺ : ∀ b c → c ≺ b → minK b c ≡ c
  minK-≺ b c h with ≺? c b
  ... | inj₁ _ = ≡-refl
  ... | inj₂ n = ⊥-elim (n h)

  minK-⊀ : ∀ b c → ¬ c ≺ b → minK b c ≡ b
  minK-⊀ b c n with ≺? c b
  ... | inj₁ h = ⊥-elim (n h)
  ... | inj₂ _ = ≡-refl

  minK-assoc : ∀ a b c → minK (minK a b) c ≡ minK a (minK b c)
  minK-assoc a b c with ≺? b a | ≺? c b
  ... | inj₁ ba | inj₁ cb rewrite minK-≺ b c cb = sym (minK-≺ a c (≺-trans cb ba))
  ... | inj₁ ba | inj₂ ncb rewrite minK-≺ a b ba | minK-⊀ b c ncb = ≡-refl
  ... | inj₂ nba | inj₁ cb = ≡-refl
  ... | inj₂ nba | inj₂ ncb =
    ≡-trans (minK-⊀ a c (λ ca → ncb (≺-≼-trans ca nba))) (sym (minK-⊀ a b nba))

  minK-comm : ∀ x y → cid x ≢ cid y → minK x y ≡ minK y x
  minK-comm x y ne with ≺? y x
  ... | inj₁ yx = sym (minK-⊀ y x (≺-asym yx))
  ... | inj₂ nyx = sym (minK-≺ y x (≺-total x y (λ e → ne (sym e)) nyx))

  pickMin-≺ : ∀ b c → c ≺ b → pickMin (just b) c ≡ just c
  pickMin-≺ b c h with candEnergy c <? candEnergy b
  ... | yes _ = ≡-refl
  ... | no ¬p with candEnergy b <? candEnergy c
  ...   | yes q = ⊥-elim (≺-asym h (lt q))
  ...   | no ¬q with cid c <ᵇ cid b in eq
  ...     | true = ≡-refl
  ...     | false with h
  ...       | lt p = ⊥-elim (¬p p)
  ...       | tie _ i = ⊥-elim (subst T eq (ℕP.<⇒<ᵇ i))

  pickMin-⊀ : ∀ b c → ¬ c ≺ b → pickMin (just b) c ≡ just b
  pickMin-⊀ b c n with candEnergy c <? candEnergy b
  ... | yes p = ⊥-elim (n (lt p))
  ... | no ¬p with candEnergy b <? candEnergy c
  ...   | yes _ = ≡-refl
  ...   | no ¬q with cid c <ᵇ cid b in eq
  ...     | false = ≡-refl
  ...     | true = ⊥-elim (n (tie (ℚP.≤-antisym (ℚP.≮⇒≥ ¬q) (ℚP.≮⇒≥ ¬p)) (ℕP.<ᵇ⇒< _ _ (subst T (sym eq) tt))))

  pickMin-minK : ∀ b c → pickMin (just b) c ≡ just (minK b c)
  pickMin-minK b c with ≺? c b
  ... | inj₁ h = pickMin-≺ b c h
  ... | inj₂ n = pickMin-⊀ b c n

  -- One step of the fold commutes with the next for candidates of distinct ids.
  pickMin-right-comm : ∀ z x y → cid x ≢ cid y → pickMin (pickMin z x) y ≡ pickMin (pickMin z y) x
  pickMin-right-comm nothing x y ne rewrite pickMin-minK x y | pickMin-minK y x = cong just (minK-comm x y ne)
  pickMin-right-comm (just a) x y ne
    rewrite pickMin-minK a x | pickMin-minK a y | pickMin-minK (minK a x) y | pickMin-minK (minK a y) x =
    cong just (≡-trans (minK-assoc a x y) (≡-trans (cong (minK a) (minK-comm x y ne)) (sym (minK-assoc a y x))))

  _≢ᶜ_ : Cand → Cand → Set
  c ≢ᶜ d = cid c ≢ cid d

  Distinct : List Cand → Set
  Distinct = AllPairs _≢ᶜ_

  distinct-↭ : ∀ {xs ys} → xs ↭ ys → Distinct xs → Distinct ys
  distinct-↭ refl d = d
  distinct-↭ (prep x p) (px ∷ d) = All-resp-↭ p px ∷ distinct-↭ p d
  distinct-↭ (swap x y p) ((x≢y ∷ px) ∷ (py ∷ d)) = ((λ e → x≢y (sym e)) ∷ All-resp-↭ p py) ∷ (All-resp-↭ p px ∷ distinct-↭ p d)
  distinct-↭ (trans p q) d = distinct-↭ q (distinct-↭ p d)

  -- The fold is invariant under permutation of candidates with distinct ids.
  fold-↭ : ∀ {xs ys} → xs ↭ ys → Distinct xs → ∀ acc → foldl pickMin acc xs ≡ foldl pickMin acc ys
  fold-↭ refl _ acc = ≡-refl
  fold-↭ (prep x p) (_ ∷ d) acc = fold-↭ p d (pickMin acc x)
  fold-↭ (swap x y p) ((x≢y ∷ _) ∷ (_ ∷ d)) acc rewrite pickMin-right-comm acc x y x≢y = fold-↭ p d (pickMin (pickMin acc y) x)
  fold-↭ (trans p q) d acc = ≡-trans (fold-↭ p d acc) (fold-↭ q (distinct-↭ p d) acc)

  -- filterᵇ on a cons cell, as an explicit choice on the head.
  fb : ∀ x xs → filterᵇ evidenceTagged (x ∷ xs) ≡ (if evidenceTagged x then x ∷ filterᵇ evidenceTagged xs else filterᵇ evidenceTagged xs)
  fb x xs with evidenceTagged x
  ... | true = ≡-refl
  ... | false = ≡-refl

  filter-↭ : ∀ {xs ys} → xs ↭ ys → filterᵇ evidenceTagged xs ↭ filterᵇ evidenceTagged ys
  filter-↭ refl = refl
  filter-↭ (prep x p) with evidenceTagged x
  ... | true = prep x (filter-↭ p)
  ... | false = filter-↭ p
  filter-↭ (swap {xs} {ys} x y p) rewrite fb x (y ∷ xs) | fb y xs | fb y (x ∷ ys) | fb x ys
    with evidenceTagged x | evidenceTagged y
  ... | true | true = swap x y (filter-↭ p)
  ... | true | false = prep x (filter-↭ p)
  ... | false | true = prep y (filter-↭ p)
  ... | false | false = filter-↭ p
  filter-↭ (trans p q) = trans (filter-↭ p) (filter-↭ q)

  all-filter : ∀ {c} xs → All (c ≢ᶜ_) xs → All (c ≢ᶜ_) (filterᵇ evidenceTagged xs)
  all-filter [] a = a
  all-filter {c} (x ∷ xs) (px ∷ a) with evidenceTagged x
  ... | true = px ∷ all-filter {c} xs a
  ... | false = all-filter {c} xs a

  distinct-filter : ∀ xs → Distinct xs → Distinct (filterᵇ evidenceTagged xs)
  distinct-filter [] d = d
  distinct-filter (x ∷ xs) (px ∷ d) with evidenceTagged x
  ... | true = all-filter {x} xs px ∷ distinct-filter xs d
  ... | false = distinct-filter xs d

  anyᵇ-↭ : ∀ (g : Cand → Bool) {xs ys} → xs ↭ ys → anyᵇ g xs ≡ anyᵇ g ys
  anyᵇ-↭ g refl = ≡-refl
  anyᵇ-↭ g (prep x p) = cong (λ r → if g x then true else r) (anyᵇ-↭ g p)
  anyᵇ-↭ g (swap x y p) with g x | g y
  ... | true | true = ≡-refl
  ... | true | false = ≡-refl
  ... | false | true = ≡-refl
  ... | false | false = anyᵇ-↭ g p
  anyᵇ-↭ g (trans p q) = ≡-trans (anyᵇ-↭ g p) (anyᵇ-↭ g q)

  onTagged-↭ : ∀ {cs cs′ t t′} → cs ↭ cs′ → t ↭ t′ → Distinct t → onTagged cs t ≡ onTagged cs′ t′
  onTagged-↭ {t = []} {t′ = []} p q d = cong (λ b → if b then inj₂ allInadmissible else inj₂ untaggedConstant)
    (anyᵇ-↭ (λ c → not (evidenceTagged c)) p)
  onTagged-↭ {t = []} {t′ = _ ∷ _} p q d = ⊥-elim (¬x∷xs↭[] (↭-sym q))
  onTagged-↭ {t = _ ∷ _} {t′ = []} p q d = ⊥-elim (¬x∷xs↭[] q)
  onTagged-↭ {t = _ ∷ _} {t′ = _ ∷ _} p q d = cong onFold (fold-↭ q d nothing)

  -- Selection does not depend on the order of candidates with distinct ids.
  select-perm-invariant : ∀ {xs ys} → xs ↭ ys → Distinct xs → select xs ≡ select ys
  select-perm-invariant {[]} {[]} p d = ≡-refl
  select-perm-invariant {[]} {_ ∷ _} p d = ⊥-elim (¬x∷xs↭[] (↭-sym p))
  select-perm-invariant {_ ∷ _} {[]} p d = ⊥-elim (¬x∷xs↭[] p)
  select-perm-invariant {x ∷ xs} {y ∷ ys} p d = onTagged-↭ p (filter-↭ p) (distinct-filter (x ∷ xs) d)
