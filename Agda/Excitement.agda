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
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Rational using (ℚ; _+_; _≤_; _<_; _<?_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; ≤-reflexive; <⇒≤; ≮⇒≥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

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
...   | here refl = here refl , eq
...   | there v∈′ = let (m , q) = ∈-filterᵇ⁻ p xs v∈′ in there m , q
∈-filterᵇ⁻ p (x ∷ xs) v∈ | false = let (m , q) = ∈-filterᵇ⁻ p xs v∈ in there m , q

∈-filterᵇ⁺ : {A : Set} (p : A → Bool) (xs : List A) {v : A} → v ∈ xs → p v ≡ true → v ∈ filterᵇ p xs
∈-filterᵇ⁺ p (x ∷ xs) (here refl) pv with p x
∈-filterᵇ⁺ p (x ∷ xs) (here refl) refl | true = here refl
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
  select-empty = refl

  pickMin-spec : ∀ acc x → ∃[ r ] (pickMin acc x ≡ just r × (r ≡ x ⊎ acc ≡ just r) × candEnergy r ≤ candEnergy x ×
    (∀ a → acc ≡ just a → candEnergy r ≤ candEnergy a))
  pickMin-spec nothing x = x , refl , inj₁ refl , ≤-refl , λ a ()
  pickMin-spec (just b) x with candEnergy x <? candEnergy b
  ... | yes p = x , refl , inj₁ refl , ≤-refl , λ { a refl → <⇒≤ p }
  ... | no ¬p with candEnergy b <? candEnergy x
  ...   | yes q = b , refl , inj₂ refl , <⇒≤ q , λ { a refl → ≤-refl }
  ...   | no ¬q with cid x <ᵇ cid b
  ...     | true = x , refl , inj₁ refl , ≤-refl , λ { a refl → ≮⇒≥ ¬q }
  ...     | false = b , refl , inj₂ refl , ≮⇒≥ ¬p , λ { a refl → ≤-refl }

  fold-spec : ∀ l acc m → foldl pickMin acc l ≡ just m →
    (m ∈ l ⊎ acc ≡ just m) × (∀ {x} → x ∈ l → candEnergy m ≤ candEnergy x) × (∀ a → acc ≡ just a → candEnergy m ≤ candEnergy a)
  fold-spec [] acc m h = inj₂ h , (λ ()) , λ a eq → ≤-reflexive (cong candEnergy (just-injective (trans (sym h) eq)))
  fold-spec (x ∷ xs) acc m h with pickMin-spec acc x
  ... | r , hr , hrmem , hrx , hracc with fold-spec xs (just r) m (subst (λ z → foldl pickMin z xs ≡ just m) hr h)
  ...   | hmem , hle , hseed = mem hmem hrmem , le , λ a eq → ≤-trans hmr (hracc a eq)
    where
    hmr : candEnergy m ≤ candEnergy r
    hmr = hseed r refl
    mem : (m ∈ xs ⊎ just r ≡ just m) → (r ≡ x ⊎ acc ≡ just r) → (m ∈ x ∷ xs ⊎ acc ≡ just m)
    mem (inj₁ m∈) _ = inj₁ (there m∈)
    mem (inj₂ eq) (inj₁ refl) with just-injective eq
    ... | refl = inj₁ (here refl)
    mem (inj₂ eq) (inj₂ acc≡) with just-injective eq
    ... | refl = inj₂ acc≡
    le : ∀ {y} → y ∈ x ∷ xs → candEnergy m ≤ candEnergy y
    le (here refl) = ≤-trans hmr hrx
    le (there y∈) = hle y∈

  decide-inl : ∀ c c′ → decide c ≡ inj₁ c′ → c ≡ c′ × candEnergy c < jointFreeEnergy src
  decide-inl c c′ h with candEnergy c <? jointFreeEnergy src
  decide-inl c .c refl | yes p = refl , p
  decide-inl c c′ () | no _

  onTagged-inl : ∀ cands tagged c → onTagged cands tagged ≡ inj₁ c →
    foldl pickMin nothing tagged ≡ just c × candEnergy c < jointFreeEnergy src
  onTagged-inl cands [] c h with anyᵇ (λ c → not (evidenceTagged c)) cands
  onTagged-inl cands [] c () | true
  onTagged-inl cands [] c () | false
  onTagged-inl cands (t ∷ ts) c h with foldl pickMin nothing (t ∷ ts)
  onTagged-inl cands (t ∷ ts) c () | nothing
  onTagged-inl cands (t ∷ ts) c h | just m with decide-inl m c h
  ... | refl , lt = refl , lt

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
