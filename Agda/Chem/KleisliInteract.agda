-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.KleisliInteract — meso/acting Kleisli Interact layer.
--
-- Mirrors Lean `UMST.Compat.Constitutional` / `Chem/KleisliInteract.lean`:
--   Kleisli arrows over cement `ThermodynamicState`, gate-mediated Interact,
--   composition safety, identity / associativity / unit coherence.
--
-- CHEM-NS-W5-FORMAL-THEOREMS (umst-formal/meso_acting fiber only).
-- physics_green: false — no new physics postulates beyond `Chem.SecondLaw`.
------------------------------------------------------------------------

module Chem.KleisliInteract where

open import Chem.SecondLaw
open import Concrete.Gate
open Concrete.Gate using (ThermodynamicState; Admissible; gate; mkAdmissible)
open import Core.Gate using (δ-mass)
open ThermodynamicState
open Admissible

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
import Data.List as List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _+_; _-_; _≤_)
open import Data.Rational.Properties as ℚ-Props using (+-inverseʳ; ≤-refl; ≤-trans)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (from-yes)

------------------------------------------------------------------------
-- Reflexivity helpers (no new postulates)
------------------------------------------------------------------------

qdiff-self-≤ : ∀ x → x - x ≤ 0ℚ
qdiff-self-≤ x rewrite +-inverseʳ x = ℚ-Props.≤-refl

δ-mass-nonneg : 0ℚ ≤ δ-mass
δ-mass-nonneg = from-yes (0ℚ ℚ.≤? δ-mass)

qdiff-self-≤δ : ∀ x → x - x ≤ δ-mass
qdiff-self-≤δ x = ℚ-Props.≤-trans (qdiff-self-≤ x) δ-mass-nonneg

admissible-refl : ∀ s → Admissible s s
admissible-refl s = mkAdmissible
  (qdiff-self-≤δ (density s) , qdiff-self-≤δ (density s))
  ℚ-Props.≤-refl
  ℚ-Props.≤-refl
  ℚ-Props.≤-refl

------------------------------------------------------------------------
-- Kleisli Interact arrows (mirrors `UMST.Compat.Constitutional`)
------------------------------------------------------------------------

KleisliArrow : Set
KleisliArrow = ThermodynamicState → Maybe ThermodynamicState

WellTyped : KleisliArrow → Set
WellTyped f = ∀ s s' → f s ≡ just s' → Admissible s s'

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

kleisli-compose : KleisliArrow → KleisliArrow → KleisliArrow
kleisli-compose f g s = go (f s)
  where
  go : Maybe ThermodynamicState → Maybe ThermodynamicState
  go nothing = nothing
  go (just s') = g s'

kleisli-compose-two-step-safe :
  ∀ (f g : KleisliArrow) → WellTyped f → WellTyped g →
  ∀ s s' s'' → f s ≡ just s' → g s' ≡ just s'' → Admissible s s' × Admissible s' s''
kleisli-compose-two-step-safe f g hf hg s s' s'' hfs hgs =
  hf s s' hfs , hg s' s'' hgs

kleisli-compose-output-admissible :
  ∀ (f g : KleisliArrow) → WellTyped f → WellTyped g →
  ∀ s s'' → kleisli-compose f g s ≡ just s'' →
  ∃[ s' ] (f s ≡ just s' × g s' ≡ just s'' × Admissible s s' × Admissible s' s'')
kleisli-compose-output-admissible f g hf hg s s'' eq with f s
kleisli-compose-output-admissible f g hf hg s s'' eq | nothing = ⊥-elim (nothing≢just eq)
kleisli-compose-output-admissible f g hf hg s s'' eq | just s' =
  s' , (refl , eq , hf s s' refl , hg s' s'' eq)

kleisli-fold : List.List KleisliArrow → KleisliArrow
kleisli-fold List.[] = λ s → just s
kleisli-fold (f List.∷ List.[]) = f
kleisli-fold (f List.∷ g List.∷ rest) = kleisli-compose f (kleisli-fold (g List.∷ rest))

AllWellTyped : List.List KleisliArrow → Set
AllWellTyped List.[] = ⊤
AllWellTyped (f List.∷ fs) = WellTyped f × AllWellTyped fs

identity-wellTyped : WellTyped (λ s → just s)
identity-wellTyped s s' eq =
  subst (Admissible s) (just-injective eq) (admissible-refl s)

kleisli-fold-id-wellTyped : WellTyped (kleisli-fold List.[])
kleisli-fold-id-wellTyped = identity-wellTyped

kleisli-fold-singleton-wellTyped :
  ∀ f → WellTyped f → WellTyped (kleisli-fold (f List.∷ List.[]))
kleisli-fold-singleton-wellTyped f wf = wf

------------------------------------------------------------------------
-- Kleisli category laws (pointwise — no funext postulate)
------------------------------------------------------------------------

kleisli-compose-assoc :
  ∀ (f g h : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose (kleisli-compose f g) h s ≡ kleisli-compose f (kleisli-compose g h) s
kleisli-compose-assoc f g h s = go (f s)
  where
  go : Maybe ThermodynamicState → _
  go nothing = refl
  go (just s') = go₂ (g s')
    where
    go₂ : Maybe ThermodynamicState → _
    go₂ nothing = refl
    go₂ (just _) = refl

kleisli-left-unit :
  ∀ (f : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose (λ s → just s) f s ≡ f s
kleisli-left-unit f s = go (f s)
  where
  go : Maybe ThermodynamicState → _
  go nothing = refl
  go (just _) = refl

kleisli-right-unit :
  ∀ (f : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose f (λ s → just s) s ≡ f s
kleisli-right-unit f s = go (f s)
  where
  go : Maybe ThermodynamicState → _
  go nothing = refl
  go (just _) = refl

------------------------------------------------------------------------
-- Module witness (meso acting Kleisli Interact anchor)
------------------------------------------------------------------------

kleisliInteractModuleWitness : KleisliArrow → Set
kleisliInteractModuleWitness f = WellTyped f
