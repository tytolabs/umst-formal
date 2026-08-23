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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
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

interact-identity : KleisliArrow
interact-identity s = just s

admissible-step : ThermodynamicState → ThermodynamicState → Set
admissible-step = Admissible

WellTyped : KleisliArrow → Set
WellTyped f = ∀ s s' → f s ≡ just s' → admissible-step s s'

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

kleisli-compose : KleisliArrow → KleisliArrow → KleisliArrow
kleisli-compose f g s = go (f s)
  where
  go : Maybe ThermodynamicState → Maybe ThermodynamicState
  go nothing = nothing
  go (just s') = g s'

make-gate-arrow : (ThermodynamicState → ThermodynamicState) → KleisliArrow
make-gate-arrow propose s with gate s (propose s)
... | yes prf = just (propose s)
... | no ¬prf = nothing

gate-arrow-wellTyped :
  ∀ propose → WellTyped (make-gate-arrow propose)
gate-arrow-wellTyped propose s s' eq with gate s (propose s)
... | yes prf = subst (admissible-step s) (just-injective eq) prf
... | no ¬prf = ⊥-elim (nothing≢just eq)

kleisli-compose-two-step-safe :
  ∀ (f g : KleisliArrow) → WellTyped f → WellTyped g →
  ∀ s s' s'' → f s ≡ just s' → g s' ≡ just s'' → Admissible s s' × Admissible s' s''
kleisli-compose-two-step-safe f g hf hg s s' s'' hfs hgs =
  hf s s' hfs , hg s' s'' hgs

kleisli-fold : List.List KleisliArrow → KleisliArrow
kleisli-fold List.[] = λ s → just s
kleisli-fold (f List.∷ List.[]) = f
kleisli-fold (f List.∷ g List.∷ rest) = kleisli-compose f (kleisli-fold (g List.∷ rest))

AllWellTyped : List.List KleisliArrow → Set
AllWellTyped List.[] = ⊤
AllWellTyped (f List.∷ fs) = WellTyped f × AllWellTyped fs

identity-wellTyped : WellTyped interact-identity
identity-wellTyped s s' eq =
  subst (admissible-step s) (just-injective eq) (admissible-refl s)

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
kleisli-compose-assoc f g h s with f s
... | nothing = refl
... | just s' with g s'
... | nothing = refl
... | just s'' = refl

kleisli-left-unit :
  ∀ (f : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose interact-identity f s ≡ f s
kleisli-left-unit f s with f s
... | nothing = refl
... | just _ = refl

kleisli-right-unit :
  ∀ (f : KleisliArrow) (s : ThermodynamicState) →
  kleisli-compose f interact-identity s ≡ f s
kleisli-right-unit f s with f s
... | nothing = refl
... | just _ = refl

kleisli-coherence-units :
  ∀ (f : KleisliArrow) (s g h : ThermodynamicState) →
  kleisli-compose interact-identity f s ≡ just g →
  kleisli-compose f interact-identity s ≡ just h →
  g ≡ h
kleisli-coherence-units f s g h hleft hright =
  let hfs = subst (λ m → m ≡ just g) (kleisli-left-unit f s) hleft
      hfs' = subst (λ m → m ≡ just h) (kleisli-right-unit f s) hright
  in just-injective (trans (sym hfs) hfs')

------------------------------------------------------------------------
-- Meso acting honesty fence (mirrors HS / Lean / Coq — physics GREEN false)
------------------------------------------------------------------------

chem-physics-green : Bool
chem-physics-green = false

chem-physics-green-false : chem-physics-green ≡ false
chem-physics-green-false = refl

kleisli-interact-production-wired : Bool
kleisli-interact-production-wired = false

kleisli-interact-production-wired-false :
  kleisli-interact-production-wired ≡ false
kleisli-interact-production-wired-false = refl

------------------------------------------------------------------------
-- Module witness (meso acting Kleisli Interact anchor)
------------------------------------------------------------------------

kleisliInteractModuleWitness : ⊤
kleisliInteractModuleWitness = tt
