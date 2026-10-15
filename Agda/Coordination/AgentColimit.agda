-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal: Coordination/AgentColimit.agda
--
-- Twin of Lean/Coordination/AgentColimit.lean and Coq/Coordination/AgentColimit.v. An agent observes a world W
-- through a map W → A; agent c knows agent a when equal c-readings give equal a-readings. The glued agent observes
-- the pair; it knows both agents, and every agent that knows both knows it: the join in the information order.
-- The kernel of the glued agent is the meet of the two kernels.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Coordination.AgentColimit where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

module _ {w} {W : Set w} where

  -- Agent c knows agent a: c's reading of the world determines a's.
  Knows : ∀ {c a} {C : Set c} {A : Set a} → (W → C) → (W → A) → Set _
  Knows c a = ∀ x y → c x ≡ c y → a x ≡ a y

  -- The glued agent observes both readings at once.
  glue : ∀ {a b} {A : Set a} {B : Set b} → (W → A) → (W → B) → W → A × B
  glue a b x = a x , b x

  knows-refl : ∀ {a} {A : Set a} (f : W → A) → Knows f f
  knows-refl f x y h = h

  knows-trans : ∀ {c b a} {C : Set c} {B : Set b} {A : Set a} {f : W → C} {g : W → B} {h : W → A} →
    Knows f g → Knows g h → Knows f h
  knows-trans k₁ k₂ x y e = k₂ x y (k₁ x y e)

  glue-knows-left : ∀ {a b} {A : Set a} {B : Set b} (f : W → A) (g : W → B) → Knows (glue f g) f
  glue-knows-left f g x y e = cong proj₁ e

  glue-knows-right : ∀ {a b} {A : Set a} {B : Set b} (f : W → A) (g : W → B) → Knows (glue f g) g
  glue-knows-right f g x y e = cong proj₂ e

  -- Universal property: an agent that knows both agents knows the glued agent.
  glue-universal : ∀ {c a b} {C : Set c} {A : Set a} {B : Set b} {h : W → C} {f : W → A} {g : W → B} →
    Knows h f → Knows h g → Knows h (glue f g)
  glue-universal kf kg x y e = cong₂ _,_ (kf x y e) (kg x y e)

  -- An agent that knows the glued agent knows both agents.
  knows-glue-elim : ∀ {c a b} {C : Set c} {A : Set a} {B : Set b} {h : W → C} {f : W → A} {g : W → B} →
    Knows h (glue f g) → Knows h f × Knows h g
  knows-glue-elim {f = f} {g = g} k = knows-trans k (glue-knows-left f g) , knows-trans k (glue-knows-right f g)

  -- The glued agent is the join: h knows it iff h knows both.
  knows-glue-⇔ : ∀ {c a b} {C : Set c} {A : Set a} {B : Set b} {h : W → C} {f : W → A} {g : W → B} →
    Knows h (glue f g) ⇔ (Knows h f × Knows h g)
  knows-glue-⇔ = mk⇔ knows-glue-elim (λ { (kf , kg) → glue-universal kf kg })

  -- The kernel of an agent: the pairs of worlds it does not tell apart.
  ker : ∀ {a} {A : Set a} → (W → A) → W → W → Set a
  ker f x y = f x ≡ f y

  -- The kernel of the glued agent is the meet of the two kernels.
  ker-glue : ∀ {a b} {A : Set a} {B : Set b} (f : W → A) (g : W → B) (x y : W) →
    ker (glue f g) x y ⇔ (ker f x y × ker g x y)
  ker-glue f g x y = mk⇔ (λ e → cong proj₁ e , cong proj₂ e) (λ { (e₁ , e₂) → cong₂ _,_ e₁ e₂ })

  -- A factorisation through c makes c know a.
  factors-knows : ∀ {c a} {C : Set c} {A : Set a} (h : W → C) (f : W → A) (φ : C → A) →
    (∀ x → f x ≡ φ (h x)) → Knows h f
  factors-knows h f φ hf x y e = trans (hf x) (trans (cong φ e) (sym (hf y)))
