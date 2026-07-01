------------------------------------------------------------------------
-- UMST.Concrete.Gate — OPC cement cartridge (full admissibility + gate).
------------------------------------------------------------------------

module Concrete.Gate where

open import Data.Integer.Base as ℤ using (ℤ; +_; ∣_∣)
open import Data.Nat.Coprimality as ℕ using (sym; 1-coprimeTo)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; mkℚ; _+_; _*_; _-_; _≤_; _<_)
open import Data.Rational.Properties as ℚ-Props
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Core.Gate as Core using (δ-mass; ThermodynamicSystem)
open ThermodynamicSystem

------------------------------------------------------------------------
-- 1. Thermodynamic State (cementitious cartridge)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  constructor mkState
  field
    density     : ℚ   -- ρ
    free-energy : ℚ   -- ψ = −Q_hyd · α  in the Rust kernel
    hydration   : ℚ   -- α
    strength    : ℚ   -- fc

open ThermodynamicState

------------------------------------------------------------------------
-- ThermodynamicSystem instance for universal core predicates
------------------------------------------------------------------------

concrete-thermodynamic-system : ThermodynamicSystem ThermodynamicState
concrete-thermodynamic-system = record
  { density     = λ s → density s
  ; free-energy = λ s → free-energy s
  }

------------------------------------------------------------------------
-- 3. Admissibility Predicate (core + constitutive order constraints)
------------------------------------------------------------------------

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    mass-conserved : (density new - density old ≤ δ-mass)
                   × (density old - density new ≤ δ-mass)
    dissipation-nonneg : free-energy new ≤ free-energy old
    hydration-monotone : hydration old ≤ hydration new
    strength-monotone : strength old ≤ strength new

open Admissible

------------------------------------------------------------------------
-- 4. Gate Decision Procedure
------------------------------------------------------------------------

gate : (old new : ThermodynamicState) → Dec (Admissible old new)
gate old new with (density new - density old) ℚ.≤? δ-mass
                 | (density old - density new) ℚ.≤? δ-mass
                 | free-energy new ℚ.≤? free-energy old
                 | hydration old ℚ.≤? hydration new
                 | strength old ℚ.≤? strength new
... | yes mc₁ | yes mc₂ | yes diss | yes hyd | yes str =
      yes (mkAdmissible (mc₁ , mc₂) diss hyd str)
... | no ¬mc₁ | _       | _        | _       | _       =
      no (λ adm → ¬mc₁ (proj₁ (mass-conserved adm)))
... | _       | no ¬mc₂ | _        | _       | _       =
      no (λ adm → ¬mc₂ (proj₂ (mass-conserved adm)))
... | _       | _       | no ¬diss | _       | _       =
      no (λ adm → ¬diss (dissipation-nonneg adm))
... | _       | _       | _        | no ¬hyd | _       =
      no (λ adm → ¬hyd (hydration-monotone adm))
... | _       | _       | _        | _       | no ¬str =
      no (λ adm → ¬str (strength-monotone adm))

------------------------------------------------------------------------
-- 5. Physical Model Postulates (Concrete cartridge only)
------------------------------------------------------------------------

postulate
  ψ-antitone : ∀ (s₁ s₂ : ThermodynamicState) →
    hydration s₁ ≤ hydration s₂ →
    free-energy s₂ ≤ free-energy s₁

  fc-monotone : ∀ (s₁ s₂ : ThermodynamicState) →
    hydration s₁ ≤ hydration s₂ →
    strength s₁ ≤ strength s₂

forward-hydration-admissible :
  ∀ (old new : ThermodynamicState) →
  hydration old ≤ hydration new →
  (density new - density old ≤ δ-mass) →
  (density old - density new ≤ δ-mass) →
  Admissible old new
forward-hydration-admissible old new α-adv mc₁ mc₂ =
  mkAdmissible
    (mc₁ , mc₂)
    (ψ-antitone old new α-adv)
    α-adv
    (fc-monotone old new α-adv)

------------------------------------------------------------------------
-- 6. Corollary: The Gate Accepts Forward Hydration
------------------------------------------------------------------------

gate-accepts-forward :
  ∀ (old new : ThermodynamicState) →
  hydration old ≤ hydration new →
  (density new - density old ≤ δ-mass) →
  (density old - density new ≤ δ-mass) →
  ∃[ prf ] (gate old new ≡ yes prf)
gate-accepts-forward old new α-adv mc₁ mc₂
  with (density new - density old) ℚ.≤? δ-mass
     | (density old - density new) ℚ.≤? δ-mass
     | free-energy new ℚ.≤? free-energy old
     | hydration old ℚ.≤? hydration new
     | strength old ℚ.≤? strength new
... | yes _  | yes _  | yes _  | yes _  | yes _  = _ , refl
... | no ¬p  | _      | _      | _      | _      = ⊥-elim (¬p mc₁)
... | _      | no ¬p  | _      | _      | _      = ⊥-elim (¬p mc₂)
... | _      | _      | no ¬p  | _      | _      = ⊥-elim (¬p (ψ-antitone old new α-adv))
... | _      | _      | _      | no ¬p  | _      = ⊥-elim (¬p α-adv)
... | _      | _      | _      | _      | no ¬p  = ⊥-elim (¬p (fc-monotone old new α-adv))

------------------------------------------------------------------------
-- 7. CSG Decomposition
------------------------------------------------------------------------

MassCond : ThermodynamicState → ThermodynamicState → Set
MassCond old new = (density new - density old ≤ δ-mass)
                 × (density old - density new ≤ δ-mass)

DissipCond : ThermodynamicState → ThermodynamicState → Set
DissipCond old new = free-energy new ≤ free-energy old

HydrationCond : ThermodynamicState → ThermodynamicState → Set
HydrationCond old new = hydration old ≤ hydration new

StrengthCond : ThermodynamicState → ThermodynamicState → Set
StrengthCond old new = strength old ≤ strength new

admissible-to-csg
  : ∀ (old new : ThermodynamicState)
  → Admissible old new
  → MassCond old new × DissipCond old new
  × HydrationCond old new × StrengthCond old new
admissible-to-csg old new adm =
  mass-conserved adm , dissipation-nonneg adm ,
  hydration-monotone adm , strength-monotone adm

csg-to-admissible
  : ∀ (old new : ThermodynamicState)
  → MassCond old new × DissipCond old new
  × HydrationCond old new × StrengthCond old new
  → Admissible old new
csg-to-admissible old new (mc , diss , hyd , str) =
  mkAdmissible mc diss hyd str
