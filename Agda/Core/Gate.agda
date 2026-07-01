------------------------------------------------------------------------
-- UMST.Core.Gate — universal thermodynamic bounds (all cartridges).
------------------------------------------------------------------------

module Core.Gate where

open import Data.Integer.Base as ℤ using (ℤ; +_; ∣_∣)
open import Data.Nat.Coprimality as ℕ using (sym; 1-coprimeTo)
open import Data.Rational as ℚ using (ℚ; mkℚ; _-_; _≤_)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Universal mass tolerance (kg/m³); SSOT across Agda / Coq / Lean / Rust.
------------------------------------------------------------------------

δ-mass : ℚ
δ-mass = mkℚ (+ 100) 0 (ℕ.sym (ℕ.1-coprimeTo ∣ + 100 ∣))

------------------------------------------------------------------------
-- Material-agnostic thermodynamic interface (mirrors Lean Core.State).
------------------------------------------------------------------------

record ThermodynamicSystem (S : Set) : Set₁ where
  field
    density     : S → ℚ
    free-energy : S → ℚ

open ThermodynamicSystem

------------------------------------------------------------------------
-- Core 1-step admissibility: metric ball + free-energy descent.
------------------------------------------------------------------------

record CoreAdmissible {S : Set} (sys : ThermodynamicSystem S)
                      (old new : S) : Set where
  field
    mass-conserved :
      (density sys new - density sys old ≤ δ-mass)
      × (density sys old - density sys new ≤ δ-mass)
    dissipation-nonneg : free-energy sys new ≤ free-energy sys old

open CoreAdmissible

------------------------------------------------------------------------
-- Named core sub-predicates (CSG half-spaces for universal laws).
------------------------------------------------------------------------

CoreMassCond : {S : Set} → ThermodynamicSystem S → S → S → Set
CoreMassCond sys old new =
  (density sys new - density sys old ≤ δ-mass)
  × (density sys old - density sys new ≤ δ-mass)

CoreDissipCond : {S : Set} → ThermodynamicSystem S → S → S → Set
CoreDissipCond sys old new =
  free-energy sys new ≤ free-energy sys old

core-admissible-iff-mass-dissip :
  ∀ {S : Set} (sys : ThermodynamicSystem S) (old new : S) →
  CoreAdmissible sys old new →
  CoreMassCond sys old new × CoreDissipCond sys old new
core-admissible-iff-mass-dissip sys old new adm =
  mass-conserved adm , dissipation-nonneg adm

core-admissible-from-mass-dissip :
  ∀ {S : Set} (sys : ThermodynamicSystem S) (old new : S) →
  CoreMassCond sys old new × CoreDissipCond sys old new →
  CoreAdmissible sys old new
core-admissible-from-mass-dissip sys old new (mc , diss) =
  record { mass-conserved = mc ; dissipation-nonneg = diss }
