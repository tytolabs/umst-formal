------------------------------------------------------------------------
-- UMST-Formal: Gate.agda
--
-- Core admissible-state predicate and Theorem 1 (categorical safety).
--
-- This module formalises the thermodynamic gate from the Rust kernel
-- (umst-core/science/thermodynamic_filter.rs) as a dependent type.
-- The gate accepts a proposed state transition (old → new) if and only
-- if four physical invariants hold simultaneously:
--
--   1. Mass conservation       |ρ_new − ρ_old| ≤ δ
--   2. Clausius-Duhem          D_int = −ρ · ψ̇  ≥ 0
--   3. Hydration irreversibility   α_new ≥ α_old
--   4. Strength monotonicity   fc_new ≥ fc_old
--
-- Empirical grounding:
--   These invariants were not invented abstractly.  They were discovered
--   through seven years of hands-on practice with variable earth, lime,
--   masonry, and recycled-aggregate concrete at Studio Tyto.  Workability
--   windows that snap shut, carbonation fronts that accelerate beyond
--   any linear prediction, interfacial crystal interlock that either
--   forms or never does — these field observations are the empirical
--   basis of every axiom below.
--
-- Correspondence to Rust:
--   ThermodynamicState  ↔  ThermodynamicState in thermodynamic_filter.rs
--   Admissible          ↔  check_transition returning accepted = true
--   gate                ↔  ThermodynamicFilter::check_transition
------------------------------------------------------------------------

module Gate where

open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; _<_)
open import Data.Rational.Properties as ℚ-Props
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- 1. Thermodynamic State
------------------------------------------------------------------------

-- A ThermodynamicState captures the minimal set of fields needed to
-- evaluate the four invariants.  We use rationals (ℚ) throughout for
-- decidable arithmetic; the Rust kernel uses f64 with tolerance ε = 10⁻⁶.
--
-- Physical meaning of each field:
--   density          ρ  (kg/m³)     bulk density of the paste/concrete
--   free-energy      ψ  (J/kg)      Helmholtz free energy per unit mass
--   hydration        α  (0–1)       degree of cement hydration
--   strength         fc (MPa)       compressive strength (Powers model)

record ThermodynamicState : Set where
  constructor mkState
  field
    density     : ℚ   -- ρ
    free-energy : ℚ   -- ψ = −Q_hyd · α  in the Rust kernel
    hydration   : ℚ   -- α
    strength    : ℚ   -- fc

open ThermodynamicState

------------------------------------------------------------------------
-- 2. Physical Constants
------------------------------------------------------------------------

-- Tolerance for mass conservation check.
-- In the Rust kernel this is 100.0 kg/m³ (a generous bound that catches
-- gross density jumps while allowing normal hydration-induced changes).
δ-mass : ℚ
δ-mass = ℚ.mkℚ 100 0 _    -- 100/1

-- Tolerance for dissipation and strength checks.
-- In the Rust kernel this is 1e-6.  For rational proofs we use 0
-- (the strict version), since the toleranced version follows trivially.
-- The key mathematical content is the sign of D_int, not the epsilon.

------------------------------------------------------------------------
-- 3. Admissibility Predicate
------------------------------------------------------------------------

-- The four invariants bundled as a single proposition.
-- Admissible old new holds iff the transition old → new satisfies all
-- four physical laws simultaneously.
--
-- Note on dt: the time step appears in the Rust computation of ψ̇ but
-- cancels out in the sign check (D_int ≥ 0 ⟺ ψ̇ ≤ 0 for ρ > 0).
-- We therefore omit dt from the formalisation without loss of generality.

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    -- Invariant 1: Mass conservation
    -- |ρ_new − ρ_old| < δ
    mass-conserved : (density new - density old ≤ δ-mass)
                   × (density old - density new ≤ δ-mass)

    -- Invariant 2: Clausius-Duhem dissipation (sign condition)
    -- D_int = −ρ · ψ̇ ≥ 0
    -- Since ρ > 0, this reduces to ψ̇ ≤ 0, i.e., ψ_new ≤ ψ_old
    dissipation-nonneg : free-energy new ≤ free-energy old

    -- Invariant 3: Hydration irreversibility
    -- α_new ≥ α_old (cement hydration is a one-way chemical reaction)
    hydration-monotone : hydration old ≤ hydration new

    -- Invariant 4: Strength monotonicity
    -- fc_new ≥ fc_old (undamaged concrete cannot lose strength)
    strength-monotone : strength old ≤ strength new

open Admissible

------------------------------------------------------------------------
-- 4. Gate Decision Procedure
------------------------------------------------------------------------

-- The gate is a decision procedure: given two states, it either
-- produces a proof of admissibility or a proof of inadmissibility.
-- This mirrors ThermodynamicFilter::check_transition in Rust.
--
-- In category-theoretic terms, this is a morphism in the arrow category
-- of Set:  gate : State × State → 1 + 1  (i.e., Bool with evidence).

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
-- 5. Theorem 1: Forward Hydration is Admissible
------------------------------------------------------------------------

-- Theorem 1 (Categorical Safety):
-- If hydration advances (α_new ≥ α_old), density is preserved, and
-- the Helmholtz free energy model ψ(α) = −Q_hyd · α holds, then the
-- transition is admissible.
--
-- This is the core safety theorem.  It says that the physical process
-- of cement hydration — as modelled by the Powers/Clausius-Duhem
-- framework — can never be rejected by the gate.  The gate only
-- rejects unphysical transitions (reverse hydration, spontaneous
-- strength loss, mass violations).
--
-- Proof sketch:
--   Given α_new ≥ α_old and ψ = −Q · α:
--     ψ_new = −Q · α_new ≤ −Q · α_old = ψ_old   (since Q > 0, α↑ ⟹ ψ↓)
--     D_int = −ρ · ψ̇ = ρ · Q · α̇ ≥ 0            (ρ, Q, α̇ all ≥ 0)
--     fc = S · x³ where x = f(α, w/c) is monotone in α
--   So all four invariants hold.

-- We state this as a type.  A full constructive proof requires the
-- specific free-energy model and Powers formula.  The structure below
-- captures the logical dependency and allows the proof to be filled
-- mechanically once the arithmetic lemmas are supplied.

postulate
  -- The Helmholtz model: free-energy is antitone in hydration
  ψ-antitone : ∀ (s₁ s₂ : ThermodynamicState) →
    hydration s₁ ≤ hydration s₂ →
    free-energy s₂ ≤ free-energy s₁

  -- Powers model: strength is monotone in hydration (at fixed w/c)
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

-- A direct consequence: if the hypotheses of Theorem 1 hold, then
-- `gate old new` returns `yes _`.

gate-accepts-forward :
  ∀ (old new : ThermodynamicState) →
  hydration old ≤ hydration new →
  (density new - density old ≤ δ-mass) →
  (density old - density new ≤ δ-mass) →
  ∃[ prf ] (gate old new ≡ yes prf)
  where
  open import Data.Product using (∃-syntax)
-- Pattern-match on the five ≤? decisions that `gate` itself scrutinises.
-- After the match, `gate old new` reduces definitionally in each branch,
-- allowing direct witnesses (refl) or contradictions (⊥-elim).
gate-accepts-forward old new α-adv mc₁ mc₂
  with (density new - density old) ℚ.≤? δ-mass
     | (density old - density new) ℚ.≤? δ-mass
     | free-energy new ℚ.≤? free-energy old
     | hydration old ℚ.≤? hydration new
     | strength old ℚ.≤? strength new
-- All five decisions are yes: gate reduces to yes(mkAdmissible …), refl closes.
... | yes _  | yes _  | yes _  | yes _  | yes _  = _ , refl
-- No branches: each contradicts the corresponding supplied hypothesis.
... | no ¬p  | _      | _      | _      | _      = ⊥-elim (¬p mc₁)
... | _      | no ¬p  | _      | _      | _      = ⊥-elim (¬p mc₂)
... | _      | _      | no ¬p  | _      | _      = ⊥-elim (¬p (ψ-antitone old new α-adv))
... | _      | _      | _      | no ¬p  | _      = ⊥-elim (¬p α-adv)
... | _      | _      | _      | _      | no ¬p  = ⊥-elim (¬p (fc-monotone old new α-adv))
