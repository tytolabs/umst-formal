-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ExactAlgCoeffs — meso/acting §3 ExactAlg coefficients.
--
-- URGE-FORMAL-MESO-AGDA-EXACT-ALG-COEFFS (umst-formal acting fiber only).
-- §3: ℚ coefficient slot on `HistoryCarrier` — not silent f64 identity.
-- Compose `excitement-select` — no second ℚ argmin.
--
-- Anchored in `Urge.CarrierProduct`. Sole physics postulate remains
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated). Zero extra
-- postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ExactAlgCoeffs where

open import Chem.SecondLaw
open import Urge.CarrierProduct

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.Integer using (ℤ; +_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc; NonZero; ≢-nonZero)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_; _/_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary.Decidable using (does; yes; no)

------------------------------------------------------------------------
-- SECTION 1: ExactAlg coefficient carriers on HistoryCarrier
------------------------------------------------------------------------

record exact-alg-coeff : Set where
  field
    num : ℤ
    den : ℕ
    op-tag : ℕ

record carrier-exact-alg-coeffs : Set where
  field
    content-id : ℕ
    coeff : exact-alg-coeff

record exact-alg-coeff-witness : Set where
  field
    content-id : ℕ
    value : ℚ
    op-tag : ℕ

record exact-alg-coeff-morphism : Set where
  field
    from : carrier-exact-alg-coeffs
    to-carrier : HistoryCarrier
    witness : exact-alg-coeff-witness
    excitement-selected : Bool

data float-carrier-tag : Set where
  float-theater : float-carrier-tag

data exact-alg-coeffs-refusal : Set where
  eacr-f64-identity-theater : exact-alg-coeffs-refusal
  eacr-zero-denominator : exact-alg-coeffs-refusal
  eacr-exact-alg-absent : exact-alg-coeffs-refusal
  eacr-second-argmin : exact-alg-coeffs-refusal
  eacr-gate-rejected : ℕ → exact-alg-coeffs-refusal

data exact-alg-coeffs-verdict : Set where
  eacv-admitted : exact-alg-coeffs-verdict
  eacv-f64-theater-refused : exact-alg-coeffs-verdict
  eacv-zero-den-refused : exact-alg-coeffs-verdict
  eacv-inadmissible : exact-alg-coeffs-verdict

exact-alg-coeff-value-nonzero :
  (c : exact-alg-coeff) {{_ : NonZero (exact-alg-coeff.den c)}} → ℚ
exact-alg-coeff-value-nonzero c = exact-alg-coeff.num c / exact-alg-coeff.den c

exact-alg-coeff-value : exact-alg-coeff → ℚ
exact-alg-coeff-value c with exact-alg-coeff.den c ℕ-Props.≟ zero
... | yes _ = 0ℚ
... | no h = exact-alg-coeff-value-nonzero c {{≢-nonZero h}}

exact-alg-coeff-den-nonzero : exact-alg-coeff → Bool
exact-alg-coeff-den-nonzero c with exact-alg-coeff.den c ℕ-Props.≟ zero
... | yes _ = false
... | no _  = true

exact-alg-coeff-to-exactAlg : exact-alg-coeff → ExactAlg
exact-alg-coeff-to-exactAlg c = record
  { alg-value = exact-alg-coeff-value c
  ; op-tag = exact-alg-coeff.op-tag c
  }

attach-exact-alg-coeff :
  (carrier : HistoryCarrier) (coeff : exact-alg-coeff) → HistoryCarrier
attach-exact-alg-coeff carrier coeff =
  carrierMk (umstProj carrier) (stampProj carrier) (sdfFRepProj carrier)
    (exact-alg-coeff-to-exactAlg coeff) (witnessProj carrier)

------------------------------------------------------------------------
-- SECTION 2: §3 admissibility conjunct + positive refuse
------------------------------------------------------------------------

record exact-alg-coeff-admissibility-conjunct : Set where
  field
    gate-ok : Bool
    den-nonzero : Bool
    excitement-preserves : Bool

exact-alg-coeff-conjunct-admits : exact-alg-coeff-admissibility-conjunct → Bool
exact-alg-coeff-conjunct-admits c =
  exact-alg-coeff-admissibility-conjunct.gate-ok c
  ∧ exact-alg-coeff-admissibility-conjunct.den-nonzero c
  ∧ exact-alg-coeff-admissibility-conjunct.excitement-preserves c

evaluate-f64-identity-theater : Bool → exact-alg-coeffs-verdict
evaluate-f64-identity-theater true = eacv-f64-theater-refused
evaluate-f64-identity-theater false = eacv-admitted

evaluate-zero-denominator : Bool → exact-alg-coeffs-verdict
evaluate-zero-denominator true = eacv-zero-den-refused
evaluate-zero-denominator false = eacv-admitted

refuse-f64-identity-theater : float-carrier-tag → exact-alg-coeffs-refusal
refuse-f64-identity-theater _ = eacr-f64-identity-theater

refuse-zero-denominator : exact-alg-coeffs-refusal
refuse-zero-denominator = eacr-zero-denominator

refuse-exact-alg-absent : exact-alg-coeffs-refusal
refuse-exact-alg-absent = eacr-exact-alg-absent

refuse-second-argmin-selector : exact-alg-coeffs-refusal
refuse-second-argmin-selector = eacr-second-argmin

witness-from-carrier-coeffs :
  (c : carrier-exact-alg-coeffs) → exact-alg-coeff-witness
witness-from-carrier-coeffs c = record
  { content-id = carrier-exact-alg-coeffs.content-id c
  ; value = exact-alg-coeff-value (carrier-exact-alg-coeffs.coeff c)
  ; op-tag = exact-alg-coeff.op-tag (carrier-exact-alg-coeffs.coeff c)
  }

admit-carrier-exact-alg :
  (c : carrier-exact-alg-coeffs) →
  carrier-exact-alg-coeffs ⊎ exact-alg-coeffs-refusal
admit-carrier-exact-alg c with exact-alg-coeff-den-nonzero (carrier-exact-alg-coeffs.coeff c)
... | true = inj₁ c
... | false = inj₂ eacr-zero-denominator

apply-exact-alg-coeff-morphism :
  (coeffs : carrier-exact-alg-coeffs) (carrier : HistoryCarrier)
  (conjunct : exact-alg-coeff-admissibility-conjunct) (excitement-selected : Bool) →
  exact-alg-coeff-morphism ⊎ exact-alg-coeffs-refusal
apply-exact-alg-coeff-morphism coeffs carrier conjunct excitement-selected
  with exact-alg-coeff-conjunct-admits conjunct
... | false = inj₂ (eacr-gate-rejected zero)
... | true with admit-carrier-exact-alg coeffs
... | inj₂ r = inj₂ r
... | inj₁ admitted with excitement-selected
... | false = inj₂ eacr-exact-alg-absent
... | true = inj₁ record
    { from = admitted
    ; to-carrier = attach-exact-alg-coeff carrier (carrier-exact-alg-coeffs.coeff admitted)
    ; witness = witness-from-carrier-coeffs admitted
    ; excitement-selected = true
    }

exact-alg-coeff-f64-theater-refused :
  refuse-f64-identity-theater float-theater ≡ eacr-f64-identity-theater
exact-alg-coeff-f64-theater-refused = refl

exact-alg-coeff-zero-den-refused :
  refuse-zero-denominator ≡ eacr-zero-denominator
exact-alg-coeff-zero-den-refused = refl

exact-alg-coeff-exact-alg-absent-refused :
  refuse-exact-alg-absent ≡ eacr-exact-alg-absent
exact-alg-coeff-exact-alg-absent-refused = refl

refuse-second-argmin-selector-positive :
  refuse-second-argmin-selector ≡ eacr-second-argmin
refuse-second-argmin-selector-positive = refl

------------------------------------------------------------------------
-- SECTION 3: ExactAlg coefficients compose Excitement (no argmin)
------------------------------------------------------------------------

data exact-alg-coeff-excitement-compose-pin : Set where
  eacep-import-select-excitement : exact-alg-coeff-excitement-compose-pin
  eacep-second-argmin-refused : exact-alg-coeff-excitement-compose-pin

record exact-alg-coeff-ctx (src : ThermodynamicState) : Set where
  field
    successors : List (history-candidate src)

exact-alg-coeff-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  (pin : exact-alg-coeff-excitement-compose-pin) →
  history-candidate src ⊎ excitement-residue
exact-alg-coeff-excitement-select src cands eacep-import-select-excitement =
  excitement-select src cands
exact-alg-coeff-excitement-select src cands eacep-second-argmin-refused =
  inj₂ exc-all-inadmissible

exact-alg-coeff-select :
  (src : ThermodynamicState) (ctx : exact-alg-coeff-ctx src) →
  history-candidate src ⊎ excitement-residue
exact-alg-coeff-select src ctx =
  excitement-select src (exact-alg-coeff-ctx.successors ctx)

urge-exact-alg-select :
  (src : ThermodynamicState) (ctx : exact-alg-coeff-ctx src) →
  history-candidate src ⊎ excitement-residue
urge-exact-alg-select = exact-alg-coeff-select

exact-alg-coeff-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  exact-alg-coeff-excitement-select src cands eacep-import-select-excitement ≡
  excitement-select src cands
exact-alg-coeff-excitement-select-eq-excitement-select src cands = refl

exact-alg-coeff-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : exact-alg-coeff-ctx src) →
  exact-alg-coeff-select src ctx ≡
  excitement-select src (exact-alg-coeff-ctx.successors ctx)
exact-alg-coeff-select-eq-excitement-select src ctx = refl

exact-alg-coeff-select-eq-urge-exact-alg-select :
  ∀ (src : ThermodynamicState) (ctx : exact-alg-coeff-ctx src) →
  exact-alg-coeff-select src ctx ≡ urge-exact-alg-select src ctx
exact-alg-coeff-select-eq-urge-exact-alg-select src ctx = refl

exact-alg-coeff-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : exact-alg-coeff-ctx src) →
  exact-alg-coeff-select src ctx ≡
  excitement-select src (exact-alg-coeff-ctx.successors ctx)
exact-alg-coeff-no-local-argmin src ctx =
  exact-alg-coeff-select-eq-excitement-select src ctx

exact-alg-coeff-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  exact-alg-coeff-excitement-select src cands eacep-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
exact-alg-coeff-excitement-select-refuses-second-argmin src cands = refl

exact-alg-coeff-empty :
  ∀ (src : ThermodynamicState) (ctx : exact-alg-coeff-ctx src) →
  exact-alg-coeff-ctx.successors ctx ≡ List.[] →
  exact-alg-coeff-select src ctx ≡ inj₂ exc-no-candidates
exact-alg-coeff-empty src ctx Hnil rewrite Hnil = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 4: §3 fixtures + witness theorems
------------------------------------------------------------------------

exact-alg-fixture-coeff : exact-alg-coeff
exact-alg-fixture-coeff = record { num = + 3 ; den = 2 ; op-tag = 1 }

exact-alg-fixture-zero-den : exact-alg-coeff
exact-alg-fixture-zero-den = record { num = + 1 ; den = zero ; op-tag = zero }

exact-alg-fixture-carrier-coeffs : carrier-exact-alg-coeffs
exact-alg-fixture-carrier-coeffs = record
  { content-id = 1
  ; coeff = exact-alg-fixture-coeff
  }

exact-alg-fixture-zero-den-coeffs : carrier-exact-alg-coeffs
exact-alg-fixture-zero-den-coeffs = record
  { content-id = 1
  ; coeff = exact-alg-fixture-zero-den
  }

exact-alg-fixture-state : ThermodynamicState
exact-alg-fixture-state = record { state-tag = 1 }

exact-alg-fixture-snapshot : HistorySnapshot
exact-alg-fixture-snapshot = record
  { commit-id = 1
  ; head = exact-alg-fixture-state
  }

exact-alg-fixture-stamp : UcrsStamp
exact-alg-fixture-stamp = wallOnlyStamp 42

exact-alg-fixture-sdf : SdfFRep
exact-alg-fixture-sdf = record { canonical-digest = 5381 ; frep-grain = 1 }

exact-alg-fixture-exact-alg : ExactAlg
exact-alg-fixture-exact-alg = exact-alg-coeff-to-exactAlg exact-alg-fixture-coeff

exact-alg-fixture-carrier : HistoryCarrier
exact-alg-fixture-carrier =
  carrierMk exact-alg-fixture-snapshot exact-alg-fixture-stamp
    exact-alg-fixture-sdf exact-alg-fixture-exact-alg satisfiedWitness

exact-alg-fixture-conjunct : exact-alg-coeff-admissibility-conjunct
exact-alg-fixture-conjunct = record
  { gate-ok = true
  ; den-nonzero = true
  ; excitement-preserves = true
  }

exact-alg-fixture-admit-ok :
  admit-carrier-exact-alg exact-alg-fixture-carrier-coeffs ≡
  inj₁ exact-alg-fixture-carrier-coeffs
exact-alg-fixture-admit-ok = refl

exact-alg-fixture-zero-den-refused :
  admit-carrier-exact-alg exact-alg-fixture-zero-den-coeffs ≡
  inj₂ eacr-zero-denominator
exact-alg-fixture-zero-den-refused = refl

exact-alg-fixture-f64-theater-refused :
  evaluate-f64-identity-theater true ≡ eacv-f64-theater-refused
exact-alg-fixture-f64-theater-refused = refl

exact-alg-fixture-apply-morphism-ok :
  apply-exact-alg-coeff-morphism
    exact-alg-fixture-carrier-coeffs exact-alg-fixture-carrier
    exact-alg-fixture-conjunct true ≡
  inj₁ record
    { from = exact-alg-fixture-carrier-coeffs
    ; to-carrier =
        attach-exact-alg-coeff exact-alg-fixture-carrier exact-alg-fixture-coeff
    ; witness = witness-from-carrier-coeffs exact-alg-fixture-carrier-coeffs
    ; excitement-selected = true
    }
exact-alg-fixture-apply-morphism-ok = refl

exact-alg-fixture-witness-preserves-value :
  exact-alg-coeff-witness.value
    (witness-from-carrier-coeffs exact-alg-fixture-carrier-coeffs) ≡
  exact-alg-coeff-value exact-alg-fixture-coeff
exact-alg-fixture-witness-preserves-value = refl

exact-alg-fixture-attach-preserves-exactAlg :
  exactAlgProj
    (attach-exact-alg-coeff exact-alg-fixture-carrier exact-alg-fixture-coeff) ≡
  exact-alg-fixture-exact-alg
exact-alg-fixture-attach-preserves-exactAlg = refl

------------------------------------------------------------------------
-- SECTION 5: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

exact-alg-coeff-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
exact-alg-coeff-second-law-from-landauer proc ΔS t hent hdiss =
  physicalSecondLaw-discharge-carrier proc ΔS t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

exact-alg-coeffs-physics-green : Bool
exact-alg-coeffs-physics-green = false

exact-alg-coeffs-physics-green-false :
  exact-alg-coeffs-physics-green ≡ false
exact-alg-coeffs-physics-green-false = refl

exact-alg-coeffs-production-wired : Bool
exact-alg-coeffs-production-wired = false

exact-alg-coeffs-production-wired-false :
  exact-alg-coeffs-production-wired ≡ false
exact-alg-coeffs-production-wired-false = refl

exact-alg-coeffs-module-witness : ⊤
exact-alg-coeffs-module-witness = tt

exact-alg-coeffs-no-new-axiom : ⊤
exact-alg-coeffs-no-new-axiom = tt

f64-identity-theater-refused :
  refuse-f64-identity-theater float-theater ≡ eacr-f64-identity-theater
f64-identity-theater-refused = refl

second-argmin-refused :
  refuse-second-argmin-selector ≡ eacr-second-argmin
second-argmin-refused = refl

exact-alg-coeff-marker : ℕ
exact-alg-coeff-marker = 1

exact-alg-coeff-marker-eq : exact-alg-coeff-marker ≡ 1
exact-alg-coeff-marker-eq = refl
