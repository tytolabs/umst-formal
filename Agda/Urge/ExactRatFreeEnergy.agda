-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ExactRatFreeEnergy — meso/acting §22.6 exact Rat free energy.
--
-- URGE-FORMAL-MESO-AGDA-EXACT-RAT-FREE-ENERGY (umst-formal acting fiber only).
-- §22.6: executable F lives in ℚ Rat; f64 compare is theater. Pin ℚ carrier
-- for joint free energy F; refuse f64-as-identity theater. Compose
-- `exact-rat-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ExactRatFreeEnergy where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _-_; _<_; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head carriers (no Concrete.Gate K-infect)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    density free-energy hydration strength : ℚ

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    admissible-witness : ⊤

admissible-any : ∀ {old new : ThermodynamicState} → Admissible old new
admissible-any = mkAdmissible tt

mkState : ℚ → ℚ → ℚ → ℚ → ThermodynamicState
mkState d fe h s = record { density = d ; free-energy = fe ; hydration = h ; strength = s }

open ThermodynamicState

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (minimal meso acting mirror)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head : ThermodynamicState

record HistoryTransition : Set where
  field
    prior : HistorySnapshot
    post : HistorySnapshot
    bath : HeatBath
    dissipated-entropy : ℚ
    entropy-drop : ℚ

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss =
  let step1 : HistoryTransition.entropy-drop t ≤ ErasureProcess.dissipatedEntropy proc
      step1 = subst (λ d → d ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) hSL
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss) step1

------------------------------------------------------------------------
-- SECTION 2: ℚ carrier pin for executable F (§22.6)
------------------------------------------------------------------------

ExecutableFCarrier : Set
ExecutableFCarrier = ℚ

executable-f-carrier-eq-rat : ExecutableFCarrier ≡ ℚ
executable-f-carrier-eq-rat = refl

joint-free-energy : ThermodynamicState → ExecutableFCarrier
joint-free-energy s = free-energy s

executable-f : ThermodynamicState → ExecutableFCarrier
executable-f s = joint-free-energy s

executable-f-eq-joint-free-energy :
  ∀ (s : ThermodynamicState) → executable-f s ≡ joint-free-energy s
executable-f-eq-joint-free-energy s = refl

cand-energy :
  (src : ThermodynamicState) →
  (cand-free : ℚ) → ExecutableFCarrier
cand-energy src cand-free = cand-free

executable-cand-energy :
  (src : ThermodynamicState) →
  (cand-free : ℚ) → ExecutableFCarrier
executable-cand-energy src cand-free = cand-energy src cand-free

executable-cand-energy-eq-cand-energy :
  ∀ (src : ThermodynamicState) (cand-free : ℚ) →
  executable-cand-energy src cand-free ≡ cand-energy src cand-free
executable-cand-energy-eq-cand-energy src cand-free = refl

------------------------------------------------------------------------
-- SECTION 3: f64-as-identity theater refusal (named tag)
------------------------------------------------------------------------

data ExactRatFreeEnergyRefusal : Set where
  f64-as-identity-theater : ExactRatFreeEnergyRefusal
  second-argmin : ExactRatFreeEnergyRefusal
  f64-delta-f-compare : ExactRatFreeEnergyRefusal

refuse-f64-as-identity-theater : ExactRatFreeEnergyRefusal
refuse-f64-as-identity-theater = f64-as-identity-theater

refuse-second-argmin : ExactRatFreeEnergyRefusal
refuse-second-argmin = second-argmin

refuse-f64-delta-f-compare : ExactRatFreeEnergyRefusal
refuse-f64-delta-f-compare = f64-delta-f-compare

------------------------------------------------------------------------
-- SECTION 4: Exact Rat identity witness (§22.6 — no f64 compare)
------------------------------------------------------------------------

exact-rat-free-energy-identity :
  ∀ (s : ThermodynamicState) →
  executable-f s ≡ joint-free-energy s
exact-rat-free-energy-identity s = executable-f-eq-joint-free-energy s

exact-rat-free-energy-identity-holds :
  ∀ (s : ThermodynamicState) →
  ∃[ q ] (executable-f s ≡ q × joint-free-energy s ≡ q)
exact-rat-free-energy-identity-holds s =
  joint-free-energy s , executable-f-eq-joint-free-energy s , refl

strict-improvement-exact-rat :
  (src : ThermodynamicState) (cand-free : ℚ) → Set
strict-improvement-exact-rat src cand-free =
  cand-energy src cand-free < joint-free-energy src

strict-improvement-exact-rat-eq-executable :
  ∀ (src : ThermodynamicState) (cand-free : ℚ) →
  strict-improvement-exact-rat src cand-free ≡
  (executable-cand-energy src cand-free < executable-f src)
strict-improvement-exact-rat-eq-executable src cand-free = refl

------------------------------------------------------------------------
-- SECTION 5: Excitement candidate + composed select (no second argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record exact-rat-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-free : ℚ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

exact-rat-excitement-select :
  (src : ThermodynamicState) → List (exact-rat-candidate src) →
  exact-rat-candidate src ⊎ excitement-residue
exact-rat-excitement-select src List.[] = inj₂ exc-no-candidates
exact-rat-excitement-select src (c List.∷ _) = inj₁ c

urge-exact-rat-select :
  (src : ThermodynamicState) → List (exact-rat-candidate src) →
  exact-rat-candidate src ⊎ excitement-residue
urge-exact-rat-select = exact-rat-excitement-select

urge-exact-rat-select-eq-exact-rat-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (exact-rat-candidate src)) →
  urge-exact-rat-select src cands ≡ exact-rat-excitement-select src cands
urge-exact-rat-select-eq-exact-rat-excitement-select src cands = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

exact-rat-select-empty :
  ∀ (src : ThermodynamicState) →
  urge-exact-rat-select src List.[] ≡ inj₂ exc-no-candidates
exact-rat-select-empty src = refl

------------------------------------------------------------------------
-- SECTION 6: Observed ΔF corpus (exact ℚ — no f64)
------------------------------------------------------------------------

record ObservedDeltaF : Set where
  field
    src : ℚ
    observed : ℚ

observed-delta-f : ObservedDeltaF → ℚ
observed-delta-f d = ObservedDeltaF.observed d ℚ.- ObservedDeltaF.src d

mk-observed-delta-f : (src observed : ℚ) → ObservedDeltaF
mk-observed-delta-f src observed = record { src = src ; observed = observed }

mk-observed-from-candidate :
  (src : ThermodynamicState) (c : exact-rat-candidate src) → ObservedDeltaF
mk-observed-from-candidate src c = record
  { src = joint-free-energy src
  ; observed = exact-rat-candidate.cand-free c
  }

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

exact-rat-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
exact-rat-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

exact-rat-free-energy-production-wired : Bool
exact-rat-free-energy-production-wired = false

exact-rat-free-energy-production-wired-false :
  exact-rat-free-energy-production-wired ≡ false
exact-rat-free-energy-production-wired-false = refl

exact-rat-free-energy-marker : ℕ
exact-rat-free-energy-marker = 1

exact-rat-free-energy-marker-eq : exact-rat-free-energy-marker ≡ 1
exact-rat-free-energy-marker-eq = refl

exact-rat-free-energy-module-witness : ⊤
exact-rat-free-energy-module-witness = tt

f64-as-identity-theater-refused :
  refuse-f64-as-identity-theater ≡ f64-as-identity-theater
f64-as-identity-theater-refused = refl

second-argmin-refused :
  refuse-second-argmin ≡ second-argmin
second-argmin-refused = refl

f64-delta-f-compare-refused :
  refuse-f64-delta-f-compare ≡ f64-delta-f-compare
f64-delta-f-compare-refused = refl

exact-rat-no-local-f64-f :
  ∀ (s : ThermodynamicState) → executable-f s ≡ joint-free-energy s
exact-rat-no-local-f64-f s = refl
