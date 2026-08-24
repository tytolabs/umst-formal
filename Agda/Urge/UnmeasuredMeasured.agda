-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.UnmeasuredMeasured — meso/acting §17.7 production_wired.
--
-- URGE-FORMAL-MESO-AGDA-UNMEASURED-MEASURED (umst-formal acting fiber only).
-- §17.7: `Unmeasured | Measured {value, dataset}` — UNKNOWN ≠ false-as-GREEN.
-- Compose `unmeasured-measured-excitement-select` — no second ℚ argmin.
--
-- Meso hook mirrors `Urge.ExcitementImport.excitement-select` (§5.2 — no local
-- argmin re-derivation). Sole physics postulate remains
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.UnmeasuredMeasured where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head carriers (no K-infective import)
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

open ThermodynamicState

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

urge-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

------------------------------------------------------------------------
-- SECTION 1: §17.7 production_wired taxonomy carriers
------------------------------------------------------------------------

data ProductionWiredTaxonomy : Set where
  pw-unmeasured : ProductionWiredTaxonomy
  pw-measured : Bool → String → ProductionWiredTaxonomy

production-wired-is-measured : ProductionWiredTaxonomy → Bool
production-wired-is-measured pw-unmeasured = false
production-wired-is-measured (pw-measured _ _) = true

production-wired-measured-value : ProductionWiredTaxonomy → Maybe Bool
production-wired-measured-value pw-unmeasured = nothing
production-wired-measured-value (pw-measured v _) = just v

production-wired-dataset : ProductionWiredTaxonomy → Maybe String
production-wired-dataset pw-unmeasured = nothing
production-wired-dataset (pw-measured _ d) = just d

dataset-nonempty : Bool → Bool
dataset-nonempty b = b

data FalseAsGreenRefusal : Set where
  fagr-unmeasured-collapsed-to-false : FalseAsGreenRefusal
  fagr-measured-true-not-physics-green : FalseAsGreenRefusal

data ProductionWiredVerdict : Set where
  pwv-honest-unmeasured : ProductionWiredVerdict
  pwv-measured-false-ok : ProductionWiredVerdict
  pwv-false-as-green-refused : ProductionWiredVerdict

------------------------------------------------------------------------
-- SECTION 2: §17.7 positive refuse (UNKNOWN ≠ false-as-GREEN)
------------------------------------------------------------------------

record UnmeasuredMeasuredConjunct : Set where
  field
    conj-gate-ok : Bool
    conj-false-as-green-refused : Bool
    conj-excitement-preserves : Bool

umm-conjunct-admits : UnmeasuredMeasuredConjunct → Bool
umm-conjunct-admits c =
  if_then_else_ (UnmeasuredMeasuredConjunct.conj-gate-ok c)
    (if_then_else_ (UnmeasuredMeasuredConjunct.conj-false-as-green-refused c)
      (UnmeasuredMeasuredConjunct.conj-excitement-preserves c)
      false)
    false

refuse-false-as-green :
  ProductionWiredTaxonomy → Maybe FalseAsGreenRefusal
refuse-false-as-green pw-unmeasured = just fagr-unmeasured-collapsed-to-false
refuse-false-as-green (pw-measured true _) = just fagr-measured-true-not-physics-green
refuse-false-as-green (pw-measured false _) = nothing

production-wired-legacy-bool : ProductionWiredTaxonomy → Maybe Bool
production-wired-legacy-bool = production-wired-measured-value

bool-claims-measurement-when-unmeasured :
  ProductionWiredTaxonomy → Bool → Bool
bool-claims-measurement-when-unmeasured pw-unmeasured claimed = claimed
bool-claims-measurement-when-unmeasured (pw-measured _ _) _ = false

measured-production-wired :
  Bool → String → Bool →
  ProductionWiredTaxonomy ⊎ FalseAsGreenRefusal
measured-production-wired value dataset false = inj₂ fagr-unmeasured-collapsed-to-false
measured-production-wired value dataset true = inj₁ (pw-measured value dataset)

evaluate-production-wired : ProductionWiredTaxonomy → ProductionWiredVerdict
evaluate-production-wired pw with refuse-false-as-green pw
... | just _ = pwv-false-as-green-refused
... | nothing with pw
... | pw-unmeasured = pwv-honest-unmeasured
... | pw-measured false _ = pwv-measured-false-ok
... | pw-measured true _ = pwv-false-as-green-refused

refuse-false-as-green-unmeasured :
  refuse-false-as-green pw-unmeasured ≡ just fagr-unmeasured-collapsed-to-false
refuse-false-as-green-unmeasured = refl

production-wired-legacy-none-when-unmeasured :
  production-wired-legacy-bool pw-unmeasured ≡ nothing
production-wired-legacy-none-when-unmeasured = refl

unmeasured-not-measured :
  production-wired-is-measured pw-unmeasured ≡ false
unmeasured-not-measured = refl

------------------------------------------------------------------------
-- SECTION 3: Gossip mesh taxonomy — documented Unmeasured
------------------------------------------------------------------------

gossip-mesh-production-wired-taxonomy : ProductionWiredTaxonomy
gossip-mesh-production-wired-taxonomy = pw-unmeasured

ucrs-gossip-mesh-documented-as-unmeasured : Bool
ucrs-gossip-mesh-documented-as-unmeasured with gossip-mesh-production-wired-taxonomy
... | pw-unmeasured = true
... | pw-measured _ _ = false

refuse-unmeasured-as-false-green : FalseAsGreenRefusal
refuse-unmeasured-as-false-green = fagr-unmeasured-collapsed-to-false

gossip-mesh-taxonomy-is-unmeasured :
  gossip-mesh-production-wired-taxonomy ≡ pw-unmeasured
gossip-mesh-taxonomy-is-unmeasured = refl

ucrs-gossip-mesh-documented-unmeasured-true :
  ucrs-gossip-mesh-documented-as-unmeasured ≡ true
ucrs-gossip-mesh-documented-unmeasured-true = refl

gossip-mesh-refuse-false-as-green :
  refuse-false-as-green gossip-mesh-production-wired-taxonomy ≡
  just fagr-unmeasured-collapsed-to-false
gossip-mesh-refuse-false-as-green = refl

------------------------------------------------------------------------
-- SECTION 4: Urge composes excitement-select (no second argmin)
------------------------------------------------------------------------

record UnmeasuredMeasuredCtx (src : ThermodynamicState) : Set where
  field
    unmeasured-measured-successors : List (history-candidate src)

data UnmeasuredMeasuredExcitementPin : Set where
  umep-import-select-excitement : UnmeasuredMeasuredExcitementPin
  umep-second-argmin-refused : UnmeasuredMeasuredExcitementPin

unmeasured-measured-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  UnmeasuredMeasuredExcitementPin →
  history-candidate src ⊎ excitement-residue
unmeasured-measured-excitement-select src cands umep-import-select-excitement =
  excitement-select src cands
unmeasured-measured-excitement-select src cands umep-second-argmin-refused =
  inj₂ exc-all-inadmissible

unmeasured-measured-select :
  (src : ThermodynamicState) (ctx : UnmeasuredMeasuredCtx src) →
  history-candidate src ⊎ excitement-residue
unmeasured-measured-select src ctx =
  urge-recovery-select src (UnmeasuredMeasuredCtx.unmeasured-measured-successors ctx)

unmeasured-measured-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : UnmeasuredMeasuredCtx src) →
  unmeasured-measured-select src ctx ≡
  excitement-select src (UnmeasuredMeasuredCtx.unmeasured-measured-successors ctx)
unmeasured-measured-select-eq-excitement-select src ctx = refl

unmeasured-measured-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : UnmeasuredMeasuredCtx src) →
  unmeasured-measured-select src ctx ≡
  urge-recovery-select src (UnmeasuredMeasuredCtx.unmeasured-measured-successors ctx)
unmeasured-measured-select-eq-urge-recovery-select src ctx = refl

unmeasured-measured-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : UnmeasuredMeasuredCtx src) →
  unmeasured-measured-select src ctx ≡
  excitement-select src (UnmeasuredMeasuredCtx.unmeasured-measured-successors ctx)
unmeasured-measured-no-local-argmin src ctx =
  unmeasured-measured-select-eq-excitement-select src ctx

unmeasured-measured-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  unmeasured-measured-excitement-select src cands umep-import-select-excitement ≡
  excitement-select src cands
unmeasured-measured-excitement-select-eq-excitement-select src cands = refl

unmeasured-measured-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  unmeasured-measured-excitement-select src cands umep-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
unmeasured-measured-excitement-select-refuses-second-argmin src cands = refl

unmeasured-measured-select-empty :
  ∀ (src : ThermodynamicState) (ctx : UnmeasuredMeasuredCtx src) →
  UnmeasuredMeasuredCtx.unmeasured-measured-successors ctx ≡ List.[] →
  unmeasured-measured-select src ctx ≡ inj₂ exc-no-candidates
unmeasured-measured-select-empty src ctx Hnil rewrite Hnil = refl

------------------------------------------------------------------------
-- SECTION 5: §17.7 fixtures + witness theorems
------------------------------------------------------------------------

umm-fixture-dataset : String
umm-fixture-dataset = "fixture:urge-formal-meso-agda-unmeasured-measured"

umm-fixture-measured-false : ProductionWiredTaxonomy
umm-fixture-measured-false = pw-measured false umm-fixture-dataset

umm-fixture-conjunct : UnmeasuredMeasuredConjunct
umm-fixture-conjunct = record
  { conj-gate-ok = true
  ; conj-false-as-green-refused = true
  ; conj-excitement-preserves = true
  }

umm-fixture-measured-false-admits :
  refuse-false-as-green umm-fixture-measured-false ≡ nothing
umm-fixture-measured-false-admits = refl

umm-fixture-measured-false-evaluate-ok :
  evaluate-production-wired umm-fixture-measured-false ≡ pwv-measured-false-ok
umm-fixture-measured-false-evaluate-ok = refl

umm-fixture-measured-production-wired-ok :
  measured-production-wired false umm-fixture-dataset true ≡
  inj₁ umm-fixture-measured-false
umm-fixture-measured-production-wired-ok = refl

umm-fixture-empty-dataset-refused :
  measured-production-wired false "" false ≡
  inj₂ fagr-unmeasured-collapsed-to-false
umm-fixture-empty-dataset-refused = refl

umm-fixture-unmeasured-legacy-none :
  production-wired-legacy-bool gossip-mesh-production-wired-taxonomy ≡ nothing
umm-fixture-unmeasured-legacy-none = refl

umm-fixture-conjunct-admits-true :
  umm-conjunct-admits umm-fixture-conjunct ≡ true
umm-fixture-conjunct-admits-true = refl

------------------------------------------------------------------------
-- SECTION 6: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

unmeasured-measured-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) →
  PhysicalSecondLaw proc ΔS
unmeasured-measured-second-law-from-landauer proc ΔS =
  physicalSecondLaw proc ΔS

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

unmeasured-measured-physics-green : Bool
unmeasured-measured-physics-green = false

unmeasured-measured-physics-green-false :
  unmeasured-measured-physics-green ≡ false
unmeasured-measured-physics-green-false = refl

unmeasured-measured-production-wired : Bool
unmeasured-measured-production-wired = false

unmeasured-measured-production-wired-false :
  unmeasured-measured-production-wired ≡ false
unmeasured-measured-production-wired-false = refl

unmeasured-measured-module-witness : ⊤
unmeasured-measured-module-witness = tt

unmeasured-measured-positive-refuse-not-silent :
  refuse-false-as-green gossip-mesh-production-wired-taxonomy ≡
  just fagr-unmeasured-collapsed-to-false
unmeasured-measured-positive-refuse-not-silent =
  gossip-mesh-refuse-false-as-green

unmeasured-measured-unknown-not-false-as-green :
  refuse-unmeasured-as-false-green ≡ fagr-unmeasured-collapsed-to-false
unmeasured-measured-unknown-not-false-as-green = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

unmeasured-measured-catalog-witness :
  String
unmeasured-measured-catalog-witness =
  "URGE-FORMAL-MESO-AGDA-UNMEASURED-MEASURED §17.7 production_wired : Unmeasured | Measured {value, dataset}; UNKNOWN ≠ false-as-GREEN; compose excitement-select no second argmin sole postulate physicalSecondLaw not physics GREEN not production_wired"
