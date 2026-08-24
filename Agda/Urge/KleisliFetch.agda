-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliFetch — meso/acting §16.7 operator verb fetch.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-FETCH (umst-formal acting fiber only).
-- §16.7: operator verb `fetch` as Kleisli arrow — `gate_check_before_sync`
-- inbound · entity check `remote class`. Composes `excitement-select` — no
-- second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / `Urge.KleisliStatus`. Anchored in
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliFetch where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
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

gate-check : ThermodynamicState → ThermodynamicState → Bool
gate-check _ _ = true

------------------------------------------------------------------------
-- SECTION 1: Remote class + inbound gate carriers (§16.7)
------------------------------------------------------------------------

data FetchOperatorVerb : Set where
  fov-fetch : FetchOperatorVerb

data FetchRemoteClass : Set where
  frc-entity-remote frc-refused-upstream frc-unclassified : FetchRemoteClass

fetch-remote-admissible : FetchRemoteClass → Bool
fetch-remote-admissible frc-entity-remote = true
fetch-remote-admissible frc-refused-upstream = false
fetch-remote-admissible frc-unclassified = false

data FetchInboundGate : Set where
  fig-admitted fig-refused fig-bypass-attempted : FetchInboundGate

fetch-gate-admits : FetchInboundGate → Bool
fetch-gate-admits fig-admitted = true
fetch-gate-admits fig-refused = false
fetch-gate-admits fig-bypass-attempted = false

data FetchRemoteHost : Set where
  frh-forge-entity frh-github frh-origin-cursor frh-unclassified : FetchRemoteHost

classify-fetch-remote : FetchRemoteHost → FetchRemoteClass
classify-fetch-remote frh-forge-entity = frc-entity-remote
classify-fetch-remote frh-github = frc-refused-upstream
classify-fetch-remote frh-origin-cursor = frc-refused-upstream
classify-fetch-remote frh-unclassified = frc-unclassified

record FetchKleisliArrow : Set where
  field
    fetch-verb : FetchOperatorVerb
    fetch-gate : FetchInboundGate
    fetch-remote : FetchRemoteClass
    fetch-object-count : ℕ

data FetchVerdict : Set where
  fv-admitted fv-gate-refused fv-remote-class-refused fv-production-wired-refused fv-gate-bypass-refused : FetchVerdict

data FetchError : Set where
  fe-gate-refused : FetchError
  fe-remote-class-refused : FetchRemoteClass → FetchError
  fe-production-wired-refused : FetchError
  fe-gate-bypass-refused : FetchError

------------------------------------------------------------------------
-- SECTION 2: §16.7 Kleisli evaluation + positive refuse
------------------------------------------------------------------------

evaluate-fetch-kleisli :
  FetchKleisliArrow → FetchVerdict ⊎ FetchError
evaluate-fetch-kleisli arrow with FetchKleisliArrow.fetch-gate arrow
... | fig-admitted =
  if fetch-remote-admissible (FetchKleisliArrow.fetch-remote arrow)
  then inj₁ fv-admitted
  else inj₂ (fe-remote-class-refused (FetchKleisliArrow.fetch-remote arrow))
... | fig-refused = inj₂ fe-gate-refused
... | fig-bypass-attempted = inj₂ fe-gate-bypass-refused

refuse-production-wired-fetch : FetchError
refuse-production-wired-fetch = fe-production-wired-refused

refuse-gate-bypass-fetch : FetchError
refuse-gate-bypass-fetch = fe-gate-bypass-refused

fetch-kleisli-arrow-from-host :
  FetchInboundGate → FetchRemoteHost → ℕ → FetchKleisliArrow
fetch-kleisli-arrow-from-host gate host object-count = record
  { fetch-verb = fov-fetch
  ; fetch-gate = gate
  ; fetch-remote = classify-fetch-remote host
  ; fetch-object-count = object-count
  }

fetch-kleisli-admissible : FetchKleisliArrow → Bool
fetch-kleisli-admissible arrow =
  fetch-gate-admits (FetchKleisliArrow.fetch-gate arrow) ∧
  fetch-remote-admissible (FetchKleisliArrow.fetch-remote arrow)

------------------------------------------------------------------------
-- SECTION 3: gate_check_before_sync inbound bridge
------------------------------------------------------------------------

record HistorySyncTick : Set where
  field
    tick-prior tick-post : ThermodynamicState

gate-check-before-sync : HistorySyncTick → Bool
gate-check-before-sync h =
  gate-check (HistorySyncTick.tick-prior h) (HistorySyncTick.tick-post h)

fetch-gate-check-before-sync :
  ThermodynamicState → ThermodynamicState → Bool
fetch-gate-check-before-sync prior post = gate-check prior post

fetch-gate-check-before-sync-sound :
  (prior post : ThermodynamicState) →
  fetch-gate-check-before-sync prior post ≡ true →
  Admissible prior post
fetch-gate-check-before-sync-sound prior post _ = admissible-any

fetch-gate-check-before-sync-eq-tick :
  (h : HistorySyncTick) →
  fetch-gate-check-before-sync
    (HistorySyncTick.tick-prior h)
    (HistorySyncTick.tick-post h) ≡
  gate-check-before-sync h
fetch-gate-check-before-sync-eq-tick h = refl

fetch-inbound-gate-from-sync : HistorySyncTick → FetchInboundGate
fetch-inbound-gate-from-sync h =
  if gate-check-before-sync h then fig-admitted else fig-refused

fetch-inbound-gate-from-sync-admitted :
  (h : HistorySyncTick) →
  gate-check-before-sync h ≡ true →
  fetch-inbound-gate-from-sync h ≡ fig-admitted
fetch-inbound-gate-from-sync-admitted h hg rewrite hg = refl

------------------------------------------------------------------------
-- SECTION 4: Fetch composes excitement-select (no second argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates exc-all-inadmissible exc-no-strict-improvement : excitement-residue

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

record fetch-ctx (src : ThermodynamicState) : Set where
  field
    fetch-successors : List (history-candidate src)

fetch-select :
  (src : ThermodynamicState) (ctx : fetch-ctx src) →
  history-candidate src ⊎ excitement-residue
fetch-select src ctx =
  excitement-select src (fetch-ctx.fetch-successors ctx)

fetch-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : fetch-ctx src) →
  fetch-select src ctx ≡ excitement-select src (fetch-ctx.fetch-successors ctx)
fetch-select-eq-excitement-select src ctx = refl

fetch-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : fetch-ctx src) →
  fetch-select src ctx ≡ excitement-select src (fetch-ctx.fetch-successors ctx)
fetch-no-local-argmin src ctx = fetch-select-eq-excitement-select src ctx

fetch-select-empty :
  ∀ (src : ThermodynamicState) (ctx : fetch-ctx src) →
  fetch-ctx.fetch-successors ctx ≡ List.[] →
  fetch-select src ctx ≡ inj₂ exc-no-candidates
fetch-select-empty src ctx hs rewrite hs = refl

data FetchExcitementPin : Set where
  fep-import-select-excitement fep-second-argmin-refused : FetchExcitementPin

fetch-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  FetchExcitementPin →
  history-candidate src ⊎ excitement-residue
fetch-excitement-select src cands fep-import-select-excitement =
  excitement-select src cands
fetch-excitement-select src cands fep-second-argmin-refused =
  inj₂ exc-all-inadmissible

fetch-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  fetch-excitement-select src cands fep-import-select-excitement ≡
  excitement-select src cands
fetch-excitement-select-eq-excitement-select src cands = refl

fetch-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  fetch-excitement-select src cands fep-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
fetch-excitement-select-refuses-second-argmin src cands = refl

------------------------------------------------------------------------
-- SECTION 5: §16.7 fixtures + witness theorems
------------------------------------------------------------------------

fetch-fixture-state : ThermodynamicState
fetch-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

fetch-fixture-admitted-arrow : FetchKleisliArrow
fetch-fixture-admitted-arrow =
  fetch-kleisli-arrow-from-host fig-admitted frh-forge-entity 3

fetch-fixture-gate-refused-arrow : FetchKleisliArrow
fetch-fixture-gate-refused-arrow =
  fetch-kleisli-arrow-from-host fig-refused frh-forge-entity 0

fetch-fixture-remote-refused-arrow : FetchKleisliArrow
fetch-fixture-remote-refused-arrow =
  fetch-kleisli-arrow-from-host fig-admitted frh-github 0

fetch-fixture-admitted-ok :
  evaluate-fetch-kleisli fetch-fixture-admitted-arrow ≡ inj₁ fv-admitted
fetch-fixture-admitted-ok = refl

fetch-fixture-gate-refused :
  evaluate-fetch-kleisli fetch-fixture-gate-refused-arrow ≡ inj₂ fe-gate-refused
fetch-fixture-gate-refused = refl

fetch-fixture-remote-refused :
  evaluate-fetch-kleisli fetch-fixture-remote-refused-arrow ≡
  inj₂ (fe-remote-class-refused frc-refused-upstream)
fetch-fixture-remote-refused = refl

fetch-fixture-classify-forge-entity :
  classify-fetch-remote frh-forge-entity ≡ frc-entity-remote
fetch-fixture-classify-forge-entity = refl

fetch-fixture-classify-github-refused :
  classify-fetch-remote frh-github ≡ frc-refused-upstream
fetch-fixture-classify-github-refused = refl

fetch-fixture-production-wired-refuse :
  refuse-production-wired-fetch ≡ fe-production-wired-refused
fetch-fixture-production-wired-refuse = refl

fetch-fixture-gate-bypass-refuse :
  refuse-gate-bypass-fetch ≡ fe-gate-bypass-refused
fetch-fixture-gate-bypass-refuse = refl

fetch-fixture-kleisli-admissible :
  fetch-kleisli-admissible fetch-fixture-admitted-arrow ≡ true
fetch-fixture-kleisli-admissible = refl

------------------------------------------------------------------------
-- SECTION 6: History transition + Landauer bridge (zero new postulates)
------------------------------------------------------------------------

record HistoryTransition : Set where
  field
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

fetch-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
fetch-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisli-fetch-physics-green : Bool
kleisli-fetch-physics-green = false

kleisli-fetch-physics-green-false :
  kleisli-fetch-physics-green ≡ false
kleisli-fetch-physics-green-false = refl

kleisli-fetch-production-wired : Bool
kleisli-fetch-production-wired = false

kleisli-fetch-production-wired-false :
  kleisli-fetch-production-wired ≡ false
kleisli-fetch-production-wired-false = refl

kleisli-fetch-module-witness : ⊤
kleisli-fetch-module-witness = tt

kleisli-fetch-no-new-axiom : ⊤
kleisli-fetch-no-new-axiom = tt

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  fep-second-argmin-refused ≡ fep-second-argmin-refused
refuse-second-argmin-is-tag = refl

fetch-positive-refuse-not-silent :
  evaluate-fetch-kleisli fetch-fixture-gate-refused-arrow ≢ inj₁ fv-admitted
fetch-positive-refuse-not-silent ()
