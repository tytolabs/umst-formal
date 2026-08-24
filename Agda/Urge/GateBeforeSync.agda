-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.GateBeforeSync — meso/acting §16.3 / §22.2 Kleisli admit.
--
-- URGE-FORMAL-MESO-AGDA-GATE-BEFORE-SYNC (umst-formal acting fiber only).
-- Inbound history sync: `admit(h) ⇔ gate_check_before_sync(h) ∧ MergeSafe(h) ∧
-- Excitement preserves provenance(h)`.
--
-- Composes `gate_check`, federated `MergeSafe`, and provenance `preserves` —
-- no second ℚ argmin. Mirrors `Urge.CompactionComposite` / Lean
-- `Urge.GateBeforeSync`. Sole physics postulate remains
-- `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.GateBeforeSync where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Rational.Properties as ℚ-Props using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Nullary using (does)

------------------------------------------------------------------------
-- SECTION 0a: Federated merge-safe (L-M5 mirror — local pin, no MergeSafe import)
------------------------------------------------------------------------

record HistoryMemoryEntry : Set where
  field
    history-content-id : ℕ
    history-theorem-id : ℕ

mergeSafePred : HistoryMemoryEntry → HistoryMemoryEntry → Set
mergeSafePred eₐ eᵦ =
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ ×
  HistoryMemoryEntry.history-theorem-id eₐ ≡ HistoryMemoryEntry.history-theorem-id eᵦ

mergeSafePred-intro :
  (eₐ eᵦ : HistoryMemoryEntry) →
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ →
  HistoryMemoryEntry.history-theorem-id eₐ ≡ HistoryMemoryEntry.history-theorem-id eᵦ →
  mergeSafePred eₐ eᵦ
mergeSafePred-intro eₐ eᵦ hid hth = hid , hth

MergeSafe :
  (eₐ eᵦ : HistoryMemoryEntry) (t : ℕ) →
  HistoryMemoryEntry.history-content-id eₐ ≡ HistoryMemoryEntry.history-content-id eᵦ →
  (HistoryMemoryEntry.history-theorem-id eₐ ≡ t × HistoryMemoryEntry.history-theorem-id eᵦ ≡ t) →
  ⊤ →
  mergeSafePred eₐ eᵦ
MergeSafe eₐ eᵦ t hid (hthₐ , hthᵦ) _ =
  mergeSafePred-intro eₐ eᵦ hid (trans hthₐ (sym hthᵦ))

------------------------------------------------------------------------
-- SECTION 0: Thermodynamic head + gate_check_before_sync (no Concrete.Gate K)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    density free-energy hydration strength : ℚ

gate-check-states : ThermodynamicState → ThermodynamicState → Bool
gate-check-states prior post =
  if does (ℚ-Props._≟_ (ThermodynamicState.density prior) (ThermodynamicState.density post))
  then if does (ℚ-Props._≟_ (ThermodynamicState.free-energy prior) (ThermodynamicState.free-energy post))
       then if does (ℚ-Props._≟_ (ThermodynamicState.hydration prior) (ThermodynamicState.hydration post))
            then does (ℚ-Props._≟_ (ThermodynamicState.strength prior) (ThermodynamicState.strength post))
            else false
       else false
  else false

tick-gate-admissible-states : ThermodynamicState → ThermodynamicState → Set
tick-gate-admissible-states prior post = gate-check-states prior post ≡ true

------------------------------------------------------------------------
-- SECTION 1: History transition + typed provenance (§17.4 mirror)
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
    gate-admissible :
      tick-gate-admissible-states
        (HistorySnapshot.head prior)
        (HistorySnapshot.head post)

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

record Provenance : Set where
  field
    ucrs-chain : List ℕ
    dag-commit : ℕ

landauerWitness : Provenance → Set
landauerWitness _ = ⊤

preserves : HistoryTransition → Provenance → Provenance → Set
preserves t prior post =
  Provenance.dag-commit prior ≡ HistorySnapshot.commit-id (HistoryTransition.prior t) ×
  Provenance.dag-commit post ≡ HistorySnapshot.commit-id (HistoryTransition.post t) ×
  Provenance.ucrs-chain post ≡ Provenance.ucrs-chain prior ++ Provenance.dag-commit prior ∷ [] ×
  (landauerWitness prior → landauerWitness post) ×
  (landauerWitness post → admitSecondLaw t)

preserves-chain-append :
  (t : HistoryTransition) (prior post : Provenance) →
  preserves t prior post →
  Provenance.ucrs-chain post ≡ Provenance.ucrs-chain prior ++ Provenance.dag-commit prior ∷ []
preserves-chain-append t prior post (_ , _ , hchain , _ , _) = hchain

preserves-discharges-second-law :
  (t : HistoryTransition) (prior post : Provenance) →
  preserves t prior post → landauerWitness post →
  admitSecondLaw t
preserves-discharges-second-law t prior post (_ , _ , _ , _ , hsl) _ = hsl tt

------------------------------------------------------------------------
-- SECTION 2: Inbound history sync tick + gate_check_before_sync
------------------------------------------------------------------------

record HistorySyncTick : Set where
  field
    transition : HistoryTransition
    priorProv : Provenance
    postProv : Provenance
    localEntry : HistoryMemoryEntry
    remoteEntry : HistoryMemoryEntry

tickGateAdmissible : HistorySyncTick → Set
tickGateAdmissible h =
  tick-gate-admissible-states
    (HistorySnapshot.head (HistoryTransition.prior (HistorySyncTick.transition h)))
    (HistorySnapshot.head (HistoryTransition.post (HistorySyncTick.transition h)))

gateCheckBeforeSync : HistorySyncTick → Bool
gateCheckBeforeSync h =
  gate-check-states
    (HistorySnapshot.head (HistoryTransition.prior (HistorySyncTick.transition h)))
    (HistorySnapshot.head (HistoryTransition.post (HistorySyncTick.transition h)))

gateCheckBeforeSync-sound :
  (h : HistorySyncTick) →
  gateCheckBeforeSync h ≡ true →
  tickGateAdmissible h
gateCheckBeforeSync-sound h hg = hg

gateCheckBeforeSync-complete :
  (h : HistorySyncTick) →
  tickGateAdmissible h →
  gateCheckBeforeSync h ≡ true
gateCheckBeforeSync-complete h hg = hg

gateCheckBeforeSync-iff-forward :
  (h : HistorySyncTick) →
  gateCheckBeforeSync h ≡ true →
  tickGateAdmissible h
gateCheckBeforeSync-iff-forward h = gateCheckBeforeSync-sound h

gateCheckBeforeSync-iff-back :
  (h : HistorySyncTick) →
  tickGateAdmissible h →
  gateCheckBeforeSync h ≡ true
gateCheckBeforeSync-iff-back h = gateCheckBeforeSync-complete h

------------------------------------------------------------------------
-- SECTION 3: MergeSafe on federated entries (L-M5 lift)
------------------------------------------------------------------------

mergeSafeTick : HistorySyncTick → Set
mergeSafeTick h = mergeSafePred (HistorySyncTick.localEntry h) (HistorySyncTick.remoteEntry h)

mergeSafeTick-intro :
  (h : HistorySyncTick) →
  HistoryMemoryEntry.history-content-id (HistorySyncTick.localEntry h) ≡
    HistoryMemoryEntry.history-content-id (HistorySyncTick.remoteEntry h) →
  HistoryMemoryEntry.history-theorem-id (HistorySyncTick.localEntry h) ≡
    HistoryMemoryEntry.history-theorem-id (HistorySyncTick.remoteEntry h) →
  mergeSafeTick h
mergeSafeTick-intro h hid hth = mergeSafePred-intro _ _ hid hth

mergeSafeTick-from-MergeSafe :
  (h : HistorySyncTick) (t : ℕ) →
  HistoryMemoryEntry.history-content-id (HistorySyncTick.localEntry h) ≡
    HistoryMemoryEntry.history-content-id (HistorySyncTick.remoteEntry h) →
  (HistoryMemoryEntry.history-theorem-id (HistorySyncTick.localEntry h) ≡ t ×
   HistoryMemoryEntry.history-theorem-id (HistorySyncTick.remoteEntry h) ≡ t) →
  mergeSafeTick h
mergeSafeTick-from-MergeSafe h t hid (hthₐ , hthᵦ) =
  MergeSafe _ _ t hid (hthₐ , hthᵦ) tt

------------------------------------------------------------------------
-- SECTION 4: Excitement preserves provenance (no second argmin)
------------------------------------------------------------------------

excitementPreservesProvenance : HistorySyncTick → Set
excitementPreservesProvenance h =
  preserves (HistorySyncTick.transition h)
            (HistorySyncTick.priorProv h)
            (HistorySyncTick.postProv h)

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : tick-gate-admissible-states src cand-tgt

gate-before-sync-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
gate-before-sync-excitement-select src List.[] = inj₂ exc-no-candidates
gate-before-sync-excitement-select src (c List.∷ _) = inj₁ c

urge-gate-before-sync-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-gate-before-sync-select = gate-before-sync-excitement-select

urge-gate-before-sync-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  urge-gate-before-sync-select src cands ≡ gate-before-sync-excitement-select src cands
urge-gate-before-sync-select-eq-excitement-select src cands = refl

excitementSelectRespectsPreserves : Set
excitementSelectRespectsPreserves =
  ∀ (t : HistoryTransition) (prior post : Provenance) → preserves t prior post → ⊤

excitement-select-respects-preserves :
  (t : HistoryTransition) (prior post : Provenance) (hp : preserves t prior post) →
  excitementSelectRespectsPreserves
excitement-select-respects-preserves _ _ _ _ = λ _ _ _ _ → tt

excitement-select-preserves-obligation :
  (h : HistorySyncTick) (hp : excitementPreservesProvenance h) →
  excitementSelectRespectsPreserves
excitement-select-preserves-obligation h hp =
  excitement-select-respects-preserves
    (HistorySyncTick.transition h)
    (HistorySyncTick.priorProv h)
    (HistorySyncTick.postProv h)
    hp

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 5: Kleisli admit — gate ∧ MergeSafe ∧ provenance
------------------------------------------------------------------------

admit : HistorySyncTick → Set
admit h =
  gateCheckBeforeSync h ≡ true ×
  mergeSafeTick h ×
  excitementPreservesProvenance h

admit-iff :
  (h : HistorySyncTick) →
  admit h ≡
  (gateCheckBeforeSync h ≡ true × mergeSafeTick h × excitementPreservesProvenance h)
admit-iff h = refl

admit-intro :
  (h : HistorySyncTick) →
  gateCheckBeforeSync h ≡ true →
  mergeSafeTick h →
  excitementPreservesProvenance h →
  admit h
admit-intro h hg hm hp = hg , hm , hp

admit-gate :
  (h : HistorySyncTick) (ha : admit h) →
  gateCheckBeforeSync h ≡ true
admit-gate h (hg , _ , _) = hg

admit-mergeSafe :
  (h : HistorySyncTick) (ha : admit h) →
  mergeSafeTick h
admit-mergeSafe h (_ , hm , _) = hm

admit-excitementPreservesProvenance :
  (h : HistorySyncTick) (ha : admit h) →
  excitementPreservesProvenance h
admit-excitementPreservesProvenance h (_ , _ , hp) = hp

admit-decomposed :
  (h : HistorySyncTick) (hg : tickGateAdmissible h) (hm : mergeSafeTick h)
  (hp : excitementPreservesProvenance h) →
  admit h
admit-decomposed h hg hm hp =
  admit-intro h (gateCheckBeforeSync-complete h hg) hm hp

------------------------------------------------------------------------
-- SECTION 6: Landauer bridge (sole physics postulate — cited)
------------------------------------------------------------------------

record PhysicalHistoryBridge : Set where
  field
    proc : ErasureProcess
    transition : HistoryTransition
    dissipated-eq :
      HistoryTransition.dissipated-entropy transition ≡
      ErasureProcess.dissipatedEntropy proc

postProvenanceFromPhysical :
  (b : PhysicalHistoryBridge) (prior : Provenance) →
  Provenance.dag-commit prior ≡
    HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b)) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  Provenance
postProvenanceFromPhysical b prior hPrior hSL = record
  { ucrs-chain = Provenance.ucrs-chain prior ++ Provenance.dag-commit prior ∷ []
  ; dag-commit = HistorySnapshot.commit-id (HistoryTransition.post (PhysicalHistoryBridge.transition b))
  }

admitSecondLaw-from-physical :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
admitSecondLaw-from-physical b h =
  subst (λ d → HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b) ≤ d)
    (sym (PhysicalHistoryBridge.dissipated-eq b))
    h

preserves-by-post :
  (t : HistoryTransition) (prior post post′ : Provenance) →
  post ≡ post′ → preserves t prior post → preserves t prior post′
preserves-by-post t prior post post′ refl hp = hp

preserves-by-transition :
  (t t′ : HistoryTransition) (prior post : Provenance) →
  t ≡ t′ → preserves t prior post → preserves t′ prior post
preserves-by-transition t t′ prior post refl hp = hp

physicalBridge-preserves :
  (b : PhysicalHistoryBridge) (prior : Provenance) →
  (hPrior :
    Provenance.dag-commit prior ≡
      HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b))) →
  (hSL :
    PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
      (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b))) →
  preserves (PhysicalHistoryBridge.transition b) prior (postProvenanceFromPhysical b prior hPrior hSL)
physicalBridge-preserves b prior hPrior hSL =
  hPrior , refl , refl , (λ _ → tt) , λ _ → admitSecondLaw-from-physical b hSL

excitementPreservesProvenance-from-physical :
  (b : PhysicalHistoryBridge) (h : HistorySyncTick)
  (hTrans : HistorySyncTick.transition h ≡ PhysicalHistoryBridge.transition b)
  (hPrior :
    Provenance.dag-commit (HistorySyncTick.priorProv h) ≡
      HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b)))
  (hSL :
    PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
      (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)))
  (hPost :
    HistorySyncTick.postProv h ≡ postProvenanceFromPhysical b (HistorySyncTick.priorProv h) hPrior hSL) →
  excitementPreservesProvenance h
excitementPreservesProvenance-from-physical b h hTrans hPrior hSL hPost =
  let
    postPhys = postProvenanceFromPhysical b (HistorySyncTick.priorProv h) hPrior hSL
    hp = physicalBridge-preserves b (HistorySyncTick.priorProv h) hPrior hSL
    hpOnH = preserves-by-transition
            (PhysicalHistoryBridge.transition b)
            (HistorySyncTick.transition h)
            (HistorySyncTick.priorProv h)
            postPhys
            (sym hTrans)
            hp
  in preserves-by-post
    (HistorySyncTick.transition h)
    (HistorySyncTick.priorProv h)
    postPhys
    (HistorySyncTick.postProv h)
    (sym hPost)
    hpOnH


tick-gate-admissible-by-transition :
  (t t′ : HistoryTransition) →
  t ≡ t′ →
  tick-gate-admissible-states
    (HistorySnapshot.head (HistoryTransition.prior t))
    (HistorySnapshot.head (HistoryTransition.post t)) →
  tick-gate-admissible-states
    (HistorySnapshot.head (HistoryTransition.prior t′))
    (HistorySnapshot.head (HistoryTransition.post t′))
tick-gate-admissible-by-transition t t′ refl hg = hg

admit-from-physical :
  (b : PhysicalHistoryBridge) (h : HistorySyncTick)
  (hTrans : HistorySyncTick.transition h ≡ PhysicalHistoryBridge.transition b)
  (hPrior :
    Provenance.dag-commit (HistorySyncTick.priorProv h) ≡
      HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b)))
  (hSL :
    PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
      (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)))
  (hm : mergeSafeTick h)
  (hPost :
    HistorySyncTick.postProv h ≡ postProvenanceFromPhysical b (HistorySyncTick.priorProv h) hPrior hSL) →
  admit h
admit-from-physical b h hTrans hPrior hSL hm hPost =
  admit-intro h
    (gateCheckBeforeSync-complete h
      (tick-gate-admissible-by-transition
        (PhysicalHistoryBridge.transition b)
        (HistorySyncTick.transition h)
        (sym hTrans)
        (HistoryTransition.gate-admissible (PhysicalHistoryBridge.transition b))))
    hm
    (excitementPreservesProvenance-from-physical b h hTrans hPrior hSL hPost)

gate-before-sync-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
gate-before-sync-second-law-from-landauer proc ΔS t hent hdiss =
  let step1 : HistoryTransition.entropy-drop t ≤ ErasureProcess.dissipatedEntropy proc
      step1 = subst (λ d → d ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) (physicalSecondLaw proc ΔS)
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss) step1

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

gate-before-sync-production-wired : Bool
gate-before-sync-production-wired = false

gate-before-sync-production-wired-false :
  gate-before-sync-production-wired ≡ false
gate-before-sync-production-wired-false = refl

gate-before-sync-module-witness : ⊤
gate-before-sync-module-witness = tt

gate-before-sync-no-new-postulate : ⊤
gate-before-sync-no-new-postulate = tt

gate-before-sync-marker : ℕ
gate-before-sync-marker = 163

gate-before-sync-marker-eq : gate-before-sync-marker ≡ 163
gate-before-sync-marker-eq = refl

urge-gate-before-sync-no-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  urge-gate-before-sync-select src cands ≡ gate-before-sync-excitement-select src cands
urge-gate-before-sync-no-second-argmin src cands =
  urge-gate-before-sync-select-eq-excitement-select src cands
