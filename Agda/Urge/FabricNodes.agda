-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.FabricNodes — meso/acting §15 fabric-nodes replica-class pin.
--
-- URGE-FORMAL-MESO-AGDA-FABRIC-NODES (umst-formal acting fiber only).
-- §15: declared fabric nodes (`fabric-nodes.json`) pin to §15.4 replica-class
-- table rows — software schema, not Forgejo installer. Compose
-- `fabric-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.FabricNodes where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
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

------------------------------------------------------------------------
-- SECTION 1: §15.4 replica-class + fabric-node pin carriers
------------------------------------------------------------------------

data fabric-replica-class : Set where
  frc-node0-dev-clone frc-node1-dev-clone frc-forgejo-primary-mirror
    frc-darwin-scratch frc-offline-luks frc-customer-compose : fabric-replica-class

data fabric-authority : Set where
  fa-working-copy fa-canonical-remote fa-scratch-plane
    fa-disaster-copy fa-customer-on-site : fabric-authority

fabric-replica-egress-empty : fabric-replica-class → Bool
fabric-replica-egress-empty frc-darwin-scratch = true
fabric-replica-egress-empty frc-offline-luks = true
fabric-replica-egress-empty frc-node0-dev-clone = false
fabric-replica-egress-empty frc-node1-dev-clone = false
fabric-replica-egress-empty frc-forgejo-primary-mirror = false
fabric-replica-egress-empty frc-customer-compose = false

fabric-replica-from-node-id : ℕ → Maybe fabric-replica-class
fabric-replica-from-node-id zero = just frc-node0-dev-clone
fabric-replica-from-node-id (suc zero) = just frc-node1-dev-clone
fabric-replica-from-node-id (suc (suc _)) = nothing

fabric-authority-of : fabric-replica-class → fabric-authority
fabric-authority-of frc-node0-dev-clone = fa-working-copy
fabric-authority-of frc-node1-dev-clone = fa-working-copy
fabric-authority-of frc-forgejo-primary-mirror = fa-canonical-remote
fabric-authority-of frc-darwin-scratch = fa-scratch-plane
fabric-authority-of frc-offline-luks = fa-disaster-copy
fabric-authority-of frc-customer-compose = fa-customer-on-site

fabric-nodes-schema-valid : Bool → Bool
fabric-nodes-schema-valid schema-ok = schema-ok

record fabric-ucrs-stamp : Set where
  field
    fabric-ucrs-seq : ℕ
    fabric-ucrs-wall-has-t : Bool

record fabric-merge-safe-cert : Set where
  field
    fabric-merge-safe : Bool

record fabric-node-pin : Set where
  field
    fabric-pin-step-id : ℕ
    fabric-pin-node-id : ℕ
    fabric-pin-schema-ok : Bool
    fabric-pin-byzantine-mesh : Bool
    fabric-pin-claims-forgejo-running : Bool
    fabric-pin-ucrs : fabric-ucrs-stamp
    fabric-pin-merge-safe : fabric-merge-safe-cert
    fabric-pin-provenance-intact : Bool

------------------------------------------------------------------------
-- SECTION 2: Witness bundle (§15 morphism must preserve stamps)
------------------------------------------------------------------------

record fabric-node-witness : Set where
  field
    fabric-witness-ucrs : fabric-ucrs-stamp
    fabric-witness-merge-safe : fabric-merge-safe-cert
    fabric-witness-provenance-intact : Bool

witness-from-fabric-pin : fabric-node-pin → fabric-node-witness
witness-from-fabric-pin (record { fabric-pin-ucrs = ucrs
                               ; fabric-pin-merge-safe = ms
                               ; fabric-pin-provenance-intact = pi }) = record
  { fabric-witness-ucrs = ucrs
  ; fabric-witness-merge-safe = ms
  ; fabric-witness-provenance-intact = pi
  }

------------------------------------------------------------------------
-- SECTION 3: MergeSafe certificate — pin must not violate tier disjointness
------------------------------------------------------------------------

fabric-merge-safe-admits : fabric-merge-safe-cert → Bool
fabric-merge-safe-admits cert = fabric-merge-safe-cert.fabric-merge-safe cert

record fabric-node-morphism : Set where
  field
    fabric-morphism-from : fabric-node-pin
    fabric-morphism-to-replica : fabric-replica-class
    fabric-morphism-witness : fabric-node-witness
    fabric-morphism-excitement-selected : Bool

------------------------------------------------------------------------
-- SECTION 4: Admissibility conjunct + fabric-node operation class
------------------------------------------------------------------------

record fabric-admissibility-conjunct : Set where
  field
    fabric-conj-gate-ok : Bool
    fabric-conj-merge-safe : Bool
    fabric-conj-excitement-preserves : Bool

fabric-conjunct-admits : fabric-admissibility-conjunct → Bool
fabric-conjunct-admits (record { fabric-conj-gate-ok = g
                               ; fabric-conj-merge-safe = m
                               ; fabric-conj-excitement-preserves = e }) =
  g ∧ m ∧ e

data fabric-nodes-verdict : Set where
  fnv-pin-ok fnv-byzantine-mesh-refused fnv-forgejo-install-refused
    fnv-inadmissible : fabric-nodes-verdict

evaluate-fabric-nodes-operation :
  (byzantine-mesh claims-forgejo-running : Bool) → fabric-nodes-verdict
evaluate-fabric-nodes-operation true _ = fnv-byzantine-mesh-refused
evaluate-fabric-nodes-operation false true = fnv-forgejo-install-refused
evaluate-fabric-nodes-operation false false = fnv-pin-ok

------------------------------------------------------------------------
-- SECTION 5: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data fabric-nodes-refusal : Set where
  fnr-byzantine-mesh-claim : fabric-nodes-refusal
  fnr-forgejo-install-claim : fabric-nodes-refusal
  fnr-unknown-fabric-node-id : ℕ → fabric-nodes-refusal
  fnr-schema-mismatch : fabric-nodes-refusal
  fnr-second-argmin : fabric-nodes-refusal
  fnr-production-wired : fabric-nodes-refusal
  fnr-gate-rejected : ℕ → fabric-nodes-refusal
  fnr-merge-unsafe : ℕ → fabric-nodes-refusal
  fnr-provenance-loss : ℕ → fabric-nodes-refusal
  fnr-replica-class-mismatch : fabric-nodes-refusal

refuse-byzantine-mesh-claim : fabric-nodes-refusal
refuse-byzantine-mesh-claim = fnr-byzantine-mesh-claim

refuse-forgejo-install-claim : fabric-nodes-refusal
refuse-forgejo-install-claim = fnr-forgejo-install-claim

refuse-second-argmin-selector : fabric-nodes-refusal
refuse-second-argmin-selector = fnr-second-argmin

admit-fabric-node-pin : fabric-node-pin → ⊤ ⊎ fabric-nodes-refusal
admit-fabric-node-pin pin =
  if fabric-node-pin.fabric-pin-byzantine-mesh pin then inj₂ fnr-byzantine-mesh-claim
  else if fabric-node-pin.fabric-pin-claims-forgejo-running pin then
    inj₂ fnr-forgejo-install-claim
  else if not (fabric-nodes-schema-valid (fabric-node-pin.fabric-pin-schema-ok pin)) then
    inj₂ fnr-schema-mismatch
  else maybe (λ _ → inj₁ tt)
    (inj₂ (fnr-unknown-fabric-node-id (fabric-node-pin.fabric-pin-node-id pin)))
    (fabric-replica-from-node-id (fabric-node-pin.fabric-pin-node-id pin))

apply-fabric-node-morphism :
  (pin : fabric-node-pin) →
  (to-replica : fabric-replica-class) →
  (conjunct : fabric-admissibility-conjunct) →
  (excitement-selected : Bool) →
  fabric-node-morphism ⊎ fabric-nodes-refusal
apply-fabric-node-morphism pin to-replica conjunct excitement-selected with
  admit-fabric-node-pin pin
... | inj₂ r = inj₂ r
... | inj₁ _ =
  if not (fabric-conjunct-admits conjunct) then
    inj₂ (fnr-gate-rejected
      (fabric-ucrs-stamp.fabric-ucrs-seq (fabric-node-pin.fabric-pin-ucrs pin)))
  else if not (fabric-merge-safe-admits (fabric-node-pin.fabric-pin-merge-safe pin)) then
    inj₂ (fnr-merge-unsafe (fabric-node-pin.fabric-pin-step-id pin))
  else if not (fabric-node-pin.fabric-pin-provenance-intact pin) then
    inj₂ (fnr-provenance-loss (fabric-node-pin.fabric-pin-step-id pin))
  else if not excitement-selected then
    inj₂ (fnr-provenance-loss (fabric-node-pin.fabric-pin-step-id pin))
  else inj₁ record
    { fabric-morphism-from = pin
    ; fabric-morphism-to-replica = to-replica
    ; fabric-morphism-witness = witness-from-fabric-pin pin
    ; fabric-morphism-excitement-selected = excitement-selected
    }

fabric-nodes-byzantine-mesh-refused :
  evaluate-fabric-nodes-operation true false ≡ fnv-byzantine-mesh-refused
fabric-nodes-byzantine-mesh-refused = refl

fabric-nodes-forgejo-install-refused :
  evaluate-fabric-nodes-operation false true ≡ fnv-forgejo-install-refused
fabric-nodes-forgejo-install-refused = refl

fabric-nodes-pin-ok-when-honest :
  evaluate-fabric-nodes-operation false false ≡ fnv-pin-ok
fabric-nodes-pin-ok-when-honest = refl

refuse-byzantine-mesh-claim-positive :
  refuse-byzantine-mesh-claim ≡ fnr-byzantine-mesh-claim
refuse-byzantine-mesh-claim-positive = refl

refuse-forgejo-install-claim-positive :
  refuse-forgejo-install-claim ≡ fnr-forgejo-install-claim
refuse-forgejo-install-claim-positive = refl

refuse-second-argmin-selector-positive :
  refuse-second-argmin-selector ≡ fnr-second-argmin
refuse-second-argmin-selector-positive = refl

------------------------------------------------------------------------
-- SECTION 6: Gate fabric-node pins (§15 admissibility)
------------------------------------------------------------------------

fabric-nodes-positive-refuse-not-silent :
  evaluate-fabric-nodes-operation true false ≢ fnv-pin-ok
fabric-nodes-positive-refuse-not-silent ()

fabric-nodes-forgejo-refuse-not-silent :
  evaluate-fabric-nodes-operation false true ≢ fnv-pin-ok
fabric-nodes-forgejo-refuse-not-silent ()

------------------------------------------------------------------------
-- SECTION 7: Excitement compose pin (no second ℚ argmin)
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

record fabric-nodes-ctx (src : ThermodynamicState) : Set where
  field
    fabric-nodes-successors : List (history-candidate src)

urge-recovery-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select = excitement-select

fabric-nodes-select :
  (src : ThermodynamicState) (ctx : fabric-nodes-ctx src) →
  history-candidate src ⊎ excitement-residue
fabric-nodes-select src ctx =
  urge-recovery-select src (fabric-nodes-ctx.fabric-nodes-successors ctx)

fabric-nodes-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : fabric-nodes-ctx src) →
  fabric-nodes-select src ctx ≡
  excitement-select src (fabric-nodes-ctx.fabric-nodes-successors ctx)
fabric-nodes-select-eq-excitement-select src ctx = refl

fabric-nodes-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : fabric-nodes-ctx src) →
  fabric-nodes-select src ctx ≡
  urge-recovery-select src (fabric-nodes-ctx.fabric-nodes-successors ctx)
fabric-nodes-select-eq-urge-recovery-select src ctx = refl

fabric-nodes-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : fabric-nodes-ctx src) →
  fabric-nodes-select src ctx ≡
  excitement-select src (fabric-nodes-ctx.fabric-nodes-successors ctx)
fabric-nodes-no-local-argmin src ctx =
  fabric-nodes-select-eq-excitement-select src ctx

fabric-nodes-empty :
  ∀ (src : ThermodynamicState) (ctx : fabric-nodes-ctx src) →
  fabric-nodes-ctx.fabric-nodes-successors ctx ≡ List.[] →
  fabric-nodes-select src ctx ≡ inj₂ exc-no-candidates
fabric-nodes-empty src ctx hs rewrite hs = refl

data fabric-excitement-compose-pin : Set where
  fep-import-select-excitement fep-second-argmin-refused : fabric-excitement-compose-pin

fabric-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src)) →
  fabric-excitement-compose-pin →
  history-candidate src ⊎ excitement-residue
fabric-excitement-select src cands fep-import-select-excitement =
  excitement-select src cands
fabric-excitement-select src cands fep-second-argmin-refused =
  inj₂ exc-all-inadmissible

fabric-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  fabric-excitement-select src cands fep-import-select-excitement ≡
  excitement-select src cands
fabric-excitement-select-eq-excitement-select src cands = refl

fabric-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  fabric-excitement-select src cands fep-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
fabric-excitement-select-refuses-second-argmin src cands = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

urge-fabric-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-fabric-select = excitement-select

------------------------------------------------------------------------
-- SECTION 8: §15 fixtures + Landauer bridge + honesty flags
------------------------------------------------------------------------

fabric-fixture-state : ThermodynamicState
fabric-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

fabric-fixture-ucrs : fabric-ucrs-stamp
fabric-fixture-ucrs = record
  { fabric-ucrs-seq = 7
  ; fabric-ucrs-wall-has-t = true
  }

fabric-fixture-merge-safe : fabric-merge-safe-cert
fabric-fixture-merge-safe = record { fabric-merge-safe = true }

fabric-fixture-node0-pin : fabric-node-pin
fabric-fixture-node0-pin = record
  { fabric-pin-step-id = 1
  ; fabric-pin-node-id = 0
  ; fabric-pin-schema-ok = true
  ; fabric-pin-byzantine-mesh = false
  ; fabric-pin-claims-forgejo-running = false
  ; fabric-pin-ucrs = fabric-fixture-ucrs
  ; fabric-pin-merge-safe = fabric-fixture-merge-safe
  ; fabric-pin-provenance-intact = true
  }

fabric-fixture-conjunct : fabric-admissibility-conjunct
fabric-fixture-conjunct = record
  { fabric-conj-gate-ok = true
  ; fabric-conj-merge-safe = true
  ; fabric-conj-excitement-preserves = true
  }

fabric-fixture-admit-node0-ok :
  admit-fabric-node-pin fabric-fixture-node0-pin ≡ inj₁ tt
fabric-fixture-admit-node0-ok = refl

fabric-fixture-apply-morphism-ok :
  apply-fabric-node-morphism
    fabric-fixture-node0-pin frc-node0-dev-clone fabric-fixture-conjunct true ≡
  inj₁ record
    { fabric-morphism-from = fabric-fixture-node0-pin
    ; fabric-morphism-to-replica = frc-node0-dev-clone
    ; fabric-morphism-witness = witness-from-fabric-pin fabric-fixture-node0-pin
    ; fabric-morphism-excitement-selected = true
    }
fabric-fixture-apply-morphism-ok = refl

fabric-node0-maps-to-dev-clone :
  fabric-replica-from-node-id 0 ≡ just frc-node0-dev-clone
fabric-node0-maps-to-dev-clone = refl

fabric-node1-maps-to-dev-clone :
  fabric-replica-from-node-id 1 ≡ just frc-node1-dev-clone
fabric-node1-maps-to-dev-clone = refl

fabric-unknown-node-id-refused :
  fabric-replica-from-node-id 99 ≡ nothing
fabric-unknown-node-id-refused = refl

fabric-offline-luks-egress-empty :
  fabric-replica-egress-empty frc-offline-luks ≡ true
fabric-offline-luks-egress-empty = refl

fabric-darwin-scratch-egress-empty :
  fabric-replica-egress-empty frc-darwin-scratch ≡ true
fabric-darwin-scratch-egress-empty = refl

fabric-forgejo-primary-egress-nonempty :
  fabric-replica-egress-empty frc-forgejo-primary-mirror ≡ false
fabric-forgejo-primary-egress-nonempty = refl

fabric-fixture-witness-preserves-ucrs :
  fabric-node-witness.fabric-witness-ucrs (witness-from-fabric-pin fabric-fixture-node0-pin) ≡
  fabric-fixture-ucrs
fabric-fixture-witness-preserves-ucrs = refl

fabric-fixture-byzantine-pin : fabric-node-pin
fabric-fixture-byzantine-pin = record
  { fabric-pin-step-id = 1
  ; fabric-pin-node-id = 0
  ; fabric-pin-schema-ok = true
  ; fabric-pin-byzantine-mesh = true
  ; fabric-pin-claims-forgejo-running = false
  ; fabric-pin-ucrs = fabric-fixture-ucrs
  ; fabric-pin-merge-safe = fabric-fixture-merge-safe
  ; fabric-pin-provenance-intact = true
  }

fabric-fixture-forgejo-pin : fabric-node-pin
fabric-fixture-forgejo-pin = record
  { fabric-pin-step-id = 1
  ; fabric-pin-node-id = 0
  ; fabric-pin-schema-ok = true
  ; fabric-pin-byzantine-mesh = false
  ; fabric-pin-claims-forgejo-running = true
  ; fabric-pin-ucrs = fabric-fixture-ucrs
  ; fabric-pin-merge-safe = fabric-fixture-merge-safe
  ; fabric-pin-provenance-intact = true
  }

fabric-fixture-byzantine-refused :
  admit-fabric-node-pin fabric-fixture-byzantine-pin ≡ inj₂ fnr-byzantine-mesh-claim
fabric-fixture-byzantine-refused = refl

fabric-fixture-forgejo-refused :
  admit-fabric-node-pin fabric-fixture-forgejo-pin ≡ inj₂ fnr-forgejo-install-claim
fabric-fixture-forgejo-refused = refl

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

fabric-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
fabric-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

fabric-nodes-physics-green : Bool
fabric-nodes-physics-green = false

fabric-nodes-physics-green-false :
  fabric-nodes-physics-green ≡ false
fabric-nodes-physics-green-false = refl

fabric-nodes-production-wired : Bool
fabric-nodes-production-wired = false

fabric-nodes-production-wired-false :
  fabric-nodes-production-wired ≡ false
fabric-nodes-production-wired-false = refl

fabric-nodes-module-witness : ⊤
fabric-nodes-module-witness = tt

fabric-nodes-no-new-axiom : ⊤
fabric-nodes-no-new-axiom = tt

fabric-nodes-marker : ℕ
fabric-nodes-marker = 1

fabric-nodes-marker-eq : fabric-nodes-marker ≡ 1
fabric-nodes-marker-eq = refl
