-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ReplicaClass — meso/acting §15.4 replica-class table.
--
-- URGE-FORMAL-MESO-AGDA-REPLICA-CLASS (umst-formal acting fiber only).
-- §15.4: replica-class table + `fabric-nodes.json` `class` field pin.
-- Positive refuse via typed errors — not only `!physics_green`. Compose
-- `excitement-select` — no second ℚ argmin.
--
-- Mirrors `Urge.CompactionComposite` / Coq `Urge.ReplicaClass`. Sole physics
-- postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited, not restated).
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ReplicaClass where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String; _==_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (does; ¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (CompactionComposite mirror)
------------------------------------------------------------------------

record HistorySnapshot : Set where
  field
    commit-id : ℕ
    head-id : ℕ

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
-- SECTION 1b: Minimal thermodynamic head carriers (no Concrete.Gate K-infect)
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
excitement-select src [] = inj₂ exc-no-candidates
excitement-select src (c ∷ _) = inj₁ c

urge-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

urge-recovery-empty :
  ∀ (src : ThermodynamicState) →
  urge-recovery-select src [] ≡ inj₂ exc-no-candidates
urge-recovery-empty src = refl

------------------------------------------------------------------------
-- SECTION 2: §15.4 replica-class table (six named rows)
------------------------------------------------------------------------

data replica-class-label : Set where
  rcl-node0-dev-clone : replica-class-label
  rcl-node1-dev-clone : replica-class-label
  rcl-forgejo-primary-mirror : replica-class-label
  rcl-darwin-scratch : replica-class-label
  rcl-offline-luks : replica-class-label
  rcl-customer-compose : replica-class-label

replica-class-class-field : replica-class-label → String
replica-class-class-field rcl-node0-dev-clone = "node-0-dev-clone"
replica-class-class-field rcl-node1-dev-clone = "node-1-dev-clone"
replica-class-class-field rcl-forgejo-primary-mirror = "forgejo-primary-mirror"
replica-class-class-field rcl-darwin-scratch = "darwin-scratch"
replica-class-class-field rcl-offline-luks = "offline-luks"
replica-class-class-field rcl-customer-compose = "customer-compose"

rcl-node0-legacy-field : String
rcl-node0-legacy-field = "node-0"

rcl-node1-legacy-field : String
rcl-node1-legacy-field = "node-1"

parse-replica-class-field : String → Maybe replica-class-label
parse-replica-class-field raw =
  if raw == "node-0-dev-clone" then just rcl-node0-dev-clone
  else if raw == rcl-node0-legacy-field then just rcl-node0-dev-clone
  else if raw == "node-1-dev-clone" then just rcl-node1-dev-clone
  else if raw == rcl-node1-legacy-field then just rcl-node1-dev-clone
  else if raw == "forgejo-primary-mirror" then just rcl-forgejo-primary-mirror
  else if raw == "darwin-scratch" then just rcl-darwin-scratch
  else if raw == "offline-luks" then just rcl-offline-luks
  else if raw == "customer-compose" then just rcl-customer-compose
  else nothing

data replica-network-egress : Set where
  rne-tailscale-admin-only : replica-network-egress
  rne-tailscale-no-public-ports : replica-network-egress
  rne-empty : replica-network-egress
  rne-mount-only : replica-network-egress
  rne-customer-policy : replica-network-egress

replica-egress-empty : replica-network-egress → Bool
replica-egress-empty rne-tailscale-admin-only = false
replica-egress-empty rne-tailscale-no-public-ports = false
replica-egress-empty rne-empty = true
replica-egress-empty rne-mount-only = true
replica-egress-empty rne-customer-policy = false

data replica-authority : Set where
  ra-working-copy : replica-authority
  ra-canonical-remote : replica-authority
  ra-backup-scratch : replica-authority
  ra-disaster-copy : replica-authority
  ra-on-site-record : replica-authority

record replica-class-table-row : Set where
  field
    replica-row-class : replica-class-label
    replica-row-egress : replica-network-egress
    replica-row-authority : replica-authority

replica-class-blueprint-row : replica-class-label → replica-class-table-row
replica-class-blueprint-row rcl-node0-dev-clone = record
  { replica-row-class = rcl-node0-dev-clone
  ; replica-row-egress = rne-tailscale-admin-only
  ; replica-row-authority = ra-working-copy
  }
replica-class-blueprint-row rcl-node1-dev-clone = record
  { replica-row-class = rcl-node1-dev-clone
  ; replica-row-egress = rne-tailscale-admin-only
  ; replica-row-authority = ra-working-copy
  }
replica-class-blueprint-row rcl-forgejo-primary-mirror = record
  { replica-row-class = rcl-forgejo-primary-mirror
  ; replica-row-egress = rne-tailscale-no-public-ports
  ; replica-row-authority = ra-canonical-remote
  }
replica-class-blueprint-row rcl-darwin-scratch = record
  { replica-row-class = rcl-darwin-scratch
  ; replica-row-egress = rne-mount-only
  ; replica-row-authority = ra-backup-scratch
  }
replica-class-blueprint-row rcl-offline-luks = record
  { replica-row-class = rcl-offline-luks
  ; replica-row-egress = rne-empty
  ; replica-row-authority = ra-disaster-copy
  }
replica-class-blueprint-row rcl-customer-compose = record
  { replica-row-class = rcl-customer-compose
  ; replica-row-egress = rne-customer-policy
  ; replica-row-authority = ra-on-site-record
  }

replica-class-table-cardinality : ℕ
replica-class-table-cardinality = 6

replica-class-label-to-nat : replica-class-label → ℕ
replica-class-label-to-nat rcl-node0-dev-clone = zero
replica-class-label-to-nat rcl-node1-dev-clone = suc zero
replica-class-label-to-nat rcl-forgejo-primary-mirror = suc (suc zero)
replica-class-label-to-nat rcl-darwin-scratch = suc (suc (suc zero))
replica-class-label-to-nat rcl-offline-luks = suc (suc (suc (suc zero)))
replica-class-label-to-nat rcl-customer-compose = suc (suc (suc (suc (suc zero))))

------------------------------------------------------------------------
-- SECTION 3: fabric-nodes.json class pin + positive refuse
------------------------------------------------------------------------

record fabric-node-class-pin : Set where
  field
    fabric-node-id : String
    fabric-class-field : Maybe String
    fabric-physics-green-claim : Bool
    fabric-joins-labs-public-gossip : Bool

data replica-class-admit : Set where
  rca-admitted : replica-class-admit

data fabric-node-class-verdict : Set where
  fncv-accept : fabric-node-class-verdict

data replica-class-refusal : Set where
  rcr-missing-class-field : replica-class-refusal
  rcr-unknown-replica-class : replica-class-refusal
  rcr-invented-physics-green : replica-class-refusal
  rcr-customer-compose-labs-gossip : replica-class-refusal
  rcr-second-excitement-argmin : replica-class-refusal

record fabric-node-class-row : Set where
  field
    fabric-row-node-id : String
    fabric-row-class : replica-class-label
    fabric-row-table : replica-class-table-row
    fabric-row-verdict : fabric-node-class-verdict
    fabric-row-admit : replica-class-admit

evaluate-fabric-node-class :
  (pin : fabric-node-class-pin) →
  fabric-node-class-row ⊎ replica-class-refusal
evaluate-fabric-node-class pin with fabric-node-class-pin.fabric-physics-green-claim pin
... | true = inj₂ rcr-invented-physics-green
... | false with fabric-node-class-pin.fabric-class-field pin
... | nothing = inj₂ rcr-missing-class-field
... | just raw with parse-replica-class-field raw
... | nothing = inj₂ rcr-unknown-replica-class
... | just cls =
  if does (ℕ-Props._≟_ (replica-class-label-to-nat cls)
                        (replica-class-label-to-nat rcl-customer-compose))
     ∧ fabric-node-class-pin.fabric-joins-labs-public-gossip pin
  then inj₂ rcr-customer-compose-labs-gossip
  else inj₁ (record
    { fabric-row-node-id = fabric-node-class-pin.fabric-node-id pin
    ; fabric-row-class = cls
    ; fabric-row-table = replica-class-blueprint-row cls
    ; fabric-row-verdict = fncv-accept
    ; fabric-row-admit = rca-admitted
    })

refuse-invented-physics-green : replica-class-refusal
refuse-invented-physics-green = rcr-invented-physics-green

refuse-missing-class-field : replica-class-refusal
refuse-missing-class-field = rcr-missing-class-field

refuse-customer-compose-labs-gossip : replica-class-refusal
refuse-customer-compose-labs-gossip = rcr-customer-compose-labs-gossip

refuse-second-excitement-argmin : replica-class-refusal
refuse-second-excitement-argmin = rcr-second-excitement-argmin

refuse-invented-physics-green-positive :
  refuse-invented-physics-green ≡ rcr-invented-physics-green
refuse-invented-physics-green-positive = refl

refuse-missing-class-field-positive :
  refuse-missing-class-field ≡ rcr-missing-class-field
refuse-missing-class-field-positive = refl

refuse-customer-compose-labs-gossip-positive :
  refuse-customer-compose-labs-gossip ≡ rcr-customer-compose-labs-gossip
refuse-customer-compose-labs-gossip-positive = refl

refuse-second-excitement-argmin-positive :
  refuse-second-excitement-argmin ≡ rcr-second-excitement-argmin
refuse-second-excitement-argmin-positive = refl

------------------------------------------------------------------------
-- SECTION 4: Replica class composes excitement-select (no argmin)
------------------------------------------------------------------------

data replica-excitement-compose-pin : Set where
  recp-import-select-excitement : replica-excitement-compose-pin
  recp-second-argmin-refused : replica-excitement-compose-pin

record replica-class-ctx (src : ThermodynamicState) : Set where
  field
    replica-class-successors : List (history-candidate src)

compose-replica-excitement-select :
  (src : ThermodynamicState) (cands : List (history-candidate src))
  (pin : replica-excitement-compose-pin) →
  history-candidate src ⊎ excitement-residue
compose-replica-excitement-select src cands recp-import-select-excitement =
  excitement-select src cands
compose-replica-excitement-select src cands recp-second-argmin-refused =
  inj₂ exc-all-inadmissible

replica-class-select :
  (src : ThermodynamicState) (ctx : replica-class-ctx src) →
  history-candidate src ⊎ excitement-residue
replica-class-select src ctx =
  urge-recovery-select src (replica-class-ctx.replica-class-successors ctx)

compose-replica-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  compose-replica-excitement-select src cands recp-import-select-excitement ≡
  excitement-select src cands
compose-replica-excitement-select-eq-excitement-select src cands = refl

replica-class-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : replica-class-ctx src) →
  replica-class-select src ctx ≡
  excitement-select src (replica-class-ctx.replica-class-successors ctx)
replica-class-select-eq-excitement-select src ctx = refl

replica-class-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : replica-class-ctx src) →
  replica-class-select src ctx ≡
  urge-recovery-select src (replica-class-ctx.replica-class-successors ctx)
replica-class-select-eq-urge-recovery-select src ctx = refl

replica-class-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : replica-class-ctx src) →
  replica-class-select src ctx ≡
  excitement-select src (replica-class-ctx.replica-class-successors ctx)
replica-class-no-local-argmin src ctx =
  replica-class-select-eq-excitement-select src ctx

compose-replica-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List (history-candidate src)) →
  compose-replica-excitement-select src cands recp-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
compose-replica-excitement-select-refuses-second-argmin src cands = refl

replica-class-select-empty :
  ∀ (src : ThermodynamicState) (ctx : replica-class-ctx src) →
  replica-class-ctx.replica-class-successors ctx ≡ [] →
  replica-class-select src ctx ≡ inj₂ exc-no-candidates
replica-class-select-empty src ctx hnil rewrite hnil = refl

------------------------------------------------------------------------
-- SECTION 5: fabric-nodes.json census + §15.4 fixtures
------------------------------------------------------------------------

fabric-nodes-json-rel : String
fabric-nodes-json-rel = "workspace/ops/fabric-nodes.json"

fabric-nodes-schema-pin : String
fabric-nodes-schema-pin = "umst_fabric_nodes_v1"

replica-class-fixture-state : ThermodynamicState
replica-class-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

replica-class-fixture-node0-pin : fabric-node-class-pin
replica-class-fixture-node0-pin = record
  { fabric-node-id = "node-0"
  ; fabric-class-field = just "node-0-dev-clone"
  ; fabric-physics-green-claim = false
  ; fabric-joins-labs-public-gossip = false
  }

replica-class-fixture-invent-green-pin : fabric-node-class-pin
replica-class-fixture-invent-green-pin = record
  { fabric-node-id = "node-invent-green"
  ; fabric-class-field = just "node-1-dev-clone"
  ; fabric-physics-green-claim = true
  ; fabric-joins-labs-public-gossip = false
  }

replica-class-fixture-compose-gossip-pin : fabric-node-class-pin
replica-class-fixture-compose-gossip-pin = record
  { fabric-node-id = "compose-customer"
  ; fabric-class-field = just "customer-compose"
  ; fabric-physics-green-claim = false
  ; fabric-joins-labs-public-gossip = true
  }

replica-class-fixture-node0-admitted :
  evaluate-fabric-node-class replica-class-fixture-node0-pin ≡
  inj₁ (record
    { fabric-row-node-id = "node-0"
    ; fabric-row-class = rcl-node0-dev-clone
    ; fabric-row-table = replica-class-blueprint-row rcl-node0-dev-clone
    ; fabric-row-verdict = fncv-accept
    ; fabric-row-admit = rca-admitted
    })
replica-class-fixture-node0-admitted = refl

replica-class-fixture-invent-green-refused :
  evaluate-fabric-node-class replica-class-fixture-invent-green-pin ≡
  inj₂ rcr-invented-physics-green
replica-class-fixture-invent-green-refused = refl

replica-class-fixture-compose-gossip-refused :
  evaluate-fabric-node-class replica-class-fixture-compose-gossip-pin ≡
  inj₂ rcr-customer-compose-labs-gossip
replica-class-fixture-compose-gossip-refused = refl

replica-class-offline-luks-egress-empty :
  replica-egress-empty (replica-class-table-row.replica-row-egress
    (replica-class-blueprint-row rcl-offline-luks)) ≡ true
replica-class-offline-luks-egress-empty = refl

replica-class-darwin-scratch-egress-empty :
  replica-egress-empty (replica-class-table-row.replica-row-egress
    (replica-class-blueprint-row rcl-darwin-scratch)) ≡ true
replica-class-darwin-scratch-egress-empty = refl

replica-class-forgejo-egress-nonempty :
  replica-egress-empty (replica-class-table-row.replica-row-egress
    (replica-class-blueprint-row rcl-forgejo-primary-mirror)) ≡ false
replica-class-forgejo-egress-nonempty = refl

replica-class-table-cardinality-six :
  replica-class-table-cardinality ≡ 6
replica-class-table-cardinality-six = refl

replica-class-node0-class-field :
  replica-class-class-field rcl-node0-dev-clone ≡ "node-0-dev-clone"
replica-class-node0-class-field = refl

replica-class-parse-legacy-node0 :
  parse-replica-class-field rcl-node0-legacy-field ≡ just rcl-node0-dev-clone
replica-class-parse-legacy-node0 = refl

replica-class-parse-unknown-none :
  parse-replica-class-field "unknown-class" ≡ nothing
replica-class-parse-unknown-none = refl

replica-class-positive-refuse-not-silent :
  evaluate-fabric-node-class replica-class-fixture-invent-green-pin ≢
  inj₁ (record
    { fabric-row-node-id = "node-invent-green"
    ; fabric-row-class = rcl-node1-dev-clone
    ; fabric-row-table = replica-class-blueprint-row rcl-node1-dev-clone
    ; fabric-row-verdict = fncv-accept
    ; fabric-row-admit = rca-admitted
    })
replica-class-positive-refuse-not-silent ()

replica-class-compose-excitement-not-argmin :
  ∀ (src : ThermodynamicState) (ctx : replica-class-ctx src) →
  replica-class-select src ctx ≡
  excitement-select src (replica-class-ctx.replica-class-successors ctx)
replica-class-compose-excitement-not-argmin src ctx =
  replica-class-no-local-argmin src ctx

------------------------------------------------------------------------
-- SECTION 6: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

replica-class-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
replica-class-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

replica-class-production-wired : Bool
replica-class-production-wired = false

replica-class-production-wired-false :
  replica-class-production-wired ≡ false
replica-class-production-wired-false = refl

replica-class-marker : ℕ
replica-class-marker = 1

replica-class-marker-eq : replica-class-marker ≡ 1
replica-class-marker-eq = refl

replica-class-module-witness : ⊤
replica-class-module-witness = tt

replica-class-no-new-postulate : ⊤
replica-class-no-new-postulate = tt
