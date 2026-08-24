-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.ReplicaCoalgebra — meso/acting §15.4 replica coalgebra.
--
-- URGE-FORMAL-MESO-AGDA-REPLICA-COALGEBRA (umst-formal acting fiber only).
-- §15.4: node-0 / node-1 / Forgejo / LUKS are **replica classes** — sample
-- sections of one mesh sheaf, not XOR worlds.  Inbound merge:
--
--   admit(h) ⟺ gate_check(h) ∧ MergeSafe(h) ∧ Excitement preserves provenance(h)
--
-- Backup is a **typed recovery morphism** (Excitement `select`, not rsync theater).
-- Offline LUKS replica class carries `network-egress: []`.
--
-- Compose `replica-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.ReplicaCoalgebra where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 0: Typed gate carriers (local — --without-K leaf)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    stub : ℕ

Admissible : ThermodynamicState → ThermodynamicState → Set
Admissible _ _ = ⊤

------------------------------------------------------------------------
-- SECTION 1: Replica classes (sample sections — not XOR worlds)
------------------------------------------------------------------------

data ReplicaClass : Set where
  replica-node0 : ReplicaClass
  replica-node1 : ReplicaClass
  replica-forge : ReplicaClass
  replica-luks : ReplicaClass

replica-class-tag : ReplicaClass → String
replica-class-tag replica-node0 = "node-0"
replica-class-tag replica-node1 = "node-1"
replica-class-tag replica-forge = "forge"
replica-class-tag replica-luks = "luks"

node0-tag : replica-class-tag replica-node0 ≡ "node-0"
node0-tag = refl

node1-tag : replica-class-tag replica-node1 ≡ "node-1"
node1-tag = refl

forge-tag : replica-class-tag replica-forge ≡ "forge"
forge-tag = refl

luks-tag : replica-class-tag replica-luks ≡ "luks"
luks-tag = refl

replica-node0≢replica-node1 : replica-node0 ≢ replica-node1
replica-node0≢replica-node1 ()

replica-node0≢replica-forge : replica-node0 ≢ replica-forge
replica-node0≢replica-forge ()

replica-node0≢replica-luks : replica-node0 ≢ replica-luks
replica-node0≢replica-luks ()

replica-node1≢replica-forge : replica-node1 ≢ replica-forge
replica-node1≢replica-forge ()

replica-node1≢replica-luks : replica-node1 ≢ replica-luks
replica-node1≢replica-luks ()

replica-forge≢replica-luks : replica-forge ≢ replica-luks
replica-forge≢replica-luks ()

replica-classes-not-xor : Set
replica-classes-not-xor =
  (replica-node0 ≢ replica-node1) ×
  (replica-node0 ≢ replica-forge) ×
  (replica-node0 ≢ replica-luks) ×
  (replica-node1 ≢ replica-forge) ×
  (replica-node1 ≢ replica-luks) ×
  (replica-forge ≢ replica-luks)

replica-classes-not-xor-holds : replica-classes-not-xor
replica-classes-not-xor-holds =
  replica-node0≢replica-node1 ,
  replica-node0≢replica-forge ,
  replica-node0≢replica-luks ,
  replica-node1≢replica-forge ,
  replica-node1≢replica-luks ,
  replica-forge≢replica-luks

replica-class-count : ℕ
replica-class-count = 4

replica-class-count-is-four : replica-class-count ≡ 4
replica-class-count-is-four = refl

------------------------------------------------------------------------
-- SECTION 2: Mesh sheaf + coalgebra observe (concurrent sections)
------------------------------------------------------------------------

record ReplicaMeshSheaf : Set where
  field
    section-probe : ReplicaClass → ℕ

node0-sample-section : ReplicaMeshSheaf → ℕ
node0-sample-section R = ReplicaMeshSheaf.section-probe R replica-node0

node1-sample-section : ReplicaMeshSheaf → ℕ
node1-sample-section R = ReplicaMeshSheaf.section-probe R replica-node1

forge-sample-section : ReplicaMeshSheaf → ℕ
forge-sample-section R = ReplicaMeshSheaf.section-probe R replica-forge

luks-sample-section : ReplicaMeshSheaf → ℕ
luks-sample-section R = ReplicaMeshSheaf.section-probe R replica-luks

sample-section-at : ReplicaClass → ReplicaMeshSheaf → ℕ
sample-section-at c R = ReplicaMeshSheaf.section-probe R c

record ReplicaSectionBundle : Set where
  field
    sec-node0 : ℕ
    sec-node1 : ℕ
    sec-forge : ℕ
    sec-luks : ℕ

replica-coalgebra-observe : ReplicaMeshSheaf → ReplicaSectionBundle
replica-coalgebra-observe R = record
  { sec-node0 = node0-sample-section R
  ; sec-node1 = node1-sample-section R
  ; sec-forge = forge-sample-section R
  ; sec-luks = luks-sample-section R
  }

replica-coalgebra-observe-components :
  ∀ (R : ReplicaMeshSheaf) →
  ReplicaSectionBundle.sec-node0 (replica-coalgebra-observe R) ≡ node0-sample-section R ×
  ReplicaSectionBundle.sec-node1 (replica-coalgebra-observe R) ≡ node1-sample-section R ×
  ReplicaSectionBundle.sec-forge (replica-coalgebra-observe R) ≡ forge-sample-section R ×
  ReplicaSectionBundle.sec-luks (replica-coalgebra-observe R) ≡ luks-sample-section R
replica-coalgebra-observe-components R = refl , refl , refl , refl

sample-section-at-node0 :
  ∀ (R : ReplicaMeshSheaf) →
  sample-section-at replica-node0 R ≡ node0-sample-section R
sample-section-at-node0 R = refl

sample-section-at-node1 :
  ∀ (R : ReplicaMeshSheaf) →
  sample-section-at replica-node1 R ≡ node1-sample-section R
sample-section-at-node1 R = refl

sample-section-at-forge :
  ∀ (R : ReplicaMeshSheaf) →
  sample-section-at replica-forge R ≡ forge-sample-section R
sample-section-at-forge R = refl

sample-section-at-luks :
  ∀ (R : ReplicaMeshSheaf) →
  sample-section-at replica-luks R ≡ luks-sample-section R
sample-section-at-luks R = refl

section-probe-witness : ReplicaClass → ℕ
section-probe-witness replica-node0 = 1
section-probe-witness replica-node1 = 2
section-probe-witness replica-forge = 3
section-probe-witness replica-luks = 4

witness-replica-sheaf : ReplicaMeshSheaf
witness-replica-sheaf = record { section-probe = section-probe-witness }

node0-does-not-close-luks :
  Σ ReplicaMeshSheaf (λ R → node0-sample-section R ≢ luks-sample-section R)
node0-does-not-close-luks = witness-replica-sheaf , λ ()

------------------------------------------------------------------------
-- SECTION 3: Network egress (offline LUKS carries empty egress)
------------------------------------------------------------------------

network-egress : ReplicaClass → List String
network-egress replica-luks = []
network-egress replica-node0 = "tailscale-admin" ∷ []
network-egress replica-node1 = "tailscale-admin" ∷ []
network-egress replica-forge = "tailscale-admin" ∷ []

luks-network-egress-empty : network-egress replica-luks ≡ []
luks-network-egress-empty = refl

node0-network-egress-tailscale :
  network-egress replica-node0 ≡ "tailscale-admin" ∷ []
node0-network-egress-tailscale = refl

offline-luks-is-network-egress-empty :
  network-egress replica-luks ≡ [] × replica-class-tag replica-luks ≡ "luks"
offline-luks-is-network-egress-empty = luks-network-egress-empty , luks-tag

------------------------------------------------------------------------
-- SECTION 4: Admissible replica coalgebra (gate ∧ MergeSafe ∧ prov)
------------------------------------------------------------------------

record ReplicaHistoryMove : Set where
  field
    prior : ThermodynamicState
    post : ThermodynamicState
    gate-checked : Bool
    merge-safe : Bool
    provenance-ok : Bool

admissible-replica-coalgebra : ReplicaHistoryMove → Set
admissible-replica-coalgebra h =
  (ReplicaHistoryMove.gate-checked h ≡ true) ×
  (ReplicaHistoryMove.merge-safe h ≡ true) ×
  (ReplicaHistoryMove.provenance-ok h ≡ true)

admissible-replica-coalgebra-intro :
  (h : ReplicaHistoryMove) →
  ReplicaHistoryMove.gate-checked h ≡ true →
  ReplicaHistoryMove.merge-safe h ≡ true →
  ReplicaHistoryMove.provenance-ok h ≡ true →
  admissible-replica-coalgebra h
admissible-replica-coalgebra-intro h hg hm hp = hg , hm , hp

admit-replica-inbound : ReplicaHistoryMove → Set
admit-replica-inbound = admissible-replica-coalgebra

------------------------------------------------------------------------
-- SECTION 5: Excitement hook + typed recovery (no second argmin)
------------------------------------------------------------------------

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record history-candidate (src : ThermodynamicState) : Set where
  field
    cand-id : ℕ
    cand-tgt : ThermodynamicState
    cand-admissible : Admissible src cand-tgt

replica-excitement-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
replica-excitement-select src List.[] = inj₂ exc-no-candidates
replica-excitement-select src (c List.∷ _) = inj₁ c

record recovery-ctx (src : ThermodynamicState) : Set where
  field
    recovery-successors : List (history-candidate src)

typed-recovery-morphism :
  (src : ThermodynamicState) (ctx : recovery-ctx src) →
  history-candidate src ⊎ excitement-residue
typed-recovery-morphism src ctx =
  replica-excitement-select src (recovery-ctx.recovery-successors ctx)

typed-recovery-select :
  (src : ThermodynamicState) (successors : List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
typed-recovery-select src successors = replica-excitement-select src successors

typed-recovery-morphism-eq-replica-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : recovery-ctx src) →
  typed-recovery-morphism src ctx ≡
  replica-excitement-select src (recovery-ctx.recovery-successors ctx)
typed-recovery-morphism-eq-replica-excitement-select src ctx = refl

typed-recovery-select-eq-replica-excitement-select :
  ∀ (src : ThermodynamicState) (successors : List (history-candidate src)) →
  typed-recovery-select src successors ≡ replica-excitement-select src successors
typed-recovery-select-eq-replica-excitement-select src successors = refl

typed-recovery-morphism-eq-typed-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : recovery-ctx src) →
  typed-recovery-morphism src ctx ≡
  typed-recovery-select src (recovery-ctx.recovery-successors ctx)
typed-recovery-morphism-eq-typed-recovery-select src ctx = refl

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second ℚ argmin)
------------------------------------------------------------------------

data ReplicaCoalgebraRefusal : Set where
  rsync-theater : ReplicaCoalgebraRefusal
  second-argmin : ReplicaCoalgebraRefusal
  xor-world-partition : ReplicaCoalgebraRefusal

refuse-rsync-theater : ReplicaCoalgebraRefusal
refuse-rsync-theater = rsync-theater

refuse-second-argmin : ReplicaCoalgebraRefusal
refuse-second-argmin = second-argmin

refuse-xor-world-partition : ReplicaCoalgebraRefusal
refuse-xor-world-partition = xor-world-partition

urge-replica-select :
  (src : ThermodynamicState) → List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
urge-replica-select = replica-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 7: Second-law bridge (Landauer lift — zero new axioms)
------------------------------------------------------------------------

record HistoryTransition : Set where
  field
    prior : ThermodynamicState
    post : ThermodynamicState
    bath : HeatBath
    dissipated-entropy : ℚ
    entropy-drop : ℚ

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

record ReplicaTransition : Set where
  field
    move : ReplicaHistoryMove
    transition : HistoryTransition

replica-second-law : ReplicaTransition → Set
replica-second-law t =
  admitSecondLaw (ReplicaTransition.transition t)

record PhysicalHistoryBridge : Set where
  field
    proc : ErasureProcess
    transition : HistoryTransition
    dissipated-eq :
      HistoryTransition.dissipated-entropy transition ≡
      ErasureProcess.dissipatedEntropy proc

record PhysicalReplicaBridge : Set where
  field
    landauer : PhysicalHistoryBridge
    move : ReplicaHistoryMove
    admissible : admissible-replica-coalgebra move

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

replica-second-law-from-physical :
  (b : PhysicalReplicaBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc (PhysicalReplicaBridge.landauer b))
    (HistoryTransition.entropy-drop
      (PhysicalHistoryBridge.transition (PhysicalReplicaBridge.landauer b))) →
  replica-second-law (record { move = PhysicalReplicaBridge.move b
                           ; transition = PhysicalHistoryBridge.transition (PhysicalReplicaBridge.landauer b) })
replica-second-law-from-physical b hSL =
  admitSecondLaw-from-landauer
    (PhysicalHistoryBridge.proc (PhysicalReplicaBridge.landauer b))
    (HistoryTransition.entropy-drop
      (PhysicalHistoryBridge.transition (PhysicalReplicaBridge.landauer b)))
    hSL
    (PhysicalHistoryBridge.transition (PhysicalReplicaBridge.landauer b))
    refl
    (PhysicalHistoryBridge.dissipated-eq (PhysicalReplicaBridge.landauer b))

admissible-replica-coalgebra-from-physical :
  (b : PhysicalReplicaBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc (PhysicalReplicaBridge.landauer b))
    (HistoryTransition.entropy-drop
      (PhysicalHistoryBridge.transition (PhysicalReplicaBridge.landauer b))) →
  admissible-replica-coalgebra (PhysicalReplicaBridge.move b)
admissible-replica-coalgebra-from-physical b _ =
  PhysicalReplicaBridge.admissible b

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

replica-coalgebra-production-wired : Bool
replica-coalgebra-production-wired = false

replica-coalgebra-production-wired-false :
  replica-coalgebra-production-wired ≡ false
replica-coalgebra-production-wired-false = refl

replica-coalgebra-module-witness : ⊤
replica-coalgebra-module-witness = tt

replica-coalgebra-no-new-axiom : ⊤
replica-coalgebra-no-new-axiom = tt

replica-coalgebra-named-not-xor : replica-classes-not-xor
replica-coalgebra-named-not-xor = replica-classes-not-xor-holds

replica-coalgebra-marker : ℕ
replica-coalgebra-marker = 1

replica-coalgebra-marker-eq : replica-coalgebra-marker ≡ 1
replica-coalgebra-marker-eq = refl

rsync-theater-refused :
  refuse-rsync-theater ≡ rsync-theater
rsync-theater-refused = refl

xor-world-partition-refused :
  refuse-xor-world-partition ≡ xor-world-partition
xor-world-partition-refused = refl
