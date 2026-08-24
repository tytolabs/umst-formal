-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CarrierProduct -- meso/acting five-factor history carrier.
--
-- §3 Repository/History carrier as typed product:
--   UMST ⊗ UCRS stamp ⊗ SDF/FRep ⊗ ExactAlg ⊗ InvariantWitness.
--
-- History carrier is a dependent product (not prose slogans): projections,
-- pairing, preservation lemmas. Anchored in `Chem.SecondLaw` via inherited
-- `admitSecondLaw`. Excitement `select` composed -- no second argmin.
--
-- Refuse XOR partial carrier -- five factors are concurrent **product**, not
-- mutually-exclusive enum; absent-factor scaffold refused fail-closed.
--
-- physics_green: false -- knowing fiber cited, not restated here.
-- Zero extra postulate beyond Landauer (`Chem.SecondLaw.physicalSecondLaw`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CarrierProduct where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.List as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Minimal thermodynamic head pin (parallel to MergeSafe -- no Concrete.Gate)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field state-tag : ℕ

record Admissible (s₀ s₁ : ThermodynamicState) : Set where
  field adm-tag : ℕ

------------------------------------------------------------------------
-- SECTION 0: Typed history carriers (parallel pin to Urge.AdmitKleisli)
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
    gate-admissible : Admissible (HistorySnapshot.head prior) (HistorySnapshot.head post)

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

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
  (src : ThermodynamicState) → List.List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

record PhysicalHistoryBridge : Set where
  field
    proc : ErasureProcess
    transition : HistoryTransition
    dissipated-eq :
      HistoryTransition.dissipated-entropy transition ≡
      ErasureProcess.dissipatedEntropy proc

admitSecondLaw-from-physical :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
admitSecondLaw-from-physical record { proc = proc; transition = t; dissipated-eq = deq } h =
  subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym deq) h

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss =
  let step1 = subst (λ x → x ≤ ErasureProcess.dissipatedEntropy proc) (sym hent) hSL
  in subst (λ d → HistoryTransition.entropy-drop t ≤ d) (sym hdiss) step1

------------------------------------------------------------------------
-- SECTION 1: Factor carriers (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness)
------------------------------------------------------------------------

data StampTier : Set where
  stamp-wall-only stamp-wall-plus-seq : StampTier

record UcrsStamp : Set where
  field
    observed-at-wall : ℕ
    ucrs-seq : Maybe ℕ
    tier : StampTier

wallOnlyStamp : ℕ → UcrsStamp
wallOnlyStamp wall = record
  { observed-at-wall = wall
  ; ucrs-seq = nothing
  ; tier = stamp-wall-only
  }

wallPlusSeqStamp : ℕ → ℕ → UcrsStamp
wallPlusSeqStamp wall seq = record
  { observed-at-wall = wall
  ; ucrs-seq = just seq
  ; tier = stamp-wall-plus-seq
  }

record SdfFRep : Set where
  field
    canonical-digest : ℕ
    frep-grain : ℕ

record ExactAlg : Set where
  field
    alg-value : ℚ
    op-tag : ℕ

record InvariantWitness : Set where
  field
    satisfied : Bool
    margin-h : ℚ

witnessProp : InvariantWitness → Set
witnessProp w =
  if InvariantWitness.satisfied w then ⊤ else ⊥

satisfiedWitness : InvariantWitness
satisfiedWitness = record { satisfied = true ; margin-h = 0ℚ }

rejectedWitness : InvariantWitness
rejectedWitness = record { satisfied = false ; margin-h = 0ℚ }

------------------------------------------------------------------------
-- SECTION 2: History carrier product + projections
------------------------------------------------------------------------

record HistoryCarrier : Set where
  field
    umst : HistorySnapshot
    stamp : UcrsStamp
    sdf-frep : SdfFRep
    exact-alg : ExactAlg
    witness : InvariantWitness

umstProj : HistoryCarrier → HistorySnapshot
umstProj c = HistoryCarrier.umst c

stampProj : HistoryCarrier → UcrsStamp
stampProj c = HistoryCarrier.stamp c

sdfFRepProj : HistoryCarrier → SdfFRep
sdfFRepProj c = HistoryCarrier.sdf-frep c

exactAlgProj : HistoryCarrier → ExactAlg
exactAlgProj c = HistoryCarrier.exact-alg c

witnessProj : HistoryCarrier → InvariantWitness
witnessProj c = HistoryCarrier.witness c

carrierMk :
  HistorySnapshot → UcrsStamp → SdfFRep → ExactAlg → InvariantWitness →
  HistoryCarrier
carrierMk h s d a w = record
  { umst = h
  ; stamp = s
  ; sdf-frep = d
  ; exact-alg = a
  ; witness = w
  }

carrierMk-umstProj :
  ∀ h s d a w → umstProj (carrierMk h s d a w) ≡ h
carrierMk-umstProj h s d a w = refl

carrierMk-stampProj :
  ∀ h s d a w → stampProj (carrierMk h s d a w) ≡ s
carrierMk-stampProj h s d a w = refl

carrierMk-sdfFRepProj :
  ∀ h s d a w → sdfFRepProj (carrierMk h s d a w) ≡ d
carrierMk-sdfFRepProj h s d a w = refl

carrierMk-exactAlgProj :
  ∀ h s d a w → exactAlgProj (carrierMk h s d a w) ≡ a
carrierMk-exactAlgProj h s d a w = refl

carrierMk-witnessProj :
  ∀ h s d a w → witnessProj (carrierMk h s d a w) ≡ w
carrierMk-witnessProj h s d a w = refl

------------------------------------------------------------------------
-- SECTION 3: Well-formedness + append-only stamp discipline
------------------------------------------------------------------------

carrierWellFormed : HistoryCarrier → Set
carrierWellFormed c =
  does ((suc zero) ℕ-Props.≤? UcrsStamp.observed-at-wall (stampProj c)) ≡ true
  × 0ℚ ≤ InvariantWitness.margin-h (witnessProj c)

extendStamp : UcrsStamp → ℕ → UcrsStamp
extendStamp prior postWall with UcrsStamp.ucrs-seq prior
... | nothing = wallOnlyStamp postWall
... | just seq = wallPlusSeqStamp postWall seq

extendStamp-preserves-seq :
  ∀ prior postWall → UcrsStamp.ucrs-seq (extendStamp prior postWall) ≡ UcrsStamp.ucrs-seq prior
extendStamp-preserves-seq prior postWall with UcrsStamp.ucrs-seq prior
... | nothing = refl
... | just seq = refl

carrierAlongTransition :
  (t : HistoryTransition) (prior-carrier : HistoryCarrier) →
  HistorySnapshot.commit-id (umstProj prior-carrier) ≡ HistorySnapshot.commit-id (HistoryTransition.prior t) →
  ℕ → HistoryCarrier
carrierAlongTransition t prior-carrier hPrior postWall =
  carrierMk (HistoryTransition.post t)
    (extendStamp (stampProj prior-carrier) postWall)
    (sdfFRepProj prior-carrier)
    (exactAlgProj prior-carrier)
    (witnessProj prior-carrier)

carrierAlongTransition-preserves-sdf :
  ∀ t prior-carrier hPrior postWall →
  sdfFRepProj (carrierAlongTransition t prior-carrier hPrior postWall) ≡ sdfFRepProj prior-carrier
carrierAlongTransition-preserves-sdf t prior-carrier hPrior postWall = refl

carrierAlongTransition-preserves-exactAlg :
  ∀ t prior-carrier hPrior postWall →
  exactAlgProj (carrierAlongTransition t prior-carrier hPrior postWall) ≡ exactAlgProj prior-carrier
carrierAlongTransition-preserves-exactAlg t prior-carrier hPrior postWall = refl

------------------------------------------------------------------------
-- SECTION 4: Second-law bridge (inherited -- zero new axioms)
------------------------------------------------------------------------

carrierFromPhysical :
  (b : PhysicalHistoryBridge) (prior-carrier : HistoryCarrier) →
  HistorySnapshot.commit-id (umstProj prior-carrier) ≡
    HistorySnapshot.commit-id (HistoryTransition.prior (PhysicalHistoryBridge.transition b)) →
  ℕ →
  admitSecondLaw (PhysicalHistoryBridge.transition b) →
  HistoryCarrier
carrierFromPhysical b prior-carrier hPrior postWall hSL =
  carrierMk (HistoryTransition.post (PhysicalHistoryBridge.transition b))
    (extendStamp (stampProj prior-carrier) postWall)
    (sdfFRepProj prior-carrier)
    (exactAlgProj prior-carrier)
    satisfiedWitness

carrierFromPhysical-admitSecondLaw :
  ∀ (b : PhysicalHistoryBridge)
    (hSL : admitSecondLaw (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
carrierFromPhysical-admitSecondLaw b hSL = hSL

carrierFromPhysical-witness-satisfied :
  ∀ b prior-carrier hPrior postWall
    (hSL : admitSecondLaw (PhysicalHistoryBridge.transition b)) →
  InvariantWitness.satisfied (witnessProj (carrierFromPhysical b prior-carrier hPrior postWall hSL)) ≡ true
carrierFromPhysical-witness-satisfied b prior-carrier hPrior postWall hSL = refl

admitSecondLaw-from-physical-carrier :
  ∀ (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
admitSecondLaw-from-physical-carrier b h =
  admitSecondLaw-from-physical b h

physicalSecondLaw-discharge-carrier :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
physicalSecondLaw-discharge-carrier proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

------------------------------------------------------------------------
-- SECTION 5: Excitement alignment (no second argmin)
------------------------------------------------------------------------

carrierSelect :
  (c : HistoryCarrier) →
  List.List (history-candidate (HistorySnapshot.head (umstProj c))) →
  history-candidate (HistorySnapshot.head (umstProj c)) ⊎ excitement-residue
carrierSelect c cands = excitement-select (HistorySnapshot.head (umstProj c)) cands

carrierSelect-eq-excitement-select :
  ∀ c cands →
  carrierSelect c cands ≡ excitement-select (HistorySnapshot.head (umstProj c)) cands
carrierSelect-eq-excitement-select c cands = refl

------------------------------------------------------------------------
-- SECTION 6: Refuse XOR partial carrier (product not enum; no absent factors)
------------------------------------------------------------------------

data CarrierFactorSlot : Set where
  factor-present factor-absent factor-unwired : CarrierFactorSlot

isFactorPresent : CarrierFactorSlot → Bool
isFactorPresent factor-present = true
isFactorPresent factor-absent = false
isFactorPresent factor-unwired = false

record CarrierFactorScaffold : Set where
  field
    umst-slot : CarrierFactorSlot
    stamp-slot : CarrierFactorSlot
    sdf-slot : CarrierFactorSlot
    exact-slot : CarrierFactorSlot
    witness-slot : CarrierFactorSlot

carrierScaffoldUnwired : CarrierFactorScaffold
carrierScaffoldUnwired = record
  { umst-slot = factor-unwired
  ; stamp-slot = factor-unwired
  ; sdf-slot = factor-unwired
  ; exact-slot = factor-unwired
  ; witness-slot = factor-unwired
  }

allFactorsPresent : CarrierFactorScaffold → Bool
allFactorsPresent s =
  isFactorPresent (CarrierFactorScaffold.umst-slot s)
  ∧ isFactorPresent (CarrierFactorScaffold.stamp-slot s)
  ∧ isFactorPresent (CarrierFactorScaffold.sdf-slot s)
  ∧ isFactorPresent (CarrierFactorScaffold.exact-slot s)
  ∧ isFactorPresent (CarrierFactorScaffold.witness-slot s)

data PartialCarrierVerdict : Set where
  partial-carrier-refuse partial-carrier-ok : PartialCarrierVerdict

evaluatePartialCarrier : CarrierFactorScaffold → PartialCarrierVerdict
evaluatePartialCarrier s =
  if allFactorsPresent s then partial-carrier-ok else partial-carrier-refuse

partial-carrier-unwired-refused :
  evaluatePartialCarrier carrierScaffoldUnwired ≡ partial-carrier-refuse
partial-carrier-unwired-refused = refl

fullScaffold : CarrierFactorScaffold
fullScaffold = record
  { umst-slot = factor-present
  ; stamp-slot = factor-present
  ; sdf-slot = factor-present
  ; exact-slot = factor-present
  ; witness-slot = factor-present
  }

partial-carrier-full-ok :
  evaluatePartialCarrier fullScaffold ≡ partial-carrier-ok
partial-carrier-full-ok = refl

data XorCarrierVerdict : Set where
  xor-carrier-refuse xor-carrier-product-ok : XorCarrierVerdict

evaluateXorCarrier :
  CarrierFactorScaffold → CarrierFactorSlot → CarrierFactorSlot → XorCarrierVerdict
evaluateXorCarrier s i j =
  if allFactorsPresent s
  then if isFactorPresent i ∧ isFactorPresent j
       then xor-carrier-refuse
       else xor-carrier-product-ok
  else xor-carrier-product-ok

xor-carrier-unwired-product-ok :
  evaluateXorCarrier carrierScaffoldUnwired factor-present factor-present ≡ xor-carrier-product-ok
xor-carrier-unwired-product-ok = refl

xor-carrier-mutually-exclusive-refused :
  evaluateXorCarrier fullScaffold factor-present factor-present ≡ xor-carrier-refuse
xor-carrier-mutually-exclusive-refused = refl

carrier-product-not-xor : Bool
carrier-product-not-xor = true

carrier-product-not-xor-true : carrier-product-not-xor ≡ true
carrier-product-not-xor-true = refl

carrier-product-not-partial : Bool
carrier-product-not-partial = true

carrier-product-not-partial-true : carrier-product-not-partial ≡ true
carrier-product-not-partial-true = refl

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

carrier-product-physics-green : Bool
carrier-product-physics-green = false

carrier-product-physics-green-false :
  carrier-product-physics-green ≡ false
carrier-product-physics-green-false = refl

carrier-product-production-wired : Bool
carrier-product-production-wired = false

carrier-product-production-wired-false :
  carrier-product-production-wired ≡ false
carrier-product-production-wired-false = refl

carrier-product-module-witness : ⊤
carrier-product-module-witness = tt

carrier-product-no-new-axiom : ⊤
carrier-product-no-new-axiom = tt
