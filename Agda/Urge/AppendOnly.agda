-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.AppendOnly — meso/acting Urge §17.6 append-only history.
--
-- Admitted history is append-only; silent rewrite refused as a positive `Set`
-- predicate (not only `physics_green` negation).
-- Self-healing adds an Excitement arrow; it does not mutate prior admitted objects.
--
-- Anchored in `Chem.SecondLaw.physicalSecondLaw` via `PhysicalHistoryBridge`
-- (sole Landauer postulate — imported, not re-declared).
-- History carriers align with `Urge.AdmitKleisli` §1 (local copy until Kleisli
-- import chain is `--without-K` coherent).
--
-- physics_green: false — knowing fiber lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.AppendOnly where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; 1+n≰n; ≰⇒>)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (mirror Urge.AdmitKleisli §1)
------------------------------------------------------------------------

record ThermodynamicState : Set where
  field
    stub : ℕ

Admissible : ThermodynamicState → ThermodynamicState → Set
Admissible _ _ = ⊤

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
  HistoryTransition.entropy-drop t ℚ.≤ HistoryTransition.dissipated-entropy t

admissibleHistoryTransition : HistoryTransition → Set
admissibleHistoryTransition t = admitSecondLaw t

------------------------------------------------------------------------
-- SECTION 2: §17.6 append-only discipline
------------------------------------------------------------------------

appendOnlyCommitMove : HistoryTransition → Set
appendOnlyCommitMove t =
  HistorySnapshot.commit-id (HistoryTransition.prior t) <
  HistorySnapshot.commit-id (HistoryTransition.post t)

appendOnlyInvariant : HistoryTransition → Set
appendOnlyInvariant t = appendOnlyCommitMove t

silentRewrite : HistoryTransition → Set
silentRewrite t =
  HistorySnapshot.commit-id (HistoryTransition.post t) ≤
  HistorySnapshot.commit-id (HistoryTransition.prior t)

silentRewriteRefused :
  ∀ (t : HistoryTransition) → appendOnlyCommitMove t → ¬ silentRewrite t
silentRewriteRefused t h contr =
  1+n≰n (≤-trans h contr)

appendOnly-from-¬silentRewrite :
  ∀ (t : HistoryTransition) → ¬ silentRewrite t → appendOnlyCommitMove t
appendOnly-from-¬silentRewrite t ¬h = ≰⇒> ¬h

appendOnlyAdmittedTransition : HistoryTransition → Set
appendOnlyAdmittedTransition t =
  admissibleHistoryTransition t × appendOnlyInvariant t

appendOnlyHistoryChain : List HistoryTransition → Set
appendOnlyHistoryChain ts = ∀ {t} → t ∈ ts → appendOnlyCommitMove t

appendOnlyHistoryChain-refusesSilentRewrite :
  ∀ (ts : List HistoryTransition) →
  appendOnlyHistoryChain ts →
  ∀ (t : HistoryTransition) → t ∈ ts → ¬ silentRewrite t
appendOnlyHistoryChain-refusesSilentRewrite ts h t t∈ts =
  silentRewriteRefused t (h t∈ts)

recoveryAppendOnly : HistorySnapshot → HistorySnapshot → Set
recoveryAppendOnly prior post =
  HistorySnapshot.commit-id prior < HistorySnapshot.commit-id post

silentRewriteSnapshots : HistorySnapshot → HistorySnapshot → Set
silentRewriteSnapshots prior post =
  HistorySnapshot.commit-id post ≤ HistorySnapshot.commit-id prior

recoveryAppendOnly-refusesSilentRewrite :
  ∀ (prior post : HistorySnapshot) →
  recoveryAppendOnly prior post → ¬ silentRewriteSnapshots prior post
recoveryAppendOnly-refusesSilentRewrite prior post h contr =
  1+n≰n (≤-trans h contr)

selfHealAppendOnly : HistoryTransition → Set
selfHealAppendOnly t =
  recoveryAppendOnly (HistoryTransition.prior t) (HistoryTransition.post t)

selfHealAppendOnly-eq-appendOnlyInvariant :
  ∀ (t : HistoryTransition) → selfHealAppendOnly t ≡ appendOnlyInvariant t
selfHealAppendOnly-eq-appendOnlyInvariant t = refl

selfHeal-not-silentRewrite :
  ∀ (t : HistoryTransition) →
  selfHealAppendOnly t → ¬ silentRewriteSnapshots (HistoryTransition.prior t) (HistoryTransition.post t)
selfHeal-not-silentRewrite t h =
  recoveryAppendOnly-refusesSilentRewrite (HistoryTransition.prior t) (HistoryTransition.post t) h

------------------------------------------------------------------------
-- SECTION 3: Physical bridge (zero new postulates beyond Landauer)
------------------------------------------------------------------------

record PhysicalHistoryBridge : Set where
  constructor mk-bridge
  field
    bridge-proc : ErasureProcess
    bridge-transition : HistoryTransition
    bridge-dissipated-eq :
      HistoryTransition.dissipated-entropy bridge-transition ≡
      ErasureProcess.dissipatedEntropy bridge-proc

admitSecondLaw-from-physical :
  (proc : ErasureProcess) (t : HistoryTransition) →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  PhysicalSecondLaw proc (HistoryTransition.entropy-drop t) →
  admitSecondLaw t
admitSecondLaw-from-physical proc t deq h =
  subst (λ d → HistoryTransition.entropy-drop t ℚ.≤ d) (sym deq) h

admitSecondLaw-from-bridge :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.bridge-proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.bridge-transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.bridge-transition b)
admitSecondLaw-from-bridge b h =
  admitSecondLaw-from-physical
    (PhysicalHistoryBridge.bridge-proc b)
    (PhysicalHistoryBridge.bridge-transition b)
    (PhysicalHistoryBridge.bridge-dissipated-eq b)
    h

appendOnlyAdmitted-from-physical :
  (b : PhysicalHistoryBridge) →
  appendOnlyCommitMove (PhysicalHistoryBridge.bridge-transition b) →
  PhysicalSecondLaw (PhysicalHistoryBridge.bridge-proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.bridge-transition b)) →
  appendOnlyAdmittedTransition (PhysicalHistoryBridge.bridge-transition b)
appendOnlyAdmitted-from-physical b hAppend hSL =
  admitSecondLaw-from-bridge b hSL , hAppend

silentRewriteRefused-from-physical :
  (b : PhysicalHistoryBridge) →
  appendOnlyCommitMove (PhysicalHistoryBridge.bridge-transition b) →
  PhysicalSecondLaw (PhysicalHistoryBridge.bridge-proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.bridge-transition b)) →
  ¬ silentRewrite (PhysicalHistoryBridge.bridge-transition b)
silentRewriteRefused-from-physical b hAppend _ =
  silentRewriteRefused (PhysicalHistoryBridge.bridge-transition b) hAppend

------------------------------------------------------------------------
-- SECTION 4: Honesty flags + catalog witnesses
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

append-only-production-wired : Bool
append-only-production-wired = false

append-only-production-wired-false :
  append-only-production-wired ≡ false
append-only-production-wired-false = refl

append-only-module-witness : ⊤
append-only-module-witness = tt

appendOnly-silentRewrite-refused :
  ∀ (t : HistoryTransition) → appendOnlyInvariant t → ¬ silentRewrite t
appendOnly-silentRewrite-refused t = silentRewriteRefused t
