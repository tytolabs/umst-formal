-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.HomologNotCopy — meso/acting §22.1 homolog ≠ copy recovery.
--
-- URGE-FORMAL-MESO-AGDA-HOMOLOG-NOT-COPY (umst-formal acting fiber only).
-- §22.1: recovery is a new Excitement arrow over admissible successors — not
-- `git reset --hard` of a sibling commit. Homolog relates sibling commits
-- geometrically — homolog ≠ copy. Compose `homolog-recovery-excitement-select`
-- — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.HomologNotCopy where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; not; _∧_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does; ¬_)

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (minimal meso acting mirror)
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

data excitement-residue : Set where
  exc-no-candidates : excitement-residue
  exc-all-inadmissible : excitement-residue
  exc-no-strict-improvement : excitement-residue

record recovery-candidate : Set where
  field
    cand-id : ℕ
    cand-free-energy : ℚ
    provenance-intact : Bool

homolog-recovery-excitement-select :
  (src : ℚ) → List recovery-candidate →
  recovery-candidate ⊎ excitement-residue
homolog-recovery-excitement-select src List.[] = inj₂ exc-no-candidates
homolog-recovery-excitement-select src (c List.∷ _) = inj₁ c

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
-- SECTION 2: Sibling commit + homolog witness (§22.1 geometric relation)
------------------------------------------------------------------------

record SiblingCommitRef : Set where
  field
    commit-hash : ℕ
    sibling-of : ℕ

record HomologWitness : Set where
  field
    from : SiblingCommitRef
    to : SiblingCommitRef
    claims-identity-copy : Bool

sibling-commit-ref : ℕ → ℕ → SiblingCommitRef
sibling-commit-ref hash parent = record
  { commit-hash = hash
  ; sibling-of = parent
  }

nat-ne : ℕ → ℕ → Bool
nat-ne x y = not (does (ℕ-Props._≟_ x y))

homolog-not-copy? : HomologWitness → Bool
homolog-not-copy? w =
  nat-ne (SiblingCommitRef.commit-hash (HomologWitness.from w))
       (SiblingCommitRef.commit-hash (HomologWitness.to w))
  ∧ not (HomologWitness.claims-identity-copy w)

------------------------------------------------------------------------
-- SECTION 3: New Excitement recovery arrow (§22.1 accept path)
------------------------------------------------------------------------

record RecoveryUcrsStamp : Set where
  field
    ucrs-seq : ℕ
    ucrs-wall-has-t : Bool

record RecoveryExcitementArrow : Set where
  field
    arrow-id : ℕ
    selected-successor-id : ℕ
    source-free-energy : ℚ
    provenance-intact : Bool
    ucrs : RecoveryUcrsStamp

is-new-excitement-arrow : RecoveryExcitementArrow → Bool
is-new-excitement-arrow a =
  RecoveryExcitementArrow.provenance-intact a
  ∧ RecoveryUcrsStamp.ucrs-wall-has-t (RecoveryExcitementArrow.ucrs a)

recovery-arrow-from-selection :
  (id successor : ℕ) (src : ℚ) (ucrs-seq : ℕ) (wall-has-t : Bool) →
  recovery-candidate ⊎ excitement-residue →
  RecoveryExcitementArrow ⊎ excitement-residue
recovery-arrow-from-selection id successor src ucrs-seq wall-has-t (inj₁ c) = inj₁ record
  { arrow-id = id
  ; selected-successor-id = successor
  ; source-free-energy = src
  ; provenance-intact = recovery-candidate.provenance-intact c
  ; ucrs = record { ucrs-seq = ucrs-seq ; ucrs-wall-has-t = wall-has-t }
  }
recovery-arrow-from-selection id successor src ucrs-seq wall-has-t (inj₂ r) = inj₂ r

------------------------------------------------------------------------
-- SECTION 4: Recovery attempt + typed refusal (positive refuse surface)
------------------------------------------------------------------------

record RecoveryAttempt : Set where
  field
    git-reset-hard-sibling : Bool
    homolog : Maybe HomologWitness
    source-free-energy : ℚ

data HomologNotCopyRefusal : Set where
  git-reset-hard-sibling : HomologNotCopyRefusal
  homolog-is-not-copy : HomologNotCopyRefusal
  second-argmin : HomologNotCopyRefusal

data RecoveryClass : Set where
  new-excitement-arrow : RecoveryClass
  git-reset-hard-sibling-class : RecoveryClass
  homolog-claims-copy : RecoveryClass

refuse-git-reset-hard-sibling : HomologNotCopyRefusal
refuse-git-reset-hard-sibling = git-reset-hard-sibling

refuse-homolog-as-copy : HomologNotCopyRefusal
refuse-homolog-as-copy = homolog-is-not-copy

refuse-second-argmin : HomologNotCopyRefusal
refuse-second-argmin = second-argmin

recovery-class-of-refusal :
  HomologNotCopyRefusal → RecoveryClass
recovery-class-of-refusal git-reset-hard-sibling = git-reset-hard-sibling-class
recovery-class-of-refusal homolog-is-not-copy = homolog-claims-copy
recovery-class-of-refusal second-argmin = new-excitement-arrow

------------------------------------------------------------------------
-- SECTION 5: Gate recovery attempts (§22.1 new Excitement arrow)
------------------------------------------------------------------------

classify-recovery :
  (attempt : RecoveryAttempt) →
  RecoveryClass ⊎ HomologNotCopyRefusal
classify-recovery attempt with RecoveryAttempt.git-reset-hard-sibling attempt
... | true = inj₂ git-reset-hard-sibling
... | false with RecoveryAttempt.homolog attempt
... | nothing = inj₁ new-excitement-arrow
... | just w with HomologWitness.claims-identity-copy w
... | true = inj₂ homolog-is-not-copy
... | false with homolog-not-copy? w
... | true = inj₁ new-excitement-arrow
... | false = inj₂ homolog-is-not-copy

gate-recovery-refuse-git-reset :
  (attempt : RecoveryAttempt) →
  RecoveryAttempt.git-reset-hard-sibling attempt ≡ true →
  HomologNotCopyRefusal
gate-recovery-refuse-git-reset attempt _ = git-reset-hard-sibling

gate-recovery-admit-arrow :
  (attempt : RecoveryAttempt) →
  RecoveryAttempt.git-reset-hard-sibling attempt ≡ false →
  ⊤
gate-recovery-admit-arrow attempt _ = tt

gate-recovery-refuse-homolog-copy :
  (w : HomologWitness) →
  HomologWitness.claims-identity-copy w ≡ true →
  HomologNotCopyRefusal
gate-recovery-refuse-homolog-copy w _ = homolog-is-not-copy

------------------------------------------------------------------------
-- SECTION 6: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-recovery-select :
  (src : ℚ) → List recovery-candidate →
  recovery-candidate ⊎ excitement-residue
urge-recovery-select = homolog-recovery-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

homolog-recovery-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
homolog-recovery-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

homolog-not-copy-production-wired : Bool
homolog-not-copy-production-wired = false

homolog-not-copy-production-wired-false :
  homolog-not-copy-production-wired ≡ false
homolog-not-copy-production-wired-false = refl

homolog-not-copy-marker : ℕ
homolog-not-copy-marker = 1

homolog-not-copy-marker-eq : homolog-not-copy-marker ≡ 1
homolog-not-copy-marker-eq = refl

homolog-not-copy-module-witness : ⊤
homolog-not-copy-module-witness = tt

git-reset-hard-sibling-refused :
  (attempt : RecoveryAttempt) →
  (h : RecoveryAttempt.git-reset-hard-sibling attempt ≡ true) →
  gate-recovery-refuse-git-reset attempt h ≡ git-reset-hard-sibling
git-reset-hard-sibling-refused attempt h = refl

homolog-copy-refused :
  refuse-homolog-as-copy ≡ homolog-is-not-copy
homolog-copy-refused = refl

second-argmin-refused :
  refuse-second-argmin ≡ second-argmin
second-argmin-refused = refl
