-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.AdmitKleisli — meso/acting Urge Kleisli admit anchor.
--
-- URGE-NS-W1-FORMAL (umst-formal acting fiber only).
-- Kleisli admit arrow on typed history transitions; inherit monad laws from
-- `Chem.KleisliInteract`; second-law accounting via `Chem.SecondLaw`
-- (`physicalSecondLaw` — sole named Landauer postulate in this fiber).
--
-- physics_green: false — knowing fiber (EpistemicMI / LandauerBound) lives on
-- `umst-formal-double-slit`; cited, not restated here.
------------------------------------------------------------------------

module Urge.AdmitKleisli where

open import Chem.SecondLaw
open import Chem.KleisliInteract
open import Concrete.Gate
open Concrete.Gate using (ThermodynamicState; Admissible)
open ThermodynamicState
open Admissible

open import Data.Bool using (Bool; false)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.List as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

------------------------------------------------------------------------
-- SECTION 1: Typed history / admit carriers (meso acting layer)
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
    dissipated-entropy : ℚ  -- W/T bundled (mirrors ErasureProcess.dissipatedEntropy)
    entropy-drop : ℚ
    gate-admissible : Admissible (HistorySnapshot.head prior) (HistorySnapshot.head post)

admitSecondLaw : HistoryTransition → Set
admitSecondLaw t =
  HistoryTransition.entropy-drop t ≤ HistoryTransition.dissipated-entropy t

admissibleHistoryTransition : HistoryTransition → Set
admissibleHistoryTransition t = admitSecondLaw t

------------------------------------------------------------------------
-- SECTION 2: Kleisli admit arrows (inherit monad laws — do not re-prove)
------------------------------------------------------------------------

AdmitArrow : Set
AdmitArrow = KleisliArrow

admit-identity : AdmitArrow
admit-identity = interact-identity

kleisliCompose : AdmitArrow → AdmitArrow → AdmitArrow
kleisliCompose = kleisli-compose

kleisliFold : List.List AdmitArrow → AdmitArrow
kleisliFold = kleisli-fold

kleisliComposeAssocAt :
  ∀ (f g h : AdmitArrow) (s : ThermodynamicState) →
  kleisliCompose (kleisliCompose f g) h s ≡ kleisliCompose f (kleisliCompose g h) s
kleisliComposeAssocAt f g h s = kleisli-compose-assoc f g h s

kleisliLeftUnitAt :
  ∀ (f : AdmitArrow) (s : ThermodynamicState) →
  kleisliCompose admit-identity f s ≡ f s
kleisliLeftUnitAt f s = kleisli-left-unit f s

kleisliRightUnitAt :
  ∀ (f : AdmitArrow) (s : ThermodynamicState) →
  kleisliCompose f admit-identity s ≡ f s
kleisliRightUnitAt f s = kleisli-right-unit f s

admit-kleisli-compose-safe :
  ∀ (f g : AdmitArrow) → WellTyped f → WellTyped g →
  ∀ s s' s'' → f s ≡ just s' → g s' ≡ just s'' →
  Admissible s s' × Admissible s' s''
admit-kleisli-compose-safe f g wf wg s s' s'' hfs hgs =
  kleisli-compose-two-step-safe f g wf wg s s' s'' hfs hgs

admit-kleisli-fold-id-wellTyped : WellTyped (kleisliFold List.[])
admit-kleisli-fold-id-wellTyped = kleisli-fold-id-wellTyped

------------------------------------------------------------------------
-- SECTION 3: Excitement composition (no local argmin re-derivation)
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

excitement-select :
  (src : ThermodynamicState) → List.List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
excitement-select src List.[] = inj₂ exc-no-candidates
excitement-select src (c List.∷ _) = inj₁ c

admit-history-select :
  (src : ThermodynamicState) → List.List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
admit-history-select = excitement-select

admit-history-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List.List (history-candidate src)) →
  admit-history-select src cands ≡ excitement-select src cands
admit-history-select-eq-excitement-select src cands = refl

------------------------------------------------------------------------
-- SECTION 4: Bridge to Chem.SecondLaw (derived — zero new postulates)
------------------------------------------------------------------------

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
admitSecondLaw-from-physical b h
  rewrite PhysicalHistoryBridge.dissipated-eq b
  = h

admitMorphism-noNewPostulate :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
admitMorphism-noNewPostulate b h = admitSecondLaw-from-physical b h

admissibleHistoryTransition-from-physical :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admissibleHistoryTransition (PhysicalHistoryBridge.transition b)
admissibleHistoryTransition-from-physical b h = admitSecondLaw-from-physical b h

admitSecondLaw-from-hypothesis :
  (t : HistoryTransition) → admitSecondLaw t → admissibleHistoryTransition t
admitSecondLaw-from-hypothesis t h = h

admitSecondLaw-from-landauer :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) →
  PhysicalSecondLaw proc entropyDecrease →
  ∀ (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
admitSecondLaw-from-landauer proc ΔS hSL t hent hdiss
  rewrite hent
  rewrite sym hdiss
  = hSL

------------------------------------------------------------------------
-- SECTION 5: Honesty flags + catalog witnesses
------------------------------------------------------------------------

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

admit-kleisli-production-wired : Bool
admit-kleisli-production-wired = false

admit-kleisli-production-wired-false :
  admit-kleisli-production-wired ≡ false
admit-kleisli-production-wired-false = refl

admit-kleisli-module-witness : ⊤
admit-kleisli-module-witness = tt
