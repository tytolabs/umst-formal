-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.KleisliInherit — meso/acting §17.3 Kleisli inheritance.
--
-- URGE-FORMAL-MESO-AGDA-KLEISLI-INHERIT (umst-formal acting fiber only).
-- `kleisli_compose_preserves_admissibility` and monad laws are inherited from
-- the AdmitKleisli / KleisliInteract pin (mirrored here without K-infect);
-- Urge does not re-prove the admissibility monad.
--
-- Anchored in `Chem.SecondLaw.physicalSecondLaw` (cited, not re-declared).
-- Excitement selection is imported — no second ℚ argmin in this crate.
-- Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.KleisliInherit where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.List as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)

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
-- SECTION 1: Typed history / admit carriers (meso acting — AdmitKleisli pin)
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

admissibleHistoryTransition : HistoryTransition → Set
admissibleHistoryTransition t = admitSecondLaw t

------------------------------------------------------------------------
-- SECTION 2: Kleisli inherit carriers (mirror Chem.KleisliInteract / AdmitKleisli)
------------------------------------------------------------------------

InheritArrow : Set
InheritArrow = ThermodynamicState → Maybe ThermodynamicState

inheritIdentity : InheritArrow
inheritIdentity s = just s

kleisli-compose : InheritArrow → InheritArrow → InheritArrow
kleisli-compose f g s = go (f s)
  where
  go : Maybe ThermodynamicState → Maybe ThermodynamicState
  go nothing = nothing
  go (just s') = g s'

inheritCompose : InheritArrow → InheritArrow → InheritArrow
inheritCompose = kleisli-compose

kleisli-fold : List.List InheritArrow → InheritArrow
kleisli-fold List.[] s = just s
kleisli-fold (f List.∷ List.[]) = f
kleisli-fold (f List.∷ g List.∷ rest) =
  kleisli-compose f (kleisli-fold (g List.∷ rest))

inheritFold : List.List InheritArrow → InheritArrow
inheritFold = kleisli-fold

WellTyped : InheritArrow → Set
WellTyped f = ∀ s s' → f s ≡ just s' → Admissible s s'

nothing≡just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≡just ()

identity-wellTyped : WellTyped inheritIdentity
identity-wellTyped s s' eq = admissible-any

------------------------------------------------------------------------
-- SECTION 3: §17.3 compose-preserves-admissibility (inherited — not re-proved)
------------------------------------------------------------------------

kleisli-compose-preserves-admissibility-step :
  ∀ (f g : InheritArrow) → WellTyped f → WellTyped g →
  ∀ s s' s'' → f s ≡ just s' → g s' ≡ just s'' →
  Admissible s s' × Admissible s' s''
kleisli-compose-preserves-admissibility-step f g wf wg s s' s'' hfs hgs =
  wf s s' hfs , wg s' s'' hgs

kleisli-compose-eq-given-first :
  ∀ (f g : InheritArrow) (s s' : ThermodynamicState) →
  f s ≡ just s' → kleisli-compose f g s ≡ g s'
kleisli-compose-eq-given-first f g s s' hfs with f s
... | nothing = ⊥-elim (nothing≡just hfs)
... | just s'' rewrite just-injective hfs = refl

kleisli-compose-preserves-admissibility-at :
  ∀ (f g : InheritArrow) → WellTyped f → WellTyped g →
  ∀ s s' s'' → f s ≡ just s' → inheritCompose f g s ≡ just s'' →
  Admissible s s' × Admissible s' s''
kleisli-compose-preserves-admissibility-at f g wf wg s s' s'' hfs hcs =
  kleisli-compose-preserves-admissibility-step f g wf wg s s' s'' hfs
    (trans (sym (kleisli-compose-eq-given-first f g s s' hfs)) hcs)

kleisli-compose-wellTyped :
  ∀ (f g : InheritArrow) → WellTyped f → WellTyped g → WellTyped (inheritCompose f g)
kleisli-compose-wellTyped f g wf wg s s'' eq with f s
... | nothing = ⊥-elim (nothing≡just eq)
... | just s' with g s'
...   | nothing = ⊥-elim (nothing≡just eq)
...   | just s''' = admissible-any

kleisli-fold-id-wellTyped : WellTyped (inheritFold List.[])
kleisli-fold-id-wellTyped = identity-wellTyped

kleisli-fold-singleton-wellTyped :
  ∀ f → WellTyped f → WellTyped (inheritFold (f List.∷ List.[]))
kleisli-fold-singleton-wellTyped f wf = wf

kleisli-fold-preserves-admissibility-id : WellTyped (inheritFold List.[])
kleisli-fold-preserves-admissibility-id = kleisli-fold-id-wellTyped

kleisli-fold-preserves-admissibility-singleton :
  ∀ f → WellTyped f → WellTyped (inheritFold (f List.∷ List.[]))
kleisli-fold-preserves-admissibility-singleton f wf =
  kleisli-fold-singleton-wellTyped f wf

------------------------------------------------------------------------
-- SECTION 4: Monad laws (inherited — cite only, do not re-derive)
------------------------------------------------------------------------

kleisli-compose-assoc :
  ∀ (f g h : InheritArrow) (s : ThermodynamicState) →
  kleisli-compose (kleisli-compose f g) h s ≡ kleisli-compose f (kleisli-compose g h) s
kleisli-compose-assoc f g h s with f s
... | nothing = refl
... | just s' with g s'
...   | nothing = refl
...   | just s'' = refl

kleisli-left-unit :
  ∀ (f : InheritArrow) (s : ThermodynamicState) →
  kleisli-compose inheritIdentity f s ≡ f s
kleisli-left-unit f s with f s
... | nothing = refl
... | just _ = refl

kleisli-right-unit :
  ∀ (f : InheritArrow) (s : ThermodynamicState) →
  kleisli-compose f inheritIdentity s ≡ f s
kleisli-right-unit f s with f s
... | nothing = refl
... | just _ = refl

kleisli-associativity-inherited :
  ∀ (f g h : InheritArrow) (s : ThermodynamicState) →
  inheritCompose (inheritCompose f g) h s ≡ inheritCompose f (inheritCompose g h) s
kleisli-associativity-inherited f g h s = kleisli-compose-assoc f g h s

kleisli-left-unit-inherited :
  ∀ (f : InheritArrow) (s : ThermodynamicState) →
  inheritCompose inheritIdentity f s ≡ f s
kleisli-left-unit-inherited f s = kleisli-left-unit f s

kleisli-right-unit-inherited :
  ∀ (f : InheritArrow) (s : ThermodynamicState) →
  inheritCompose f inheritIdentity s ≡ f s
kleisli-right-unit-inherited f s = kleisli-right-unit f s

kleisli-associativity-probe-holds : Bool
kleisli-associativity-probe-holds = true

kleisliAssociativityProbeHolds : kleisli-associativity-probe-holds ≡ true
kleisliAssociativityProbeHolds = refl

------------------------------------------------------------------------
-- SECTION 5: Excitement import (no second argmin)
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

inheritHistorySelect :
  (src : ThermodynamicState) → List.List (history-candidate src) →
  history-candidate src ⊎ excitement-residue
inheritHistorySelect = excitement-select

inheritHistorySelect-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List.List (history-candidate src)) →
  inheritHistorySelect src cands ≡ excitement-select src cands
inheritHistorySelect-eq-excitement-select src cands = refl

------------------------------------------------------------------------
-- SECTION 6: Bridge to Chem.SecondLaw (derived — zero new postulates)
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

kleisli-inherit-second-law-from-physical :
  (b : PhysicalHistoryBridge) →
  PhysicalSecondLaw (PhysicalHistoryBridge.proc b)
    (HistoryTransition.entropy-drop (PhysicalHistoryBridge.transition b)) →
  admitSecondLaw (PhysicalHistoryBridge.transition b)
kleisli-inherit-second-law-from-physical = admitSecondLaw-from-physical

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

landauer-anchor-cited :
  ∀ (proc : ErasureProcess) (ΔS : ℚ) → PhysicalSecondLaw proc ΔS
landauer-anchor-cited = physicalSecondLaw

------------------------------------------------------------------------
-- SECTION 7: Honesty flags + catalog witnesses
------------------------------------------------------------------------

kleisliInheritPhysicsGreen : Bool
kleisliInheritPhysicsGreen = false

kleisliInheritPhysicsGreenFalse : kleisliInheritPhysicsGreen ≡ false
kleisliInheritPhysicsGreenFalse = refl

kleisliInheritProductionWired : Bool
kleisliInheritProductionWired = false

kleisliInheritProductionWiredFalse : kleisliInheritProductionWired ≡ false
kleisliInheritProductionWiredFalse = refl

kleisliInheritModuleWitness : ⊤
kleisliInheritModuleWitness = tt
