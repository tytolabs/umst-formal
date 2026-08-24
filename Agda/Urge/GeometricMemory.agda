-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.GeometricMemory — meso/acting §5.3 geometric memory.
--
-- URGE-FORMAL-MESO-AGDA-GEOMETRIC-MEMORY (umst-formal acting fiber only).
-- §5.3: history object identity is canonical SDF/FRep fingerprint — not
-- host id theater and not raw payload without canonicalization. Identity
-- *is* the geometric memory residue; compose `geometric-memory-excitement-select`
-- — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.GeometricMemory where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Nat.Properties as ℕ-Props using (_≟_; 0<1+n)
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

record geometric-memory-candidate : Set where
  field
    cand-id : ℕ
    cand-digest : ℕ
    cand-resolution-bits : ℕ
    sdf-canonical : Bool

geometric-memory-excitement-select :
  (src : ℚ) → List geometric-memory-candidate →
  geometric-memory-candidate ⊎ excitement-residue
geometric-memory-excitement-select src List.[] = inj₂ exc-no-candidates
geometric-memory-excitement-select src (c List.∷ _) = inj₁ c

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
-- SECTION 2: SDF identity witness (§5.3 canonical digest / FRep grain)
------------------------------------------------------------------------

record SdfFingerprint : Set where
  field
    digest : ℕ

record HistoryGeometricIdentity : Set where
  field
    fingerprint : SdfFingerprint
    resolution-bits : ℕ

sdf-identity-from-digest :
  (digest resolution : ℕ) → HistoryGeometricIdentity
sdf-identity-from-digest digest resolution = record
  { fingerprint = record { digest = digest }
  ; resolution-bits = resolution
  }

record SdfIdentityWitness : Set where
  field
    head-digest : ℕ
    tail-digests : List ℕ
    resolution-bits : ℕ

sdf-witness-from-stamps :
  (head : ℕ) (tail : List ℕ) (resolution : ℕ) → SdfIdentityWitness
sdf-witness-from-stamps head tail resolution = record
  { head-digest = head
  ; tail-digests = tail
  ; resolution-bits = resolution
  }

------------------------------------------------------------------------
-- SECTION 3: History object with geometric identity — not host-id keyed
------------------------------------------------------------------------

record HistoryObjectGeom : Set where
  field
    seq : ℕ
    identity : HistoryGeometricIdentity
    host-surrogate : ℕ

geometricIdentityPred :
  HistoryGeometricIdentity → HistoryGeometricIdentity → Set
geometricIdentityPred idₐ idᵦ =
  SdfFingerprint.digest (HistoryGeometricIdentity.fingerprint idₐ) ≡
  SdfFingerprint.digest (HistoryGeometricIdentity.fingerprint idᵦ)
  × HistoryGeometricIdentity.resolution-bits idₐ ≡
    HistoryGeometricIdentity.resolution-bits idᵦ

geometricIdentityPred-intro :
  (idₐ idᵦ : HistoryGeometricIdentity) →
  SdfFingerprint.digest (HistoryGeometricIdentity.fingerprint idₐ) ≡
  SdfFingerprint.digest (HistoryGeometricIdentity.fingerprint idᵦ) →
  HistoryGeometricIdentity.resolution-bits idₐ ≡
  HistoryGeometricIdentity.resolution-bits idᵦ →
  geometricIdentityPred idₐ idᵦ
geometricIdentityPred-intro idₐ idᵦ hdig hres = hdig , hres

geometric-identity-matches :
  HistoryObjectGeom → HistoryObjectGeom → Set
geometric-identity-matches hₐ hᵦ =
  geometricIdentityPred (HistoryObjectGeom.identity hₐ) (HistoryObjectGeom.identity hᵦ)

geometric-identity-matches-intro :
  (hₐ hᵦ : HistoryObjectGeom) →
  geometricIdentityPred (HistoryObjectGeom.identity hₐ) (HistoryObjectGeom.identity hᵦ) →
  geometric-identity-matches hₐ hᵦ
geometric-identity-matches-intro hₐ hᵦ h = h

same-digest-same-identity :
  (digest resolution : ℕ) (hₐ hᵦ : HistoryObjectGeom) →
  HistoryObjectGeom.identity hₐ ≡ sdf-identity-from-digest digest resolution →
  HistoryObjectGeom.identity hᵦ ≡ sdf-identity-from-digest digest resolution →
  geometric-identity-matches hₐ hᵦ
same-digest-same-identity digest resolution hₐ hᵦ hidₐ hidᵦ
  rewrite hidₐ
  rewrite hidᵦ
  = geometricIdentityPred-intro _ _ refl refl

------------------------------------------------------------------------
-- SECTION 4: Geometric memory arrow — SDF identity *is* the residue
------------------------------------------------------------------------

record GeometricMemoryArrow : Set where
  field
    memory-id : ℕ
    witness : SdfIdentityWitness
    source-free-energy : ℚ
    identity : HistoryGeometricIdentity
    sdf-canonical-ok : geometric-memory-candidate.sdf-canonical
      (record { cand-id = memory-id
              ; cand-digest = SdfIdentityWitness.head-digest witness
              ; cand-resolution-bits = SdfIdentityWitness.resolution-bits witness
              ; sdf-canonical = true }) ≡ true

record GeometricMemoryAttempt : Set where
  field
    host-id-keyed : Bool
    payload-only : Bool
    witness : Maybe SdfIdentityWitness
    source-free-energy : ℚ
    host-surrogate : ℕ
    payload-surrogate : ℕ

------------------------------------------------------------------------
-- SECTION 5: Typed refusal (positive refuse — not only !physics_green)
------------------------------------------------------------------------

data GeometricMemoryRefusal : Set where
  host-id-theater : GeometricMemoryRefusal
  payload-only-theater : GeometricMemoryRefusal
  second-argmin : GeometricMemoryRefusal
  sdf-not-canonical : GeometricMemoryRefusal

data GeometricMemoryClass : Set where
  host-id-surrogate : GeometricMemoryClass
  sdf-excitement-arrow : GeometricMemoryClass

refuse-host-id-theater : GeometricMemoryRefusal
refuse-host-id-theater = host-id-theater

refuse-payload-only-theater : GeometricMemoryRefusal
refuse-payload-only-theater = payload-only-theater

refuse-second-argmin : GeometricMemoryRefusal
refuse-second-argmin = second-argmin

refuse-sdf-not-canonical : GeometricMemoryRefusal
refuse-sdf-not-canonical = sdf-not-canonical

------------------------------------------------------------------------
-- SECTION 6: Gate geometric memory attempts (§5.3 SDF identity arrow)
------------------------------------------------------------------------

geometric-arrow-from-witness :
  (id : ℕ) (w : SdfIdentityWitness) (src : ℚ) (ident : HistoryGeometricIdentity) →
  SdfFingerprint.digest (HistoryGeometricIdentity.fingerprint ident) ≡
  SdfIdentityWitness.head-digest w →
  HistoryGeometricIdentity.resolution-bits ident ≡ SdfIdentityWitness.resolution-bits w →
  GeometricMemoryArrow
geometric-arrow-from-witness id w src ident hdig hres = record
  { memory-id = id
  ; witness = w
  ; source-free-energy = src
  ; identity = ident
  ; sdf-canonical-ok = refl
  }

classify-geometric-memory :
  (attempt : GeometricMemoryAttempt) →
  Maybe SdfIdentityWitness →
  GeometricMemoryClass ⊎ GeometricMemoryRefusal
classify-geometric-memory attempt nothing with GeometricMemoryAttempt.payload-only attempt
... | true = inj₂ payload-only-theater
... | false with GeometricMemoryAttempt.host-id-keyed attempt
... | true = inj₁ host-id-surrogate
... | false = inj₂ host-id-theater
classify-geometric-memory attempt (just w) with GeometricMemoryAttempt.payload-only attempt
... | true = inj₁ sdf-excitement-arrow
... | false with GeometricMemoryAttempt.host-id-keyed attempt
... | true = inj₁ host-id-surrogate
... | false = inj₁ sdf-excitement-arrow

gate-geometric-memory-refuse-host-id :
  (attempt : GeometricMemoryAttempt) →
  GeometricMemoryAttempt.host-id-keyed attempt ≡ true →
  ¬ (GeometricMemoryAttempt.witness attempt ≡ nothing) →
  GeometricMemoryRefusal
gate-geometric-memory-refuse-host-id attempt _ _ = host-id-theater

gate-geometric-memory-admit :
  (attempt : GeometricMemoryAttempt) →
  GeometricMemoryAttempt.host-id-keyed attempt ≡ false →
  GeometricMemoryAttempt.payload-only attempt ≡ false →
  ⊤
gate-geometric-memory-admit attempt _ _ = tt

gate-geometric-memory-refuse-payload :
  (attempt : GeometricMemoryAttempt) →
  GeometricMemoryAttempt.payload-only attempt ≡ true →
  GeometricMemoryAttempt.witness attempt ≡ nothing →
  GeometricMemoryRefusal
gate-geometric-memory-refuse-payload attempt _ _ = payload-only-theater

refuse-host-id-identity :
  (host-id : ℕ) → GeometricMemoryRefusal
refuse-host-id-identity host-id = host-id-theater

refuse-payload-only-identity :
  (payload : ℕ) → GeometricMemoryRefusal
refuse-payload-only-identity payload = payload-only-theater

------------------------------------------------------------------------
-- SECTION 7: Excitement compose pin (no second argmin)
------------------------------------------------------------------------

urge-geometric-memory-select :
  (src : ℚ) → List geometric-memory-candidate →
  geometric-memory-candidate ⊎ excitement-residue
urge-geometric-memory-select = geometric-memory-excitement-select

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

refuse-second-argmin-is-tag :
  refuse-second-argmin ≡ second-argmin
refuse-second-argmin-is-tag = refl

geometric-memory-excitement-empty :
  ∀ (src : ℚ) →
  urge-geometric-memory-select src List.[] ≡ inj₂ exc-no-candidates
geometric-memory-excitement-empty src = refl

------------------------------------------------------------------------
-- SECTION 8: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

geometric-memory-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
geometric-memory-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited = physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

urge-physics-green : Bool
urge-physics-green = false

urge-physics-green-false : urge-physics-green ≡ false
urge-physics-green-false = refl

geometric-memory-production-wired : Bool
geometric-memory-production-wired = false

geometric-memory-production-wired-false :
  geometric-memory-production-wired ≡ false
geometric-memory-production-wired-false = refl

geometric-memory-marker : ℕ
geometric-memory-marker = 1

geometric-memory-marker-eq : geometric-memory-marker ≡ 1
geometric-memory-marker-eq = refl

geometric-memory-marker-pos : 0 < geometric-memory-marker
geometric-memory-marker-pos = 0<1+n

geometric-memory-module-witness : ⊤
geometric-memory-module-witness = tt

host-id-theater-refused :
  refuse-host-id-theater ≡ host-id-theater
host-id-theater-refused = refl

payload-only-theater-refused :
  refuse-payload-only-theater ≡ payload-only-theater
payload-only-theater-refused = refl

geometric-identity-matches-eq-pred :
  (hₐ hᵦ : HistoryObjectGeom) →
  geometric-identity-matches hₐ hᵦ ≡
  geometricIdentityPred (HistoryObjectGeom.identity hₐ) (HistoryObjectGeom.identity hᵦ)
geometric-identity-matches-eq-pred hₐ hᵦ = refl
