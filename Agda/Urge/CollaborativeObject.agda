-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CollaborativeObject — meso/acting §3 COB admit anchor.
--
-- URGE-FORMAL-MESO-AGDA-COLLABORATIVE-OBJECT (umst-formal acting fiber only).
-- CollaborativeObject (COB) = same Repository/History carrier product
-- (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness) plus typed social graph
-- overlay (patch, issue, review, identity). Excitement `select` composed —
-- no second argmin. Sole physics postulate: `Chem.SecondLaw.physicalSecondLaw`.
--
-- physics_green: false — knowing fiber cited, not restated here.
-- Zero extra postulate beyond Landauer. Unwired.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CollaborativeObject where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.List as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does; yes; no)


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
-- SECTION 1: Typed history carriers (meso acting layer — AdmitKleisli pin)
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
  exc-no-candidates exc-all-inadmissible exc-no-strict-improvement : excitement-residue

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

------------------------------------------------------------------------
-- SECTION 2: History carrier product (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness)
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

satisfiedWitness : InvariantWitness
satisfiedWitness = record { satisfied = true ; margin-h = 0ℚ }

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

carrierPopulated : HistoryCarrier → Bool
carrierPopulated c =
  does (suc zero ≤? HistorySnapshot.commit-id (umstProj c)) ∧
  does (suc zero ≤? UcrsStamp.observed-at-wall (stampProj c))

------------------------------------------------------------------------
-- SECTION 3: Typed social graph (patch / issue / review / identity)
------------------------------------------------------------------------

data SocialNodeKind : Set where
  social-patch social-issue social-review social-identity : SocialNodeKind

record SocialNode : Set where
  field
    node-id : ℕ
    kind : SocialNodeKind
    label : String

record SocialEdge : Set where
  field
    from : ℕ
    to : ℕ
    from-kind : SocialNodeKind
    to-kind : SocialNodeKind

record TypedSocialGraph : Set where
  field
    nodes : List.List SocialNode
    edges : List.List SocialEdge
    next-id : ℕ

emptySocialGraph : TypedSocialGraph
emptySocialGraph = record
  { nodes = List.[]
  ; edges = List.[]
  ; next-id = zero
  }

findSocialNode : List.List SocialNode → ℕ → Maybe SocialNode
findSocialNode List.[] _ = nothing
findSocialNode (n List.∷ rest) nid with nid ≟ SocialNode.node-id n
... | yes _ = just n
... | no _ = findSocialNode rest nid

socialNodeKindEq : SocialNodeKind → SocialNodeKind → Bool
socialNodeKindEq social-patch social-patch = true
socialNodeKindEq social-patch social-issue = false
socialNodeKindEq social-patch social-review = false
socialNodeKindEq social-patch social-identity = false
socialNodeKindEq social-issue social-patch = false
socialNodeKindEq social-issue social-issue = true
socialNodeKindEq social-issue social-review = false
socialNodeKindEq social-issue social-identity = false
socialNodeKindEq social-review social-patch = false
socialNodeKindEq social-review social-issue = false
socialNodeKindEq social-review social-review = true
socialNodeKindEq social-review social-identity = false
socialNodeKindEq social-identity social-patch = false
socialNodeKindEq social-identity social-issue = false
socialNodeKindEq social-identity social-review = false
socialNodeKindEq social-identity social-identity = true

addSocialNode :
  TypedSocialGraph → SocialNodeKind → String →
  SocialNode × TypedSocialGraph
addSocialNode g kind label =
  let nid = TypedSocialGraph.next-id g
      node = record { node-id = nid ; kind = kind ; label = label }
      g′ = record
        { nodes = node List.∷ TypedSocialGraph.nodes g
        ; edges = TypedSocialGraph.edges g
        ; next-id = suc nid
        }
  in node , g′

data cob-link-verdict : Set where
  cob-link-ok cob-untyped-social-edge-refused cob-node-not-found : cob-link-verdict

linkTypedEdge :
  TypedSocialGraph → ℕ → ℕ → SocialNodeKind → SocialNodeKind →
  cob-link-verdict × TypedSocialGraph
linkTypedEdge g from to from-kind to-kind with findSocialNode (TypedSocialGraph.nodes g) from
... | nothing = cob-node-not-found , g
... | just from-node with findSocialNode (TypedSocialGraph.nodes g) to
...   | nothing = cob-node-not-found , g
...   | just to-node =
        if socialNodeKindEq (SocialNode.kind from-node) from-kind ∧
           socialNodeKindEq (SocialNode.kind to-node) to-kind
        then cob-link-ok , record
          { nodes = TypedSocialGraph.nodes g
          ; edges = record
              { from = from
              ; to = to
              ; from-kind = from-kind
              ; to-kind = to-kind
              } List.∷ TypedSocialGraph.edges g
          ; next-id = TypedSocialGraph.next-id g
          }
        else cob-untyped-social-edge-refused , g

------------------------------------------------------------------------
-- SECTION 4: Repository identity + CollaborativeObject (§3 COB)
------------------------------------------------------------------------

record RepositoryIdentity : Set where
  field
    rid : String
    carrier : HistoryCarrier

data cob-identity-verdict : Set where
  cob-identity-ok : RepositoryIdentity → cob-identity-verdict
  cob-git-hash-only-identity-refused : String → cob-identity-verdict

refuseGitHashOnlyIdentity : String → cob-identity-verdict
refuseGitHashOnlyIdentity rid = cob-git-hash-only-identity-refused rid

repositoryIdentityWithCarrier : String → HistoryCarrier → cob-identity-verdict
repositoryIdentityWithCarrier rid c = cob-identity-ok (record { rid = rid ; carrier = c })

record CollaborativeObject : Set where
  field
    identity : RepositoryIdentity
    social : TypedSocialGraph

cobNew : RepositoryIdentity → CollaborativeObject
cobNew id = record { identity = id ; social = emptySocialGraph }

cobCarrier : CollaborativeObject → HistoryCarrier
cobCarrier cob = RepositoryIdentity.carrier (CollaborativeObject.identity cob)

------------------------------------------------------------------------
-- SECTION 5: Positive refuse witnesses
------------------------------------------------------------------------

refuse-git-hash-only-is-refused :
  ∀ rid → refuseGitHashOnlyIdentity rid ≡ cob-git-hash-only-identity-refused rid
refuse-git-hash-only-is-refused rid = refl

------------------------------------------------------------------------
-- SECTION 6: Excitement alignment (no second argmin)
------------------------------------------------------------------------

cobSelect :
  (cob : CollaborativeObject) →
  List.List (history-candidate (HistorySnapshot.head (umstProj (cobCarrier cob)))) →
  history-candidate (HistorySnapshot.head (umstProj (cobCarrier cob))) ⊎ excitement-residue
cobSelect cob cands =
  excitement-select (HistorySnapshot.head (umstProj (cobCarrier cob))) cands

cobSelect-eq-excitement-select :
  ∀ cob cands →
  cobSelect cob cands ≡
  excitement-select (HistorySnapshot.head (umstProj (cobCarrier cob))) cands
cobSelect-eq-excitement-select cob cands = refl

cob-no-local-argmin :
  ∀ cob cands →
  cobSelect cob cands ≡
  excitement-select (HistorySnapshot.head (umstProj (cobCarrier cob))) cands
cob-no-local-argmin cob cands = refl

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge (derived — zero new physics postulates)
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

physicalSecondLaw-discharge :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ entropyDecrease →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
physicalSecondLaw-discharge proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

------------------------------------------------------------------------
-- SECTION 8: Honesty flags + catalog witnesses
------------------------------------------------------------------------

collaborative-object-physics-green : Bool
collaborative-object-physics-green = false

collaborative-object-physics-green-false :
  collaborative-object-physics-green ≡ false
collaborative-object-physics-green-false = refl

collaborative-object-production-wired : Bool
collaborative-object-production-wired = false

collaborative-object-production-wired-false :
  collaborative-object-production-wired ≡ false
collaborative-object-production-wired-false = refl

collaborative-object-non-claim : String
collaborative-object-non-claim =
  "§3 COB CollaborativeObject: same carrier + typed social graph (patch, issue, review, identity); geometric identity primary; not physics GREEN; not production_wired"

collaborative-object-module-witness : ⊤
collaborative-object-module-witness = tt

collaborative-object-no-new-axiom : ⊤
collaborative-object-no-new-axiom = tt
