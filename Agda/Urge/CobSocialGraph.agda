-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Urge.CobSocialGraph — meso/acting §3 COB typed social graph.
--
-- URGE-FORMAL-MESO-AGDA-COB-SOCIAL-GRAPH (umst-formal acting fiber only).
-- §3 COB typed social graph (patch/issue/review/identity). Radicle-style
-- overlay with typed nodes and edges. Positive refuse via untyped-edge and
-- git-hash-only identity — not silent accept. Compose
-- `cob-social-excitement-select` — no second ℚ argmin.
--
-- Sole physics postulate remains `Chem.SecondLaw.physicalSecondLaw` (cited,
-- not restated). Zero extra postulates beyond Landauer.
--
-- physics_green: false — knowing fiber (EpistemicMI) lives on umst-formal-double-slit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --exact-split #-}

module Urge.CobSocialGraph where

open import Chem.SecondLaw

open import Data.Bool using (Bool; false; true; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.List as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (does; yes; no)

------------------------------------------------------------------------
-- SECTION 0: Minimal thermodynamic head + excitement carriers
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

urge-recovery-select :
  (src : ThermodynamicState) (successors : List.List (history-candidate src)) →
  history-candidate src ⊎ excitement-residue
urge-recovery-select src successors = excitement-select src successors

------------------------------------------------------------------------
-- SECTION 1: Typed history carriers (minimal meso acting mirror)
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
-- SECTION 2: History carrier product (RepositoryIdentity pin)
------------------------------------------------------------------------

data StampTier : Set where
  stamp-wall-only stamp-wall-plus-seq : StampTier

record UcrsStamp : Set where
  field
    observed-at-wall : ℕ
    ucrs-seq : Maybe ℕ
    tier : StampTier

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

socialNodeKindTag : SocialNodeKind → ℕ
socialNodeKindTag social-patch = zero
socialNodeKindTag social-issue = suc zero
socialNodeKindTag social-review = suc (suc zero)
socialNodeKindTag social-identity = suc (suc (suc zero))

socialNodeKindEq : SocialNodeKind → SocialNodeKind → Bool
socialNodeKindEq k1 k2 = does (socialNodeKindTag k1 ≟ socialNodeKindTag k2)

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
-- SECTION 4: Repository identity + positive refuse (§3 COB)
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

data cob-social-refusal : Set where
  csr-untyped-social-edge : ℕ → ℕ → cob-social-refusal
  csr-node-not-found : ℕ → cob-social-refusal
  csr-git-hash-only-identity : String → cob-social-refusal
  csr-second-argmin-refused : cob-social-refusal

data cob-social-link-verdict : Set where
  cslv-accept cslv-refuse-untyped-edge cslv-refuse-missing-node : cob-social-link-verdict

evaluate-social-link :
  TypedSocialGraph → ℕ → ℕ → SocialNodeKind → SocialNodeKind →
  cob-social-link-verdict
evaluate-social-link g from to from-kind to-kind with
  proj₁ (linkTypedEdge g from to from-kind to-kind)
... | cob-link-ok = cslv-accept
... | cob-untyped-social-edge-refused = cslv-refuse-untyped-edge
... | cob-node-not-found = cslv-refuse-missing-node

refuse-git-hash-only : String → cob-social-refusal
refuse-git-hash-only rid = csr-git-hash-only-identity rid

refuse-second-argmin : cob-social-refusal
refuse-second-argmin = csr-second-argmin-refused

refuse-git-hash-only-identity-positive :
  ∀ rid → refuseGitHashOnlyIdentity rid ≡ cob-git-hash-only-identity-refused rid
refuse-git-hash-only-identity-positive rid = refl

refuse-git-hash-only-eq-csr :
  ∀ rid → refuse-git-hash-only rid ≡ csr-git-hash-only-identity rid
refuse-git-hash-only-eq-csr rid = refl

refuse-second-argmin-positive :
  refuse-second-argmin ≡ csr-second-argmin-refused
refuse-second-argmin-positive = refl

------------------------------------------------------------------------
-- SECTION 5: COB social graph composes Excitement (no second argmin)
------------------------------------------------------------------------

data cob-excitement-compose-pin : Set where
  csg-import-select-excitement csg-second-argmin-refused : cob-excitement-compose-pin

record cob-social-recovery-ctx (src : ThermodynamicState) : Set where
  field
    cob-social-successors : List.List (history-candidate src)

cob-social-select :
  (src : ThermodynamicState) (ctx : cob-social-recovery-ctx src) →
  history-candidate src ⊎ excitement-residue
cob-social-select src ctx =
  urge-recovery-select src (cob-social-recovery-ctx.cob-social-successors ctx)

cob-social-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (ctx : cob-social-recovery-ctx src) →
  cob-social-select src ctx ≡
  excitement-select src (cob-social-recovery-ctx.cob-social-successors ctx)
cob-social-select-eq-excitement-select src ctx = refl

cob-social-select-eq-urge-recovery-select :
  ∀ (src : ThermodynamicState) (ctx : cob-social-recovery-ctx src) →
  cob-social-select src ctx ≡
  urge-recovery-select src (cob-social-recovery-ctx.cob-social-successors ctx)
cob-social-select-eq-urge-recovery-select src ctx = refl

cob-social-no-local-argmin :
  ∀ (src : ThermodynamicState) (ctx : cob-social-recovery-ctx src) →
  cob-social-select src ctx ≡
  excitement-select src (cob-social-recovery-ctx.cob-social-successors ctx)
cob-social-no-local-argmin src ctx =
  cob-social-select-eq-excitement-select src ctx

cob-social-excitement-select :
  (src : ThermodynamicState) (cands : List.List (history-candidate src)) →
  cob-excitement-compose-pin →
  history-candidate src ⊎ excitement-residue
cob-social-excitement-select src cands csg-import-select-excitement =
  excitement-select src cands
cob-social-excitement-select src cands csg-second-argmin-refused =
  inj₂ exc-all-inadmissible

cob-social-excitement-select-eq-excitement-select :
  ∀ (src : ThermodynamicState) (cands : List.List (history-candidate src)) →
  cob-social-excitement-select src cands csg-import-select-excitement ≡
  excitement-select src cands
cob-social-excitement-select-eq-excitement-select src cands = refl

cob-social-excitement-select-refuses-second-argmin :
  ∀ (src : ThermodynamicState) (cands : List.List (history-candidate src)) →
  cob-social-excitement-select src cands csg-second-argmin-refused ≡
  inj₂ exc-all-inadmissible
cob-social-excitement-select-refuses-second-argmin src cands = refl

cob-social-select-empty :
  ∀ (src : ThermodynamicState) (ctx : cob-social-recovery-ctx src) →
  cob-social-recovery-ctx.cob-social-successors ctx ≡ List.[] →
  cob-social-select src ctx ≡ inj₂ exc-no-candidates
cob-social-select-empty src ctx Hnil rewrite Hnil = refl

excitement-compose-pin : ℕ
excitement-compose-pin = 0

excitement-compose-pin-marker : excitement-compose-pin ≡ 0
excitement-compose-pin-marker = refl

------------------------------------------------------------------------
-- SECTION 6: §3 fixtures + witness theorems
------------------------------------------------------------------------

cob-fixture-graph : TypedSocialGraph
cob-fixture-graph =
  let patch-node , g1 = addSocialNode emptySocialGraph social-patch "patch-admissible"
      issue-node , g2 = addSocialNode g1 social-issue "issue-thread"
      review-node , g3 = addSocialNode g2 social-review "review-verdict"
      _ , g4 = addSocialNode g3 social-identity "did:umst:cob"
  in g4

cob-fixture-patch-id : ℕ
cob-fixture-patch-id = zero

cob-fixture-issue-id : ℕ
cob-fixture-issue-id = suc zero

cob-fixture-review-id : ℕ
cob-fixture-review-id = suc (suc zero)

cob-fixture-accept-link :
  evaluate-social-link cob-fixture-graph
    cob-fixture-patch-id cob-fixture-issue-id
    social-patch social-issue ≡ cslv-accept
cob-fixture-accept-link = refl

cob-fixture-untyped-link-refused :
  evaluate-social-link cob-fixture-graph
    cob-fixture-patch-id cob-fixture-review-id
    social-patch social-issue ≡ cslv-refuse-untyped-edge
cob-fixture-untyped-link-refused = refl

cob-fixture-missing-node-refused :
  evaluate-social-link cob-fixture-graph
    cob-fixture-patch-id 999 social-patch social-issue ≡
  cslv-refuse-missing-node
cob-fixture-missing-node-refused = refl

cob-fixture-git-hash-only-refused :
  refuse-git-hash-only "sha1:deadbeef" ≡ csr-git-hash-only-identity "sha1:deadbeef"
cob-fixture-git-hash-only-refused = refl

cob-fixture-state : ThermodynamicState
cob-fixture-state = record
  { density = 0ℚ
  ; free-energy = 0ℚ
  ; hydration = 0ℚ
  ; strength = 0ℚ
  }

cob-fixture-excitement-compose :
  cob-social-excitement-select cob-fixture-state List.[]
    csg-import-select-excitement ≡ inj₂ exc-no-candidates
cob-fixture-excitement-compose = refl

------------------------------------------------------------------------
-- SECTION 7: Landauer bridge + honesty flags (zero new postulates)
------------------------------------------------------------------------

cob-social-second-law-from-landauer :
  (proc : ErasureProcess) (ΔS : ℚ) (t : HistoryTransition) →
  HistoryTransition.entropy-drop t ≡ ΔS →
  HistoryTransition.dissipated-entropy t ≡ ErasureProcess.dissipatedEntropy proc →
  admitSecondLaw t
cob-social-second-law-from-landauer proc ΔS t hent hdiss =
  admitSecondLaw-from-landauer proc ΔS (physicalSecondLaw proc ΔS) t hent hdiss

landauer-anchor-cited :
  PhysicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ
landauer-anchor-cited =
  physicalSecondLaw (record { bath = record { temperature = 0ℚ } ; dissipatedEntropy = 0ℚ }) 0ℚ

cob-social-graph-physics-green : Bool
cob-social-graph-physics-green = false

cob-social-graph-physics-green-false :
  cob-social-graph-physics-green ≡ false
cob-social-graph-physics-green-false = refl

cob-social-graph-production-wired : Bool
cob-social-graph-production-wired = false

cob-social-graph-production-wired-false :
  cob-social-graph-production-wired ≡ false
cob-social-graph-production-wired-false = refl

cob-social-graph-non-claim : String
cob-social-graph-non-claim =
  "§3 COB typed social graph (patch/issue/review/identity); positive refuse not only !physics_green; compose excitement_select not local argmin; not physics GREEN; not production_wired"

cob-social-graph-module-witness : ⊤
cob-social-graph-module-witness = tt

cob-social-graph-no-new-axiom : ⊤
cob-social-graph-no-new-axiom = tt

cob-social-graph-marker : ℕ
cob-social-graph-marker = 1

cob-social-graph-marker-eq : cob-social-graph-marker ≡ 1
cob-social-graph-marker-eq = refl
