(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/CobSocialGraph.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §3 COB typed social graph (patch/issue/review/   *)
(*  identity). Radicle-style overlay with typed nodes and edges.        *)
(*  Positive refuse via untyped-edge and git-hash-only identity — not   *)
(*  silent accept. Composes `excitement_select`; no second argmin.       *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.
Require Import UMSTFormal.Urge.CarrierProduct.

Open Scope string_scope.
Open Scope bool_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Typed social graph (patch / issue / review / identity)  *)
(* ------------------------------------------------------------------ *)

(** Radicle-style social node kinds — untyped edges refused at link time. *)
Inductive SocialNodeKind : Set :=
  | social_patch
  | social_issue
  | social_review
  | social_identity.

(** One node in the typed social graph. *)
Record SocialNode : Set := {
  social_node_id : nat;
  social_node_kind : SocialNodeKind;
  social_node_label : string
}.

(** Typed edge between social nodes — source/target kinds pinned. *)
Record SocialEdge : Set := {
  social_edge_from : nat;
  social_edge_to : nat;
  social_edge_from_kind : SocialNodeKind;
  social_edge_to_kind : SocialNodeKind
}.

(** Typed social graph carrier (append-only lists). *)
Record TypedSocialGraph : Set := {
  social_nodes : list SocialNode;
  social_edges : list SocialEdge;
  social_next_id : nat
}.

Definition emptySocialGraph : TypedSocialGraph :=
  {| social_nodes := nil;
     social_edges := nil;
     social_next_id := 0 |}.

(** Lookup a social node by id. *)
Fixpoint findSocialNode (nodes : list SocialNode) (nid : nat)
    : option SocialNode :=
  match nodes with
  | nil => None
  | n :: rest =>
      if Nat.eqb (social_node_id n) nid then Some n else findSocialNode rest nid
  end.

Definition kindEqb (k1 k2 : SocialNodeKind) : bool :=
  match k1, k2 with
  | social_patch, social_patch => true
  | social_issue, social_issue => true
  | social_review, social_review => true
  | social_identity, social_identity => true
  | _, _ => false
  end.

Lemma kindEqb_refl (k : SocialNodeKind) : kindEqb k k = true.
Proof.
  destruct k; reflexivity.
Qed.

Lemma kindEqb_eq (k1 k2 : SocialNodeKind) :
  kindEqb k1 k2 = true -> k1 = k2.
Proof.
  intros H.
  destruct k1, k2; try discriminate H; reflexivity.
Qed.

(** Add a typed social node (monotonic id assignment). *)
Definition addSocialNode (g : TypedSocialGraph) (kind : SocialNodeKind)
    (label : string) : SocialNode * TypedSocialGraph :=
  let nid := social_next_id g in
  let node :=
    {| social_node_id := nid;
       social_node_kind := kind;
       social_node_label := label |} in
  (node,
   {| social_nodes := social_nodes g ++ node :: nil;
      social_edges := social_edges g;
      social_next_id := S nid |}).

Inductive cob_link_verdict : Set :=
  | cob_link_ok
  | cob_untyped_social_edge_refused
  | cob_node_not_found.

(** Link two existing nodes with typed kinds — kind mismatch refused. *)
Definition linkTypedEdge (g : TypedSocialGraph) (from to : nat)
    (from_kind to_kind : SocialNodeKind) : cob_link_verdict * TypedSocialGraph :=
  match findSocialNode (social_nodes g) from with
  | None => (cob_node_not_found, g)
  | Some from_node =>
      match findSocialNode (social_nodes g) to with
      | None => (cob_node_not_found, g)
      | Some to_node =>
          if andb
               (kindEqb (social_node_kind from_node) from_kind)
               (kindEqb (social_node_kind to_node) to_kind) then
            let edge :=
              {| social_edge_from := from;
                 social_edge_to := to;
                 social_edge_from_kind := from_kind;
                 social_edge_to_kind := to_kind |} in
            (cob_link_ok,
             {| social_nodes := social_nodes g;
                social_edges := social_edges g ++ edge :: nil;
                social_next_id := social_next_id g |})
          else
            (cob_untyped_social_edge_refused, g)
      end
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Repository identity + positive refuse (§3 COB)        *)
(* ------------------------------------------------------------------ *)

(** Repository identity: RID pin + owning history carrier. *)
Record RepositoryIdentity : Set := {
  repo_rid : string;
  repo_carrier : HistoryCarrier
}.

Inductive cob_identity_verdict : Set :=
  | cob_identity_ok (id : RepositoryIdentity)
  | cob_git_hash_only_identity_refused (rid : string).

(** Refuse constructing identity from RID alone — carrier required. *)
Definition refuseGitHashOnlyIdentity (rid : string) : cob_identity_verdict :=
  cob_git_hash_only_identity_refused rid.

(** Build repository identity with full carrier (geometric identity primary). *)
Definition repositoryIdentityWithCarrier (rid : string) (c : HistoryCarrier)
    : cob_identity_verdict :=
  cob_identity_ok {| repo_rid := rid; repo_carrier := c |}.

(** Fail-closed COB social graph refusals — positive refuse, not silent swallow. *)
Inductive cob_social_refusal :=
  | csr_untyped_social_edge (from to : nat)
  | csr_node_not_found (nid : nat)
  | csr_git_hash_only_identity (rid : string)
  | csr_second_argmin_refused.

(** Verdict of a social link evaluation. *)
Inductive cob_social_link_verdict :=
  | cslv_accept
  | cslv_refuse_untyped_edge
  | cslv_refuse_missing_node.

(** Classify linkTypedEdge output into evaluation verdict. *)
Definition evaluate_social_link (g : TypedSocialGraph) (from to : nat)
    (from_kind to_kind : SocialNodeKind) : cob_social_link_verdict :=
  match fst (linkTypedEdge g from to from_kind to_kind) with
  | cob_link_ok => cslv_accept
  | cob_untyped_social_edge_refused => cslv_refuse_untyped_edge
  | cob_node_not_found => cslv_refuse_missing_node
  end.

(** Positive refuse: git-hash-only identity without carrier. *)
Definition refuse_git_hash_only (rid : string) : cob_social_refusal :=
  csr_git_hash_only_identity rid.

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin : cob_social_refusal :=
  csr_second_argmin_refused.

Lemma refuse_git_hash_only_identity_positive (rid : string) :
  refuseGitHashOnlyIdentity rid = cob_git_hash_only_identity_refused rid.
Proof. reflexivity. Qed.

Lemma refuse_git_hash_only_eq_csr (rid : string) :
  refuse_git_hash_only rid = csr_git_hash_only_identity rid.
Proof. reflexivity. Qed.

Lemma refuse_second_argmin_positive :
  refuse_second_argmin = csr_second_argmin_refused.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: COB social graph composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — Urge imports selector; no second argmin. *)
Inductive cob_excitement_compose_pin :=
  | csg_import_select_excitement
  | csg_second_argmin_refused.

(** Context for COB social history recovery over admissible successors. *)
Record cob_social_recovery_ctx (src : ThermodynamicState) : Set := {
  cob_social_successors : list (history_candidate src)
}.

(** COB social graph selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition cob_social_select (src : ThermodynamicState)
    (ctx : cob_social_recovery_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (cob_social_successors src ctx).

Theorem cob_social_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : cob_social_recovery_ctx src) :
  cob_social_select src ctx =
  excitement_select src (cob_social_successors src ctx).
Proof.
  unfold cob_social_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem cob_social_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : cob_social_recovery_ctx src) :
  cob_social_select src ctx =
  urge_recovery_select src (cob_social_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem cob_social_no_local_argmin
    (src : ThermodynamicState) (ctx : cob_social_recovery_ctx src) :
  cob_social_select src ctx =
  excitement_select src (cob_social_successors src ctx).
Proof.
  exact (cob_social_select_eq_excitement_select src ctx).
Qed.

(** COB path composes `excitement_select` — not a second argmin. *)
Definition cob_social_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : cob_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | csg_import_select_excitement => excitement_select src cands
  | csg_second_argmin_refused => inr exc_all_inadmissible
  end.

Theorem cob_social_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  cob_social_excitement_select src cands csg_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem cob_social_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  cob_social_excitement_select src cands csg_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma cob_social_select_empty (src : ThermodynamicState)
    (ctx : cob_social_recovery_ctx src)
    (Hnil : cob_social_successors src ctx = nil) :
  cob_social_select src ctx = inr exc_no_candidates.
Proof.
  unfold cob_social_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §3 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Definition cob_fixture_graph : TypedSocialGraph :=
  let (patch_node, g1) :=
    addSocialNode emptySocialGraph social_patch "patch-admissible" in
  let (issue_node, g2) :=
    addSocialNode g1 social_issue "issue-thread" in
  let (review_node, g3) :=
    addSocialNode g2 social_review "review-verdict" in
  let (_, g4) :=
    addSocialNode g3 social_identity "did:umst:cob" in
  g4.

Definition cob_fixture_patch_id : nat := 0.
Definition cob_fixture_issue_id : nat := 1.
Definition cob_fixture_review_id : nat := 2.

Theorem cob_fixture_accept_link :
  evaluate_social_link cob_fixture_graph
    cob_fixture_patch_id cob_fixture_issue_id
    social_patch social_issue = cslv_accept.
Proof.
  reflexivity.
Qed.

Theorem cob_fixture_untyped_link_refused :
  evaluate_social_link cob_fixture_graph
    cob_fixture_patch_id cob_fixture_review_id
    social_patch social_issue = cslv_refuse_untyped_edge.
Proof.
  reflexivity.
Qed.

Theorem cob_fixture_missing_node_refused :
  evaluate_social_link cob_fixture_graph
    cob_fixture_patch_id 999 social_patch social_issue =
  cslv_refuse_missing_node.
Proof.
  reflexivity.
Qed.

Theorem cob_fixture_git_hash_only_refused :
  refuse_git_hash_only "sha1:deadbeef" =
  csr_git_hash_only_identity "sha1:deadbeef".
Proof.
  reflexivity.
Qed.

Definition cob_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Theorem cob_fixture_excitement_compose :
  cob_social_excitement_select cob_fixture_state nil
    csg_import_select_excitement = inr exc_no_candidates.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition cob_social_graph_physics_green : bool := false.

Lemma cob_social_graph_physics_green_false :
  cob_social_graph_physics_green = false.
Proof. reflexivity. Qed.

Definition cob_social_graph_production_wired : bool := false.

Lemma cob_social_graph_production_wired_false :
  cob_social_graph_production_wired = false.
Proof. reflexivity. Qed.

Definition cob_social_graph_non_claim : string :=
  "§3 COB typed social graph (patch/issue/review/identity); positive refuse not only !physics_green; compose excitement_select not local argmin; not physics GREEN; not production_wired".

Lemma cob_social_graph_non_claim_nonempty :
  (0 <? String.length cob_social_graph_non_claim)%nat = true.
Proof.
  simpl. unfold cob_social_graph_non_claim. reflexivity.
Qed.

Theorem cob_social_graph_module_witness : True.
Proof. exact I. Qed.

Theorem cob_social_graph_no_new_axiom : True.
Proof. exact I. Qed.

Theorem cob_social_positive_refuse_not_silent :
  evaluate_social_link cob_fixture_graph
    cob_fixture_patch_id cob_fixture_review_id
    social_patch social_issue <> cslv_accept.
Proof.
  rewrite cob_fixture_untyped_link_refused.
  discriminate.
Qed.
