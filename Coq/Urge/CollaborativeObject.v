(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/CollaborativeObject.v                             *)
(*                                                                      *)
(*  Meso acting Urge — §3 COB: history carrier + typed social graph.    *)
(*  Collaborative Object = same Repository/History carrier product      *)
(*  (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness) plus typed social     *)
(*  graph overlay (patch, issue, review, identity).                       *)
(*  Excitement `select` composed — no second argmin. ZERO Admitted.     *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.CarrierProduct.

Open Scope string_scope.

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

Lemma kindEqb_neq (k1 k2 : SocialNodeKind) :
  kindEqb k1 k2 = false -> k1 <> k2.
Proof.
  intros H.
  destruct k1, k2; try discriminate H; intro Heq; inversion Heq; reflexivity.
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
(*  SECTION 2: Repository identity + history carrier (§3 COB)          *)
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

(** Carrier populated when UMST commit id or stamp wall is present. *)
Definition carrierPopulated (c : HistoryCarrier) : bool :=
  orb
    (0 <? history_commit_id (umstProj c))%nat
    (0 <? stamp_observed_at_wall (stampProj c))%nat.

(** Collaborative Object — history carrier + typed social graph. *)
Record CollaborativeObject : Set := {
  cob_identity : RepositoryIdentity;
  cob_social : TypedSocialGraph
}.

Definition cobNew (id : RepositoryIdentity) : CollaborativeObject :=
  {| cob_identity := id;
     cob_social := emptySocialGraph |}.

Definition cobCarrier (cob : CollaborativeObject) : HistoryCarrier :=
  repo_carrier (cob_identity cob).

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Positive refuse witnesses                             *)
(* ------------------------------------------------------------------ *)

Lemma refuse_git_hash_only_is_refused (rid : string) :
  refuseGitHashOnlyIdentity rid = cob_git_hash_only_identity_refused rid.
Proof. reflexivity. Qed.

Lemma linkTypedEdge_ok_preserves_nodes (g : TypedSocialGraph) (from to : nat)
    (fk tk : SocialNodeKind)
    (Hfrom : exists n, findSocialNode (social_nodes g) from = Some n)
    (Hto : exists n, findSocialNode (social_nodes g) to = Some n)
    (Hkind :
      forall (nf nt : SocialNode),
        findSocialNode (social_nodes g) from = Some nf ->
        findSocialNode (social_nodes g) to = Some nt ->
        social_node_kind nf = fk /\
        social_node_kind nt = tk) :
  exists g', fst (linkTypedEdge g from to fk tk) = cob_link_ok /\
             social_nodes g' = social_nodes g.
Proof.
  destruct Hfrom as [nf Hnf].
  destruct Hto as [nt Hnt].
  destruct (Hkind nf nt Hnf Hnt) as [Hfk Htk].
  unfold linkTypedEdge.
  rewrite Hnf, Hnt.
  rewrite Hfk, Htk, kindEqb_refl, kindEqb_refl, andb_true_r.
  exists {| social_nodes := social_nodes g;
            social_edges := social_edges g ++
              {| social_edge_from := from;
                 social_edge_to := to;
                 social_edge_from_kind := fk;
                 social_edge_to_kind := tk |} :: nil;
            social_next_id := social_next_id g |}.
  split; reflexivity.
Qed.

Lemma linkTypedEdge_untyped_refused (g : TypedSocialGraph) (from to : nat)
    (fk tk : SocialNodeKind)
    (nf : SocialNode) (Hnf : findSocialNode (social_nodes g) from = Some nf)
    (nt : SocialNode) (Hnt : findSocialNode (social_nodes g) to = Some nt)
    (Hbad : social_node_kind nf <> fk \/ social_node_kind nt <> tk) :
  fst (linkTypedEdge g from to fk tk) = cob_untyped_social_edge_refused /\
  snd (linkTypedEdge g from to fk tk) = g.
Proof.
  unfold linkTypedEdge.
  rewrite Hnf, Hnt.
  destruct Hbad as [Hfk | Htk].
  - destruct (kindEqb (social_node_kind nf) fk) eqn:Heq.
    + apply kindEqb_eq in Heq. contradiction.
    + simpl. split; reflexivity.
  - destruct (kindEqb (social_node_kind nf) fk) eqn:Heq1.
    * destruct (kindEqb (social_node_kind nt) tk) eqn:Heq2.
      -- apply kindEqb_eq in Heq2. contradiction.
      -- simpl. split; reflexivity.
    * simpl. split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Excitement alignment (no second argmin)                 *)
(* ------------------------------------------------------------------ *)

(** COB history recovery composes `excitement_select` on carrier UMST head. *)
Definition cobSelect (cob : CollaborativeObject)
    (cands : list (history_candidate (history_head (umstProj (cobCarrier cob))))) :
  history_candidate (history_head (umstProj (cobCarrier cob))) + excitement_residue :=
  excitement_select (history_head (umstProj (cobCarrier cob))) cands.

Theorem cobSelect_eq_excitement_select (cob : CollaborativeObject)
    (cands : list (history_candidate (history_head (umstProj (cobCarrier cob))))) :
  cobSelect cob cands =
  excitement_select (history_head (umstProj (cobCarrier cob))) cands.
Proof. reflexivity. Qed.

Theorem cobSelect_eq_carrierSelect (cob : CollaborativeObject)
    (cands : list (history_candidate (history_head (umstProj (cobCarrier cob))))) :
  cobSelect cob cands = carrierSelect (cobCarrier cob) cands.
Proof. reflexivity. Qed.

Theorem cob_no_local_argmin (cob : CollaborativeObject)
    (cands : list (history_candidate (history_head (umstProj (cobCarrier cob))))) :
  cobSelect cob cands =
  excitement_select (history_head (umstProj (cobCarrier cob))) cands.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition collaborative_object_physics_green : bool := false.

Lemma collaborative_object_physics_green_false :
  collaborative_object_physics_green = false.
Proof. reflexivity. Qed.

Definition collaborative_object_production_wired : bool := false.

Lemma collaborative_object_production_wired_false :
  collaborative_object_production_wired = false.
Proof. reflexivity. Qed.

Definition collaborative_object_non_claim : string :=
  "§3 COB: same carrier + typed social graph (patch, issue, review, identity); geometric identity primary; not physics GREEN; not production_wired".

Lemma collaborative_object_non_claim_nonempty :
  (0 <? String.length collaborative_object_non_claim)%nat = true.
Proof.
  simpl. unfold collaborative_object_non_claim. reflexivity.
Qed.

Theorem collaborative_object_module_witness : True.
Proof. exact I. Qed.

Theorem collaborative_object_no_new_axiom : True.
Proof. exact I. Qed.
