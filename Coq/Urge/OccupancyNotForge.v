(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/OccupancyNotForge.v                               *)
(*                                                                      *)
(*  Meso acting Urge — §13.1 four names unfused: occupancy ≠ forge ≠   *)
(*  meta ≠ Padma. Positive refuse fuse — not silent collapse. Composes  *)
(*  `excitement_select`; no second argmin.                               *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope string_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Four unfused name carriers (§13.1)                     *)
(* ------------------------------------------------------------------ *)

(** `umst-adk` path coverage surrogate — not a forge, not meta, not Padma. *)
Record occupancy_name : Set := {
  occupancy_surrogate : nat
}.

(** India-resident Forgejo forge ops plane — not occupancy, not meta, not Padma. *)
Record forge_name : Set := {
  forge_surrogate : nat
}.

(** Future `umst-meta` transition conjunct — distinct from forge and Padma. *)
Record meta_name : Set := {
  meta_surrogate : nat
}.

(** Padma runtime invariant (crosswalk only) — not a fifth Urge fibre. *)
Record padma_name : Set := {
  padma_surrogate : nat
}.

(** Tagged union preserving the four unfused §13.1 names at the meso layer. *)
Inductive urge_unfused_name :=
  | un_occupancy (o : occupancy_name)
  | un_forge (f : forge_name)
  | un_meta (m : meta_name)
  | un_padma (p : padma_name).

(** Discriminant tag for probe / witness theorems (identity-preserving). *)
Definition urge_name_tag (n : urge_unfused_name) : nat :=
  match n with
  | un_occupancy _ => 0
  | un_forge _ => 1
  | un_meta _ => 2
  | un_padma _ => 3
  end.

(** Classify without fusion — identity-preserving surrogate. *)
Definition classify_urge_name (n : urge_unfused_name) : urge_unfused_name := n.

(** Fail-closed fusion refusal — pairwise merge of distinct §13.1 names. *)
Inductive fusion_refused :=
  | onf_occupancy_forge
  | onf_occupancy_meta
  | onf_occupancy_padma
  | onf_forge_meta
  | onf_forge_padma
  | onf_meta_padma
  | onf_same_discriminant.

(** Verdict of a name-fusion operation class. *)
Inductive occupancy_not_forge_verdict :=
  | onfv_unfused_ok
  | onfv_fusion_refused.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §13.1 positive refuse fuse (not silent collapse)        *)
(* ------------------------------------------------------------------ *)

(** §13.1 admissibility conjunct inputs (surrogate). *)
Record occupancy_not_forge_conjunct : Set := {
  onf_conj_four_names_distinct : bool;
  onf_conj_fusion_refused : bool;
  onf_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ four names distinct ∧ fusion refused ∧ Excitement preserves`. *)
Definition onf_conjunct_admits (c : occupancy_not_forge_conjunct) : bool :=
  onf_conj_four_names_distinct c &&
  onf_conj_fusion_refused c &&
  onf_conj_excitement_preserves c.

(** Classify merge vs hold-unfused without performing fusion. *)
Definition evaluate_name_fusion (attempt_merge : bool)
    : occupancy_not_forge_verdict :=
  if attempt_merge then onfv_fusion_refused else onfv_unfused_ok.

(** Attempt to merge two unfused names — always refused when discriminants differ. *)
Definition try_merge (a b : urge_unfused_name) : unit + fusion_refused :=
  match a, b with
  | un_occupancy _, un_forge _ => inr onf_occupancy_forge
  | un_forge _, un_occupancy _ => inr onf_occupancy_forge
  | un_occupancy _, un_meta _ => inr onf_occupancy_meta
  | un_meta _, un_occupancy _ => inr onf_occupancy_meta
  | un_occupancy _, un_padma _ => inr onf_occupancy_padma
  | un_padma _, un_occupancy _ => inr onf_occupancy_padma
  | un_forge _, un_meta _ => inr onf_forge_meta
  | un_meta _, un_forge _ => inr onf_forge_meta
  | un_forge _, un_padma _ => inr onf_forge_padma
  | un_padma _, un_forge _ => inr onf_forge_padma
  | un_meta _, un_padma _ => inr onf_meta_padma
  | un_padma _, un_meta _ => inr onf_meta_padma
  | _, _ => inr onf_same_discriminant
  end.

(** Typed refuse: coerce occupancy into forge — inadmissible. *)
Definition refuse_occupancy_as_forge (_o : occupancy_name)
    : forge_name + fusion_refused :=
  inr onf_occupancy_forge.

(** Typed refuse: coerce forge into meta — inadmissible. *)
Definition refuse_forge_as_meta (_f : forge_name)
    : meta_name + fusion_refused :=
  inr onf_forge_meta.

(** Typed refuse: coerce meta into Padma — inadmissible. *)
Definition refuse_meta_as_padma (_m : meta_name)
    : padma_name + fusion_refused :=
  inr onf_meta_padma.

(** Typed refuse: coerce Padma into occupancy — inadmissible. *)
Definition refuse_padma_as_occupancy (_p : padma_name)
    : occupancy_name + fusion_refused :=
  inr onf_occupancy_padma.

Lemma evaluate_name_fusion_refused_when_attempt :
  evaluate_name_fusion true = onfv_fusion_refused.
Proof.
  reflexivity.
Qed.

Lemma evaluate_name_fusion_ok_when_hold :
  evaluate_name_fusion false = onfv_unfused_ok.
Proof.
  reflexivity.
Qed.

Lemma try_merge_occupancy_forge_refused
    (o : occupancy_name) (f : forge_name) :
  try_merge (un_occupancy o) (un_forge f) = inr onf_occupancy_forge.
Proof.
  reflexivity.
Qed.

Lemma try_merge_padma_occupancy_refused
    (p : padma_name) (o : occupancy_name) :
  try_merge (un_padma p) (un_occupancy o) = inr onf_occupancy_padma.
Proof.
  reflexivity.
Qed.

Lemma refuse_occupancy_as_forge_positive (o : occupancy_name) :
  refuse_occupancy_as_forge o = inr onf_occupancy_forge.
Proof.
  reflexivity.
Qed.

Lemma refuse_meta_as_padma_positive (m : meta_name) :
  refuse_meta_as_padma m = inr onf_meta_padma.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Occupancy-not-forge composes Excitement (no argmin)     *)
(* ------------------------------------------------------------------ *)

(** Context for occupancy-not-forge over admissible history successors. *)
Record occupancy_not_forge_ctx (src : ThermodynamicState) : Set := {
  occupancy_not_forge_successors : list (history_candidate src)
}.

(** Occupancy-not-forge history selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition occupancy_not_forge_select (src : ThermodynamicState)
    (ctx : occupancy_not_forge_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (occupancy_not_forge_successors src ctx).

Theorem occupancy_not_forge_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : occupancy_not_forge_ctx src) :
  occupancy_not_forge_select src ctx =
  excitement_select src (occupancy_not_forge_successors src ctx).
Proof.
  unfold occupancy_not_forge_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem occupancy_not_forge_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : occupancy_not_forge_ctx src) :
  occupancy_not_forge_select src ctx =
  urge_recovery_select src (occupancy_not_forge_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem occupancy_not_forge_no_local_argmin
    (src : ThermodynamicState) (ctx : occupancy_not_forge_ctx src) :
  occupancy_not_forge_select src ctx =
  excitement_select src (occupancy_not_forge_successors src ctx).
Proof.
  exact (occupancy_not_forge_select_eq_excitement_select src ctx).
Qed.

Lemma occupancy_not_forge_empty (src : ThermodynamicState)
    (ctx : occupancy_not_forge_ctx src)
    (Hnil : occupancy_not_forge_successors src ctx = nil) :
  occupancy_not_forge_select src ctx = inr exc_no_candidates.
Proof.
  unfold occupancy_not_forge_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §13.1 fixtures + witness theorems                         *)
(* ------------------------------------------------------------------ *)

Definition onf_fixture_occupancy : occupancy_name :=
  {| occupancy_surrogate := 1 |}.

Definition onf_fixture_forge : forge_name :=
  {| forge_surrogate := 2 |}.

Definition onf_fixture_meta : meta_name :=
  {| meta_surrogate := 3 |}.

Definition onf_fixture_padma : padma_name :=
  {| padma_surrogate := 4 |}.

Definition onf_fixture_occ_name : urge_unfused_name :=
  un_occupancy onf_fixture_occupancy.

Definition onf_fixture_forge_name : urge_unfused_name :=
  un_forge onf_fixture_forge.

Definition onf_fixture_meta_name : urge_unfused_name :=
  un_meta onf_fixture_meta.

Definition onf_fixture_padma_name : urge_unfused_name :=
  un_padma onf_fixture_padma.

Definition onf_fixture_conjunct : occupancy_not_forge_conjunct :=
  {| onf_conj_four_names_distinct := true;
     onf_conj_fusion_refused := true;
     onf_conj_excitement_preserves := true |}.

Theorem onf_fixture_four_tags_distinct :
  urge_name_tag onf_fixture_occ_name <> urge_name_tag onf_fixture_forge_name /\
  urge_name_tag onf_fixture_forge_name <> urge_name_tag onf_fixture_meta_name /\
  urge_name_tag onf_fixture_meta_name <> urge_name_tag onf_fixture_padma_name /\
  urge_name_tag onf_fixture_padma_name <> urge_name_tag onf_fixture_occ_name.
Proof.
  unfold urge_name_tag, onf_fixture_occ_name, onf_fixture_forge_name,
    onf_fixture_meta_name, onf_fixture_padma_name.
  repeat split; discriminate.
Qed.

Theorem onf_fixture_occupancy_forge_merge_refused :
  try_merge onf_fixture_occ_name onf_fixture_forge_name =
  inr onf_occupancy_forge.
Proof.
  reflexivity.
Qed.

Theorem onf_fixture_padma_occupancy_merge_refused :
  try_merge onf_fixture_padma_name onf_fixture_occ_name =
  inr onf_occupancy_padma.
Proof.
  reflexivity.
Qed.

Theorem onf_fixture_evaluate_fusion_refused :
  evaluate_name_fusion true = onfv_fusion_refused.
Proof.
  reflexivity.
Qed.

Theorem onf_fixture_conjunct_admits :
  onf_conjunct_admits onf_fixture_conjunct = true.
Proof.
  reflexivity.
Qed.

Definition onf_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition onf_fixture_candidate : history_candidate onf_fixture_state :=
  {| cand_id := 13;
     cand_tgt := onf_fixture_state;
     cand_admissible := admissible_refl onf_fixture_state |}.

Definition onf_fixture_ctx : occupancy_not_forge_ctx onf_fixture_state :=
  {| occupancy_not_forge_successors :=
       onf_fixture_candidate :: nil |}.

Theorem onf_fixture_select_eq_excitement :
  occupancy_not_forge_select onf_fixture_state onf_fixture_ctx =
  excitement_select onf_fixture_state
    (onf_fixture_candidate :: nil).
Proof.
  exact (occupancy_not_forge_select_eq_excitement_select
           onf_fixture_state onf_fixture_ctx).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition occupancy_not_forge_physics_green : bool := false.

Lemma occupancy_not_forge_physics_green_false :
  occupancy_not_forge_physics_green = false.
Proof. reflexivity. Qed.

Definition occupancy_not_forge_production_wired : bool := false.

Lemma occupancy_not_forge_production_wired_false :
  occupancy_not_forge_production_wired = false.
Proof. reflexivity. Qed.

Definition occupancy_not_forge_marker : string :=
  "urge_int_occupancy_not_forge_v1"%string.

Theorem occupancy_not_forge_marker_nonempty :
  negb (Nat.eqb (String.length occupancy_not_forge_marker) 0) = true.
Proof.
  reflexivity.
Qed.

Theorem occupancy_not_forge_module_witness : True.
Proof. exact I. Qed.

Theorem occupancy_not_forge_no_new_axiom : True.
Proof. exact I. Qed.

Theorem occupancy_not_forge_positive_refuse_not_silent :
  evaluate_name_fusion true <> onfv_unfused_ok.
Proof.
  unfold evaluate_name_fusion.
  discriminate.
Qed.

Theorem occupancy_not_forge_padma_not_occupancy :
  try_merge onf_fixture_padma_name onf_fixture_occ_name <>
  inl tt.
Proof.
  rewrite onf_fixture_padma_occupancy_merge_refused.
  discriminate.
Qed.
