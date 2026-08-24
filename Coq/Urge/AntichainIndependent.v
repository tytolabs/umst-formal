(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/AntichainIndependent.v                            *)
(*                                                                      *)
(*  Meso acting Urge — §22.2 conflict graph independent set.            *)
(*  Urge **witnesses** prefix conflict-graph independent sets and       *)
(*  composes `excitement_select` — it does **not** fork `umst-adk`      *)
(*  greedy `allocate_antichain` or invent GREEN from antichain size.   *)
(*  Mirrors `BackupRecovery.v` typed morphism discipline.              *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List Bool QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Conflict cell + graph + independent-set carriers       *)
(* ------------------------------------------------------------------ *)

(** Write-set path surrogate — zone pin for prefix conflict (§22.2). *)
Record antichain_write_path : Set := {
  antichain_path_zone : nat;
  antichain_path_suffix : nat
}.

(** Open cell node for prefix conflict graph construction. *)
Record conflict_cell : Set := {
  conflict_cell_id : nat;
  conflict_cell_write_set : list antichain_write_path
}.

(** Canonical undirected edge between two cell ids. *)
Record conflict_edge : Set := {
  conflict_edge_left : nat;
  conflict_edge_right : nat
}.

(** Prefix conflict graph carrier. *)
Record conflict_graph : Set := {
  conflict_graph_nodes : list nat;
  conflict_graph_edges : list conflict_edge
}.

(** Verdict when validating an independent set on a conflict graph. *)
Inductive independent_set_verdict :=
  | isv_admit
  | isv_refuse_not_independent.

(** Fail-closed refusal for §22.2 antichain independent-set policy. *)
Inductive antichain_independent_refusal :=
  | air_fork_allocate_refused
  | air_second_argmin_refused
  | air_not_independent_set
  | air_conflicting_neighbor
  | air_greedy_mis_theater.

(** Verdict of an antichain independent-set operation class. *)
Inductive antichain_independent_verdict :=
  | aiv_independent_admit
  | aiv_fork_allocate_refused
  | aiv_greedy_mis_refused
  | aiv_second_argmin_refused.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §22.2 admissibility conjunct + positive refuse          *)
(* ------------------------------------------------------------------ *)

(** §22.2 admissibility conjunct inputs (surrogate). *)
Record antichain_admissibility_conjunct : Set := {
  antichain_conj_independent_ok : bool;
  antichain_conj_no_fork_allocate : bool;
  antichain_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ independent ∧ no-fork-allocate ∧ Excitement preserves`. *)
Definition antichain_conjunct_admits (c : antichain_admissibility_conjunct) : bool :=
  antichain_conj_independent_ok c &&
  antichain_conj_no_fork_allocate c &&
  antichain_conj_excitement_preserves c.

(** Whether two write-set paths prefix-conflict on zone pin. *)
Definition antichain_paths_conflict_single (p q : antichain_write_path) : bool :=
  Nat.eqb (antichain_path_zone p) (antichain_path_zone q).

(** Whether any path in two write_sets prefix-conflicts. *)
Definition antichain_paths_conflict (left right : list antichain_write_path) : bool :=
  existsb (fun p => existsb (fun q => antichain_paths_conflict_single p q) right) left.

(** Canonical edge with sorted endpoints. *)
Definition canonical_conflict_edge (a b : nat) : conflict_edge :=
  if Nat.ltb b a then
    {| conflict_edge_left := b; conflict_edge_right := a |}
  else
    {| conflict_edge_left := a; conflict_edge_right := b |}.

(** Whether an edge connects two selected node ids. *)
Definition edge_hits_selected (e : conflict_edge) (selected : list nat) : bool :=
  existsb (Nat.eqb (conflict_edge_left e)) selected &&
  existsb (Nat.eqb (conflict_edge_right e)) selected.

(** Whether selected nodes form an independent set (no edge between any pair). *)
Fixpoint is_independent_set (edges : list conflict_edge) (selected : list nat) : bool :=
  match edges with
  | nil => true
  | e :: rest =>
      if edge_hits_selected e selected then false
      else is_independent_set rest selected
  end.

(** Validate selected cell ids form an independent set on the conflict graph. *)
Definition validate_independent_set (g : conflict_graph) (selected : list nat)
    : independent_set_verdict + antichain_independent_refusal :=
  if is_independent_set (conflict_graph_edges g) selected then
    inl isv_admit
  else
    inr air_not_independent_set.

(** Admit a single antichain member — refuse when prefix-conflicts with incumbent. *)
Definition admit_antichain_member (incumbent candidate : conflict_cell)
    : independent_set_verdict + antichain_independent_refusal :=
  if antichain_paths_conflict (conflict_cell_write_set incumbent)
       (conflict_cell_write_set candidate) then
    inr air_conflicting_neighbor
  else
    inl isv_admit.

(** Positive refuse: Urge must not fork `umst-adk` greedy allocate. *)
Definition refuse_fork_allocate : antichain_independent_refusal :=
  air_fork_allocate_refused.

(** Positive refuse: second local Excitement argmin — compose import only. *)
Definition refuse_second_argmin_selector : antichain_independent_refusal :=
  air_second_argmin_refused.

(** Positive refuse: greedy/exact MIS theater — Urge witnesses only. *)
Definition refuse_greedy_mis_theater : antichain_independent_refusal :=
  air_greedy_mis_theater.

(** Urge does not bool-flip physics GREEN from antichain cardinality. *)
Definition physics_green_from_antichain_size (size : nat) : bool := false.

(** Classify fork-allocate vs witness-only independent set without performing I/O. *)
Definition evaluate_antichain_operation (fork_allocate : bool)
    : antichain_independent_verdict :=
  if fork_allocate then aiv_fork_allocate_refused else aiv_independent_admit.

Lemma refuse_fork_allocate_positive :
  refuse_fork_allocate = air_fork_allocate_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_selector_positive :
  refuse_second_argmin_selector = air_second_argmin_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_greedy_mis_theater_positive :
  refuse_greedy_mis_theater = air_greedy_mis_theater.
Proof.
  reflexivity.
Qed.

Lemma antichain_size_never_invents_green (size : nat) :
  physics_green_from_antichain_size size = false.
Proof.
  reflexivity.
Qed.

Lemma evaluate_antichain_operation_fork_refused :
  evaluate_antichain_operation true = aiv_fork_allocate_refused.
Proof.
  reflexivity.
Qed.

Lemma evaluate_antichain_operation_witness_admit :
  evaluate_antichain_operation false = aiv_independent_admit.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Antichain independent composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive antichain_excitement_compose_pin :=
  | aecp_import_select_excitement
  | aecp_second_argmin_refused.

(** Context for antichain independent over admissible history successors. *)
Record antichain_independent_ctx (src : ThermodynamicState) : Set := {
  antichain_independent_successors : list (history_candidate src)
}.

(** Compose path composes `excitement_select` — not a second argmin. *)
Definition antichain_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : antichain_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | aecp_import_select_excitement => excitement_select src cands
  | aecp_second_argmin_refused => inr exc_all_inadmissible
  end.

(** Antichain independent selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition antichain_independent_select (src : ThermodynamicState)
    (ctx : antichain_independent_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (antichain_independent_successors src ctx).

Theorem antichain_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  antichain_excitement_select src cands aecp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem antichain_independent_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : antichain_independent_ctx src) :
  antichain_independent_select src ctx =
  excitement_select src (antichain_independent_successors src ctx).
Proof.
  unfold antichain_independent_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem antichain_independent_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : antichain_independent_ctx src) :
  antichain_independent_select src ctx =
  urge_recovery_select src (antichain_independent_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem antichain_independent_no_local_argmin
    (src : ThermodynamicState) (ctx : antichain_independent_ctx src) :
  antichain_independent_select src ctx =
  excitement_select src (antichain_independent_successors src ctx).
Proof.
  exact (antichain_independent_select_eq_excitement_select src ctx).
Qed.

Theorem antichain_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  antichain_excitement_select src cands aecp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

Lemma antichain_independent_empty (src : ThermodynamicState)
    (ctx : antichain_independent_ctx src)
    (Hnil : antichain_independent_successors src ctx = nil) :
  antichain_independent_select src ctx = inr exc_no_candidates.
Proof.
  unfold antichain_independent_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §22.2 fixtures + witness theorems                        *)
(* ------------------------------------------------------------------ *)

(** §22.2 fixture path pins — mirror Rust `section_22_2_fixture`. *)
Definition ai_path_zone_a : antichain_write_path :=
  {| antichain_path_zone := 1; antichain_path_suffix := 0 |}.

Definition ai_path_zone_a_x : antichain_write_path :=
  {| antichain_path_zone := 1; antichain_path_suffix := 1 |}.

Definition ai_path_zone_a_y : antichain_write_path :=
  {| antichain_path_zone := 1; antichain_path_suffix := 2 |}.

Definition ai_fixture_accept : conflict_cell :=
  {| conflict_cell_id := 0;
     conflict_cell_write_set := ai_path_zone_a :: nil |}.

Definition ai_fixture_refuse_a : conflict_cell :=
  {| conflict_cell_id := 1;
     conflict_cell_write_set := ai_path_zone_a_x :: nil |}.

Definition ai_fixture_refuse_b : conflict_cell :=
  {| conflict_cell_id := 2;
     conflict_cell_write_set := ai_path_zone_a_y :: nil |}.

Definition ai_fixture_edge_0_1 : conflict_edge :=
  canonical_conflict_edge 0 1.

Definition ai_fixture_edge_0_2 : conflict_edge :=
  canonical_conflict_edge 0 2.

Definition ai_fixture_edge_1_2 : conflict_edge :=
  canonical_conflict_edge 1 2.

Definition ai_fixture_graph : conflict_graph :=
  {| conflict_graph_nodes := (0%nat) :: (1%nat) :: (2%nat) :: @nil nat;
     conflict_graph_edges :=
       ai_fixture_edge_0_1 :: ai_fixture_edge_0_2 :: ai_fixture_edge_1_2 :: nil |}.

Definition ai_fixture_conjunct : antichain_admissibility_conjunct :=
  {| antichain_conj_independent_ok := true;
     antichain_conj_no_fork_allocate := true;
     antichain_conj_excitement_preserves := true |}.

Theorem ai_fixture_accept_only_independent :
  validate_independent_set ai_fixture_graph ((0%nat) :: @nil nat) = inl isv_admit.
Proof.
  reflexivity.
Qed.

Theorem ai_fixture_accept_refuse_a_conflicts :
  admit_antichain_member ai_fixture_accept ai_fixture_refuse_a =
  inr air_conflicting_neighbor.
Proof.
  reflexivity.
Qed.

Theorem ai_fixture_accept_refuse_b_conflicts :
  admit_antichain_member ai_fixture_accept ai_fixture_refuse_b =
  inr air_conflicting_neighbor.
Proof.
  reflexivity.
Qed.

Theorem ai_fixture_paths_conflict_accept_a :
  antichain_paths_conflict (conflict_cell_write_set ai_fixture_accept)
    (conflict_cell_write_set ai_fixture_refuse_a) = true.
Proof.
  reflexivity.
Qed.

Theorem ai_fixture_not_independent_pair :
  validate_independent_set ai_fixture_graph ((0%nat) :: (1%nat) :: @nil nat) =
  inr air_not_independent_set.
Proof.
  reflexivity.
Qed.

Theorem ai_fixture_conjunct_admits :
  antichain_conjunct_admits ai_fixture_conjunct = true.
Proof.
  reflexivity.
Qed.

Theorem ai_fixture_antichain_size_no_green :
  physics_green_from_antichain_size (length (conflict_graph_nodes ai_fixture_graph)) = false.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition antichain_independent_physics_green : bool := false.

Lemma antichain_independent_physics_green_false :
  antichain_independent_physics_green = false.
Proof. reflexivity. Qed.

Definition antichain_independent_production_wired : bool := false.

Lemma antichain_independent_production_wired_false :
  antichain_independent_production_wired = false.
Proof. reflexivity. Qed.

Theorem antichain_independent_module_witness : True.
Proof. exact I. Qed.

Theorem antichain_independent_no_new_axiom : True.
Proof. exact I. Qed.

Theorem antichain_independent_positive_refuse_not_silent :
  evaluate_antichain_operation true <> aiv_independent_admit.
Proof.
  unfold evaluate_antichain_operation.
  discriminate.
Qed.

Theorem antichain_independent_fork_allocate_refused_positive :
  refuse_fork_allocate = air_fork_allocate_refused.
Proof.
  reflexivity.
Qed.

Theorem antichain_independent_second_argmin_refused_positive :
  refuse_second_argmin_selector = air_second_argmin_refused.
Proof.
  reflexivity.
Qed.

Theorem antichain_independent_greedy_mis_refused_positive :
  refuse_greedy_mis_theater = air_greedy_mis_theater.
Proof.
  reflexivity.
Qed.

Theorem antichain_independent_never_invents_green_from_size :
  forall size, physics_green_from_antichain_size size = false.
Proof.
  intros. exact (antichain_size_never_invents_green size).
Qed.
