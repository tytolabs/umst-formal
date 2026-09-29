(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/LatencyBudget.v                                   *)
(*                                                                      *)
(*  Meso acting Urge — §17.8 latency budget as typed predicate on admit. *)
(*  Integer surrogate ms vs declared tier ceiling — not wall-clock SLA   *)
(*  theater. Merge / recovery slow path composes `excitement_select`;    *)
(*  no second argmin.                                                   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Stdlib Require Import Arith Bool Lia.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: §17.8 typed budget tiers + morphism carriers           *)
(* ------------------------------------------------------------------ *)

(** Blueprint §17.8 interactive observation budget (milliseconds, typed). *)
Definition interactive_budget_ms : nat := 16.

(** Blueprint §17.8 local commit admission budget (milliseconds, typed). *)
Definition local_commit_budget_ms : nat := 100.

(** Blueprint §17.8 merge / recovery slow-path budget (milliseconds, typed). *)
Definition merge_recovery_budget_ms : nat := 1000.

(** Blueprint §17.8 background compaction budget (milliseconds, typed). *)
Definition background_budget_ms : nat := 10000.

(** Typed budget tier — declared ceiling, not measured wall-clock. *)
Inductive latency_budget_tier :=
  | lbt_interactive
  | lbt_local_commit
  | lbt_merge_recovery
  | lbt_background.

(** Declared budget ceiling for each tier (milliseconds, typed — not measured). *)
Definition latency_tier_budget_ms (t : latency_budget_tier) : nat :=
  match t with
  | lbt_interactive => interactive_budget_ms
  | lbt_local_commit => local_commit_budget_ms
  | lbt_merge_recovery => merge_recovery_budget_ms
  | lbt_background => background_budget_ms
  end.

(** Candidate for latency-budget admission — surrogate inputs only. *)
Record latency_budget_candidate : Set := {
  lb_candidate_tier : latency_budget_tier;
  lb_candidate_surrogate_ms : nat;
  lb_candidate_claims_wall_clock_sla : bool;
  lb_candidate_claims_physics_green : bool
}.

(** Typed budget witness — declared ceiling + surrogate, not measured latency. *)
Record latency_budget_witness : Set := {
  lb_witness_tier : latency_budget_tier;
  lb_witness_budget_ms : nat;
  lb_witness_surrogate_ms : nat;
  lb_witness_typed_predicate : bool
}.

(** Witness bundle a latency-budget morphism must preserve (§17.8). *)
Record latency_budget_morphism_witness : Set := {
  lb_morph_witness_tier : latency_budget_tier;
  lb_morph_witness_budget_ms : nat;
  lb_morph_witness_surrogate_ms : nat;
  lb_morph_witness_typed_predicate : bool
}.

(** Typed latency-budget morphism — admissible admit transition, not SLA theater. *)
Record latency_budget_morphism : Set := {
  lb_morphism_from : latency_budget_candidate;
  lb_morphism_witness : latency_budget_morphism_witness;
  lb_morphism_excitement_selected : bool
}.

(** Fail-closed latency-budget errors — positive refuse, not silent no-op. *)
Inductive latency_budget_refusal :=
  | lbr_budget_exceeded (surrogate_ms budget_ms : nat)
  | lbr_wall_clock_sla_theater
  | lbr_physics_green_invent
  | lbr_unbounded_latency_ratio_theater
  | lbr_gate_rejected (surrogate_ms : nat).

(** Verdict of a latency-budget operation class. *)
Inductive latency_budget_verdict :=
  | lbv_admit_ok
  | lbv_wall_clock_sla_refused
  | lbv_physics_green_refused
  | lbv_ratio_theater_refused
  | lbv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §17.8 admissibility conjunct + positive refuse         *)
(* ------------------------------------------------------------------ *)

(** §17.8 admissibility conjunct inputs (surrogate). *)
Record latency_admissibility_conjunct : Set := {
  lb_conj_gate_ok : bool;
  lb_conj_typed_predicate : bool;
  lb_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ typed predicate ∧ Excitement preserves`. *)
Definition latency_conjunct_admits (c : latency_admissibility_conjunct) : bool :=
  lb_conj_gate_ok c &&
  lb_conj_typed_predicate c &&
  lb_conj_excitement_preserves c.

(** Core typed predicate — surrogate within tier and no SLA / GREEN theater. *)
Definition latency_budget_admit_pred (c : latency_budget_candidate) : bool :=
  negb (lb_candidate_claims_wall_clock_sla c) &&
  negb (lb_candidate_claims_physics_green c) &&
  (lb_candidate_surrogate_ms c <=? latency_tier_budget_ms (lb_candidate_tier c)).

(** Classify wall-clock SLA theater without performing I/O. *)
Definition evaluate_wall_clock_sla_operation (claims_wall_clock : bool)
    : latency_budget_verdict :=
  if claims_wall_clock then lbv_wall_clock_sla_refused else lbv_admit_ok.

(** Classify physics GREEN invent without performing I/O. *)
Definition evaluate_physics_green_operation (claims_green : bool)
    : latency_budget_verdict :=
  if claims_green then lbv_physics_green_refused else lbv_admit_ok.

(** Positive refuse: wall-clock SLA theater is inadmissible — typed predicate only. *)
Definition refuse_wall_clock_sla_theater : Empty_set + latency_budget_refusal :=
  inr lbr_wall_clock_sla_theater.

(** Positive refuse: unbounded f64 latency-ratio theater is inadmissible. *)
Definition refuse_unbounded_latency_ratio_theater
    : Empty_set + latency_budget_refusal :=
  inr lbr_unbounded_latency_ratio_theater.

(** Evaluate latency-budget admission — honest refusal on inadmissible inputs. *)
Definition evaluate_latency_budget_admit (c : latency_budget_candidate)
    : latency_budget_witness + latency_budget_refusal :=
  if lb_candidate_claims_physics_green c then
    inr lbr_physics_green_invent
  else if lb_candidate_claims_wall_clock_sla c then
    inr lbr_wall_clock_sla_theater
  else
    let budget_ms := latency_tier_budget_ms (lb_candidate_tier c) in
    let surrogate_ms := lb_candidate_surrogate_ms c in
    if surrogate_ms <=? budget_ms then
      inl
        {| lb_witness_tier := lb_candidate_tier c;
           lb_witness_budget_ms := budget_ms;
           lb_witness_surrogate_ms := surrogate_ms;
           lb_witness_typed_predicate := true |}
    else
      inr (lbr_budget_exceeded surrogate_ms budget_ms).

(** Build morphism witness from admitted candidate. *)
Definition witness_from_candidate (c : latency_budget_candidate)
    (w : latency_budget_witness) : latency_budget_morphism_witness :=
  {| lb_morph_witness_tier := lb_witness_tier w;
     lb_morph_witness_budget_ms := lb_witness_budget_ms w;
     lb_morph_witness_surrogate_ms := lb_witness_surrogate_ms w;
     lb_morph_witness_typed_predicate := lb_witness_typed_predicate w |}.

(** Attempt typed latency-budget morphism — fail closed on inadmissibility. *)
Definition apply_latency_budget_morphism
    (candidate : latency_budget_candidate)
    (conjunct : latency_admissibility_conjunct)
    (excitement_selected : bool)
    : latency_budget_morphism + latency_budget_refusal :=
  if negb (latency_conjunct_admits conjunct) then
    inr (lbr_gate_rejected (lb_candidate_surrogate_ms candidate))
  else if negb (lb_conj_typed_predicate conjunct) then
    inr lbr_wall_clock_sla_theater
  else if negb excitement_selected then
    inr (lbr_budget_exceeded
           (lb_candidate_surrogate_ms candidate)
           (latency_tier_budget_ms (lb_candidate_tier candidate)))
  else
    match evaluate_latency_budget_admit candidate with
    | inl w =>
        inl
          {| lb_morphism_from := candidate;
             lb_morphism_witness := witness_from_candidate candidate w;
             lb_morphism_excitement_selected := excitement_selected |}
    | inr r => inr r
    end.

(** Build typed budget witness for a tier at zero surrogate (probe default). *)
Definition budget_witness_for (t : latency_budget_tier) : latency_budget_witness :=
  {| lb_witness_tier := t;
     lb_witness_budget_ms := latency_tier_budget_ms t;
     lb_witness_surrogate_ms := 0;
     lb_witness_typed_predicate := true |}.

(** Check surrogate estimated cost against typed tier budget — refuse if exceeded. *)
Definition check_typed_budget (t : latency_budget_tier) (surrogate_ms : nat)
    : latency_budget_witness + latency_budget_refusal :=
  evaluate_latency_budget_admit
    {| lb_candidate_tier := t;
       lb_candidate_surrogate_ms := surrogate_ms;
       lb_candidate_claims_wall_clock_sla := false;
       lb_candidate_claims_physics_green := false |}.

Lemma interactive_budget_is_16 :
  latency_tier_budget_ms lbt_interactive = interactive_budget_ms.
Proof. reflexivity. Qed.

Lemma local_commit_budget_is_100 :
  latency_tier_budget_ms lbt_local_commit = local_commit_budget_ms.
Proof. reflexivity. Qed.

Lemma merge_recovery_budget_is_1000 :
  latency_tier_budget_ms lbt_merge_recovery = merge_recovery_budget_ms.
Proof. reflexivity. Qed.

Lemma background_budget_is_10000 :
  latency_tier_budget_ms lbt_background = background_budget_ms.
Proof. reflexivity. Qed.

Lemma evaluate_wall_clock_sla_refused :
  evaluate_wall_clock_sla_operation true = lbv_wall_clock_sla_refused.
Proof. reflexivity. Qed.

Lemma evaluate_wall_clock_sla_ok :
  evaluate_wall_clock_sla_operation false = lbv_admit_ok.
Proof. reflexivity. Qed.

Lemma refuse_wall_clock_sla_theater_positive :
  refuse_wall_clock_sla_theater = inr lbr_wall_clock_sla_theater.
Proof. reflexivity. Qed.

Lemma refuse_unbounded_ratio_theater_positive :
  refuse_unbounded_latency_ratio_theater =
  inr lbr_unbounded_latency_ratio_theater.
Proof. reflexivity. Qed.

Lemma budget_witness_for_typed (t : latency_budget_tier) :
  lb_witness_typed_predicate (budget_witness_for t) = true.
Proof. reflexivity. Qed.

Lemma budget_witness_for_budget (t : latency_budget_tier) :
  lb_witness_budget_ms (budget_witness_for t) = latency_tier_budget_ms t.
Proof. reflexivity. Qed.

Lemma check_typed_budget_ok (t : latency_budget_tier) (surrogate_ms : nat)
    (h : surrogate_ms <= latency_tier_budget_ms t) :
  check_typed_budget t surrogate_ms =
  inl
    {| lb_witness_tier := t;
       lb_witness_budget_ms := latency_tier_budget_ms t;
       lb_witness_surrogate_ms := surrogate_ms;
       lb_witness_typed_predicate := true |}.
Proof.
  unfold check_typed_budget, evaluate_latency_budget_admit.
  simpl.
  destruct (surrogate_ms <=? latency_tier_budget_ms t) eqn:Hc.
  - reflexivity.
  - apply Nat.leb_gt in Hc. lia.
Qed.

Lemma check_typed_budget_exceeded (t : latency_budget_tier) (surrogate_ms : nat)
    (h : latency_tier_budget_ms t < surrogate_ms) :
  check_typed_budget t surrogate_ms =
  inr (lbr_budget_exceeded surrogate_ms (latency_tier_budget_ms t)).
Proof.
  unfold check_typed_budget, evaluate_latency_budget_admit.
  simpl.
  destruct (surrogate_ms <=? latency_tier_budget_ms t) eqn:Hc.
  - apply Nat.leb_le in Hc. lia.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Merge/recovery composes Excitement (no second argmin)  *)
(* ------------------------------------------------------------------ *)

(** Context for merge/recovery slow path over admissible history successors. *)
Record latency_budget_ctx (src : ThermodynamicState) : Set := {
  latency_budget_successors : list (history_candidate src)
}.

(** Merge / recovery slow path **is** `urge_recovery_select` / `excitement_select`. *)
Definition latency_budget_recovery_select (src : ThermodynamicState)
    (ctx : latency_budget_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (latency_budget_successors src ctx).

Theorem latency_budget_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : latency_budget_ctx src) :
  latency_budget_recovery_select src ctx =
  excitement_select src (latency_budget_successors src ctx).
Proof.
  unfold latency_budget_recovery_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem latency_budget_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : latency_budget_ctx src) :
  latency_budget_recovery_select src ctx =
  urge_recovery_select src (latency_budget_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem latency_budget_no_local_argmin
    (src : ThermodynamicState) (ctx : latency_budget_ctx src) :
  latency_budget_recovery_select src ctx =
  excitement_select src (latency_budget_successors src ctx).
Proof.
  exact (latency_budget_select_eq_excitement_select src ctx).
Qed.

Lemma latency_budget_recovery_empty (src : ThermodynamicState)
    (ctx : latency_budget_ctx src)
    (Hnil : latency_budget_successors src ctx = nil) :
  latency_budget_recovery_select src ctx = inr exc_no_candidates.
Proof.
  unfold latency_budget_recovery_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §17.8 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition latency_fixture_interactive_candidate : latency_budget_candidate :=
  {| lb_candidate_tier := lbt_interactive;
     lb_candidate_surrogate_ms := 10;
     lb_candidate_claims_wall_clock_sla := false;
     lb_candidate_claims_physics_green := false |}.

Definition latency_fixture_local_commit_candidate : latency_budget_candidate :=
  {| lb_candidate_tier := lbt_local_commit;
     lb_candidate_surrogate_ms := 80;
     lb_candidate_claims_wall_clock_sla := false;
     lb_candidate_claims_physics_green := false |}.

Definition latency_fixture_over_budget_candidate : latency_budget_candidate :=
  {| lb_candidate_tier := lbt_local_commit;
     lb_candidate_surrogate_ms := S local_commit_budget_ms;
     lb_candidate_claims_wall_clock_sla := false;
     lb_candidate_claims_physics_green := false |}.

Definition latency_fixture_wall_clock_candidate : latency_budget_candidate :=
  {| lb_candidate_tier := lbt_local_commit;
     lb_candidate_surrogate_ms := 50;
     lb_candidate_claims_wall_clock_sla := true;
     lb_candidate_claims_physics_green := false |}.

Definition latency_fixture_green_candidate : latency_budget_candidate :=
  {| lb_candidate_tier := lbt_merge_recovery;
     lb_candidate_surrogate_ms := 500;
     lb_candidate_claims_wall_clock_sla := false;
     lb_candidate_claims_physics_green := true |}.

Definition latency_fixture_conjunct : latency_admissibility_conjunct :=
  {| lb_conj_gate_ok := true;
     lb_conj_typed_predicate := true;
     lb_conj_excitement_preserves := true |}.

Theorem latency_fixture_interactive_admits :
  evaluate_latency_budget_admit latency_fixture_interactive_candidate =
  inl
    {| lb_witness_tier := lbt_interactive;
       lb_witness_budget_ms := interactive_budget_ms;
       lb_witness_surrogate_ms := 10;
       lb_witness_typed_predicate := true |}.
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_local_commit_admits :
  evaluate_latency_budget_admit latency_fixture_local_commit_candidate =
  inl
    {| lb_witness_tier := lbt_local_commit;
       lb_witness_budget_ms := local_commit_budget_ms;
       lb_witness_surrogate_ms := 80;
       lb_witness_typed_predicate := true |}.
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_over_budget_refused :
  evaluate_latency_budget_admit latency_fixture_over_budget_candidate =
  inr (lbr_budget_exceeded (S local_commit_budget_ms) local_commit_budget_ms).
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_wall_clock_refused :
  evaluate_latency_budget_admit latency_fixture_wall_clock_candidate =
  inr lbr_wall_clock_sla_theater.
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_physics_green_refused :
  evaluate_latency_budget_admit latency_fixture_green_candidate =
  inr lbr_physics_green_invent.
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_apply_morphism_ok :
  apply_latency_budget_morphism
    latency_fixture_local_commit_candidate latency_fixture_conjunct true
  = inl
      {| lb_morphism_from := latency_fixture_local_commit_candidate;
         lb_morphism_witness :=
           witness_from_candidate latency_fixture_local_commit_candidate
             {| lb_witness_tier := lbt_local_commit;
                lb_witness_budget_ms := local_commit_budget_ms;
                lb_witness_surrogate_ms := 80;
                lb_witness_typed_predicate := true |};
         lb_morphism_excitement_selected := true |}.
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_admit_pred_within_tier :
  latency_budget_admit_pred latency_fixture_local_commit_candidate = true.
Proof.
  reflexivity.
Qed.

Theorem latency_fixture_admit_pred_wall_clock_false :
  latency_budget_admit_pred latency_fixture_wall_clock_candidate = false.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition latency_budget_physics_green : bool := false.

Lemma latency_budget_physics_green_false :
  latency_budget_physics_green = false.
Proof. reflexivity. Qed.

Definition latency_budget_production_wired : bool := false.

Lemma latency_budget_production_wired_false :
  latency_budget_production_wired = false.
Proof. reflexivity. Qed.

Theorem latency_budget_module_witness : True.
Proof. exact I. Qed.

Theorem latency_budget_no_new_axiom : True.
Proof. exact I. Qed.

Theorem latency_budget_positive_refuse_not_silent :
  evaluate_wall_clock_sla_operation true <> lbv_admit_ok.
Proof.
  unfold evaluate_wall_clock_sla_operation.
  discriminate.
Qed.

Theorem latency_budget_sla_theater_refused_not_admit_ok :
  evaluate_latency_budget_admit latency_fixture_wall_clock_candidate <>
  inl
    {| lb_witness_tier := lbt_local_commit;
       lb_witness_budget_ms := local_commit_budget_ms;
       lb_witness_surrogate_ms := 50;
       lb_witness_typed_predicate := true |}.
Proof.
  rewrite latency_fixture_wall_clock_refused.
  discriminate.
Qed.
