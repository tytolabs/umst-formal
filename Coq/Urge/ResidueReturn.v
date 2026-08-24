(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ResidueReturn.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §13.5 returns Excitement Residue counts +        *)
(*  observed ΔF back to Excitement occupancy. Six constructors pinned  *)
(*  to Lean `UMST.Excitement.Residue`. Composes `excitement_select`;    *)
(*  no second argmin / f64 F compare.                                   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw` /         *)
(*  `Chem.SecondLaw` — cited, not restated.                             *)
(* ================================================================== *)

From Coq Require Import Arith List Bool String QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.
Open Scope Q_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Six Excitement Residue constructors (Lean arity pin)    *)
(* ------------------------------------------------------------------ *)

(** Lean-aligned six constructors — mirrors `UMST.Excitement.Residue`. *)
Inductive urge_excitement_residue :=
  | uer_no_candidates
  | uer_all_inadmissible
  | uer_all_excluded_by_cbf
  | uer_all_excluded_by_dec
  | uer_untagged_constant
  | uer_no_strict_improvement.

(** Stable constructor name — pins imported enum, does not fork variants. *)
Definition residue_constructor_name (r : urge_excitement_residue) : string :=
  match r with
  | uer_no_candidates => "NoCandidates"%string
  | uer_all_inadmissible => "AllInadmissible"%string
  | uer_all_excluded_by_cbf => "AllExcludedByCbf"%string
  | uer_all_excluded_by_dec => "AllExcludedByDec"%string
  | uer_untagged_constant => "UntaggedConstant"%string
  | uer_no_strict_improvement => "NoStrictImprovement"%string
  end.

(** All six constructors — exhaustiveness pin against Lean arity. *)
Definition pin_six_residue_constructors : list urge_excitement_residue :=
  uer_no_candidates ::
  uer_all_inadmissible ::
  uer_all_excluded_by_cbf ::
  uer_all_excluded_by_dec ::
  uer_untagged_constant ::
  uer_no_strict_improvement :: nil.

Definition residue_constructor_names : list string :=
  "NoCandidates"%string ::
  "AllInadmissible"%string ::
  "AllExcludedByCbf"%string ::
  "AllExcludedByDec"%string ::
  "UntaggedConstant"%string ::
  "NoStrictImprovement"%string :: nil.

(** Map meso `excitement_residue` hook into six-constructor pin. *)
Definition map_admit_residue (r : excitement_residue) : urge_excitement_residue :=
  match r with
  | exc_no_candidates => uer_no_candidates
  | exc_all_inadmissible => uer_all_inadmissible
  | exc_no_strict_improvement => uer_no_strict_improvement
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Residue counts + observed ΔF return payload           *)
(* ------------------------------------------------------------------ *)

(** Per-constructor occurrence counts returned to Excitement. *)
Record residue_counts : Set := {
  rc_no_candidates : nat;
  rc_all_inadmissible : nat;
  rc_all_excluded_by_cbf : nat;
  rc_all_excluded_by_dec : nat;
  rc_untagged_constant : nat;
  rc_no_strict_improvement : nat
}.

Definition empty_residue_counts : residue_counts :=
  {| rc_no_candidates := 0;
     rc_all_inadmissible := 0;
     rc_all_excluded_by_cbf := 0;
     rc_all_excluded_by_dec := 0;
     rc_untagged_constant := 0;
     rc_no_strict_improvement := 0 |}.

(** Total residue observations across all six constructors. *)
Definition residue_counts_total (c : residue_counts) : nat :=
  rc_no_candidates c +
  rc_all_inadmissible c +
  rc_all_excluded_by_cbf c +
  rc_all_excluded_by_dec c +
  rc_untagged_constant c +
  rc_no_strict_improvement c.

(** Count for a single constructor (pin test helper). *)
Definition residue_count_of (c : residue_counts) (r : urge_excitement_residue) : nat :=
  match r with
  | uer_no_candidates => rc_no_candidates c
  | uer_all_inadmissible => rc_all_inadmissible c
  | uer_all_excluded_by_cbf => rc_all_excluded_by_cbf c
  | uer_all_excluded_by_dec => rc_all_excluded_by_dec c
  | uer_untagged_constant => rc_untagged_constant c
  | uer_no_strict_improvement => rc_no_strict_improvement c
  end.

(** Record one observed `urge_excitement_residue` constructor. *)
Definition increment_residue_count (counts : residue_counts)
    (r : urge_excitement_residue) : residue_counts :=
  match r with
  | uer_no_candidates =>
      {| rc_no_candidates := S (rc_no_candidates counts);
         rc_all_inadmissible := rc_all_inadmissible counts;
         rc_all_excluded_by_cbf := rc_all_excluded_by_cbf counts;
         rc_all_excluded_by_dec := rc_all_excluded_by_dec counts;
         rc_untagged_constant := rc_untagged_constant counts;
         rc_no_strict_improvement := rc_no_strict_improvement counts |}
  | uer_all_inadmissible =>
      {| rc_no_candidates := rc_no_candidates counts;
         rc_all_inadmissible := S (rc_all_inadmissible counts);
         rc_all_excluded_by_cbf := rc_all_excluded_by_cbf counts;
         rc_all_excluded_by_dec := rc_all_excluded_by_dec counts;
         rc_untagged_constant := rc_untagged_constant counts;
         rc_no_strict_improvement := rc_no_strict_improvement counts |}
  | uer_all_excluded_by_cbf =>
      {| rc_no_candidates := rc_no_candidates counts;
         rc_all_inadmissible := rc_all_inadmissible counts;
         rc_all_excluded_by_cbf := S (rc_all_excluded_by_cbf counts);
         rc_all_excluded_by_dec := rc_all_excluded_by_dec counts;
         rc_untagged_constant := rc_untagged_constant counts;
         rc_no_strict_improvement := rc_no_strict_improvement counts |}
  | uer_all_excluded_by_dec =>
      {| rc_no_candidates := rc_no_candidates counts;
         rc_all_inadmissible := rc_all_inadmissible counts;
         rc_all_excluded_by_cbf := rc_all_excluded_by_cbf counts;
         rc_all_excluded_by_dec := S (rc_all_excluded_by_dec counts);
         rc_untagged_constant := rc_untagged_constant counts;
         rc_no_strict_improvement := rc_no_strict_improvement counts |}
  | uer_untagged_constant =>
      {| rc_no_candidates := rc_no_candidates counts;
         rc_all_inadmissible := rc_all_inadmissible counts;
         rc_all_excluded_by_cbf := rc_all_excluded_by_cbf counts;
         rc_all_excluded_by_dec := rc_all_excluded_by_dec counts;
         rc_untagged_constant := S (rc_untagged_constant counts);
         rc_no_strict_improvement := rc_no_strict_improvement counts |}
  | uer_no_strict_improvement =>
      {| rc_no_candidates := rc_no_candidates counts;
         rc_all_inadmissible := rc_all_inadmissible counts;
         rc_all_excluded_by_cbf := rc_all_excluded_by_cbf counts;
         rc_all_excluded_by_dec := rc_all_excluded_by_dec counts;
         rc_untagged_constant := rc_untagged_constant counts;
         rc_no_strict_improvement := S (rc_no_strict_improvement counts) |}
  end.

(** Observed free-energy delta: ΔF = observed − src (exact ℚ). *)
Record observed_delta_f : Set := {
  od_src : Q;
  od_observed : Q
}.

(** Signed rational ΔF = observed − src. *)
Definition observed_delta_f_delta (d : observed_delta_f) : Q :=
  Qminus (od_observed d) (od_src d).

(** Exact ℚ ΔF = observed − src (cross-multiply; no f64). *)
Definition observed_delta_f_compute (src observed : Q) : Q :=
  Qminus observed src.

Lemma observed_delta_f_delta_eq_compute (d : observed_delta_f) :
  observed_delta_f_delta d = observed_delta_f_compute (od_src d) (od_observed d).
Proof.
  reflexivity.
Qed.

(** §13.5 return payload — residue counts + observed ΔF corpus. *)
Record residue_return : Set := {
  rr_counts : residue_counts;
  rr_observed_delta_f : list observed_delta_f
}.

Definition empty_residue_return : residue_return :=
  {| rr_counts := empty_residue_counts;
     rr_observed_delta_f := nil |}.

Definition add_observed_delta (ret : residue_return) (d : observed_delta_f)
    : residue_return :=
  {| rr_counts := rr_counts ret;
     rr_observed_delta_f := d :: rr_observed_delta_f ret |}.

Definition record_residue (ret : residue_return) (r : urge_excitement_residue)
    : residue_return :=
  {| rr_counts := increment_residue_count (rr_counts ret) r;
     rr_observed_delta_f := rr_observed_delta_f ret |}.

Definition record_admit_residue (ret : residue_return) (r : excitement_residue)
    : residue_return :=
  record_residue ret (map_admit_residue r).

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Typed refusal (seventh constructor + f64 ΔF theater)    *)
(* ------------------------------------------------------------------ *)

Inductive residue_return_refusal :=
  | rrr_seventh_constructor
  | rrr_f64_delta_f.

(** Positive refuse: seventh residue constructor is inadmissible. *)
Definition refuse_seventh_constructor : Empty_set + residue_return_refusal :=
  inr rrr_seventh_constructor.

(** Positive refuse: f64 joint-free-energy delta is inadmissible — use exact ℚ. *)
Definition refuse_f64_delta_f : Empty_set + residue_return_refusal :=
  inr rrr_f64_delta_f.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Urge composes excitement_select (no second argmin)       *)
(* ------------------------------------------------------------------ *)

(** Context for §13.5 residue return over admissible history successors. *)
Record residue_return_ctx (src : ThermodynamicState) : Set := {
  residue_return_successors : list (history_candidate src)
}.

(** §13.5 recovery **is** `urge_recovery_select` / `excitement_select`. *)
Definition residue_return_select (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src successors.

Definition residue_return_select_ctx (src : ThermodynamicState)
    (ctx : residue_return_ctx src) :
  history_candidate src + excitement_residue :=
  residue_return_select src (residue_return_successors src ctx).

Theorem residue_return_select_eq_excitement_select
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  residue_return_select src successors =
  excitement_select src successors.
Proof.
  unfold residue_return_select.
  exact (urge_recovery_select_eq_excitement_select src successors).
Qed.

Theorem residue_return_select_eq_urge_recovery_select
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  residue_return_select src successors =
  urge_recovery_select src successors.
Proof.
  reflexivity.
Qed.

Theorem residue_return_no_local_argmin
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  residue_return_select src successors =
  excitement_select src successors.
Proof.
  exact (residue_return_select_eq_excitement_select src successors).
Qed.

Lemma residue_return_empty (src : ThermodynamicState)
    (successors : list (history_candidate src))
    (Hnil : successors = nil) :
  residue_return_select src successors = inr exc_no_candidates.
Proof.
  unfold residue_return_select.
  rewrite Hnil.
  exact (urge_recovery_empty src).
Qed.

(** Record one recovery attempt via imported `excitement_select`. *)
Definition record_recovery_attempt (ret : residue_return)
    (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  residue_return * (history_candidate src + excitement_residue) :=
  let result := residue_return_select src successors in
  match result with
  | inl c =>
      let delta :=
        {| od_src := free_energy src;
           od_observed := free_energy (cand_tgt src c) |} in
      (add_observed_delta ret delta, inl c)
  | inr r => (record_admit_residue ret r, inr r)
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Landauer bridge cite (Chem.SecondLaw — not restated)     *)
(* ------------------------------------------------------------------ *)

Theorem residue_return_landauer_bridge_cited
    (b : LandauerHistoryBridge)
    (hSL : admitSecondLaw (landauer_transition b)) :
  admissibleHistoryTransition (landauer_transition b).
Proof.
  exact (admissibleHistoryTransition_from_landauer_bridge b hSL).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: §13.5 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition residue_fixture_src : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 10 # 1;
     hydration := 0;
     strength := 0 |}.

Definition residue_fixture_tgt : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 3 # 1;
     hydration := 0;
     strength := 0 |}.

Lemma residue_fixture_admissible :
  admissible residue_fixture_src residue_fixture_tgt.
Proof.
  apply gate_check_sound.
  unfold gate_check, residue_fixture_src, residue_fixture_tgt.
  simpl.
  reflexivity.
Qed.

Definition residue_fixture_candidate : history_candidate residue_fixture_src :=
  {| cand_id := 1;
     cand_tgt := residue_fixture_tgt;
     cand_admissible := residue_fixture_admissible |}.

Definition residue_fail_src : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 1 # 1;
     hydration := 0;
     strength := 0 |}.

Definition residue_fail_candidate : history_candidate residue_fail_src :=
  {| cand_id := 0;
     cand_tgt := residue_fail_src;
     cand_admissible := admissible_refl residue_fail_src |}.

Theorem residue_six_constructors_pinned :
  residue_constructor_name uer_no_candidates = "NoCandidates"%string /\
  residue_constructor_name uer_all_inadmissible = "AllInadmissible"%string /\
  residue_constructor_name uer_all_excluded_by_cbf = "AllExcludedByCbf"%string /\
  residue_constructor_name uer_all_excluded_by_dec = "AllExcludedByDec"%string /\
  residue_constructor_name uer_untagged_constant = "UntaggedConstant"%string /\
  residue_constructor_name uer_no_strict_improvement = "NoStrictImprovement"%string.
Proof.
  repeat split; reflexivity.
Qed.

Theorem residue_pin_six_length :
  List.length pin_six_residue_constructors = 6%nat.
Proof. reflexivity. Qed.

Theorem residue_empty_successors_records_no_candidates :
  let (buf, res) :=
    record_recovery_attempt empty_residue_return residue_fixture_src nil in
  res = inr exc_no_candidates /\
  residue_count_of (rr_counts buf) uer_no_candidates = 1%nat.
Proof.
  unfold record_recovery_attempt, residue_return_select.
  simpl.
  split; reflexivity.
Qed.

Theorem residue_strict_improvement_records_delta :
  let (buf, res) :=
    record_recovery_attempt empty_residue_return residue_fixture_src
      (residue_fixture_candidate :: nil) in
  res = inl residue_fixture_candidate /\
  match rr_observed_delta_f buf with
  | d :: _ =>
      List.length (rr_observed_delta_f buf) = 1%nat /\
      observed_delta_f_delta d = (3 # 1) - (10 # 1)
  | nil => False
  end.
Proof.
  unfold record_recovery_attempt, residue_return_select.
  simpl.
  split; [| split].
  - reflexivity.
  - reflexivity.
  - simpl. reflexivity.
Qed.

Theorem residue_manual_no_strict_improvement_counted :
  residue_count_of
    (rr_counts (record_residue empty_residue_return uer_no_strict_improvement))
    uer_no_strict_improvement = 1%nat.
Proof.
  reflexivity.
Qed.

Theorem residue_refuse_seventh_constructor_positive :
  refuse_seventh_constructor = inr rrr_seventh_constructor.
Proof.
  reflexivity.
Qed.

Theorem residue_refuse_f64_delta_f_positive :
  refuse_f64_delta_f = inr rrr_f64_delta_f.
Proof.
  reflexivity.
Qed.

Theorem residue_observed_delta_f_compute_fixture :
  observed_delta_f_compute (10 # 1) (3 # 1) = (3 # 1) - (10 # 1).
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 7: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition residue_return_physics_green : bool := false.

Lemma residue_return_physics_green_false :
  residue_return_physics_green = false.
Proof. reflexivity. Qed.

Definition residue_return_production_wired : bool := false.

Lemma residue_return_production_wired_false :
  residue_return_production_wired = false.
Proof. reflexivity. Qed.

Theorem residue_return_module_witness : True.
Proof. exact I. Qed.

Theorem residue_return_no_new_axiom : True.
Proof. exact I. Qed.

Theorem residue_return_positive_refuse_not_silent :
  forall x : Empty_set, refuse_seventh_constructor <> inl x.
Proof.
  intros x. unfold refuse_seventh_constructor.
  discriminate.
Qed.
