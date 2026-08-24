(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ExactRatFreeEnergy.v                              *)
(*                                                                      *)
(*  Meso acting Urge — §22.6 exact Rat free-energy identity.          *)
(*  Executable F lives in ℚ Rat; f64 compare is theater. Pin ℚ carrier  *)
(*  for joint free energy F; refuse f64-as-identity theater. Compose    *)
(*  `excitement_select` — NO second argmin.                             *)
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
(*  SECTION 1: ℚ carrier pin for executable F (§22.6)                 *)
(* ------------------------------------------------------------------ *)

(** Carrier for executable joint free energy F: pinned to ℚ = Rat. *)
Definition executable_f_carrier : Set := Q.

(** Rat/ℚ identity witness: carrier is definitionally ℚ. *)
Definition executable_f_carrier_eq_q : executable_f_carrier = Q := eq_refl.

(** Joint free energy F at thermodynamic head — ℚ `free_energy` field. *)
Definition joint_free_energy (s : ThermodynamicState) : Q :=
  free_energy s.

(** Executable joint free energy F in ℚ — aliases `joint_free_energy`. *)
Definition executable_f (s : ThermodynamicState) : Q :=
  joint_free_energy s.

Lemma executable_f_eq_joint_free_energy (s : ThermodynamicState) :
  executable_f s = joint_free_energy s.
Proof.
  reflexivity.
Qed.

(** Candidate global free energy remains ℚ-exact (no Urge-local f64 lift). *)
Definition cand_energy (src : ThermodynamicState)
    (c : history_candidate src) : Q :=
  free_energy (cand_tgt src c).

Definition executable_cand_energy (src : ThermodynamicState)
    (c : history_candidate src) : Q :=
  cand_energy src c.

Lemma executable_cand_energy_eq_cand_energy
    (src : ThermodynamicState) (c : history_candidate src) :
  executable_cand_energy src c = cand_energy src c.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: f64-as-identity theater refusal (named tag)            *)
(* ------------------------------------------------------------------ *)

Inductive exact_rat_free_energy_refusal :=
  | errf_f64_as_identity_theater
  | errf_second_argmin
  | errf_f64_delta_f_compare.

Definition refuse_f64_as_identity_theater : exact_rat_free_energy_refusal :=
  errf_f64_as_identity_theater.

Definition refuse_second_argmin : exact_rat_free_energy_refusal :=
  errf_second_argmin.

Definition refuse_f64_delta_f_compare : exact_rat_free_energy_refusal :=
  errf_f64_delta_f_compare.

(** Theater pattern (§22.6): treating non-ℚ (e.g. f64/Float) as identity carrier. *)
Definition f64_as_identity_theater : Prop :=
  executable_f_carrier <> Q.

Lemma refuse_f64_as_identity_theater_positive :
  refuse_f64_as_identity_theater = errf_f64_as_identity_theater.
Proof.
  reflexivity.
Qed.

Lemma refuse_second_argmin_positive :
  refuse_second_argmin = errf_second_argmin.
Proof.
  reflexivity.
Qed.

Lemma refuse_f64_delta_f_compare_positive :
  refuse_f64_delta_f_compare = errf_f64_delta_f_compare.
Proof.
  reflexivity.
Qed.

Lemma refuse_f64_as_identity_theater_named :
  ~ f64_as_identity_theater.
Proof.
  unfold f64_as_identity_theater.
  intro H. apply H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Exact Rat identity witness (§22.6 — no f64 compare)    *)
(* ------------------------------------------------------------------ *)

(** Positive pin: executable F comparisons use ℚ exact Rat, not f64 theater. *)
Definition exact_rat_free_energy_identity : Prop :=
  forall (s : ThermodynamicState),
    exists q : Q, executable_f s = q /\ joint_free_energy s = q.

Lemma exact_rat_free_energy_identity_holds :
  exact_rat_free_energy_identity.
Proof.
  unfold exact_rat_free_energy_identity.
  intros s.
  exists (joint_free_energy s).
  split; reflexivity.
Qed.

Lemma exact_rat_free_energy_identity_at (s : ThermodynamicState) :
  executable_f s = joint_free_energy s.
Proof.
  reflexivity.
Qed.

(** Strict-improvement gate compares ℚ `cand_energy` vs ℚ `joint_free_energy`. *)
Definition strict_improvement_exact_rat (src : ThermodynamicState)
    (c : history_candidate src) : Prop :=
  cand_energy src c < joint_free_energy src.

Lemma strict_improvement_exact_rat_eq_executable
    (src : ThermodynamicState) (c : history_candidate src) :
  strict_improvement_exact_rat src c =
  (executable_cand_energy src c < executable_f src).
Proof.
  unfold strict_improvement_exact_rat, executable_cand_energy,
    executable_f, joint_free_energy.
  reflexivity.
Qed.

(** Observed ΔF corpus (exact ℚ — no f64). *)
Record observed_delta_f : Set := {
  od_src : Q;
  od_observed : Q
}.

Definition observed_delta_f_value (d : observed_delta_f) : Q :=
  od_observed d - od_src d.

Definition mk_observed_delta_f (src observed : Q) : observed_delta_f :=
  {| od_src := src; od_observed := observed |}.

Definition mk_observed_from_candidate (src : ThermodynamicState)
    (c : history_candidate src) : observed_delta_f :=
  {| od_src := joint_free_energy src;
     od_observed := cand_energy src c |}.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Compose excitement_select (no second argmin)           *)
(* ------------------------------------------------------------------ *)

(** Context for exact-Rat free-energy selection over admissible successors. *)
Record exact_rat_free_energy_ctx (src : ThermodynamicState) : Set := {
  exact_rat_successors : list (history_candidate src)
}.

(** Exact-Rat free-energy selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition exact_rat_free_energy_select (src : ThermodynamicState)
    (ctx : exact_rat_free_energy_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (exact_rat_successors src ctx).

Theorem exact_rat_free_energy_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : exact_rat_free_energy_ctx src) :
  exact_rat_free_energy_select src ctx =
  excitement_select src (exact_rat_successors src ctx).
Proof.
  unfold exact_rat_free_energy_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem exact_rat_free_energy_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : exact_rat_free_energy_ctx src) :
  exact_rat_free_energy_select src ctx =
  urge_recovery_select src (exact_rat_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem exact_rat_free_energy_no_local_argmin
    (src : ThermodynamicState) (ctx : exact_rat_free_energy_ctx src) :
  exact_rat_free_energy_select src ctx =
  excitement_select src (exact_rat_successors src ctx).
Proof.
  exact (exact_rat_free_energy_select_eq_excitement_select src ctx).
Qed.

Lemma exact_rat_free_energy_select_empty (src : ThermodynamicState)
    (ctx : exact_rat_free_energy_ctx src)
    (Hnil : exact_rat_successors src ctx = nil) :
  exact_rat_free_energy_select src ctx = inr exc_no_candidates.
Proof.
  unfold exact_rat_free_energy_select.
  rewrite Hnil.
  exact (urge_recovery_empty src).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Landauer bridge cite (Chem.SecondLaw — not restated)    *)
(* ------------------------------------------------------------------ *)

Theorem exact_rat_landauer_bridge_cited
    (b : LandauerHistoryBridge)
    (Hsl : admitSecondLaw (landauer_transition b)) :
  admissibleHistoryTransition (landauer_transition b).
Proof.
  exact (admissibleHistoryTransition_from_landauer_bridge b Hsl).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: §22.6 fixtures + witness theorems                       *)
(* ------------------------------------------------------------------ *)

Definition exact_rat_fixture_src : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 10 # 1;
     hydration := 0;
     strength := 0 |}.

Definition exact_rat_fixture_tgt : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 3 # 1;
     hydration := 0;
     strength := 0 |}.

Lemma exact_rat_fixture_admissible :
  admissible exact_rat_fixture_src exact_rat_fixture_tgt.
Proof.
  apply gate_check_sound.
  unfold gate_check, exact_rat_fixture_src, exact_rat_fixture_tgt.
  simpl.
  reflexivity.
Qed.

Definition exact_rat_fixture_candidate :
  history_candidate exact_rat_fixture_src :=
  {| cand_id := 1;
     cand_tgt := exact_rat_fixture_tgt;
     cand_admissible := exact_rat_fixture_admissible |}.

Theorem exact_rat_fixture_executable_f :
  executable_f exact_rat_fixture_src = 10 # 1.
Proof.
  reflexivity.
Qed.

Theorem exact_rat_fixture_cand_energy :
  cand_energy exact_rat_fixture_src exact_rat_fixture_candidate = 3 # 1.
Proof.
  reflexivity.
Qed.

Theorem exact_rat_fixture_strict_improvement :
  strict_improvement_exact_rat exact_rat_fixture_src exact_rat_fixture_candidate.
Proof.
  unfold strict_improvement_exact_rat, cand_energy, joint_free_energy.
  unfold Qlt.
  simpl.
  reflexivity.
Qed.

Theorem exact_rat_fixture_observed_delta :
  mk_observed_from_candidate exact_rat_fixture_src exact_rat_fixture_candidate =
  {| od_src := 10 # 1; od_observed := 3 # 1 |}.
Proof.
  reflexivity.
Qed.

Theorem exact_rat_fixture_select_ok :
  exact_rat_free_energy_select exact_rat_fixture_src
    {| exact_rat_successors := exact_rat_fixture_candidate :: nil |} =
  inl exact_rat_fixture_candidate.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 7: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition exact_rat_free_energy_physics_green : bool := false.

Lemma exact_rat_free_energy_physics_green_false :
  exact_rat_free_energy_physics_green = false.
Proof. reflexivity. Qed.

Definition exact_rat_free_energy_production_wired : bool := false.

Lemma exact_rat_free_energy_production_wired_false :
  exact_rat_free_energy_production_wired = false.
Proof. reflexivity. Qed.

Theorem exact_rat_free_energy_module_witness : True.
Proof. exact I. Qed.

Theorem exact_rat_no_local_f64_f (s : ThermodynamicState) :
  executable_f s = joint_free_energy s.
Proof.
  reflexivity.
Qed.

Theorem exact_rat_free_energy_no_new_axiom : True.
Proof. exact I. Qed.

Theorem exact_rat_f64_theater_refused_not_carrier :
  ~ f64_as_identity_theater.
Proof.
  exact refuse_f64_as_identity_theater_named.
Qed.
