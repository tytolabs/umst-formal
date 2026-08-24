(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/Constants/TemperatureGraph.v                      *)
(*                                                                      *)
(*  Meso/acting chemistry constants — temperature as an Interact-graph *)
(*  field T : GraphVertex -> R+, not a floating scalar pin.             *)
(*                                                                      *)
(*  Under Landauer, 1/T = dS/dU at each graph vertex; ambient         *)
(*  convention values are named *sections* of this field, not SI pins.  *)
(*                                                                      *)
(*  Imports Chem.SecondLaw + Chem.Conservation only; ZERO new axioms. *)
(*  physics_green stays false — thermo witnesses remain Unwired.        *)
(* ================================================================== *)

From Coq Require Import Reals QArith List.
Require Import UMSTFormal.Chem.SecondLaw.
Require Import UMSTFormal.Chem.Conservation.
Require Import UMSTFormal.InfoTheory.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Interact-graph carrier (design scaffold — four fixture slots)      *)
(* ------------------------------------------------------------------ *)

Inductive interact_graph_vertex : Type :=
  | vtx_H
  | vtx_O
  | vtx_Ca
  | vtx_Si.

Definition interact_graph_vertex_beq (a b : interact_graph_vertex) : bool :=
  match a, b with
  | vtx_H, vtx_H | vtx_O, vtx_O | vtx_Ca, vtx_Ca | vtx_Si, vtx_Si => true
  | _, _ => false
  end.

Lemma interact_graph_vertex_beq_true_iff :
  forall a b : interact_graph_vertex,
  interact_graph_vertex_beq a b = true <-> a = b.
Proof.
  intros a b; destruct a; destruct b; simpl; split; auto;
    try discriminate; try reflexivity.
Qed.

Lemma interact_graph_vertex_beq_refl (v : interact_graph_vertex) :
  interact_graph_vertex_beq v v = true.
Proof. destruct v; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Temperature as graph function (not a bare float constant)          *)
(* ------------------------------------------------------------------ *)

Definition temperature_graph_field : Type :=
  interact_graph_vertex -> R.

Definition temperature_field_positive (T : temperature_graph_field) : Prop :=
  forall v, 0 < T v.

Definition inverse_temperature_at
  (T : temperature_graph_field) (v : interact_graph_vertex) : R :=
  / (T v).

Definition landauer_floor_at
  (T : temperature_graph_field) (v : interact_graph_vertex) : R :=
  chem_landauer_floor (T v).

Definition measurement_floor_at
  (T : temperature_graph_field) (v : interact_graph_vertex) (mi_bits : R) : R :=
  chem_measurement_floor (T v) mi_bits.

(** Ambient convention is a *section* of the graph field, not a global pin. *)
Definition ambient_graph_vertex : interact_graph_vertex := vtx_O.

Definition ambient_temperature_section (T : temperature_graph_field) : R :=
  T ambient_graph_vertex.

(* ------------------------------------------------------------------ *)
(*  Landauer bridge (second law — zero new axioms)                     *)
(* ------------------------------------------------------------------ *)

Lemma landauer_floor_at_pos :
  forall (T : temperature_graph_field) (v : interact_graph_vertex),
  0 < T v ->
  0 < landauer_floor_at T v.
Proof.
  intros T v HT.
  unfold landauer_floor_at.
  exact (chem_landauer_floor_pos (T v) HT).
Qed.

Lemma measurement_floor_at_zero :
  forall (T : temperature_graph_field) (v : interact_graph_vertex),
  measurement_floor_at T v 0 = 0.
Proof.
  intros T v.
  unfold measurement_floor_at.
  exact (chem_measurement_floor_zero (T v)).
Qed.

Lemma measurement_floor_at_scale :
  forall (T : temperature_graph_field) (v : interact_graph_vertex) (k : R),
  measurement_floor_at T v k = k * landauer_floor_at T v.
Proof.
  intros T v k.
  unfold measurement_floor_at, landauer_floor_at.
  exact (chem_measurement_floor_scale (T v) k).
Qed.

Lemma inverse_temperature_pos :
  forall (T : temperature_graph_field) (v : interact_graph_vertex),
  0 < T v ->
  0 < inverse_temperature_at T v.
Proof.
  intros T v HT.
  unfold inverse_temperature_at.
  apply Rinv_0_lt_compat.
  exact HT.
Qed.

(* ------------------------------------------------------------------ *)
(*  Conservation bridge (composition / mass — zero new axioms)         *)
(* ------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Lemma temperature_joint_mass_conserved (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1.
Proof.
  intros Hp Hq.
  exact (chem_joint_mass_conserved p q Hp Hq).
Qed.

Lemma temperature_joint_mass_product (p q : list Q) :
  sum_flat (product_joint p q) == sum_list p * sum_list q.
Proof.
  exact (chem_joint_mass_product p q).
Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty fence (physics_green false — not a measured T pin)         *)
(* ------------------------------------------------------------------ *)

Definition chem_temperature_graph_physics_green : bool := false.

Lemma chem_temperature_graph_physics_green_false :
  chem_temperature_graph_physics_green = false.
Proof. reflexivity. Qed.

Definition temperature_graph_production_wired : bool := false.

Lemma temperature_graph_production_wired_false :
  temperature_graph_production_wired = false.
Proof. reflexivity. Qed.

Lemma temperature_graph_module_witness : True.
Proof. exact I. Qed.
