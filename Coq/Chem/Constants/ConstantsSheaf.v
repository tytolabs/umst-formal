(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/Constants/ConstantsSheaf.v                        *)
(*                                                                      *)
(*  Meso/acting chemistry constants — T, P, μ as Interact-graph sheaf    *)
(*  sections, not floating scalar pins.  Gibbs–Duhem interdependence   *)
(*  records that section variations are constrained, not independent.    *)
(*                                                                      *)
(*  Imports Chem.SecondLaw + Chem.Conservation only; ZERO new axioms.  *)
(*  physics_green stays false — thermo witnesses remain Unwired.        *)
(* ================================================================== *)

From Stdlib Require Import Reals QArith List.
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
(*  Sheaf fields: T, P, μ as graph functions (not bare float pins)     *)
(* ------------------------------------------------------------------ *)

Definition temperature_graph_field : Type :=
  interact_graph_vertex -> R.

Definition pressure_graph_field : Type :=
  interact_graph_vertex -> R.

Definition chemical_potential_graph_field : Type :=
  interact_graph_vertex -> R.

Record constants_sheaf : Type := {
  sheaf_temperature : temperature_graph_field;
  sheaf_pressure : pressure_graph_field;
  sheaf_chemical_potential : chemical_potential_graph_field
}.

Definition temperature_field_positive (T : temperature_graph_field) : Prop :=
  forall v, 0 < T v.

Definition pressure_field_positive (P : pressure_graph_field) : Prop :=
  forall v, 0 < P v.

(** Ambient / standard convention vertices are named *sections*, not SI pins. *)
Definition ambient_graph_vertex : interact_graph_vertex := vtx_O.

Definition standard_pressure_graph_vertex : interact_graph_vertex := vtx_Ca.

Definition reference_potential_graph_vertex : interact_graph_vertex := vtx_Si.

Definition ambient_temperature_section
  (S : constants_sheaf) : R :=
  sheaf_temperature S ambient_graph_vertex.

Definition standard_pressure_section
  (S : constants_sheaf) : R :=
  sheaf_pressure S standard_pressure_graph_vertex.

Definition reference_chemical_potential_section
  (S : constants_sheaf) : R :=
  sheaf_chemical_potential S reference_potential_graph_vertex.

Definition gibbs_duhem_balance
  (entropy volume delta_temperature delta_pressure delta_mu : R) : Prop :=
  delta_mu = (- entropy) * delta_temperature + volume * delta_pressure.

Definition constants_sheaf_sections_interdependent (S : constants_sheaf) : Prop :=
  forall v,
  0 < sheaf_temperature S v ->
  0 < sheaf_pressure S v.

(* ------------------------------------------------------------------ *)
(*  Second-law bridge (Landauer at temperature sections — zero axioms) *)
(* ------------------------------------------------------------------ *)

Definition landauer_floor_at_sheaf
  (S : constants_sheaf) (v : interact_graph_vertex) : R :=
  chem_landauer_floor (sheaf_temperature S v).

Lemma constants_sheaf_landauer_floor_at_pos :
  forall (S : constants_sheaf) (v : interact_graph_vertex),
  0 < sheaf_temperature S v ->
  0 < landauer_floor_at_sheaf S v.
Proof.
  intros S v HT.
  unfold landauer_floor_at_sheaf.
  exact (chem_landauer_floor_pos (sheaf_temperature S v) HT).
Qed.

Lemma constants_sheaf_measurement_floor_zero :
  forall (S : constants_sheaf) (v : interact_graph_vertex),
  chem_measurement_floor (sheaf_temperature S v) 0 = 0.
Proof.
  intros S v.
  exact (chem_measurement_floor_zero (sheaf_temperature S v)).
Qed.

Lemma constants_sheaf_measurement_floor_scale :
  forall (S : constants_sheaf) (v : interact_graph_vertex) (k : R),
  chem_measurement_floor (sheaf_temperature S v) k =
  k * landauer_floor_at_sheaf S v.
Proof.
  intros S v k.
  unfold landauer_floor_at_sheaf.
  exact (chem_measurement_floor_scale (sheaf_temperature S v) k).
Qed.

(* ------------------------------------------------------------------ *)
(*  Gibbs–Duhem interdependence (composition-weighted mu variation)    *)
(* ------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Fixpoint dot_list (xs ys : list Q) : Q :=
  match xs with
  | nil => 0
  | x :: xs' =>
      match ys with
      | nil => 0
      | y :: ys' => x * y + dot_list xs' ys'
      end
  end.

(** At constant T,P: sum x_i dmu_i = 0 on normalized composition fractions. *)
Definition gibbs_duhem_interdependence
  (fractions potential_variations : list Q) : Prop :=
  dot_list fractions potential_variations == 0.

(* ------------------------------------------------------------------ *)
(*  Conservation bridge (composition constrains mu — zero new axioms)  *)
(* ------------------------------------------------------------------ *)

Lemma constants_sheaf_joint_mass_conserved (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1.
Proof.
  intros Hp Hq.
  exact (chem_joint_mass_conserved p q Hp Hq).
Qed.

Lemma constants_sheaf_joint_mass_product (p q : list Q) :
  sum_flat (product_joint p q) == sum_list p * sum_list q.
Proof.
  exact (chem_joint_mass_product p q).
Qed.

Lemma dot_list_zero_map :
  forall (xs : list Q), dot_list xs (map (fun _ => 0%Q) xs) == 0.
Proof.
  intros xs. induction xs as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma gibbs_duhem_zero_variation :
  forall (fractions : list Q),
  gibbs_duhem_interdependence fractions (map (fun _ => 0%Q) fractions).
Proof.
  intros fractions.
  unfold gibbs_duhem_interdependence.
  exact (dot_list_zero_map fractions).
Qed.

Lemma gibbs_duhem_conservation_normalized (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1 /\
  gibbs_duhem_interdependence p (map (fun _ => 0%Q) p).
Proof.
  intros Hp Hq.
  split.
  - exact (chem_joint_mass_conserved p q Hp Hq).
  - exact (gibbs_duhem_zero_variation p).
Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty fence (physics_green false — not measured constant pins)   *)
(* ------------------------------------------------------------------ *)

Definition chem_constants_sheaf_physics_green : bool := false.

Lemma chem_constants_sheaf_physics_green_false :
  chem_constants_sheaf_physics_green = false.
Proof. reflexivity. Qed.

Definition constants_sheaf_production_wired : bool := false.

Lemma constants_sheaf_production_wired_false :
  constants_sheaf_production_wired = false.
Proof. reflexivity. Qed.

Lemma constants_sheaf_module_witness : True.
Proof. exact I. Qed.
