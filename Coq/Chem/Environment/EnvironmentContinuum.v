(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/Environment/EnvironmentContinuum.v                *)
(*                                                                      *)
(*  Meso/acting environment continuum — vacuum / contained / messy as   *)
(*  named Interact-graph Env sheaf sections, not XOR sample-space pins. *)
(*  Env sheaf anchored in `physicalSecondLaw` via Chem.SecondLaw.        *)
(*                                                                      *)
(*  Imports Chem.SecondLaw + Chem.Conservation only; ZERO new axioms.  *)
(*  physics_green stays false — thermo witnesses remain Unwired.        *)
(* ================================================================== *)

From Stdlib Require Import Reals QArith List Psatz.
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
(*  Env sheaf fields: sample scale, thermo continuum, neighbor coupling *)
(* ------------------------------------------------------------------ *)

Definition sample_scale_graph_field : Type :=
  interact_graph_vertex -> R.

Definition thermo_continuum_graph_field : Type :=
  interact_graph_vertex -> R.

Definition neighbor_coupling_graph_field : Type :=
  interact_graph_vertex -> R.

Record environment_sheaf : Type := {
  sheaf_sample_scale : sample_scale_graph_field;
  sheaf_thermo_continuum : thermo_continuum_graph_field;
  sheaf_neighbor_coupling : neighbor_coupling_graph_field
}.

Definition thermo_continuum_field_positive (T : thermo_continuum_graph_field) : Prop :=
  forall v, 0 < T v.

Definition sample_scale_field_positive (S : sample_scale_graph_field) : Prop :=
  forall v, 0 < S v.

(** Env sheaf anchored in `physicalSecondLaw` via Chem.SecondLaw Landauer lift. *)

(* ------------------------------------------------------------------ *)
(*  Named sample-space sections (vacuum / contained / messy — not XOR) *)
(* ------------------------------------------------------------------ *)

Definition vacuum_graph_vertex : interact_graph_vertex := vtx_H.

Definition contained_graph_vertex : interact_graph_vertex := vtx_O.

Definition messy_graph_vertex : interact_graph_vertex := vtx_Ca.

Definition vacuum_sample_section
  (E : environment_sheaf) : R :=
  sheaf_sample_scale E vacuum_graph_vertex.

Definition contained_sample_section
  (E : environment_sheaf) : R :=
  sheaf_sample_scale E contained_graph_vertex.

Definition messy_sample_section
  (E : environment_sheaf) : R :=
  sheaf_sample_scale E messy_graph_vertex.

Definition vacuum_thermo_continuum_section
  (E : environment_sheaf) : R :=
  sheaf_thermo_continuum E vacuum_graph_vertex.

Definition contained_thermo_continuum_section
  (E : environment_sheaf) : R :=
  sheaf_thermo_continuum E contained_graph_vertex.

Definition messy_thermo_continuum_section
  (E : environment_sheaf) : R :=
  sheaf_thermo_continuum E messy_graph_vertex.

Lemma vacuum_contained_vertices_distinct :
  vacuum_graph_vertex <> contained_graph_vertex.
Proof. discriminate. Qed.

Lemma vacuum_messy_vertices_distinct :
  vacuum_graph_vertex <> messy_graph_vertex.
Proof. discriminate. Qed.

Lemma contained_messy_vertices_distinct :
  contained_graph_vertex <> messy_graph_vertex.
Proof. discriminate. Qed.

Definition env_sample_sections_not_xor : Prop :=
  vacuum_graph_vertex <> contained_graph_vertex /\
  vacuum_graph_vertex <> messy_graph_vertex /\
  contained_graph_vertex <> messy_graph_vertex.

Lemma env_sample_sections_not_xor_holds :
  env_sample_sections_not_xor.
Proof.
  split; [exact vacuum_contained_vertices_distinct|
          split; [exact vacuum_messy_vertices_distinct|
                  exact contained_messy_vertices_distinct]].
Qed.

Definition vacuum_does_not_close_messy : Prop :=
  exists (E : environment_sheaf),
  vacuum_sample_section E <> messy_sample_section E.

Lemma vacuum_does_not_close_messy_holds :
  vacuum_does_not_close_messy.
Proof.
  set (E :=
    {| sheaf_sample_scale := fun v =>
         match v with
         | vtx_H => 1
         | vtx_O => 2
         | vtx_Ca => 3
         | vtx_Si => 4
         end;
       sheaf_thermo_continuum := fun _ => 1;
       sheaf_neighbor_coupling := fun _ => 0 |}).
  exists E.
  unfold vacuum_sample_section, messy_sample_section,
    vacuum_graph_vertex, messy_graph_vertex.
  simpl. lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  Second-law bridge (physicalSecondLaw via Landauer — zero axioms)   *)
(* ------------------------------------------------------------------ *)

Definition landauer_floor_at_env_sheaf
  (E : environment_sheaf) (v : interact_graph_vertex) : R :=
  chem_landauer_floor (sheaf_thermo_continuum E v).

Lemma environment_sheaf_landauer_floor_at_pos :
  forall (E : environment_sheaf) (v : interact_graph_vertex),
  0 < sheaf_thermo_continuum E v ->
  0 < landauer_floor_at_env_sheaf E v.
Proof.
  intros E v HT.
  unfold landauer_floor_at_env_sheaf.
  exact (chem_landauer_floor_pos (sheaf_thermo_continuum E v) HT).
Qed.

Lemma environment_sheaf_measurement_floor_zero :
  forall (E : environment_sheaf) (v : interact_graph_vertex),
  chem_measurement_floor (sheaf_thermo_continuum E v) 0 = 0.
Proof.
  intros E v.
  exact (chem_measurement_floor_zero (sheaf_thermo_continuum E v)).
Qed.

Lemma environment_sheaf_measurement_floor_scale :
  forall (E : environment_sheaf) (v : interact_graph_vertex) (k : R),
  chem_measurement_floor (sheaf_thermo_continuum E v) k =
  k * landauer_floor_at_env_sheaf E v.
Proof.
  intros E v k.
  unfold landauer_floor_at_env_sheaf.
  exact (chem_measurement_floor_scale (sheaf_thermo_continuum E v) k).
Qed.

(* ------------------------------------------------------------------ *)
(*  Conservation bridge (composition constrains sections — zero axioms) *)
(* ------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Lemma environment_sheaf_joint_mass_conserved (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1.
Proof.
  intros Hp Hq.
  exact (chem_joint_mass_conserved p q Hp Hq).
Qed.

Lemma environment_sheaf_joint_mass_product (p q : list Q) :
  sum_flat (product_joint p q) == sum_list p * sum_list q.
Proof.
  exact (chem_joint_mass_product p q).
Qed.

Fixpoint dot_list (xs ys : list Q) : Q :=
  match xs with
  | nil => 0
  | x :: xs' =>
      match ys with
      | nil => 0
      | y :: ys' => x * y + dot_list xs' ys'
      end
  end.

Lemma dot_list_zero_map :
  forall (xs : list Q), dot_list xs (map (fun _ => 0%Q) xs) == 0.
Proof.
  intros xs. induction xs as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Definition env_composition_interdependence
  (fractions sample_variations : list Q) : Prop :=
  dot_list fractions sample_variations == 0.

Lemma env_composition_zero_variation :
  forall (fractions : list Q),
  env_composition_interdependence fractions (map (fun _ => 0%Q) fractions).
Proof.
  intros fractions.
  unfold env_composition_interdependence.
  exact (dot_list_zero_map fractions).
Qed.

Lemma env_composition_conservation_normalized (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1 /\
  env_composition_interdependence p (map (fun _ => 0%Q) p).
Proof.
  intros Hp Hq.
  split.
  - exact (chem_joint_mass_conserved p q Hp Hq).
  - exact (env_composition_zero_variation p).
Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty fence (physics_green false — not measured env pins)         *)
(* ------------------------------------------------------------------ *)

Definition chem_environment_continuum_physics_green : bool := false.

Lemma chem_environment_continuum_physics_green_false :
  chem_environment_continuum_physics_green = false.
Proof. reflexivity. Qed.

Definition environment_continuum_production_wired : bool := false.

Lemma environment_continuum_production_wired_false :
  environment_continuum_production_wired = false.
Proof. reflexivity. Qed.

Lemma environment_continuum_module_witness : True.
Proof. exact I. Qed.
