(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/Environment/EnvGibbsDuhem.v                     *)
(*                                                                      *)
(*  Meso/acting chemistry — Env coordinates covary (Gibbs–Duhem /      *)
(*  Maxwell / Debye) as sheaf interdependence, not independent floats.  *)
(*  Gibbs–Duhem probe on EnvironmentContinuum + EnvSampleSections,     *)
(*  reusing ConstantsSheaf interdependence pattern.                      *)
(*                                                                      *)
(*  Imports EnvironmentContinuum, EnvSampleSections, ConstantsSheaf;  *)
(*  ZERO new axioms.  physics_green stays false.                         *)
(* ================================================================== *)

From Coq Require Import Reals QArith List Psatz.
Require UMSTFormal.Chem.Constants.ConstantsSheaf.
Require Import UMSTFormal.Chem.Conservation.
Require Import UMSTFormal.InfoTheory.
Require Import UMSTFormal.Chem.Environment.EnvironmentContinuum.
Require Import UMSTFormal.Chem.Environment.EnvSampleSections.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Gibbs–Duhem legs (T, P, μ — not independent float pins)          *)
(* ------------------------------------------------------------------ *)

Inductive env_gibbs_duhem_leg : Type :=
  | env_leg_temperature
  | env_leg_pressure
  | env_leg_chemical_potential.

Definition env_gibbs_duhem_leg_tags : list env_gibbs_duhem_leg :=
  env_leg_temperature :: env_leg_pressure :: env_leg_chemical_potential :: nil.

Definition env_gibbs_duhem_leg_cardinality : nat := 3.

Lemma env_gibbs_duhem_leg_temperature_pressure_distinct :
  env_leg_temperature <> env_leg_pressure.
Proof. discriminate. Qed.

Lemma env_gibbs_duhem_leg_temperature_mu_distinct :
  env_leg_temperature <> env_leg_chemical_potential.
Proof. discriminate. Qed.

Lemma env_gibbs_duhem_leg_pressure_mu_distinct :
  env_leg_pressure <> env_leg_chemical_potential.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Debye square legs (T, I, ε_r → κ⁻¹ composite — not magic prefactor) *)
(* ------------------------------------------------------------------ *)

Inductive env_debye_square_leg : Type :=
  | env_leg_debye_temperature
  | env_leg_debye_ionic_strength
  | env_leg_debye_permittivity.

Definition env_debye_square_leg_tags : list env_debye_square_leg :=
  env_leg_debye_temperature ::
  env_leg_debye_ionic_strength ::
  env_leg_debye_permittivity :: nil.

Definition env_debye_square_leg_cardinality : nat := 3.

Lemma env_debye_leg_temperature_ionic_distinct :
  env_leg_debye_temperature <> env_leg_debye_ionic_strength.
Proof. discriminate. Qed.

Lemma env_debye_leg_temperature_permittivity_distinct :
  env_leg_debye_temperature <> env_leg_debye_permittivity.
Proof. discriminate. Qed.

Lemma env_debye_leg_ionic_permittivity_distinct :
  env_leg_debye_ionic_strength <> env_leg_debye_permittivity.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Maxwell commute scaffold (mixed partials of G(T,P,n) — not pins)   *)
(* ------------------------------------------------------------------ *)

Definition env_maxwell_commute_balance
  (partial_S_at_constant_P partial_V_at_constant_T : R) : Prop :=
  partial_S_at_constant_P = partial_V_at_constant_T.

Lemma env_maxwell_commute_zero :
  env_maxwell_commute_balance 0 0.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Gibbs–Duhem differential on Env thermo sections (not float bag)    *)
(* ------------------------------------------------------------------ *)

Record env_gibbs_duhem_differential := {
  egd_entropy : R;
  egd_volume : R;
  egd_delta_temperature : R;
  egd_delta_pressure : R;
  egd_delta_mu : R
}.

Definition env_gibbs_duhem_differential_holds
  (d : env_gibbs_duhem_differential) : Prop :=
  UMSTFormal.Chem.Constants.ConstantsSheaf.gibbs_duhem_balance
    (egd_entropy d) (egd_volume d)
    (egd_delta_temperature d) (egd_delta_pressure d) (egd_delta_mu d).

Definition env_gibbs_duhem_zero_differential : env_gibbs_duhem_differential :=
  {| egd_entropy := 0; egd_volume := 0;
     egd_delta_temperature := 0; egd_delta_pressure := 0;
     egd_delta_mu := 0 |}.

Lemma env_gibbs_duhem_zero_differential_holds :
  env_gibbs_duhem_differential_holds env_gibbs_duhem_zero_differential.
Proof.
  unfold env_gibbs_duhem_differential_holds, env_gibbs_duhem_zero_differential,
    UMSTFormal.Chem.Constants.ConstantsSheaf.gibbs_duhem_balance.
  simpl. lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  Env thermo coordinate sections (graph functions — not bare pins)   *)
(* ------------------------------------------------------------------ *)

Definition env_thermo_coordinate_section
  (E : environment_sheaf) (v : interact_graph_vertex) : R :=
  sheaf_thermo_continuum E v.

Definition env_neighbor_coupling_section
  (E : environment_sheaf) (v : interact_graph_vertex) : R :=
  sheaf_neighbor_coupling E v.

Definition env_thermo_at_vacuum (E : environment_sheaf) : R :=
  env_thermo_coordinate_section E vacuum_graph_vertex.

Definition env_thermo_at_contained (E : environment_sheaf) : R :=
  env_thermo_coordinate_section E contained_graph_vertex.

Definition env_thermo_at_messy (E : environment_sheaf) : R :=
  env_thermo_coordinate_section E messy_graph_vertex.

Definition env_coordinates_sections_distinct_on_fixture : Prop :=
  ess_vacuum (env_sample_sections_triple env_sample_fixture_sheaf) <>
  ess_messy (env_sample_sections_triple env_sample_fixture_sheaf).

Lemma env_coordinates_sections_distinct_on_fixture_holds :
  env_coordinates_sections_distinct_on_fixture.
Proof.
  exact env_sample_sections_fixture_triple_distinct.
Qed.

Definition refuse_independent_env_float_bag : Prop :=
  exists (E : environment_sheaf),
  vacuum_sample_section E <> messy_sample_section E.

Lemma refuse_independent_env_float_bag_holds :
  refuse_independent_env_float_bag.
Proof.
  unfold refuse_independent_env_float_bag.
  exists env_sample_fixture_sheaf.
  exact env_sample_sections_fixture_triple_distinct.
Qed.

Lemma env_gibbs_duhem_fixture_thermo_sections_positive :
  forall v, 0 < env_thermo_coordinate_section env_sample_fixture_sheaf v.
Proof.
  intros v; destruct v.
  all: unfold env_thermo_coordinate_section, env_sample_fixture_sheaf; simpl.
  all: apply Rlt_0_1.
Qed.

(* ------------------------------------------------------------------ *)
(*  Composition-weighted interdependence (reuse ConstantsSheaf pattern) *)
(* ------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Definition env_gibbs_duhem_interdependence
  (fractions coordinate_variations : list Q) : Prop :=
  UMSTFormal.Chem.Constants.ConstantsSheaf.gibbs_duhem_interdependence fractions coordinate_variations.

Definition env_debye_square_interdependence
  (legs leg_variations : list Q) : Prop :=
  env_composition_interdependence legs leg_variations.

Lemma env_gibbs_duhem_zero_coordinate_variation :
  forall (fractions : list Q),
  env_gibbs_duhem_interdependence fractions (map (fun _ => 0%Q) fractions).
Proof.
  intros fractions.
  unfold env_gibbs_duhem_interdependence.
  exact (UMSTFormal.Chem.Constants.ConstantsSheaf.gibbs_duhem_zero_variation fractions).
Qed.

Lemma env_debye_square_zero_variation :
  forall (legs : list Q),
  env_debye_square_interdependence legs (map (fun _ => 0%Q) legs).
Proof.
  intros legs.
  unfold env_debye_square_interdependence.
  exact (env_composition_zero_variation legs).
Qed.

Lemma env_gibbs_duhem_matches_constants_pattern (fractions : list Q) :
  env_gibbs_duhem_interdependence fractions (map (fun _ => 0%Q) fractions) /\
  UMSTFormal.Chem.Constants.ConstantsSheaf.gibbs_duhem_interdependence fractions (map (fun _ => 0%Q) fractions).
Proof.
  split.
  - exact (env_gibbs_duhem_zero_coordinate_variation fractions).
  - exact (UMSTFormal.Chem.Constants.ConstantsSheaf.gibbs_duhem_zero_variation fractions).
Qed.

Lemma env_debye_matches_composition_pattern (legs : list Q) :
  env_debye_square_interdependence legs (map (fun _ => 0%Q) legs) /\
  env_composition_interdependence legs (map (fun _ => 0%Q) legs).
Proof.
  split.
  - exact (env_debye_square_zero_variation legs).
  - exact (env_composition_zero_variation legs).
Qed.

(* ------------------------------------------------------------------ *)
(*  Env sheaf + sample sections coupled interdependence witness        *)
(* ------------------------------------------------------------------ *)

Definition env_gibbs_duhem_fixture_fractions : list Q :=
  1%Q :: 0%Q :: 0%Q :: 0%Q :: nil.

Definition env_debye_square_fixture_legs : list Q :=
  1%Q :: 0%Q :: 0%Q :: nil.

Definition env_gibbs_duhem_coupled_sections (E : environment_sheaf) : Prop :=
  env_sample_sections_well_typed E /\
  thermo_continuum_field_positive (sheaf_thermo_continuum E) /\
  env_gibbs_duhem_interdependence
    env_gibbs_duhem_fixture_fractions
    (map (fun _ => 0%Q) env_gibbs_duhem_fixture_fractions) /\
  env_debye_square_interdependence
    env_debye_square_fixture_legs
    (map (fun _ => 0%Q) env_debye_square_fixture_legs).

Lemma env_gibbs_duhem_fixture_coupled :
  env_gibbs_duhem_coupled_sections env_sample_fixture_sheaf.
Proof.
  unfold env_gibbs_duhem_coupled_sections.
  split.
  - exact env_sample_sections_fixture_well_typed.
  - split.
    + intros v; unfold env_sample_fixture_sheaf; destruct v; simpl; lra.
    + split.
      * exact (env_gibbs_duhem_zero_coordinate_variation env_gibbs_duhem_fixture_fractions).
      * exact (env_debye_square_zero_variation env_debye_square_fixture_legs).
Qed.

Lemma env_gibbs_duhem_fixture_sample_triple_distinct :
  ess_vacuum (env_sample_sections_triple env_sample_fixture_sheaf) <>
  ess_messy (env_sample_sections_triple env_sample_fixture_sheaf).
Proof.
  exact env_sample_sections_fixture_triple_distinct.
Qed.

(* ------------------------------------------------------------------ *)
(*  Conservation-normalized env coordinate covariation witness         *)
(* ------------------------------------------------------------------ *)

Lemma env_gibbs_duhem_conservation_normalized (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1 /\
  env_gibbs_duhem_interdependence p (map (fun _ => 0%Q) p) /\
  env_debye_square_interdependence p (map (fun _ => 0%Q) p).
Proof.
  intros Hp Hq.
  split.
  - exact (chem_joint_mass_conserved p q Hp Hq).
  - split.
    + exact (env_gibbs_duhem_zero_coordinate_variation p).
    + exact (env_debye_square_zero_variation p).
Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty fence (physics_green false — not measured env pins)         *)
(* ------------------------------------------------------------------ *)

Definition chem_env_gibbs_duhem_physics_green : bool := false.

Lemma chem_env_gibbs_duhem_physics_green_false :
  chem_env_gibbs_duhem_physics_green = false.
Proof. reflexivity. Qed.

Definition env_gibbs_duhem_production_wired : bool := false.

Lemma env_gibbs_duhem_production_wired_false :
  env_gibbs_duhem_production_wired = false.
Proof. reflexivity. Qed.

Lemma env_gibbs_duhem_module_witness : True.
Proof. exact I. Qed.
