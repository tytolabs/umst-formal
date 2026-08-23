(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/Environment/EnvSampleSections.v                 *)
(*                                                                      *)
(*  Meso/acting chemistry — named Env sample sections (probe layer).    *)
(*  Vacuum / contained / messy are **named sample sections** of one     *)
(*  Env sheaf on the Interact graph — a simultaneous triple, not XOR  *)
(*  worlds and not a third axiom.  Sample-probe layer on               *)
(*  EnvironmentContinuum.                                             *)
(*                                                                      *)
(*  Imports EnvironmentContinuum only; ZERO new axioms.               *)
(*  physics_green stays false — thermo witnesses remain Unwired.        *)
(* ================================================================== *)

From Stdlib Require Import Reals List Psatz.
Require Import UMSTFormal.Chem.Environment.EnvironmentContinuum.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Regime tags (named sections — not XOR regime selection)            *)
(* ------------------------------------------------------------------ *)

Inductive env_section_regime : Type :=
  | env_vacuum_section
  | env_contained_section
  | env_messy_section.

Definition environment_section_regime_tags : list env_section_regime :=
  env_vacuum_section :: env_contained_section :: env_messy_section :: nil.

Definition environment_regime_cardinality : nat := 3.

(* ------------------------------------------------------------------ *)
(*  Named sample probes (vacuum | contained | messy — not XOR)         *)
(* ------------------------------------------------------------------ *)

Definition vacuum_sample_probe (E : environment_sheaf) : R :=
  vacuum_sample_section E.

Definition contained_sample_probe (E : environment_sheaf) : R :=
  contained_sample_section E.

Definition messy_sample_probe (E : environment_sheaf) : R :=
  messy_sample_section E.

Definition sample_section_at_regime
  (r : env_section_regime) (E : environment_sheaf) : R :=
  match r with
  | env_vacuum_section => vacuum_sample_probe E
  | env_contained_section => contained_sample_probe E
  | env_messy_section => messy_sample_probe E
  end.

Definition vacuum_thermo_sample_probe (E : environment_sheaf) : R :=
  vacuum_thermo_continuum_section E.

Definition contained_thermo_sample_probe (E : environment_sheaf) : R :=
  contained_thermo_continuum_section E.

Definition messy_thermo_sample_probe (E : environment_sheaf) : R :=
  messy_thermo_continuum_section E.

(* ------------------------------------------------------------------ *)
(*  Simultaneous triple on one Env sheaf (not XOR sample-space pick)   *)
(* ------------------------------------------------------------------ *)

Record env_sample_sections := {
  ess_vacuum : R;
  ess_contained : R;
  ess_messy : R
}.

Definition env_sample_sections_triple (E : environment_sheaf) : env_sample_sections :=
  {| ess_vacuum := vacuum_sample_probe E;
     ess_contained := contained_sample_probe E;
     ess_messy := messy_sample_probe E |}.

Lemma env_sample_sections_triple_components
  (E : environment_sheaf) :
  ess_vacuum (env_sample_sections_triple E) = vacuum_sample_probe E /\
  ess_contained (env_sample_sections_triple E) = contained_sample_probe E /\
  ess_messy (env_sample_sections_triple E) = messy_sample_probe E.
Proof.
  simpl. split; [reflexivity|split; reflexivity].
Qed.

Definition env_sample_sections_well_typed (E : environment_sheaf) : Prop :=
  0 < vacuum_sample_probe E /\
  0 < contained_sample_probe E /\
  0 < messy_sample_probe E /\
  thermo_continuum_field_positive (sheaf_thermo_continuum E).

Lemma env_sample_sections_named_not_xor : env_sample_sections_not_xor.
Proof. exact env_sample_sections_not_xor_holds. Qed.

Lemma env_sample_sections_regime_vacuum_contained_distinct :
  env_vacuum_section <> env_contained_section.
Proof. discriminate. Qed.

Lemma env_sample_sections_regime_vacuum_messy_distinct :
  env_vacuum_section <> env_messy_section.
Proof. discriminate. Qed.

Lemma env_sample_sections_regime_contained_messy_distinct :
  env_contained_section <> env_messy_section.
Proof. discriminate. Qed.

Definition env_sample_sections_regime_distinct : Prop :=
  env_vacuum_section <> env_contained_section /\
  env_vacuum_section <> env_messy_section /\
  env_contained_section <> env_messy_section.

Lemma env_sample_sections_regime_distinct_holds :
  env_sample_sections_regime_distinct.
Proof.
  split; [exact env_sample_sections_regime_vacuum_contained_distinct|
          split; [exact env_sample_sections_regime_vacuum_messy_distinct|
                  exact env_sample_sections_regime_contained_messy_distinct]].
Qed.

Lemma sample_section_at_regime_matches_triple
  (E : environment_sheaf) :
  sample_section_at_regime env_vacuum_section E =
    ess_vacuum (env_sample_sections_triple E) /\
  sample_section_at_regime env_contained_section E =
    ess_contained (env_sample_sections_triple E) /\
  sample_section_at_regime env_messy_section E =
    ess_messy (env_sample_sections_triple E).
Proof.
  simpl. split; [reflexivity|split; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture sheaf: simultaneous named sample triple on one Env sheaf     *)
(* ------------------------------------------------------------------ *)

Definition env_sample_fixture_sheaf : environment_sheaf :=
  {| sheaf_sample_scale := fun v =>
       match v with
       | vtx_H => 1
       | vtx_O => 2
       | vtx_Ca => 3
       | vtx_Si => 4
       end;
     sheaf_thermo_continuum := fun _ => 1;
     sheaf_neighbor_coupling := fun _ => 0 |}.

Lemma env_sample_sections_fixture_well_typed :
  env_sample_sections_well_typed env_sample_fixture_sheaf.
Proof.
  unfold env_sample_sections_well_typed, env_sample_fixture_sheaf.
  simpl.
  repeat split; lra || (intros v; destruct v; lra).
Qed.

Lemma env_sample_sections_fixture_triple_distinct :
  ess_vacuum (env_sample_sections_triple env_sample_fixture_sheaf) <>
  ess_messy (env_sample_sections_triple env_sample_fixture_sheaf).
Proof.
  simpl.
  unfold env_sample_fixture_sheaf, env_sample_sections_triple,
    vacuum_sample_probe, messy_sample_probe,
    vacuum_sample_section, messy_sample_section,
    vacuum_graph_vertex, messy_graph_vertex.
  simpl. lra.
Qed.

Lemma env_sample_sections_fixture_witness :
  env_sample_sections_well_typed env_sample_fixture_sheaf /\
  vacuum_does_not_close_messy.
Proof.
  split.
  - exact env_sample_sections_fixture_well_typed.
  - exact vacuum_does_not_close_messy_holds.
Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty fence (physics_green false — not measured env pins)         *)
(* ------------------------------------------------------------------ *)

Definition chem_env_sample_sections_physics_green : bool := false.

Lemma chem_env_sample_sections_physics_green_false :
  chem_env_sample_sections_physics_green = false.
Proof. reflexivity. Qed.

Definition env_sample_sections_production_wired : bool := false.

Lemma env_sample_sections_production_wired_false :
  env_sample_sections_production_wired = false.
Proof. reflexivity. Qed.

Lemma env_sample_sections_module_witness : True.
Proof. exact I. Qed.
