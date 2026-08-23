(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/Conservation.v                                    *)
(*                                                                      *)
(*  Meso/acting chemistry fiber — composition / mass conservation via  *)
(*  InfoTheory joint lifts.  ZERO new axioms.                          *)
(* ================================================================== *)

From Coq Require Import QArith Qring List.
Import ListNotations.

Require Import UMSTFormal.InfoTheory.

Open Scope Q_scope.

(** Normalized species composition (mass fractions summing to unity). *)
Definition species_composition (masses : list Q) : Prop :=
  sum_list masses == 1.

Lemma chem_joint_mass_conserved (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1.
Proof.
  intros Hp Hq.
  unfold species_composition in Hp, Hq.
  exact (joint_mass_one p q Hp Hq).
Qed.

Lemma chem_joint_mass_product (p q : list Q) :
  sum_flat (product_joint p q) == sum_list p * sum_list q.
Proof.
  exact (joint_mass_product p q).
Qed.

Lemma chem_first_marginal_normalized (p q : list Q) :
  species_composition q ->
  Forall2 Qeq (marginal_first (product_joint p q)) p.
Proof.
  intros Hq.
  unfold species_composition in Hq.
  exact (marginal_first_product_normalized p q Hq).
Qed.

Lemma chem_second_marginal_normalized (p q : list Q) :
  p <> [] ->
  species_composition p ->
  Forall2 Qeq (marginal_second (product_joint p q)) q.
Proof.
  intros Hne Hp.
  unfold species_composition in Hp.
  exact (marginal_second_product_normalized p q Hne Hp).
Qed.
