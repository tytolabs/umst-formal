(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/KleisliInteract.v                                 *)
(*                                                                      *)
(*  Meso/acting chemistry fiber — Kleisli `Interact` morphism laws.      *)
(*  Mirrors `Lean/Chem/KleisliInteract.lean` on `umst-formal/meso_acting` *)
(*  and the CHEM-L0-CAT-00 Rust scaffold (`kleisli_interact.rs`).       *)
(*                                                                      *)
(*  Algebraic Kleisli laws (identity / associativity / coherence) are  *)
(*  machine-checked.  `physics_green` stays false — thermo witnesses   *)
(*  remain Unwired until FORMAL BAR + path census.                       *)
(*                                                                      *)
(*  Imports only existing UMSTFormal modules; ZERO new axioms.           *)
(* ================================================================== *)

From Coq Require Import Arith Arith.PeanoNat Bool List Reals QArith Lia.
Require Import UMSTFormal.Chem.SecondLaw.
Require Import UMSTFormal.Chem.Conservation.
Require Import UMSTFormal.InfoTheory.

Open Scope bool_scope.
Open Scope R_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  L0 element carrier (design scaffold — four fixture slots)          *)
(* ------------------------------------------------------------------ *)

Inductive element_id : Type :=
  | elem_H
  | elem_O
  | elem_Ca
  | elem_Si.

Definition element_id_beq (a b : element_id) : bool :=
  match a, b with
  | elem_H, elem_H | elem_O, elem_O | elem_Ca, elem_Ca | elem_Si, elem_Si => true
  | _, _ => false
  end.

Lemma element_id_beq_true_iff :
  forall a b : element_id, element_id_beq a b = true <-> a = b.
Proof.
  intros a b; destruct a; destruct b; simpl; split; auto;
    try discriminate; try reflexivity.
Qed.

Lemma element_id_beq_false_iff :
  forall a b : element_id, element_id_beq a b = false <-> a <> b.
Proof.
  intros a b; destruct a; destruct b; simpl; split; auto;
    try discriminate; try (intros H; exfalso; apply H; reflexivity).
Qed.

Lemma element_id_beq_refl (e : element_id) : element_id_beq e e = true.
Proof. destruct e; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Interact step + Kleisli operators                                  *)
(* ------------------------------------------------------------------ *)

Record interact_step : Type := {
  interact_from : element_id;
  interact_to : element_id;
  interact_tag : nat
}.

Definition interact_identity (e : element_id) : interact_step :=
  {| interact_from := e; interact_to := e; interact_tag := 0 |}.

Definition interact_compose (left right : interact_step) : option interact_step :=
  if element_id_beq left.(interact_to) right.(interact_from) then
    Some {| interact_from := left.(interact_from);
            interact_to := right.(interact_to);
            interact_tag := left.(interact_tag) + right.(interact_tag) + 1 |}
  else None.

(* ------------------------------------------------------------------ *)
(*  Kleisli laws (algebraic — proved, not physics GREEN)               *)
(* ------------------------------------------------------------------ *)

Lemma kleisli_left_unit_endpoints :
  forall (f : interact_step),
  forall g, interact_compose (interact_identity f.(interact_from)) f = Some g ->
  g.(interact_from) = f.(interact_from) /\
  g.(interact_to) = f.(interact_to).
Proof.
  intros f g H.
  unfold interact_compose, interact_identity in H.
  rewrite element_id_beq_refl in H.
  inversion H; subst; split; reflexivity.
Qed.

Lemma kleisli_right_unit_endpoints :
  forall (f : interact_step),
  forall g, interact_compose f (interact_identity f.(interact_to)) = Some g ->
  g.(interact_from) = f.(interact_from) /\
  g.(interact_to) = f.(interact_to).
Proof.
  intros f g H.
  unfold interact_compose, interact_identity in H.
  rewrite element_id_beq_refl in H.
  inversion H; subst; split; reflexivity.
Qed.

Lemma kleisli_associativity :
  forall (f g h fg gh : interact_step),
  interact_to f = interact_from g ->
  interact_to g = interact_from h ->
  interact_compose f g = Some fg ->
  interact_compose g h = Some gh ->
  interact_compose fg h = interact_compose f gh.
Proof.
  intros f g h fg gh Hfg Hgh Hfg_ok Hgh_ok.
  assert (Hfgb : element_id_beq (interact_to f) (interact_from g) = true) by
    (apply element_id_beq_true_iff; exact Hfg).
  assert (Hghb : element_id_beq (interact_to g) (interact_from h) = true) by
    (apply element_id_beq_true_iff; exact Hgh).
  unfold interact_compose in *.
  rewrite Hfgb in Hfg_ok.
  rewrite Hghb in Hgh_ok.
  inversion Hfg_ok; subst fg.
  inversion Hgh_ok; subst gh.
  simpl.
  rewrite Hfgb, Hghb.
  apply f_equal.
  f_equal.
  lia.
Qed.

Lemma kleisli_coherence_units_endpoints :
  forall (f : interact_step) (g h : interact_step),
  interact_compose (interact_identity f.(interact_from)) f = Some g ->
  interact_compose f (interact_identity f.(interact_to)) = Some h ->
  g.(interact_from) = h.(interact_from) /\
  g.(interact_to) = h.(interact_to).
Proof.
  intros f g h Hleft Hright.
  pose proof (kleisli_left_unit_endpoints f g Hleft) as [Hlf Hlt].
  pose proof (kleisli_right_unit_endpoints f h Hright) as [Hrf Hrt].
  split.
  - transitivity (interact_from f); [exact Hlf | symmetry; exact Hrf].
  - transitivity (interact_to f); [exact Hlt | symmetry; exact Hrt].
Qed.

(* ------------------------------------------------------------------ *)
(*  Meso acting bridge (second law + conservation — zero new axioms)   *)
(* ------------------------------------------------------------------ *)

Local Close Scope Q_scope.

Definition chem_physics_green : bool := false.

Lemma chem_physics_green_false : chem_physics_green = false.
Proof. reflexivity. Qed.

Definition kleisli_interact_production_wired : bool := false.

Lemma kleisli_interact_production_wired_false :
  kleisli_interact_production_wired = false.
Proof. reflexivity. Qed.

Lemma interact_landauer_floor_pos (T : R) :
  0 < T -> 0 < chem_landauer_floor T.
Proof.
  intros HT.
  exact (chem_landauer_floor_pos T HT).
Qed.

Lemma interact_measurement_floor_zero (T : R) :
  chem_measurement_floor T 0 = 0.
Proof.
  exact (chem_measurement_floor_zero T).
Qed.

Local Open Scope Q_scope.

Lemma interact_joint_mass_conserved (p q : list Q) :
  species_composition p ->
  species_composition q ->
  sum_flat (product_joint p q) == 1.
Proof.
  intros Hp Hq.
  exact (chem_joint_mass_conserved p q Hp Hq).
Qed.

Lemma kleisli_interact_module_witness : True.
Proof. exact I. Qed.
