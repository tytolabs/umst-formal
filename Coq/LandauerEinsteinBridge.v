(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: LandauerEinsteinBridge.v                              *)
(*                                                                      *)
(*  Mathematical content (standalone artifact):                         *)
(*                                                                      *)
(*    **Proved** (SI literals k_B, c, ln 2 as Definitions):             *)
(*    algebraic consequences of taking the Landauer dissipation scale   *)
(*    [k_B T ln 2] (energy) together with special-relativistic           *)
(*    mass–energy [E = m c^2], yielding                                 *)
(*                                                                      *)
(*           m_eq(T) = (k_B T ln 2) / c^2 .                             *)
(*                                                                      *)
(*    **Outside the theorems of this module:** identifying the above    *)
(*    quantity with additional physical interpretations (e.g. measured  *)
(*    gravitational coupling of “information” as a separate substance   *)
(*    hypothesis) is not derived here.  See PROOF-STATUS.md.            *)
(*                                                                      *)
(*    Lean 4 (`Lean/LandauerEinsteinBridge.lean`) uses exact SI values   *)
(*    for k_B and c, [Real.log 2] for ln 2, and proves coarse and tight *)
(*    numeric brackets at T = 300 K (tight bracket from Mathlib         *)
(*    [log_two_near_10]).                                               *)
(*                                                                      *)
(*  P0 lane A: [kB_SI], [c_SI] via Q2R rationals; [ln2] := ln 2.       *)
(*  ZERO Parameter / Axiom in this module.                              *)
(* ================================================================== *)

From Stdlib Require Import Reals Lra Field.
From Stdlib Require Import Rpower.
From Stdlib Require Import QArith Qreals.
From Stdlib Require Import ZArith.

Open Scope R_scope.

Definition kB_SI : R :=
  Q2R (inject_Z 1380649 / inject_Z (Z.pow 10 29)).

Definition c_SI : R := Q2R (inject_Z 299792458).

Definition ln2 : R := ln 2.

Lemma inj_Q2R_zero : 0%R = Q2R 0%Q.
Proof.
  symmetry.
  unfold Q2R.
  simpl.
  field.
Qed.

Lemma kB_SI_pos : 0 < kB_SI.
Proof.
  unfold kB_SI.
  rewrite inj_Q2R_zero.
  apply Qlt_Rlt.
  unfold Qlt; simpl; repeat (split; auto with zarith).
Qed.

Lemma c_SI_pos : 0 < c_SI.
Proof.
  unfold c_SI.
  rewrite inj_Q2R_zero.
  apply Qlt_Rlt.
  unfold Qlt; simpl; repeat (split; auto with zarith).
Qed.

Lemma ln2_pos : 0 < ln2.
Proof.
  unfold ln2.
  apply Rlt_trans with (r2 := /2).
  - lra.
  - apply ln_lt_2.
Qed.

(* ------------------------------------------------------------------ *)
(*  Definitions and proved lemmas                                      *)
(* ------------------------------------------------------------------ *)

Definition E_Landauer_bit (T : R) : R :=
  kB_SI * T * ln2.

Definition m_mass_equivalent (T : R) : R :=
  E_Landauer_bit T / (c_SI * c_SI).

Lemma c_SI_sq_pos : 0 < c_SI * c_SI.
Proof.
  apply Rmult_lt_0_compat; apply c_SI_pos.
Qed.

Lemma c_SI_sq_nonzero : c_SI * c_SI <> 0.
Proof.
  assert (H : 0 < c_SI * c_SI); [apply c_SI_sq_pos | lra].
Qed.

Lemma E_Landauer_bit_pos (T : R) :
  0 < T -> 0 < E_Landauer_bit T.
Proof.
  intros HT.
  unfold E_Landauer_bit.
  replace (kB_SI * T * ln2) with ((kB_SI * T) * ln2) by ring.
  apply Rmult_lt_0_compat.
  + apply Rmult_lt_0_compat; [apply kB_SI_pos | exact HT].
  + apply ln2_pos.
Qed.

Lemma m_mass_equivalent_pos (T : R) :
  0 < T -> 0 < m_mass_equivalent T.
Proof.
  intros HT.
  unfold m_mass_equivalent.
  exact (Rdiv_lt_0_compat (E_Landauer_bit T) (c_SI * c_SI)
           (E_Landauer_bit_pos T HT) c_SI_sq_pos).
Qed.

(** Scaling: m(a·T) = a·m(T) for fixed SI constants. *)
Lemma m_mass_equivalent_linear (T1 T2 a : R) :
  0 < a ->
  T2 = a * T1 ->
  m_mass_equivalent T2 = a * m_mass_equivalent T1.
Proof.
  intros _ Heq.
  unfold m_mass_equivalent, E_Landauer_bit, Rdiv.
  subst T2.
  replace (kB_SI * (a * T1) * ln2) with (a * (kB_SI * T1 * ln2)) by ring.
  rewrite Rmult_assoc.
  reflexivity.
Qed.
