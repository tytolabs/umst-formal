(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: Concrete/SecondLaw.v                                     *)
(*                                                                        *)
(*  Twin of Lean/Concrete/SecondLaw.lean: the cement cartridge composes   *)
(*  over the one predicate. Cement admissibility is the transition        *)
(*  instance with hydration and strength non-decreasing; a passing gate   *)
(*  is a member of the predicate; for Helmholtz states a step within the  *)
(*  mass tolerance is a member exactly when hydration does not go         *)
(*  backwards (the irreversibility of hydration, derived).                *)
(* ===================================================================== *)

From Stdlib Require Import QArith Lqa.
Require Import UMSTFormal.Concrete.Gate UMSTFormal.Concrete.Helmholtz UMSTFormal.Process.

Open Scope Q_scope.

(** Cement admissibility is the transition instance of the second law with the constitutive order constraints. *)
Theorem admissible_iff_secondLaw (old new_ : ThermodynamicState) :
  admissible old new_ <->
    SecondLaw transition (thermodynamic old new_) /\ hydration old <= hydration new_ /\ strength old <= strength new_.
Proof. simpl. unfold admissible, core_admissible. tauto. Qed.

(** A step the runtime gate passes is a member of the second-law predicate. *)
Theorem gate_check_secondLaw (old new_ : ThermodynamicState) :
  gate_check old new_ = true -> SecondLaw transition (thermodynamic old new_).
Proof. intro h. apply admissible_iff_secondLaw. apply gate_check_correct. exact h. Qed.

(** Hydration is irreversible by the second law: for Helmholtz states within the mass tolerance, a step is a member
    of the predicate exactly when hydration does not go backwards. *)
Theorem helmholtz_secondLaw_iff (old new_ : ThermodynamicState) :
  helmholtz_state old -> helmholtz_state new_ ->
  density new_ - density old <= delta_mass -> density old - density new_ <= delta_mass ->
  (SecondLaw transition (thermodynamic old new_) <-> hydration old <= hydration new_).
Proof.
  unfold helmholtz_state, helmholtz, Q_hyd. intros ho hn m1 m2. simpl. unfold core_admissible.
  rewrite ho, hn. split.
  - intros [_ [_ h]]. lra.
  - intro h. split; [exact m1 | split; [exact m2 | lra]].
Qed.
