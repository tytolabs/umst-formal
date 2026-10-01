(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/SecondLaw.v                                       *)
(*                                                                      *)
(*  Meso/acting chemistry fiber — second-law accounting via Landauer   *)
(*  lift.  Imports only existing UMSTFormal modules; ZERO new axioms.    *)
(* ================================================================== *)

From Stdlib Require Import Reals.
Require Import UMSTFormal.LandauerEinsteinBridge.
Require Import UMSTFormal.MeasurementCost.

Open Scope R_scope.

(** Minimum dissipated energy per erased bit at temperature [T] (SI scale). *)
Definition chem_landauer_floor (T : R) : R := E_Landauer_bit T.

(** Landauer lower bound for a measurement gaining [MI_bits] bits. *)
Definition chem_measurement_floor (T MI_bits : R) : R :=
  measurementEnergyLowerBound T MI_bits.

Lemma chem_landauer_floor_pos (T : R) :
  0 < T -> 0 < chem_landauer_floor T.
Proof.
  intros HT.
  unfold chem_landauer_floor.
  exact (E_Landauer_bit_pos T HT).
Qed.

Lemma chem_measurement_floor_zero (T : R) :
  chem_measurement_floor T 0 = 0.
Proof.
  unfold chem_measurement_floor.
  exact (zero_info_zero_energy T).
Qed.

Lemma chem_measurement_floor_scale (T k : R) :
  chem_measurement_floor T k = k * chem_landauer_floor T.
Proof.
  unfold chem_measurement_floor, chem_landauer_floor, measurementEnergyLowerBound.
  ring.
Qed.

Lemma chem_landauer_mass_positive (T : R) :
  0 < T -> 0 < m_mass_equivalent T.
Proof.
  intros HT.
  exact (m_mass_equivalent_pos T HT).
Qed.

(* ------------------------------------------------------------------ *)
(*  The chemical second law: an instance of the one predicate           *)
(* ------------------------------------------------------------------ *)

From UMSTFormal Require Import Process.

(** A thermochemical update of an assemblage: bath, state distributions before and after, the work it
    dissipates (units of k_B times kelvin) and a structural defect scalar. *)
Record ThermochemicalTransition : Type := mkThermochemicalTransition {
  tcBath : HeatBath;
  tcPrior : ProbDist;
  tcPost : ProbDist;
  tcWork : R;
  tcDefect : R
}.

Definition structurallyCoherent (t : ThermochemicalTransition) : Prop := tcDefect t = 0.

(** The erasure that pays for a transition. *)
Definition tcErasure (t : ThermochemicalTransition) : ErasureProcess := mkErasure (tcBath t) (tcWork t).

(** The chemical second law: a coherent update whose erasure obeys the one second law on its transformation. *)
Definition chemSecondLaw (t : ThermochemicalTransition) : Prop :=
  structurallyCoherent t /\ SecondLaw (erase (tcErasure t)) (transformation (tcPrior t) (tcPost t)).

Theorem chemSecondLaw_iff (t : ThermochemicalTransition) :
  chemSecondLaw t <->
    structurallyCoherent t /\ shannon (tcPrior t) - shannon (tcPost t) <= tcWork t / bathTemp (tcBath t).
Proof. reflexivity. Qed.

(** Two coherent updates at one bath, the second starting where the first ends, compose: the whole update obeys
    the second law at the summed work. *)
Theorem chemSecondLaw_comp (t1 t2 : ThermochemicalTransition) :
  tcBath t1 = tcBath t2 -> tcPost t1 = tcPrior t2 -> chemSecondLaw t1 -> chemSecondLaw t2 ->
  SecondLaw (erase (mkErasure (tcBath t1) (tcWork t1 + tcWork t2))) (transformation (tcPrior t1) (tcPost t2)).
Proof.
  intros hb hp [_ h1] [_ h2]. unfold tcErasure in *. rewrite <- hb in h2. rewrite <- hp in h2.
  exact (SecondLaw_transformation_comp (tcBath t1) _ _ _ _ _ h1 h2).
Qed.
