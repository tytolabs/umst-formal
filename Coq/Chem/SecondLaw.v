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
