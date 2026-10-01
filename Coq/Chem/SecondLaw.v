(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/SecondLaw.v                                       *)
(*                                                                      *)
(*  Meso/acting chemistry fiber — second-law accounting via Landauer   *)
(*  lift.  Imports only existing UMSTFormal modules; ZERO new axioms.    *)
(* ================================================================== *)

From Stdlib Require Import Reals Lra.
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

(** The entropy drop of an update's state distribution (nats). *)
Definition assemblageEntropyDrop (t : ThermochemicalTransition) : R := shannon (tcPrior t) - shannon (tcPost t).

(* ------------------------------------------------------------------ *)
(*  The Landauer refinement floor is the second law                     *)
(* ------------------------------------------------------------------ *)

(** Landauer work floor for an entropy drop at bath temperature [T]. *)
Definition refinementWorkFloor (entropyDrop T : R) : R := T * entropyDrop.

(** Dissipated work meets the floor for the update's entropy drop. *)
Definition refinementWorkAccounted (t : ThermochemicalTransition) : Prop :=
  refinementWorkFloor (assemblageEntropyDrop t) (bathTemp (tcBath t)) <= tcWork t.

(** The floor is the entropy clause of the second law: at a positive bath temperature, T dS <= W exactly when
    dS <= W / T. *)
Theorem refinementWorkAccounted_iff (t : ThermochemicalTransition) :
  refinementWorkAccounted t <-> assemblageEntropyDrop t <= tcWork t / bathTemp (tcBath t).
Proof.
  unfold refinementWorkAccounted, refinementWorkFloor.
  pose proof (bathTemp_pos (tcBath t)) as hT. pose proof (Rgt_not_eq _ _ hT) as hT0.
  split; intro h.
  - apply (Rmult_le_reg_r (bathTemp (tcBath t))); [exact hT |]. unfold Rdiv.
    rewrite Rmult_assoc, (Rinv_l _ hT0), Rmult_1_r, Rmult_comm. exact h.
  - apply Rmult_le_compat_r with (r := bathTemp (tcBath t)) in h; [| exact (Rlt_le _ _ hT)]. unfold Rdiv in h.
    rewrite Rmult_assoc, (Rinv_l _ hT0), Rmult_1_r in h. rewrite Rmult_comm. exact h.
Qed.

(** The refinement floor is the chemical second law: a coherent update obeys it exactly when its dissipated work
    meets the Landauer floor of its entropy drop. *)
Theorem chemSecondLaw_iff_accounted (t : ThermochemicalTransition) :
  chemSecondLaw t <-> structurallyCoherent t /\ refinementWorkAccounted t.
Proof. rewrite chemSecondLaw_iff, refinementWorkAccounted_iff. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Bridge: a physical binary erasure realises an assemblage update     *)
(* ------------------------------------------------------------------ *)

(** Physical realisation of a binary assemblage erasure (uniform to Dirac). *)
Record PhysicalChemBridge : Type := mkPhysicalChemBridge {
  pcProc : ErasureProcess;
  pcTransition : ThermochemicalTransition;
  pcBathEq : tcBath pcTransition = erasureBath pcProc;
  pcWorkEq : tcWork pcTransition = work pcProc;
  pcPriorEq : tcPrior pcTransition = asProbDist uniform2;
  pcPostEq : tcPost pcTransition = asProbDist dirac0;
  pcCoherent : structurallyCoherent pcTransition
}.

(** The erase instance of the second law discharges the entropy clause of the chemical second law. *)
Theorem chem_entropy_bound_from_physical (b : PhysicalChemBridge) :
  eraseSecondLaw (pcProc b) uniform2 ->
  assemblageEntropyDrop (pcTransition b) <= tcWork (pcTransition b) / bathTemp (tcBath (pcTransition b)).
Proof.
  intro h. unfold assemblageEntropyDrop.
  rewrite (pcPriorEq b), (pcPostEq b), (pcWorkEq b), (pcBathEq b), !shannon_asProbDist. exact h.
Qed.

(** Landauer bound on the dissipated work of a physically bridged assemblage erasure. *)
Theorem refinementLandauerBound (b : PhysicalChemBridge) :
  eraseSecondLaw (pcProc b) uniform2 -> bathTemp (tcBath (pcTransition b)) * ln 2 <= tcWork (pcTransition b).
Proof. intro h. rewrite (pcBathEq b), (pcWorkEq b). exact (landauerBound (pcProc b) h). Qed.

(** A physically bridged coherent update obeys the chemical second law. *)
Theorem chemSecondLaw_from_physical (b : PhysicalChemBridge) :
  eraseSecondLaw (pcProc b) uniform2 -> chemSecondLaw (pcTransition b).
Proof.
  intro h. apply chemSecondLaw_iff. split; [exact (pcCoherent b) |].
  exact (chem_entropy_bound_from_physical b h).
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture: the coherent identity update                               *)
(* ------------------------------------------------------------------ *)

(** A coherent update of the uniform binary assemblage to itself at 300 K, dissipating nothing. *)
Definition coherentP0Transition : ThermochemicalTransition :=
  mkThermochemicalTransition (mkHeatBath 300 ltac:(lra)) (asProbDist uniform2) (asProbDist uniform2) 0 0.

Theorem coherentP0_zero_entropy_drop : assemblageEntropyDrop coherentP0Transition = 0.
Proof. unfold assemblageEntropyDrop. cbn [tcPrior tcPost coherentP0Transition]. ring. Qed.

Theorem coherentP0_structurallyCoherent : structurallyCoherent coherentP0Transition.
Proof. reflexivity. Qed.

Theorem coherentP0_chemSecondLaw : chemSecondLaw coherentP0Transition.
Proof.
  apply chemSecondLaw_iff. split; [reflexivity |].
  pose proof coherentP0_zero_entropy_drop as h. unfold assemblageEntropyDrop in h. rewrite h.
  cbn [tcWork tcBath bathTemp coherentP0Transition]. unfold Rdiv. rewrite Rmult_0_l. lra.
Qed.
