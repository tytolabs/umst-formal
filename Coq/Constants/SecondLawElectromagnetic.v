(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Constants.SecondLawElectromagnetic — four electromagnetic    *)
(*  constants bounded by the second law (twin of                            *)
(*  Lean/Constants/SecondLawElectromagnetic.lean).                          *)
(*                                                                          *)
(*  A passive step at fixed density is a transition case of SecondLaw       *)
(*  exactly when the free energy does not rise. A vacuum field relaxing     *)
(*  from 1/2 eps E^2 (or B^2/(2 mu)) to zero, and a Joule step dissipating  *)
(*  G V^2 dt (or R I^2 dt), are admitted for every field, voltage or        *)
(*  current exactly when eps >= 0, mu > 0, G >= 0, R >= 0. The exact SI    *)
(*  values of Constants/SI.v lie inside each bound. Each result is a bound, *)
(*  never a value. Zero Axiom, Parameter or Admitted.                       *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qfield Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Core.Gate UMSTFormal.Process UMSTFormal.Constants.SI.

Open Scope Q_scope.

(** A passive step of the vacuum at density [rho] from free energy [psi] to [psi']. *)
Definition passiveStep (rho psi psi' : Q) : Prior :=
  thermodynamic (mkState rho psi 0 0) (mkState rho psi' 0 0).

Lemma passiveStep_secondLaw_iff (rho psi psi' : Q) :
  SecondLaw transition (passiveStep rho psi psi') <-> psi' <= psi.
Proof.
  simpl. unfold core_admissible, delta_mass. simpl. split.
  - intros [_ [_ h]]. exact h.
  - intros h. split; [| split]; [lra | lra | exact h].
Qed.

(** Electric field energy: every relaxation from 1/2 eps E^2 to zero is admitted exactly when eps >= 0. *)
Theorem electricRelaxation_secondLaw_iff (eps : Q) :
  (forall rho E, SecondLaw transition (passiveStep rho ((1#2) * eps * (E * E)) 0)) <-> 0 <= eps.
Proof.
  split.
  - intros h. pose proof (proj1 (passiveStep_secondLaw_iff 0 _ 0) (h 0 1)) as h1. nra.
  - intros he rho E. apply passiveStep_secondLaw_iff.
    assert (0 <= E * E) by nra. nra.
Qed.

(** Magnetic field energy: for mu <> 0, every relaxation from B^2/(2 mu) to zero is admitted exactly when
    mu > 0. *)
Theorem magneticRelaxation_secondLaw_iff (mu : Q) :
  ~ mu == 0 ->
  ((forall rho B, SecondLaw transition (passiveStep rho (B * B / (2 * mu)) 0)) <-> 0 < mu).
Proof.
  intros hmu. assert (hinv : mu * (1 * 1 / (2 * mu)) == 1#2) by (field; exact hmu).
  split.
  - intros h. pose proof (proj1 (passiveStep_secondLaw_iff 0 _ 0) (h 0 1)) as h1.
    destruct (Qlt_le_dec 0 mu) as [p|n]; [exact p | exfalso].
    assert (mu * (1 * 1 / (2 * mu)) <= 0) by nra. lra.
  - intros hp rho B. apply passiveStep_secondLaw_iff.
    assert (h2 : 0 < 2 * mu) by lra.
    assert (0 <= B * B) by nra.
    unfold Qdiv. apply Qmult_le_0_compat; [exact H |].
    apply Qlt_le_weak, Qinv_lt_0_compat, h2.
Qed.

(** Conductance: every Joule step dissipating G V^2 dt (dt > 0) is admitted exactly when G >= 0. *)
Theorem conductanceDissipation_secondLaw_iff (G : Q) :
  (forall rho psi V dt, 0 < dt -> SecondLaw transition (passiveStep rho psi (psi - G * (V * V) * dt)))
  <-> 0 <= G.
Proof.
  split.
  - intros h. pose proof (proj1 (passiveStep_secondLaw_iff 0 0 _) (h 0 0 1 1 ltac:(lra))) as h1. nra.
  - intros hG rho psi V dt hdt. apply passiveStep_secondLaw_iff.
    assert (0 <= V * V) by nra. assert (0 <= G * (V * V)) by nra. nra.
Qed.

(** Resistance: every Joule step dissipating R I^2 dt (dt > 0) is admitted exactly when R >= 0. *)
Theorem resistanceDissipation_secondLaw_iff (R : Q) :
  (forall rho psi I dt, 0 < dt -> SecondLaw transition (passiveStep rho psi (psi - R * (I * I) * dt)))
  <-> 0 <= R.
Proof. exact (conductanceDissipation_secondLaw_iff R). Qed.

(** The exact SI values lie inside the bounds. *)
Theorem vacuumPermittivity_relaxation_secondLaw (rho E : Q) :
  SecondLaw transition (passiveStep rho ((1#2) * vacuumPermittivity * (E * E)) 0).
Proof.
  apply (proj2 (electricRelaxation_secondLaw_iff vacuumPermittivity)).
  apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem vacuumPermeability_relaxation_secondLaw (rho B : Q) :
  SecondLaw transition (passiveStep rho (B * B / (2 * vacuumPermeability)) 0).
Proof.
  assert (hp : 0 < vacuumPermeability).
  { apply Qnot_le_lt. intros h. apply Qle_bool_iff in h. vm_compute in h. discriminate h. }
  apply (proj2 (magneticRelaxation_secondLaw_iff vacuumPermeability ltac:(intros e; rewrite e in hp; lra)) hp).
Qed.

Theorem conductanceQuantum_dissipation_secondLaw (rho psi V dt : Q) :
  0 < dt -> SecondLaw transition (passiveStep rho psi (psi - conductanceQuantum * (V * V) * dt)).
Proof.
  apply (proj2 (conductanceDissipation_secondLaw_iff conductanceQuantum)).
  apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem vonKlitzing_dissipation_secondLaw (rho psi I dt : Q) :
  0 < dt -> SecondLaw transition (passiveStep rho psi (psi - vonKlitzing * (I * I) * dt)).
Proof.
  apply (proj2 (resistanceDissipation_secondLaw_iff vonKlitzing)).
  apply Qle_bool_iff. vm_compute. reflexivity.
Qed.
