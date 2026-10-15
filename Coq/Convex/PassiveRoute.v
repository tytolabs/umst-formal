(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ======================================================================== *)
(*  UMSTFormal.Convex.PassiveRoute — the passive route into the transition  *)
(*  case of SecondLaw (twin of Lean/Convex/PassiveRoute.lean and of the     *)
(*  passive cartridge law of Lean/ConvexPhiDissipation.lean).               *)
(*                                                                          *)
(*  A passive step supplies no power: (psi_new - psi_old) + D = 0 with the  *)
(*  mass condition of the gate. On such a step the transition case of       *)
(*  SecondLaw holds exactly when D >= 0 (passive_secondLaw_iff). Forward,   *)
(*  a convex dissipation potential phi >= 0 with phi 0 = 0 makes the power  *)
(*  D = x * dphi x non-negative (gsmCartridge_passive_secondLaw); backward, *)
(*  a SecondLaw step whose dissipation has a constitutive form bounds the   *)
(*  coefficient (dissipation_nonneg_of_secondLaw). Coq carries a potential  *)
(*  over the rationals in supporting-line form, phi with a slope dphi such  *)
(*  that phi x + dphi x * (y - x) <= phi y: convexity with a subgradient,   *)
(*  the rational twin of Lean's convex differentiable phi with its          *)
(*  derivative. Zero Axiom, Parameter or Admitted.                          *)
(* ======================================================================== *)

From Stdlib Require Import QArith Lqa.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope Q_scope.

(** Passive balance of one step dissipating [d]: the mass condition of the gate and Delta psi + d = 0. *)
Definition PassiveBalance (d : Q) (old new : ThermodynamicState) : Prop :=
  density new - density old <= delta_mass /\ density old - density new <= delta_mass /\
  (free_energy new - free_energy old) + d == 0.

(** The passive route: on a passive balance the transition case of SecondLaw holds exactly when d >= 0. *)
Theorem passive_secondLaw_iff (d : Q) (old new : ThermodynamicState) :
  PassiveBalance d old new -> (SecondLaw transition (thermodynamic old new) <-> 0 <= d).
Proof.
  intros [hm1 [hm2 hb]]. simpl. unfold core_admissible. split.
  - intros [_ [_ hd]]. lra.
  - intros hd. split; [exact hm1 | split; [exact hm2 | lra]].
Qed.

(** The released free energy psi_old - psi_new is the dissipation of a passive balance in the mass ball. *)
Theorem passiveBalance_released (old new : ThermodynamicState) :
  density new - density old <= delta_mass -> density old - density new <= delta_mass ->
  PassiveBalance (free_energy old - free_energy new) old new.
Proof. intros h1 h2. unfold PassiveBalance. split; [exact h1 | split; [exact h2 | ring]]. Qed.

(** Bounds through the passive route: a SecondLaw step whose balance names its dissipation d has d >= 0. *)
Theorem dissipation_nonneg_of_secondLaw (d : Q) (old new : ThermodynamicState) :
  SecondLaw transition (thermodynamic old new) -> (free_energy new - free_energy old) + d == 0 -> 0 <= d.
Proof.
  intros h hb. pose proof h as h'. simpl in h'. unfold core_admissible in h'. destruct h' as [hm1 [hm2 _]].
  apply (proj1 (passive_secondLaw_iff d old new (conj hm1 (conj hm2 hb)))). exact h.
Qed.

(** A step from free energy psi that dissipates d obeys the second law only with d >= 0. *)
Theorem step_dissipation_nonneg (rho rho' psi d : Q) :
  SecondLaw transition (thermodynamic (mkState rho psi 0 0) (mkState rho' (psi - d) 0 0)) -> 0 <= d.
Proof. intros h. apply (dissipation_nonneg_of_secondLaw d _ _ h). simpl. ring. Qed.

(** A passive relaxation from a stored free energy psi to the natural state dissipates psi: psi >= 0. *)
Theorem relaxation_stored_nonneg (rho rho' psi : Q) :
  SecondLaw transition (thermodynamic (mkState rho psi 0 0) (mkState rho' 0 0 0)) -> 0 <= psi.
Proof. intros h. apply (dissipation_nonneg_of_secondLaw psi _ _ h). simpl. ring. Qed.

(** Inequality form: Delta psi + d <= 0 with d >= 0 and the mass condition is a SecondLaw step. *)
Theorem passive_inequality_secondLaw (d : Q) (old new : ThermodynamicState) :
  density new - density old <= delta_mass -> density old - density new <= delta_mass ->
  0 <= d -> (free_energy new - free_energy old) + d <= 0 ->
  SecondLaw transition (thermodynamic old new).
Proof.
  intros h1 h2 hd hb.
  apply (proj2 (passive_secondLaw_iff _ old new (passiveBalance_released old new h1 h2))). lra.
Qed.

(** Refusal through the passive route: a balance Delta psi + d = 0 with d < 0 is refused. *)
Theorem passive_refused_of_neg (d : Q) (old new : ThermodynamicState) :
  (free_energy new - free_energy old) + d == 0 -> d < 0 -> ~ SecondLaw transition (thermodynamic old new).
Proof. intros hb hd h. pose proof (dissipation_nonneg_of_secondLaw d old new h hb). lra. Qed.

(* ------------------------------------------------------------------------ *)
(*  The convex dissipation potential and the passive cartridge law          *)
(* ------------------------------------------------------------------------ *)

(** A GSM dissipation potential: convex in supporting-line form, non-negative, zero at zero. *)
Record GsmDissipationPotential : Type := mkGsmDissipationPotential {
  phi : Q -> Q;
  dphi : Q -> Q;
  phi_support : forall x y, phi x + dphi x * (y - x) <= phi y;
  phi_nonneg : forall x, 0 <= phi x;
  phi_zero : phi 0 == 0
}.

(** Dissipation power at rate x: D = x * dphi x. *)
Definition dissipationPower (P : GsmDissipationPotential) (x : Q) : Q := x * dphi P x.

(** The supporting line at x through 0: phi x <= x * dphi x. *)
Theorem convex_phi_le_dissipationPower (P : GsmDissipationPotential) (x : Q) : phi P x <= dissipationPower P x.
Proof.
  unfold dissipationPower. pose proof (phi_support P x 0) as h. pose proof (phi_zero P) as hz.
  setoid_replace (dphi P x * (0 - x)) with (- (x * dphi P x)) in h by ring. lra.
Qed.

(** Non-negative dissipation from a convex, non-negative potential pinned at zero. *)
Theorem convex_phi_dissipation_nonneg (P : GsmDissipationPotential) (x : Q) : 0 <= dissipationPower P x.
Proof. apply (Qle_trans _ (phi P x)); [apply phi_nonneg | apply convex_phi_le_dissipationPower]. Qed.

(** A GSM cartridge packages a dissipation potential. *)
Record GsmCartridge : Type := mkGsmCartridge { dissip : GsmDissipationPotential }.

(** One-step passive energy balance of a cartridge: Delta psi + D = 0 with D = x * dphi x. *)
Definition PassiveGsmEnergyBalance (C : GsmCartridge) (old new : ThermodynamicState) (x : Q) : Prop :=
  PassiveBalance (dissipationPower (dissip C) x) old new.

(** Passive SecondLaw for a GSM cartridge: convexity gives D >= 0 and the passive route closes the step. *)
Theorem gsmCartridge_passive_secondLaw (C : GsmCartridge) (old new : ThermodynamicState) (x : Q) :
  PassiveGsmEnergyBalance C old new x -> SecondLaw transition (thermodynamic old new).
Proof.
  intros h. apply (proj2 (passive_secondLaw_iff _ old new h)). apply convex_phi_dissipation_nonneg.
Qed.
