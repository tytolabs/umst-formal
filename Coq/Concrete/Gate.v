(* ================================================================== *)
(*  UMSTFormal.Concrete.Gate — OPC cement cartridge.                  *)
(* ================================================================== *)

From Coq Require Import QArith.
From Coq Require Import Qfield.
From Coq Require Import Qring.
From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import ZArith.

Require Import UMSTFormal.Core.Gate.
Export UMSTFormal.Core.Gate.

Open Scope Q_scope.

Record ThermodynamicState : Set := mkState {
  density     : Q;
  free_energy : Q;
  hydration   : Q;
  strength    : Q
}.

Definition Q_hyd : Q := 450 # 1.

Definition helmholtz (alpha : Q) : Q := (-Q_hyd) * alpha.

Definition admissible (old new_ : ThermodynamicState) : Prop :=
  (density new_ - density old <= delta_mass)     /\
  (density old - density new_ <= delta_mass)     /\
  (free_energy new_ <= free_energy old)          /\
  (hydration old <= hydration new_)              /\
  (strength old <= strength new_).

Definition dissipation_nonneg (old new_ : ThermodynamicState) : Prop :=
  free_energy new_ <= free_energy old.

Definition gate_check (old new_ : ThermodynamicState) : bool :=
  Qle_bool (density new_ - density old) delta_mass     &&
  Qle_bool (density old - density new_) delta_mass     &&
  Qle_bool (free_energy new_) (free_energy old)        &&
  Qle_bool (hydration old) (hydration new_)            &&
  Qle_bool (strength old) (strength new_).

Local Lemma andb5_true (a b c d e : bool) :
  a && b && c && d && e = true ->
  a = true /\ b = true /\ c = true /\ d = true /\ e = true.
Proof.
  destruct a, b, c, d, e; simpl; intro H; try discriminate H; auto 10.
Qed.

Local Lemma andb5_intro (a b c d e : bool) :
  a = true -> b = true -> c = true -> d = true -> e = true ->
  a && b && c && d && e = true.
Proof.
  intros -> -> -> -> ->. reflexivity.
Qed.

Axiom psi_antitone : forall s1 s2 : ThermodynamicState,
  hydration s1 <= hydration s2 ->
  free_energy s2 <= free_energy s1.

Axiom fc_monotone : forall s1 s2 : ThermodynamicState,
  hydration s1 <= hydration s2 ->
  strength s1 <= strength s2.

Lemma helmholtz_antitone : forall a1 a2 : Q,
  a1 <= a2 -> helmholtz a2 <= helmholtz a1.
Proof.
  intros a1 a2 H.
  unfold helmholtz, Q_hyd.
  assert (e2 : (- (450 # 1)) * a2 == - ((450 # 1) * a2)) by field.
  assert (e1 : (- (450 # 1)) * a1 == - ((450 # 1) * a1)) by field.
  assert (Hmul : (450 # 1) * a1 <= (450 # 1) * a2).
  { rewrite (Qmult_comm (450 # 1) a1), (Qmult_comm (450 # 1) a2).
    apply Qmult_le_compat_r with (z := (450 # 1)).
    - exact H.
    - unfold Qle. simpl. lia. }
  assert (Hopp : - ((450 # 1) * a2) <= - ((450 # 1) * a1)).
  { now apply Qopp_le_compat. }
  rewrite e2, e1.
  exact Hopp.
Qed.

Lemma helmholtz_gradient : forall alpha eps : Q,
  helmholtz (alpha + eps) - helmholtz alpha == - (Q_hyd * eps).
Proof.
  intros alpha eps.
  unfold helmholtz, Q_hyd.
  ring.
Qed.

Lemma helmholtz_additive : forall a1 a2 : Q,
  helmholtz (a1 + a2) == helmholtz a1 + helmholtz a2.
Proof.
  intros a1 a2.
  unfold helmholtz, Q_hyd.
  ring.
Qed.

Theorem clausius_duhem_forward :
  forall s1 s2 : ThermodynamicState,
  hydration s1 <= hydration s2 ->
  free_energy s2 <= free_energy s1.
Proof.
  intros s1 s2 Hhyd.
  exact (psi_antitone s1 s2 Hhyd).
Qed.

Theorem strength_monotone_powers :
  forall s1 s2 : ThermodynamicState,
  hydration s1 <= hydration s2 ->
  strength s1 <= strength s2.
Proof.
  intros s1 s2 Hhyd.
  exact (fc_monotone s1 s2 Hhyd).
Qed.

Theorem forward_hydration_admissible :
  forall old new_ : ThermodynamicState,
  hydration old <= hydration new_ ->
  density new_ - density old <= delta_mass ->
  density old - density new_ <= delta_mass ->
  admissible old new_.
Proof.
  intros old new_ Hhyd Hmc1 Hmc2.
  unfold admissible.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact Hmc1.
  - exact Hmc2.
  - exact (psi_antitone old new_ Hhyd).
  - exact Hhyd.
  - exact (fc_monotone old new_ Hhyd).
Qed.

Theorem gate_check_correct :
  forall old new_ : ThermodynamicState,
  gate_check old new_ = true <-> admissible old new_.
Proof.
  intros old new_.
  unfold gate_check, admissible.
  split.
  - intro H.
    apply andb5_true in H.
    destruct H as (H1 & H2 & H3 & H4 & H5).
    refine (conj _ (conj _ (conj _ (conj _ _))));
      apply (proj1 (Qle_bool_iff _ _)); assumption.
  - intros (H1 & H2 & H3 & H4 & H5).
    apply andb5_intro;
      apply (proj2 (Qle_bool_iff _ _)); assumption.
Qed.

Corollary gate_check_sound :
  forall old new_ : ThermodynamicState,
  gate_check old new_ = true -> admissible old new_.
Proof.
  intros old new_.
  apply (proj1 (gate_check_correct old new_)).
Qed.

Corollary gate_check_complete :
  forall old new_ : ThermodynamicState,
  admissible old new_ -> gate_check old new_ = true.
Proof.
  intros old new_.
  apply (proj2 (gate_check_correct old new_)).
Qed.

Corollary gate_accepts_forward_hydration :
  forall old new_ : ThermodynamicState,
  hydration old <= hydration new_ ->
  density new_ - density old <= delta_mass ->
  density old - density new_ <= delta_mass ->
  gate_check old new_ = true.
Proof.
  intros old new_ Hhyd Hmc1 Hmc2.
  apply gate_check_complete.
  exact (forward_hydration_admissible old new_ Hhyd Hmc1 Hmc2).
Qed.

Definition admissible_N (n : nat) (old new_ : ThermodynamicState) : Prop :=
  (density new_ - density old <= inject_Z (Z.of_nat n) * delta_mass) /\
  (density old - density new_ <= inject_Z (Z.of_nat n) * delta_mass) /\
  (free_energy new_ <= free_energy old) /\
  (hydration old <= hydration new_) /\
  (strength old <= strength new_).

Lemma admissible_N_refl : forall (n : nat) (s : ThermodynamicState),
  admissible_N n s s.
Proof.
  intros n s.
  unfold admissible_N.
  repeat split.
  - ring_simplify (density s - density s).
    apply Qmult_le_0_compat.
    + destruct n; simpl; unfold inject_Z; simpl; try apply Qle_refl.
      unfold Qle. simpl. lia.
    + unfold delta_mass. unfold Qle. simpl. lia.
  - ring_simplify (density s - density s).
    apply Qmult_le_0_compat.
    + destruct n; simpl; unfold inject_Z; simpl; try apply Qle_refl.
      unfold Qle. simpl. lia.
    + unfold delta_mass. unfold Qle. simpl. lia.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply Qle_refl.
Qed.

Lemma admissible_implies_admissible_N1 : forall old new_ : ThermodynamicState,
  admissible old new_ -> admissible_N 1 old new_.
Proof.
  intros old new_ (Hmc1 & Hmc2 & Hdiss & Hhyd & Hstr).
  unfold admissible_N.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - assert (Hq : inject_Z (Z.of_nat 1) * delta_mass == delta_mass) by (simpl; ring).
    rewrite <- Hq.
    exact Hmc1.
  - assert (Hq : inject_Z (Z.of_nat 1) * delta_mass == delta_mass) by (simpl; ring).
    rewrite <- Hq.
    exact Hmc2.
  - exact Hdiss.
  - exact Hhyd.
  - exact Hstr.
Qed.
