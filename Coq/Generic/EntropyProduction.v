(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Generic.EntropyProduction — the GENERIC form and its        *)
(*  entropy-production theorem over exact rationals (twin of               *)
(*  Lean/Generic/EntropyProduction.lean).                                   *)
(*                                                                          *)
(*  GENERIC (Grmela and Oettinger, Phys. Rev. E 56, 6620 and 6633 (1997))   *)
(*  writes the rate of an n-coordinate state as L dE + M dS with L          *)
(*  antisymmetric, M symmetric positive semidefinite, L dS = 0 and          *)
(*  M dE = 0. At one state the energy rate dE.(L dE + M dS) is zero and the *)
(*  entropy rate dS.(L dE + M dS) = dS.M dS is nonnegative. Coq states the  *)
(*  rates at one state; the bridge to SecondLaw takes a reservoir           *)
(*  temperature T >= 0 (free energy E - T S), a step of length h >= 0 whose *)
(*  free energy changes by h times the free-energy rate, and the mass       *)
(*  condition, which GENERIC does not supply. Zero Axiom, Parameter or      *)
(*  Admitted.                                                               *)
(* ======================================================================== *)

From Stdlib Require Import QArith Lqa Lia Setoid Morphisms Arith.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope Q_scope.

(** ** Finite sums, pairings and matrices on n coordinates *)

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S n' => qsum n' f + f n'
  end.

Definition dot (n : nat) (u v : nat -> Q) : Q := qsum n (fun i => u i * v i).
Definition mulVec (n : nat) (A : nat -> nat -> Q) (v : nat -> Q) : nat -> Q :=
  fun i => qsum n (fun j => A i j * v j).
Definition transpose (A : nat -> nat -> Q) : nat -> nat -> Q := fun i j => A j i.

Lemma qsum_ext (n : nat) (f g : nat -> Q) : (forall i, (i < n)%nat -> f i == g i) -> qsum n f == qsum n g.
Proof.
  induction n as [|n IH]; intros h; cbn [qsum]; [reflexivity |].
  rewrite IH by (intros i hi; apply h; lia). rewrite (h n) by lia. reflexivity.
Qed.

Lemma qsum_add (n : nat) (f g : nat -> Q) : qsum n (fun i => f i + g i) == qsum n f + qsum n g.
Proof. induction n as [|n IH]; cbn [qsum]; [ring | rewrite IH; ring]. Qed.

Lemma qsum_scal (n : nat) (c : Q) (f : nat -> Q) : qsum n (fun i => c * f i) == c * qsum n f.
Proof. induction n as [|n IH]; cbn [qsum]; [ring | rewrite IH; ring]. Qed.

Lemma qsum_const0 (n : nat) : qsum n (fun _ => 0) == 0.
Proof. induction n as [|n IH]; cbn [qsum]; [reflexivity | rewrite IH; ring]. Qed.

Lemma qsum_zero (n : nat) (f : nat -> Q) : (forall i, (i < n)%nat -> f i == 0) -> qsum n f == 0.
Proof. intros h. rewrite (qsum_ext n f (fun _ => 0) h). apply qsum_const0. Qed.

Lemma qsum_swap (n m : nat) (f : nat -> nat -> Q) :
  qsum n (fun i => qsum m (fun j => f i j)) == qsum m (fun j => qsum n (fun i => f i j)).
Proof.
  induction n as [|n IH]; cbn [qsum].
  - symmetry. apply qsum_zero. intros. reflexivity.
  - rewrite IH. rewrite <- qsum_add. reflexivity.
Qed.

(** u.(A w) = (A^T u).w *)
Lemma pair_transpose (n : nat) (A : nat -> nat -> Q) (u w : nat -> Q) :
  dot n u (mulVec n A w) == dot n (mulVec n (transpose A) u) w.
Proof.
  unfold dot, mulVec, transpose.
  rewrite (qsum_ext n (fun i => u i * qsum n (fun j => A i j * w j))
                      (fun i => qsum n (fun j => u i * A i j * w j)))
    by (intros i _; rewrite <- qsum_scal; apply qsum_ext; intros; ring).
  rewrite (qsum_ext n (fun i => qsum n (fun j => A j i * u j) * w i)
                      (fun i => qsum n (fun j => u j * A j i * w i)))
    by (intros i _; rewrite Qmult_comm, <- qsum_scal; apply qsum_ext; intros; ring).
  apply qsum_swap.
Qed.

(** ** The GENERIC conditions at one state *)

Record GenericAt (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) : Prop := mkGenericAt {
  antisymm : forall i j, (i < n)%nat -> (j < n)%nat -> L j i == - L i j;
  symm : forall i j, (i < n)%nat -> (j < n)%nat -> M j i == M i j;
  psd : forall v, 0 <= dot n v (mulVec n M v);
  degenL : forall i, (i < n)%nat -> mulVec n L dS i == 0;
  degenM : forall i, (i < n)%nat -> mulVec n M dE i == 0
}.

Definition genericField (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) : nat -> Q :=
  fun i => mulVec n L dE i + mulVec n M dS i.

Lemma dot_add_r (n : nat) (u v w : nat -> Q) : dot n u (fun i => v i + w i) == dot n u v + dot n u w.
Proof. unfold dot. rewrite <- qsum_add. apply qsum_ext. intros. ring. Qed.

Lemma dot_zero_l (n : nat) (u v : nat -> Q) : (forall i, (i < n)%nat -> u i == 0) -> dot n u v == 0.
Proof. intros h. unfold dot. apply qsum_zero. intros i hi. rewrite (h i hi). ring. Qed.

Lemma dot_comm (n : nat) (u v : nat -> Q) : dot n u v == dot n v u.
Proof. unfold dot. apply qsum_ext. intros. ring. Qed.

Lemma transpose_antisymm (n : nat) (L : nat -> nat -> Q) (v : nat -> Q) :
  (forall i j, (i < n)%nat -> (j < n)%nat -> L j i == - L i j) ->
  forall i, (i < n)%nat -> mulVec n (transpose L) v i == - mulVec n L v i.
Proof.
  intros hL i hi. unfold mulVec, transpose.
  rewrite (qsum_ext n (fun j => L j i * v j) (fun j => -1 * (L i j * v j)))
    by (intros j hj; rewrite (hL i j hi hj); ring).
  rewrite qsum_scal. ring.
Qed.

Lemma transpose_symm (n : nat) (M : nat -> nat -> Q) (v : nat -> Q) :
  (forall i j, (i < n)%nat -> (j < n)%nat -> M j i == M i j) ->
  forall i, (i < n)%nat -> mulVec n (transpose M) v i == mulVec n M v i.
Proof.
  intros hM i hi. unfold mulVec, transpose. apply qsum_ext. intros j hj. rewrite (hM i j hi hj). reflexivity.
Qed.

(** An antisymmetric operator pairs every vector with itself to zero. *)
Lemma antisymm_pair_self (n : nat) (L : nat -> nat -> Q) (v : nat -> Q) :
  (forall i j, (i < n)%nat -> (j < n)%nat -> L j i == - L i j) -> dot n v (mulVec n L v) == 0.
Proof.
  intros hL. assert (h := pair_transpose n L v v).
  assert (h2 : dot n (mulVec n (transpose L) v) v == - dot n (mulVec n L v) v).
  { unfold dot. rewrite (qsum_ext n (fun i => mulVec n (transpose L) v i * v i)
                                   (fun i => -1 * (mulVec n L v i * v i)))
      by (intros i hi; rewrite (transpose_antisymm n L v hL i hi); ring).
    rewrite qsum_scal. ring. }
  rewrite (dot_comm n (mulVec n L v) v) in h2. lra.
Qed.

(** Energy conservation: dE.(L dE + M dS) = 0. *)
Theorem energy_rate_zero (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) :
  GenericAt n L M dE dS -> dot n dE (genericField n L M dE dS) == 0.
Proof.
  intros h. unfold genericField. rewrite dot_add_r.
  rewrite (antisymm_pair_self n L dE (antisymm n L M dE dS h)).
  rewrite pair_transpose.
  rewrite (dot_zero_l n (mulVec n (transpose M) dE) dS)
    by (intros i hi; rewrite (transpose_symm n M dE (symm n L M dE dS h) i hi); exact (degenM n L M dE dS h i hi)).
  ring.
Qed.

(** The entropy rate is the friction pairing dS.M dS. *)
Theorem entropy_rate_eq (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) :
  GenericAt n L M dE dS -> dot n dS (genericField n L M dE dS) == dot n dS (mulVec n M dS).
Proof.
  intros h. unfold genericField. rewrite dot_add_r.
  rewrite pair_transpose.
  rewrite (dot_zero_l n (mulVec n (transpose L) dS) dE).
  - ring.
  - intros i hi. rewrite (transpose_antisymm n L dS (antisymm n L M dE dS h) i hi).
    rewrite (degenL n L M dE dS h i hi). reflexivity.
Qed.

(** Entropy production: dS.(L dE + M dS) >= 0. *)
Theorem entropy_rate_nonneg (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) :
  GenericAt n L M dE dS -> 0 <= dot n dS (genericField n L M dE dS).
Proof. intros h. rewrite (entropy_rate_eq n L M dE dS h). apply (psd n L M dE dS h). Qed.

(** At a reservoir temperature T >= 0 the free-energy rate Edot - T Sdot is not positive. *)
Theorem free_energy_rate_nonpos (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) (T : Q) :
  GenericAt n L M dE dS -> 0 <= T ->
  dot n dE (genericField n L M dE dS) - T * dot n dS (genericField n L M dE dS) <= 0.
Proof.
  intros h hT. rewrite (energy_rate_zero n L M dE dS h).
  assert (hS := entropy_rate_nonneg n L M dE dS h).
  assert (0 <= T * dot n dS (genericField n L M dE dS)) by (apply Qmult_le_0_compat; assumption).
  lra.
Qed.

(** Bridge to the second law: a step of length h >= 0 whose free energy changes by h times the GENERIC free-energy
    rate at reservoir temperature T >= 0, with the mass condition, is a transition case of SecondLaw. The
    temperature, the step and the mass condition are the hypotheses GENERIC does not supply. *)
Theorem generic_second_law (n : nat) (L M : nat -> nat -> Q) (dE dS : nat -> Q) (T step : Q)
    (old new : ThermodynamicState) :
  GenericAt n L M dE dS -> 0 <= T -> 0 <= step ->
  density new - density old <= delta_mass -> density old - density new <= delta_mass ->
  free_energy new - free_energy old ==
    step * (dot n dE (genericField n L M dE dS) - T * dot n dS (genericField n L M dE dS)) ->
  SecondLaw transition (thermodynamic old new).
Proof.
  intros h hT hstep hm1 hm2 hpsi. simpl. unfold core_admissible.
  assert (hr := free_energy_rate_nonpos n L M dE dS T h hT).
  assert (step * (dot n dE (genericField n L M dE dS) - T * dot n dS (genericField n L M dE dS)) <= 0).
  { setoid_replace (step * (dot n dE (genericField n L M dE dS) - T * dot n dS (genericField n L M dE dS)))
      with (- (step * - (dot n dE (genericField n L M dE dS) - T * dot n dS (genericField n L M dE dS)))) by ring.
    assert (0 <= step * - (dot n dE (genericField n L M dE dS) - T * dot n dS (genericField n L M dE dS)))
      by (apply Qmult_le_0_compat; lra).
    lra. }
  split; [exact hm1 | split; [exact hm2 | lra]].
Qed.
