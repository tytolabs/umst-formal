(* ================================================================== *)
(*  UMST-Formal: InfoTheory.v                                           *)
(*                                                                      *)
(*  Finite product joint on lists of rationals (Q). Mirrors the       *)
(*  algebraic content of @Lean/InfoTheory.lean@ (marginals of the       *)
(*  independent product) and @Haskell/InfoTheory.hs@ (QC layer).      *)
(*                                                                      *)
(*  Rational identities use setoid equality [==] ([Qeq]).             *)
(*  List-valued results use [Forall2 Qeq] pointwise.                  *)
(*                                                                      *)
(*  Second marginal: [marginal_second] = column sums (fold of rows).    *)
(* ================================================================== *)

From Stdlib Require Import QArith Qring List Lia.
Import ListNotations.

Open Scope Q_scope.

Fixpoint sum_list (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint map_mul_row (x : Q) (row : list Q) : list Q :=
  match row with
  | [] => []
  | y :: ys => (x * y) :: map_mul_row x ys
  end.

Lemma sum_map_mul_distr_l (x : Q) (l : list Q) :
  sum_list (map_mul_row x l) == x * sum_list l.
Proof.
  induction l as [|a la IH]; simpl.
  - symmetry. apply Qmult_0_r.
  - rewrite IH. symmetry. apply Qmult_plus_distr_r.
Qed.

Fixpoint product_joint (p q : list Q) : list (list Q) :=
  match p with
  | [] => []
  | ph :: pt => map_mul_row ph q :: product_joint pt q
  end.

Fixpoint marginal_first (j : list (list Q)) : list Q :=
  match j with
  | [] => []
  | row :: rest => sum_list row :: marginal_first rest
  end.

Fixpoint pointwise_add (a b : list Q) : list Q :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | ha :: ta, hb :: tb => (ha + hb) :: pointwise_add ta tb
  end.

Definition marginal_second (j : list (list Q)) : list Q :=
  match j with
  | [] => []
  | r :: rs => List.fold_left pointwise_add rs r
  end.

Fixpoint sum_flat (j : list (list Q)) : Q :=
  match j with
  | [] => 0
  | row :: rest => sum_list row + sum_flat rest
  end.

(* ------------------------------------------------------------------ *)
(*  Flat mass: product of marginal sums                               *)
(* ------------------------------------------------------------------ *)

Theorem joint_mass_product (p q : list Q) :
  sum_flat (product_joint p q) == sum_list p * sum_list q.
Proof.
  induction p as [|ph pt IH]; simpl.
  - rewrite Qmult_0_l. reflexivity.
  - rewrite IH. rewrite sum_map_mul_distr_l. ring.
Qed.

Corollary joint_mass_one (p q : list Q) :
  sum_list p == 1 ->
  sum_list q == 1 ->
  sum_flat (product_joint p q) == 1.
Proof.
  intros Hp Hq. rewrite joint_mass_product. rewrite Hp, Hq. ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  First marginal                                                      *)
(* ------------------------------------------------------------------ *)

Theorem marginal_first_product (p q : list Q) :
  Forall2 Qeq (marginal_first (product_joint p q))
    (map (fun pi : Q => pi * sum_list q) p).
Proof.
  induction p as [|ph pt IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + apply sum_map_mul_distr_l.
    + exact IH.
Qed.

Corollary marginal_first_product_normalized (p q : list Q) :
  sum_list q == 1 ->
  Forall2 Qeq (marginal_first (product_joint p q)) p.
Proof.
  intros Hq. induction p as [|ph pt IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + rewrite sum_map_mul_distr_l. rewrite Hq. rewrite Qmult_1_r. reflexivity.
    + apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(*  Forall2 helpers                                                     *)
(* ------------------------------------------------------------------ *)

Lemma Forall2_Qeq_refl (l : list Q) : Forall2 Qeq l l.
Proof. induction l; [apply Forall2_nil | apply Forall2_cons; [apply Qeq_refl | exact IHl]]. Qed.

Lemma Forall2_Qeq_sym (l1 l2 : list Q) :
  Forall2 Qeq l1 l2 -> Forall2 Qeq l2 l1.
Proof.
  induction 1; [apply Forall2_nil | apply Forall2_cons; auto using Qeq_sym].
Qed.

Lemma Forall2_Qeq_trans (l1 l2 l3 : list Q) :
  Forall2 Qeq l1 l2 -> Forall2 Qeq l2 l3 -> Forall2 Qeq l1 l3.
Proof.
  intros H12 H23.
  revert l3 H23.
  induction H12; intros l3 H23; inversion H23; subst;
    [apply Forall2_nil | apply Forall2_cons]; eauto using Qeq_trans.
Qed.

Lemma Forall2_length (l1 l2 : list Q) :
  Forall2 Qeq l1 l2 -> length l1 = length l2.
Proof. induction 1; simpl; auto. Qed.

Lemma pointwise_add_assoc (a b c : list Q) :
  length a = length b ->
  length b = length c ->
  Forall2 Qeq (pointwise_add (pointwise_add a b) c)
    (pointwise_add a (pointwise_add b c)).
Proof.
  intros Hab Hbc.
  revert a b Hab Hbc.
  induction c as [|hc tc IHc]; intros b a Hab Hbc;
    destruct a as [|ha ta]; destruct b as [|hb tb]; try discriminate; simpl in *.
  - apply Forall2_nil.
  - injection Hab as Hab'. injection Hbc as Hbc'.
    specialize (IHc tb ta Hab' Hbc').
    apply Forall2_cons; [|exact IHc]. ring.
Qed.

Lemma length_pointwise_add (a b : list Q) :
  length a = length b -> length (pointwise_add a b) = length a.
Proof.
  intros H; revert b H.
  induction a; intros [|b]; simpl in *; try discriminate; auto.
Qed.

Lemma pointwise_add_compat_l (R0 : list Q) (l1 l2 : list Q) :
  Forall2 Qeq l1 l2 ->
  Forall2 Qeq (pointwise_add R0 l1) (pointwise_add R0 l2).
Proof.
  intros H.
  revert R0.
  induction H as [|x y l l' Hxy Hll IH]; intro R0; simpl.
  - destruct R0; apply Forall2_Qeq_refl.
  - destruct R0 as [|hr rt]; simpl.
    + apply Forall2_cons; [|apply (IH [])]. exact Hxy.
    + apply Forall2_cons; [|apply (IH rt)]. rewrite Hxy. ring.
Qed.

Lemma product_joint_row_lengths (p q : list Q) (row : list Q) :
  In row (product_joint p q) -> length row = length q.
Proof.
  intros Hin.
  induction p as [|ph pt IH]; simpl in *; [contradiction|].
  destruct Hin as [<-|Hin'].
  - clear IH. induction q as [|a qt IHq]; simpl; [reflexivity|f_equal; apply IHq].
  - apply IH, Hin'.
Qed.

Lemma length_fold_pointwise (acc : list Q) (rows : list (list Q)) :
  (forall row : list Q, In row rows -> length row = length acc) ->
  length (List.fold_left pointwise_add rows acc) = length acc.
Proof.
  revert acc.
  induction rows as [|r0 rs IH]; simpl; intros acc H.
  - reflexivity.
  - assert (Hr0 : length r0 = length acc) by (apply H, in_eq).
    assert (Hlenp : length (pointwise_add acc r0) = length acc)
      by (apply length_pointwise_add; auto).
    transitivity (length (List.fold_left pointwise_add rs (pointwise_add acc r0))).
    { reflexivity. }
    transitivity (length (pointwise_add acc r0)).
    + apply IH. intros row Hin.
      transitivity (length acc).
      * apply H, in_cons, Hin.
      * symmetry; exact Hlenp.
    + exact Hlenp.
Qed.

Lemma fold_pointwise_commute : forall (rs : list (list Q)) (Racc racc : list Q),
  length Racc = length racc ->
  (forall row : list Q, In row rs -> length row = length Racc) ->
  Forall2 Qeq (List.fold_left pointwise_add rs (pointwise_add Racc racc))
    (pointwise_add Racc (List.fold_left pointwise_add rs racc)).
Proof.
  induction rs as [|r1 rs IH]; simpl.
  + intros; apply Forall2_Qeq_refl.
  + intros Racc racc Hlen Hdim.
  - assert (Hr1 : length r1 = length Racc) by (apply Hdim, in_eq).
    assert (Hdim' : forall row : list Q, In row rs -> length row = length Racc).
    { intros row Hin'; apply Hdim, in_cons, Hin'. }
    assert (Hlen_pr : length (pointwise_add Racc racc) = length r1).
    { transitivity (length Racc).
      - apply length_pointwise_add, Hlen.
      - symmetry; exact Hr1. }
    assert (Hdim'' : forall row : list Q, In row rs -> length row = length (pointwise_add Racc racc)).
    { intros row Hin. transitivity (length r1).
      - transitivity (length Racc); [apply Hdim', Hin|symmetry; exact Hr1].
      - symmetry; exact Hlen_pr. }
    assert (IH1 := IH (pointwise_add Racc racc) r1 Hlen_pr Hdim'').
    assert (Hlen2 : length racc = length r1).
    { transitivity (length Racc).
      - symmetry; exact Hlen.
      - symmetry; exact Hr1. }
    assert (Hdim2 : forall row : list Q, In row rs -> length row = length racc).
    { intros row Hin. transitivity (length Racc); [apply Hdim', Hin|exact Hlen]. }
    assert (IH2 := IH racc r1 Hlen2 Hdim2).
    assert (Hfl : length (List.fold_left pointwise_add rs r1) = length r1).
    { apply length_fold_pointwise.
      intros row Hin. transitivity (length Racc).
      - apply Hdim', Hin.
      - symmetry; exact Hr1. }
    eapply Forall2_Qeq_trans; [exact IH1|].
    eapply Forall2_Qeq_trans.
    * apply pointwise_add_assoc.
      -- exact Hlen.
      -- transitivity (length r1); [exact Hlen2|symmetry; exact Hfl].
    * apply pointwise_add_compat_l, Forall2_Qeq_sym, IH2.
Qed.

Lemma marginal_second_fold (R : list Q) (rows : list (list Q)) :
  (forall row : list Q, In row rows -> length row = length R) ->
  Forall2 Qeq (List.fold_left pointwise_add rows R)
    (pointwise_add R (marginal_second rows)).
Proof.
  intros Hdim. destruct rows as [|r rs]; simpl.
  - destruct R; simpl; apply Forall2_Qeq_refl || apply Forall2_nil.
  - simpl marginal_second. apply fold_pointwise_commute.
    + symmetry; apply Hdim, in_eq.
    + intros row Hin. apply Hdim, in_cons, Hin.
Qed.

Lemma map_mul_row_as_map (ph : Q) (q : list Q) :
  Forall2 Qeq (map_mul_row ph q) (map (fun qk : Q => qk * ph) q).
Proof.
  induction q as [|qh qt IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons; [|exact IH]. apply Qmult_comm.
Qed.

Lemma pointwise_add_map_mul (ph S : Q) (q : list Q) :
  Forall2 Qeq
    (pointwise_add (map_mul_row ph q) (map (fun qk : Q => qk * S) q))
    (map (fun qk : Q => qk * (ph + S)) q).
Proof.
  induction q as [|qh qt IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons; [|exact IH]. ring.
Qed.

Lemma Forall2_map_scale_Qeq (l : list Q) (c1 c2 : Q) :
  c1 == c2 ->
  Forall2 Qeq (map (fun qk : Q => qk * c1) l) (map (fun qk : Q => qk * c2) l).
Proof.
  intros Hc; induction l as [|qh qt IHl]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons; [|exact IHl]. rewrite Hc. ring.
Qed.

Theorem marginal_second_product (ph : Q) (pt q : list Q) :
  Forall2 Qeq (marginal_second (product_joint (ph :: pt) q))
    (map (fun qk : Q => qk * sum_list (ph :: pt)) q).
Proof.
  revert ph q; induction pt as [|a pt' IH]; intros ph q; simpl.
  - unfold marginal_second; simpl.
    eapply Forall2_Qeq_trans.
    + apply map_mul_row_as_map.
    + induction q as [|qh qt IHq]; simpl.
      * apply Forall2_nil.
      * apply Forall2_cons; [|exact IHq]. ring.
  -     assert (Hrows :
      forall row : list Q,
        In row (product_joint (a :: pt') q) -> length row = length q).
    { intros row0 Hin0.
      exact (product_joint_row_lengths (a :: pt') q row0 Hin0). }
    assert (Hdimrows :
      forall row0 : list Q,
        In row0 (product_joint (a :: pt') q) ->
        length row0 = length (map_mul_row ph q)).
    { intros row0 Hin0. transitivity (length q).
      - apply Hrows, Hin0.
      - clear - ph q. induction q; simpl; auto. }
    eapply Forall2_Qeq_trans.
    + exact (marginal_second_fold (map_mul_row ph q) (product_joint (a :: pt') q) Hdimrows).
    + eapply Forall2_Qeq_trans.
      * apply pointwise_add_compat_l, (IH a q).
      * eapply Forall2_Qeq_trans.
        ** apply pointwise_add_map_mul.
        ** apply Forall2_map_scale_Qeq.
           simpl sum_list. ring.
Qed.

Theorem marginal_second_product_nonempty (p q : list Q) :
  p <> [] ->
  Forall2 Qeq (marginal_second (product_joint p q))
    (map (fun qk : Q => qk * sum_list p) q).
Proof.
  intros Hp. destruct p as [|ph pt]; [contradiction Hp; reflexivity|].
  apply marginal_second_product.
Qed.

Corollary marginal_second_product_normalized (p q : list Q) :
  p <> [] ->
  sum_list p == 1 ->
  Forall2 Qeq (marginal_second (product_joint p q)) q.
Proof.
  intros Hp H1.
  eapply Forall2_Qeq_trans.
  - apply marginal_second_product_nonempty, Hp.
  - induction q as [|qh qt IH]; simpl.
    + apply Forall2_nil.
    + apply Forall2_cons.
      * rewrite H1. rewrite Qmult_1_r. reflexivity.
      * apply IH.
Qed.
