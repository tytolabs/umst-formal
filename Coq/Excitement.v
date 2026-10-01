(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: Excitement.v                                             *)
(*                                                                        *)
(*  Twin of Lean/Excitement.lean, Lean/ExcitementProofs.lean and the      *)
(*  selection theorems of Lean/Concrete/SecondLaw.lean: selection under   *)
(*  cost over cement candidates. Each candidate carries the admissibility *)
(*  of its move; selection returns the evidence-tagged candidate of least *)
(*  global free energy (ties by id) when it lowers the source's free      *)
(*  energy, and a residue otherwise. The joint free energy is a parameter *)
(*  (a class parameter, JointThermo, in Lean).                            *)
(* ===================================================================== *)

From Stdlib Require Import QArith List Bool Arith Lqa Lia Permutation.
Import ListNotations.
Require Import UMSTFormal.Concrete.Gate UMSTFormal.Process UMSTFormal.Concrete.SecondLaw.

Open Scope Q_scope.

(** Why selection returns no candidate. *)
Inductive Residue : Type :=
  | noCandidates | allInadmissible | allExcludedByCBF | allExcludedByDEC | untaggedConstant | noStrictImprovement.

Section Select.

Variable jointFreeEnergy : ThermodynamicState -> Q.
Variable src : ThermodynamicState.

(** A candidate move from [src]: its id, target, the admissibility of the move, its ledger total and whether it
    carries evidence. *)
Record Cand : Type := mkCand {
  cid : nat;
  tgt : ThermodynamicState;
  step : admissible src tgt;
  ledger : Q;
  evidenceTagged : bool
}.

Definition candEnergy (c : Cand) : Q := jointFreeEnergy (tgt c) + ledger c.

Definition pickMin (acc : option Cand) (c : Cand) : option Cand :=
  match acc with
  | None => Some c
  | Some b =>
      if Qlt_le_dec (candEnergy c) (candEnergy b) then Some c
      else if Qlt_le_dec (candEnergy b) (candEnergy c) then Some b
      else if Nat.ltb (cid c) (cid b) then Some c else Some b
  end.

Definition select (cands : list Cand) : Cand + Residue :=
  match cands with
  | [] => inr noCandidates
  | _ =>
      match filter evidenceTagged cands with
      | [] => if existsb (fun c => negb (evidenceTagged c)) cands then inr allInadmissible else inr untaggedConstant
      | tagged =>
          match fold_left pickMin tagged None with
          | None => inr allInadmissible
          | Some c => if Qlt_le_dec (candEnergy c) (jointFreeEnergy src) then inl c else inr noStrictImprovement
          end
      end
  end.

Theorem select_empty : select [] = inr noCandidates.
Proof. reflexivity. Qed.

Lemma pickMin_spec (acc : option Cand) (x : Cand) :
  exists r, pickMin acc x = Some r /\ (r = x \/ acc = Some r) /\ candEnergy r <= candEnergy x /\
    forall a, acc = Some a -> candEnergy r <= candEnergy a.
Proof.
  destruct acc as [b |].
  - simpl. destruct (Qlt_le_dec (candEnergy x) (candEnergy b)) as [h | h].
    + exists x. repeat split; [left; reflexivity | apply Qle_refl |].
      intros a ha. inversion ha; subst. apply Qlt_le_weak. exact h.
    + destruct (Qlt_le_dec (candEnergy b) (candEnergy x)) as [h' | h'].
      * exists b. repeat split; [right; reflexivity | apply Qlt_le_weak; exact h' |].
        intros a ha. inversion ha; subst. apply Qle_refl.
      * destruct (Nat.ltb (cid x) (cid b)).
        -- exists x. repeat split; [left; reflexivity | apply Qle_refl |].
           intros a ha. inversion ha; subst. exact h'.
        -- exists b. repeat split; [right; reflexivity | exact h |].
           intros a ha. inversion ha; subst. apply Qle_refl.
  - exists x. repeat split; [left; reflexivity | apply Qle_refl |]. intros a ha. discriminate.
Qed.

Lemma fold_pickMin_spec (l : list Cand) (acc : option Cand) (m : Cand) :
  fold_left pickMin l acc = Some m ->
  (In m l \/ acc = Some m) /\ (forall x, In x l -> candEnergy m <= candEnergy x) /\
    (forall a, acc = Some a -> candEnergy m <= candEnergy a).
Proof.
  revert acc. induction l as [| x xs IH]; intros acc h; simpl in h.
  - subst acc. split; [right; reflexivity | split; [intros x [] |]].
    intros a ha. inversion ha; subst. apply Qle_refl.
  - destruct (pickMin_spec acc x) as [r [hr [hrmem [hrx hracc]]]].
    rewrite hr in h. destruct (IH (Some r) h) as [hmem [hle hseed]].
    pose proof (hseed r eq_refl) as hmr.
    split; [| split].
    + destruct hmem as [hm | hm].
      * left. right. exact hm.
      * inversion hm; subst. destruct hrmem as [-> | hacc]; [left; left; reflexivity | right; exact hacc].
    + intros y [<- | hy]; [exact (Qle_trans _ _ _ hmr hrx) | exact (hle y hy)].
    + intros a ha. exact (Qle_trans _ _ _ hmr (hracc a ha)).
Qed.

Lemma select_inl_spec (cands : list Cand) (c : Cand) :
  select cands = inl c ->
  fold_left pickMin (filter evidenceTagged cands) None = Some c /\ candEnergy c < jointFreeEnergy src.
Proof.
  unfold select. destruct cands as [| c0 rest]; [discriminate |].
  destruct (filter evidenceTagged (c0 :: rest)) as [| t ts] eqn:hf.
  - destruct (existsb _ _); discriminate.
  - destruct (fold_left pickMin (t :: ts) None) as [m |] eqn:hfold; [| discriminate].
    destruct (Qlt_le_dec (candEnergy m) (jointFreeEnergy src)) as [hlt |]; [| discriminate].
    intro h. inversion h; subst. split; [reflexivity | exact hlt].
Qed.

(** Selection is a minimum: the selected candidate is an evidence-tagged member and no evidence-tagged candidate has
    lower global free energy. *)
Theorem select_minimal (cands : list Cand) (c : Cand) :
  select cands = inl c ->
  In c cands /\ evidenceTagged c = true /\
    forall c', In c' cands -> evidenceTagged c' = true -> candEnergy c <= candEnergy c'.
Proof.
  intro hsel. destruct (select_inl_spec cands c hsel) as [hf _].
  destruct (fold_pickMin_spec _ None c hf) as [hmem [hle _]].
  destruct hmem as [hmem | hmem]; [| discriminate].
  apply filter_In in hmem as [hin ht].
  split; [exact hin | split; [exact ht |]].
  intros c' hc' ht'. apply hle. apply filter_In. split; assumption.
Qed.

(** Selection descends: the selected candidate's global free energy is strictly below the source's. *)
Theorem select_descent (cands : list Cand) (c : Cand) :
  select cands = inl c -> candEnergy c < jointFreeEnergy src.
Proof. intro hsel. exact (proj2 (select_inl_spec cands c hsel)). Qed.

(** Every candidate move is a member of the second-law predicate. *)
Theorem cand_secondLaw (c : Cand) : SecondLaw transition (thermodynamic src (tgt c)).
Proof. exact (proj1 (proj1 (admissible_iff_secondLaw src (tgt c)) (step c))). Qed.

(** pickMin is right-commutative for candidates of distinct ids: the lexicographic order on (energy, id) is a strict
    total order on them. *)
Lemma pickMin_right_comm (z : option Cand) (x y : Cand) :
  cid x <> cid y -> pickMin (pickMin z x) y = pickMin (pickMin z y) x.
Proof.
  intro hid. destruct z as [a |]; simpl;
  repeat (match goal with
          | |- context [Qlt_le_dec ?p ?q] => destruct (Qlt_le_dec p q)
          | |- context [Nat.ltb ?m ?n] => destruct (Nat.ltb_spec m n)
          end; simpl);
  first [reflexivity | exfalso; lra | exfalso; lia | idtac].
Qed.

Lemma NoDup_map_filter (f : Cand -> bool) (l : list Cand) :
  NoDup (map cid l) -> NoDup (map cid (filter f l)).
Proof.
  induction l as [| c l IH]; simpl; intro h; [constructor |].
  inversion h as [| ? ? hnin hnd]; subst. destruct (f c); simpl; [| exact (IH hnd)].
  constructor; [| exact (IH hnd)].
  intro hin. apply hnin. apply in_map_iff in hin as [d [hd hdin]]. apply filter_In in hdin as [hdl _].
  rewrite <- hd. apply in_map. exact hdl.
Qed.

(** The fold is invariant under permutation of candidates with distinct ids. *)
Lemma fold_pickMin_perm (l1 l2 : list Cand) :
  Permutation l1 l2 -> NoDup (map cid l1) -> forall acc, fold_left pickMin l1 acc = fold_left pickMin l2 acc.
Proof.
  induction 1 as [| x l l' hp IH | x y l | l l' l'' h1 IH1 h2 IH2]; intros hnd acc; simpl.
  - reflexivity.
  - inversion hnd; subst. apply IH. assumption.
  - simpl in hnd. inversion hnd as [| ? ? hnin _]; subst.
    rewrite (pickMin_right_comm acc y x); [reflexivity |]. intro e. apply hnin. rewrite e. left. reflexivity.
  - rewrite (IH1 hnd acc). apply IH2. exact (Permutation_NoDup (Permutation_map cid h1) hnd).
Qed.

Lemma filter_perm (f : Cand -> bool) (l1 l2 : list Cand) : Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
Proof.
  induction 1 as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; simpl.
  - constructor.
  - destruct (f x); [constructor |]; exact IH.
  - destruct (f x), (f y); try constructor; reflexivity.
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma existsb_perm (f : Cand -> bool) (l1 l2 : list Cand) : Permutation l1 l2 -> existsb f l1 = existsb f l2.
Proof.
  intro hp. apply Bool.eq_true_iff_eq. rewrite !existsb_exists. split; intros [x [hx hf]]; exists x; split; auto.
  - exact (Permutation_in x hp hx).
  - exact (Permutation_in x (Permutation_sym hp) hx).
Qed.

(** Selection does not depend on the order of candidates with distinct ids. *)
Theorem select_perm_invariant (l1 l2 : list Cand) :
  Permutation l1 l2 -> NoDup (map cid l1) -> select l1 = select l2.
Proof.
  intros hp hnd. unfold select.
  destruct l1 as [| c1 r1]; destruct l2 as [| c2 r2].
  - reflexivity.
  - apply Permutation_nil in hp. discriminate.
  - apply Permutation_sym, Permutation_nil in hp. discriminate.
  - pose proof (filter_perm evidenceTagged _ _ hp) as hf.
    pose proof (NoDup_map_filter evidenceTagged _ hnd) as hfnd.
    destruct (filter evidenceTagged (c1 :: r1)) as [| t1 ts1] eqn:e1;
    destruct (filter evidenceTagged (c2 :: r2)) as [| t2 ts2] eqn:e2.
    + rewrite (existsb_perm _ _ _ hp). reflexivity.
    + apply Permutation_nil in hf. discriminate.
    + apply Permutation_sym, Permutation_nil in hf. discriminate.
    + rewrite (fold_pickMin_perm _ _ hf hfnd None). reflexivity.
Qed.

End Select.
