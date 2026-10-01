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

From Stdlib Require Import QArith List Bool Arith Lqa.
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

End Select.
