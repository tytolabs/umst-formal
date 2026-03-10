(* ================================================================== *)
(*  UMST-Formal: Constitutional.v                                      *)
(*                                                                      *)
(*  Kleisli Admissibility Theorem and Subject Reduction Lemma.         *)
(*                                                                      *)
(*  This module provides machine-checked proofs of:                    *)
(*                                                                      *)
(*    1. Kleisli Admissibility Theorem:                                 *)
(*       An N-step constitutional sequence is thermodynamically safe   *)
(*       if each step is well-typed as an admissible transition.        *)
(*       Proved by structural induction on N.                          *)
(*                                                                      *)
(*    2. Subject Reduction Lemma:                                       *)
(*       Well-typedness of a constitutional sequence is preserved      *)
(*       under one reduction step (evaluation of the head transition). *)
(*       Proved by inversion on the sequence type.                     *)
(*                                                                      *)
(*  Connection to existing proofs:                                      *)
(*    gate_check_sound     (Gate.v): gate_check = true → admissible    *)
(*    gate_check_complete  (Gate.v): admissible → gate_check = true    *)
(*    gate_check_correct   (Gate.v): full biconditional                *)
(*                                                                      *)
(*  Proof status:  ZERO admits.  All theorems fully proved.            *)
(*                                                                      *)
(*  Kleisli Admissibility ≡ kleisli_fold_well_typed                   *)
(*  Subject Reduction     ≡ subject_reduction                         *)
(* ================================================================== *)

Require Import QArith.
Require Import Bool.
Require Import List.
Import ListNotations.

Require Import Gate.

(* ================================================================== *)
(*  SECTION 1: Constitutional Sequences                                 *)
(*                                                                      *)
(*  A constitutional sequence [s0, s1, ..., sN] is well-typed iff     *)
(*  every consecutive pair (si, si+1) satisfies gate_check.           *)
(*  Type-theoretic encoding: a well-typed                              *)
(*  constitutional program has an execution trace in the admissible    *)
(*  region.                                                             *)
(* ================================================================== *)

Inductive ConstitutionalSeq : list ThermodynamicState -> Prop :=
  | CSNil  : ConstitutionalSeq []
  | CSOne  : forall s, ConstitutionalSeq [s]
  | CSCons : forall s1 s2 rest,
               gate_check s1 s2 = true ->
               ConstitutionalSeq (s2 :: rest) ->
               ConstitutionalSeq (s1 :: s2 :: rest).

(* ================================================================== *)
(*  SECTION 2: Subject Reduction                                        *)
(*                                                                      *)
(*  Lemma (Subject Reduction):                                          *)
(*    If [s1, s2, rest...] is a constitutional sequence, then          *)
(*    [s2, rest...] is also a constitutional sequence.                 *)
(*    Proved by inversion — the CSCons constructor carries the         *)
(*    sub-proof for the tail.                                          *)
(*                                                                      *)
(*  Interpretation: after the gate evaluates and accepts s1 → s2,    *)
(*  the remaining program [s2, rest...] is still well-typed.          *)
(* ================================================================== *)

Lemma subject_reduction :
  forall (s1 s2 : ThermodynamicState) (rest : list ThermodynamicState),
  ConstitutionalSeq (s1 :: s2 :: rest) ->
  ConstitutionalSeq (s2 :: rest).
Proof.
  intros s1 s2 rest H.
  inversion H; assumption.
Qed.

(* ================================================================== *)
(*  SECTION 3: Kleisli Admissibility                                    *)
(*                                                                      *)
(*  Theorem (Kleisli Admissibility):                                    *)
(*    Every consecutive pair in a constitutional sequence satisfies    *)
(*    the full admissibility predicate.                                *)
(*    Proved by structural induction on the sequence.                  *)
(* ================================================================== *)

Theorem kleisli_admissibility :
  forall (seq : list ThermodynamicState),
  ConstitutionalSeq seq ->
  forall (s1 s2 : ThermodynamicState) (i : nat),
  nth_error seq i = Some s1 ->
  nth_error seq (S i) = Some s2 ->
  admissible s1 s2.
Proof.
  intros seq Hseq.
  induction Hseq as [| s | s1 s2 rest Hcheck Htail IH].
  - intros s1 s2 i H1 H2.
    simpl in H1. destruct i; discriminate.
  - intros s1 s2 i H1 H2.
    simpl in H1. destruct i as [| i'].
    + injection H1; intros; subst.
      simpl in H2. discriminate.
    + destruct i'; discriminate.
  - intros s s' i H1 H2.
    destruct i as [| i'].
    + simpl in H1. injection H1; intros; subst.
      simpl in H2. injection H2; intros; subst.
      exact (gate_check_sound s s' Hcheck).
    + simpl in H1. simpl in H2.
      exact (IH s s' i' H1 H2).
Qed.

(* ================================================================== *)
(*  SECTION 4: Corollary — Two-Step Composition                         *)
(*                                                                      *)
(*  Corollary: A two-step sequence [s0; s1; s2] is safe:               *)
(*  both s0 → s1 and s1 → s2 satisfy the gate.                        *)
(* ================================================================== *)

Corollary sequential_composition_safe :
  forall (s0 s1 s2 : ThermodynamicState),
  ConstitutionalSeq [s0; s1; s2] ->
  admissible s0 s1 /\ admissible s1 s2.
Proof.
  intros s0 s1 s2 Hseq.
  split.
  - exact (kleisli_admissibility [s0; s1; s2] Hseq s0 s1 0 eq_refl eq_refl).
  - exact (kleisli_admissibility [s0; s1; s2] Hseq s1 s2 1 eq_refl eq_refl).
Qed.

(* ================================================================== *)
(*  SECTION 5: Reflexivity of admissible                                *)
(*                                                                      *)
(*  A state is admissible with itself (the identity transition).        *)
(*  This is needed to close the identity-arrow case in Section 6.      *)
(*                                                                      *)
(*  Proof:                                                              *)
(*    density s - density s = 0 ≤ delta_mass = 100   (ring + Qle)     *)
(*    free_energy s ≤ free_energy s                   (Qle_refl)       *)
(*    hydration s ≤ hydration s                       (Qle_refl)       *)
(*    strength s ≤ strength s                         (Qle_refl)       *)
(* ================================================================== *)

(** Helper: the rational 0 is ≤ 100 (the mass tolerance). *)
Lemma zero_le_delta_mass : 0 <= delta_mass.
Proof.
  unfold delta_mass, Qle. simpl. lia.
Qed.

(** Helper: x - x <= 0 for any rational x.
    Follows from Qplus_opp_r (q + -q == 0) and Qle_lteq. *)
Lemma Qminus_self_le_zero : forall x : Q, x - x <= 0.
Proof.
  intro x.
  apply (proj2 (Qle_lteq _ _)).
  right.
  (* x - x == 0: Qeq goal, proved by ring *)
  ring.
Qed.

Lemma admissible_refl :
  forall (s : ThermodynamicState),
  admissible s s.
Proof.
  intro s.
  unfold admissible.
  refine (conj _ (conj _ (conj (Qle_refl _) (conj (Qle_refl _) (Qle_refl _))))).
  all: apply Qle_trans with (y := 0 : Q).
  - exact (Qminus_self_le_zero (density s)).
  - exact zero_le_delta_mass.
  - exact (Qminus_self_le_zero (density s)).
  - exact zero_le_delta_mass.
Qed.

Lemma gate_check_refl :
  forall (s : ThermodynamicState),
  gate_check s s = true.
Proof.
  intro s.
  exact (gate_check_complete s s (admissible_refl s)).
Qed.

(* ================================================================== *)
(*  SECTION 6: Kleisli Arrow Type                                       *)
(*                                                                      *)
(*  We formalise the Kleisli arrows as Coq functions.                  *)
(*  A Kleisli arrow is a function                                       *)
(*    ThermodynamicState → option ThermodynamicState                   *)
(*  that produces the next state iff the gate accepts the transition,  *)
(*  and None (⊥) otherwise.  The ⊥-absorbing semantics means a        *)
(*  rejected transition halts the pipeline.                            *)
(* ================================================================== *)

Definition KleisliArrow := ThermodynamicState -> option ThermodynamicState.

(** A Kleisli arrow is well-typed if every state it produces is
    admissible from the input state. *)
Definition WellTyped (f : KleisliArrow) : Prop :=
  forall (s s' : ThermodynamicState),
  f s = Some s' ->
  admissible s s'.

(** A gate-mediated arrow: apply `propose` to compute the candidate
    next state, then gate-check the transition. *)
Definition make_gate_arrow (propose : ThermodynamicState -> ThermodynamicState)
  : KleisliArrow :=
  fun s =>
    let s' := propose s in
    if gate_check s s' then Some s' else None.

(** Any gate-mediated arrow is well-typed. *)
Theorem gate_arrow_well_typed :
  forall (propose : ThermodynamicState -> ThermodynamicState),
  WellTyped (make_gate_arrow propose).
Proof.
  intros propose s s' H.
  unfold make_gate_arrow in H.
  destruct (gate_check s (propose s)) eqn:Hcheck.
  - injection H; intros; subst.
    exact (gate_check_sound s s' Hcheck).
  - discriminate.
Qed.

(** Kleisli composition: first apply f, then g to the result.
    If either step returns None, the composition returns None. *)
Definition kleisli_compose (f g : KleisliArrow) : KleisliArrow :=
  fun s =>
    match f s with
    | None    => None
    | Some s' => g s'
    end.

(** Composing two well-typed arrows gives a well-typed arrow.
    This is the Kleisli-arrow form of Subject Reduction: the type of
    a sequential composition is preserved step by step. *)
Theorem kleisli_compose_well_typed :
  forall (f g : KleisliArrow),
  WellTyped f ->
  WellTyped g ->
  WellTyped (kleisli_compose f g).
Proof.
  intros f g Hf Hg s s'' Hcomp.
  unfold kleisli_compose in Hcomp.
  destruct (f s) as [s' |] eqn:Hfs.
  - exact (Hg s' s'' Hcomp).
  - discriminate.
Qed.

(** N-step Kleisli composition: fold a list of arrows.
    The empty list is the identity arrow (returns Some s for any s). *)
Fixpoint kleisli_fold (arrows : list KleisliArrow) : KleisliArrow :=
  match arrows with
  | []       => fun s => Some s
  | [f]      => f
  | f :: rest => kleisli_compose f (kleisli_fold rest)
  end.

Definition AllWellTyped (arrows : list KleisliArrow) : Prop :=
  Forall WellTyped arrows.

(** Theorem (Kleisli Admissibility, N-step):
    Folding N well-typed arrows gives a well-typed arrow.
    Proved by structural induction on the arrow list.
    The identity-arrow base case uses admissible_refl (Section 5). *)
Theorem kleisli_fold_well_typed :
  forall (arrows : list KleisliArrow),
  AllWellTyped arrows ->
  WellTyped (kleisli_fold arrows).
Proof.
  intros arrows Hall.
  induction arrows as [| f rest IH].
  - (* Empty list: identity arrow. *)
    unfold WellTyped, kleisli_fold.
    intros s s' H.
    injection H; intros; subst.
    exact (admissible_refl s).
  - destruct rest as [| g rest'].
    + simpl. inversion Hall; assumption.
    + simpl.
      apply kleisli_compose_well_typed.
      * inversion Hall; assumption.
      * apply IH. inversion Hall; assumption.
Qed.

(* ================================================================== *)
(*  SECTION 7: Summary                                                  *)
(*                                                                      *)
(*  Claim                       │ This File                            *)
(*  ────────────────────────────┼─────────────────────────────────────*)
(*  "Kleisli Admissibility      │ kleisli_admissibility (Section 3)   *)
(*   Theorem" (N-step safe)     │ kleisli_fold_well_typed (Section 6) *)
(*  "Subject Reduction Lemma"   │ subject_reduction (Section 2)       *)
(*                              │ kleisli_compose_well_typed (Sec 6)  *)
(*  ⊥-absorbing monad           │ kleisli_compose / kleisli_fold      *)
(*  ConstitutionalSeq type      │ ConstitutionalSeq (Section 1)       *)
(*  Identity arrow reflexivity  │ admissible_refl (Section 5)         *)
(*                                                                      *)
(*  Proof status: ALL theorems fully proved.  Zero admits.             *)
(* ================================================================== *)
