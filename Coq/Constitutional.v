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

From Stdlib Require Import QArith.
From Stdlib Require Import Qfield.
From Stdlib Require Import Setoid.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import UMSTFormal.Gate.

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

(* NOTE: admissible_trans has been REMOVED.
   It was refutable: |ρ₃ - ρ₁| ≤ |ρ₃ - ρ₂| + |ρ₂ - ρ₁| ≤ 2·δ, NOT ≤ δ.
   Counterexample: ρ₁=0, ρ₂=99, ρ₃=198 — each step ≤ 100 but |198-0|=198 > 100.
   Replacement: admissible_N_compose in this file (proved via Q triangle inequality).
   See: Lean/GraphProperties.lean mass_not_transitive. *)

(** Graded admissibility [admissible_N] is defined in [UMSTFormal.Gate]
    (two-sided rational bounds, matching [admissible]). *)

(** Single-step admissible is admissible_N 1. *)
Lemma admissible_iff_admissible_N1 : forall old new_ : ThermodynamicState,
  admissible old new_ <-> admissible_N 1 old new_.
Proof.
  intros old new_.
  split.
  - apply admissible_implies_admissible_N1.
  - intros (H1 & H2 & Hdiss & Hhyd & Hstr).
    unfold admissible.
    refine (conj _ (conj _ (conj Hdiss (conj Hhyd Hstr)))).
    + assert (Hq : inject_Z (Z.of_nat 1) * delta_mass == delta_mass) by (simpl; ring).
      rewrite Hq in H1. exact H1.
    + assert (Hq : inject_Z (Z.of_nat 1) * delta_mass == delta_mass) by (simpl; ring).
      rewrite Hq in H2. exact H2.
Qed.

Lemma inject_mass_triangle_rhs (m n : nat) :
  inject_Z (Z.of_nat m) * delta_mass + inject_Z (Z.of_nat n) * delta_mass <=
  inject_Z (Z.of_nat (m + n)) * delta_mass.
Proof.
  assert (Hcast : inject_Z (Z.of_nat (m + n)) * delta_mass ==
                  inject_Z (Z.of_nat m) * delta_mass + inject_Z (Z.of_nat n) * delta_mass).
  { rewrite Nat2Z.inj_add. rewrite inject_Z_plus. ring. }
  rewrite <- Hcast.
  apply Qle_refl.
Qed.

(** Graded composition via telescoping density differences (no [Qabs]). *)
Lemma admissible_N_compose : forall (m n : nat) (s s' s'' : ThermodynamicState),
  admissible_N m s s' ->
  admissible_N n s' s'' ->
  admissible_N (m + n) s s''.
Proof.
  intros m n s s' s''
         (Hm1 & Hm2 & Hm_diss & Hm_hyd & Hm_str)
         (Hn1 & Hn2 & Hn_diss & Hn_hyd & Hn_str).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - assert (Hd : density s'' - density s ==
              (density s'' - density s') + (density s' - density s)) by field.
    assert (Hperm : (density s'' - density s') + (density s' - density s) ==
                    (density s' - density s) + (density s'' - density s')) by ring.
    apply Qle_trans with (y := inject_Z (Z.of_nat m) * delta_mass + inject_Z (Z.of_nat n) * delta_mass).
    + apply Qle_trans with (y := (density s' - density s) + (density s'' - density s')).
      * apply Qle_trans with (y := (density s'' - density s') + (density s' - density s)).
        -- rewrite Hd. apply Qle_refl.
        -- setoid_rewrite Hperm. apply Qle_refl.
      * apply Qplus_le_compat; [exact Hm1 | exact Hn1].
    + exact (inject_mass_triangle_rhs m n).
  - assert (Hd : density s - density s'' ==
              (density s - density s') + (density s' - density s'')) by field.
    apply Qle_trans with (y := (density s - density s') + (density s' - density s'')).
    + rewrite Hd. apply Qle_refl.
    + apply Qle_trans with (y := inject_Z (Z.of_nat m) * delta_mass + inject_Z (Z.of_nat n) * delta_mass).
      * apply Qplus_le_compat; [exact Hm2 | exact Hn2].
      * exact (inject_mass_triangle_rhs m n).
  - apply Qle_trans with (y := free_energy s'); assumption.
  - apply Qle_trans with (y := hydration s'); assumption.
  - apply Qle_trans with (y := strength s'); assumption.
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
  - assert (Es : s' = propose s) by (injection H; easy).
    rewrite Es.
    exact (gate_check_sound s (propose s) Hcheck).
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

(** N-step well-typedness. *)
Definition well_typed_N (n : nat) (f : KleisliArrow) : Prop :=
  forall (s s' : ThermodynamicState), f s = Some s' -> admissible_N n s s'.

(** Composing two well-typed arrows gives a 2-step graded well-typed arrow.
    NOTE: proves [well_typed_N 2], not [WellTyped], because the single-step
    mass condition is NOT transitive (see comment before [admissible_N] above).
    Two admissible steps accumulate up to 2·delta_mass, handled by
    [admissible_N_compose] with m=1, n=1. *)
Theorem kleisli_compose_well_typed :
  forall (f g : KleisliArrow),
  WellTyped f ->
  WellTyped g ->
  well_typed_N 2 (kleisli_compose f g).
Proof.
  intros f g Hf Hg s s'' Hcomp.
  unfold kleisli_compose in Hcomp.
  destruct (f s) as [s' |] eqn:Hfs.
  - apply (admissible_N_compose 1 1 s s' s'').
    + apply (proj1 (admissible_iff_admissible_N1 s s')).
      apply Hf; exact Hfs.
    + apply (proj1 (admissible_iff_admissible_N1 s' s'')).
      apply Hg; exact Hcomp.
  - discriminate.
Qed.

(** General graded composition: m-step ∘ n-step = (m+n)-step.
    Proved from [admissible_N_compose]; no axioms. *)
Theorem kleisli_compose_well_typed_N (m n : nat) (f g : KleisliArrow) :
  well_typed_N m f ->
  well_typed_N n g ->
  well_typed_N (m + n) (kleisli_compose f g).
Proof.
  intros Hf Hg s s'' Hcomp.
  unfold kleisli_compose in Hcomp.
  destruct (f s) as [s' |] eqn:Hfs.
  - apply (admissible_N_compose m n s s' s'').
    + apply Hf; exact Hfs.
    + apply Hg; exact Hcomp.
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

(** Theorem (Kleisli Admissibility, N-step, graded):
    Folding N well-typed arrows gives a [well_typed_N N] arrow.
    Mass tolerance accumulates as N * delta_mass (triangle inequality).
    The three order conditions (Clausius-Duhem, hydration, strength)
    hold end-to-end by transitivity.
    Proved by structural induction without axioms. *)
Theorem kleisli_fold_well_typed_N :
  forall (arrows : list KleisliArrow),
  AllWellTyped arrows ->
  well_typed_N (length arrows) (kleisli_fold arrows).
Proof.
  intros arrows Hall.
  induction arrows as [| f rest IH].
  - (* Empty list: identity arrow is well_typed_N 0. *)
    intros s s' H.
    simpl in H.
    injection H as <-.
    exact (admissible_N_refl 0 s).
  - destruct rest as [| g rest'].
    + (* Single arrow: well_typed_N 1. *)
      simpl.
      intros s s' Hfs.
      apply (proj1 (admissible_iff_admissible_N1 s s')).
      exact (Forall_inv Hall s s' Hfs).
    + (* Cons case: length = 1 + length (g :: rest'). *)
      simpl.
      apply (kleisli_compose_well_typed_N 1 (length (g :: rest'))).
      * intros s s' Hfs.
        apply (proj1 (admissible_iff_admissible_N1 s s')).
        exact (Forall_inv Hall s s' Hfs).
      * apply IH.
        exact (Forall_inv_tail Hall).
Qed.

(** Backward-compatible alias. *)
Theorem kleisli_fold_well_typed :
  forall (arrows : list KleisliArrow),
  AllWellTyped arrows ->
  well_typed_N (length arrows) (kleisli_fold arrows).
Proof. intros; apply kleisli_fold_well_typed_N; assumption. Qed.

(* ================================================================== *)
(*  SECTION 7: Summary                                                  *)
(*                                                                      *)
(*  Claim                           │ This File                            *)
(*  ────────────────────────────────┼────────────────────────────────────  *)
(*  Kleisli Admissibility (seq)     │ kleisli_admissibility (Section 3)    *)
(*  Kleisli Admissibility (N-step)  │ kleisli_fold_well_typed_N (Sec 6)    *)
(*  Subject Reduction Lemma         │ subject_reduction (Section 2)        *)
(*  2-step composition              │ kleisli_compose_well_typed (Sec 6)   *)
(*  General graded composition      │ kleisli_compose_well_typed_N (Sec 6) *)
(*  Graded N-fold                   │ kleisli_fold_well_typed_N (Sec 6)    *)
(*  ⊥-absorbing monad               │ kleisli_compose / kleisli_fold       *)
(*  ConstitutionalSeq type          │ ConstitutionalSeq (Section 1)        *)
(*  Identity reflexivity (1-step)   │ admissible_refl (Section 5)          *)
(*  Identity reflexivity (0-step)   │ admissible_N_refl (Section 5)        *)
(*                                                                          *)
(*  Proof status: ZERO admits.  [admissible_trans] REMOVED (refutable);    *)
(*  replaced by [admissible_N] / [admissible_N_compose] (triangle ineq).   *)
(*  [kleisli_compose_well_typed]   → [well_typed_N 2]                      *)
(*  [kleisli_fold_well_typed_N]    → [well_typed_N (length arrows)]         *)
(* ================================================================== *)
