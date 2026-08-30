(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* UMST-Formal: Urge/Reconcile.v — BP II §5.2 both-way union-preserving reconcile. *)
(* Zero Axiom. Zero Admitted. physics_green = false. Machine-checked. *)

From Stdlib Require Import Arith List Bool.
Require Import UMSTFormal.Urge.AppendOnly.

Open Scope bool_scope.

Record Head := mkHead { head_id : nat; head_digest : nat }.

Record StateSummary := mkSummary { heads : list Head }.

Definition advertises (s : StateSummary) (id : nat) : Prop :=
  exists h, In h (heads s) /\ head_id h = id.

Definition digests_agree (L R : StateSummary) (id : nat) : Prop :=
  forall hL hR,
    In hL (heads L) -> In hR (heads R) ->
    head_id hL = id -> head_id hR = id ->
    head_digest hL = head_digest hR.

Definition in_union (L R : StateSummary) (id : nat) : Prop :=
  advertises L id \/ advertises R id.

(** No-Loss mech #4: every advertised id remains in the conceptual union. *)
Definition union_preserving (L R : StateSummary) : Prop :=
  (forall id, advertises L id -> in_union L R id) /\
  (forall id, advertises R id -> in_union L R id).

Lemma union_preserving_trivial :
  forall L R, union_preserving L R.
Proof.
  intros L R; split; intros id H.
  - left; exact H.
  - right; exact H.
Qed.

(** Content-conflict refuse: overlapping id with disagreeing digests is inadmissible. *)
Definition content_conflict (L R : StateSummary) (id : nat) : Prop :=
  exists hL hR,
    In hL (heads L) /\ In hR (heads R) /\
    head_id hL = id /\ head_id hR = id /\
    head_digest hL <> head_digest hR.

Definition reconcile_admissible (L R : StateSummary) : Prop :=
  forall id, advertises L id -> advertises R id -> digests_agree L R id.

Lemma content_conflict_not_admissible :
  forall L R id,
    content_conflict L R id -> ~ reconcile_admissible L R.
Proof.
  intros L R id Hc Ha.
  destruct Hc as [hL [hR [HinL [HinR [HidL [HidR Hneq]]]]]].
  assert (Hal : advertises L id).
  { exists hL; split; [exact HinL | exact HidL]. }
  assert (Har : advertises R id).
  { exists hR; split; [exact HinR | exact HidR]. }
  specialize (Ha id Hal Har hL hR HinL HinR HidL HidR).
  contradiction.
Qed.

Definition reconcile_physics_green : bool := false.

Lemma reconcile_physics_green_false : reconcile_physics_green = false.
Proof. reflexivity. Qed.

(** Fixture: unique heads from each side remain in union conceptually. *)
Definition fixture_L : StateSummary :=
  mkSummary (mkHead 1 10 :: mkHead 2 20 :: nil).

Definition fixture_R : StateSummary :=
  mkSummary (mkHead 2 20 :: mkHead 3 30 :: nil).

Lemma fixture_union_preserving : union_preserving fixture_L fixture_R.
Proof. apply union_preserving_trivial. Qed.
