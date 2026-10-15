(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: Coordination/AgentColimit.v                              *)
(*                                                                        *)
(*  Twin of Lean/Coordination/AgentColimit.lean. An agent observes a      *)
(*  world W through a map W -> A; agent c knows agent a when equal        *)
(*  c-readings give equal a-readings. The glued agent observes the pair;  *)
(*  it knows both agents, and every agent that knows both knows it: the   *)
(*  join in the information order. The kernel of the glued agent is the  *)
(*  meet of the two kernels. Knowing is factoring through c.              *)
(*  Zero Axiom, Parameter or Admitted.                                    *)
(* ===================================================================== *)

Section AgentColimit.

Variable W : Type.

Definition Knows {C A : Type} (c : W -> C) (a : W -> A) : Prop :=
  forall w w', c w = c w' -> a w = a w'.

Definition glue {A B : Type} (a : W -> A) (b : W -> B) : W -> A * B :=
  fun w => (a w, b w).

Theorem knows_refl {A : Type} (a : W -> A) : Knows a a.
Proof. intros w w' h. exact h. Qed.

Theorem knows_trans {C B A : Type} (c : W -> C) (b : W -> B) (a : W -> A) :
  Knows c b -> Knows b a -> Knows c a.
Proof. intros h1 h2 w w' h. apply h2, h1, h. Qed.

Theorem glue_knows_left {A B : Type} (a : W -> A) (b : W -> B) : Knows (glue a b) a.
Proof. intros w w' h. unfold glue in h. injection h. intros _ h1. exact h1. Qed.

Theorem glue_knows_right {A B : Type} (a : W -> A) (b : W -> B) : Knows (glue a b) b.
Proof. intros w w' h. unfold glue in h. injection h. intros h2 _. exact h2. Qed.

Theorem glue_universal {C A B : Type} (c : W -> C) (a : W -> A) (b : W -> B) :
  Knows c a -> Knows c b -> Knows c (glue a b).
Proof. intros ha hb w w' h. unfold glue. rewrite (ha w w' h), (hb w w' h). reflexivity. Qed.

Theorem knows_glue_iff {C A B : Type} (c : W -> C) (a : W -> A) (b : W -> B) :
  Knows c (glue a b) <-> Knows c a /\ Knows c b.
Proof.
  split.
  - intro h. split.
    + exact (knows_trans c (glue a b) a h (glue_knows_left a b)).
    + exact (knows_trans c (glue a b) b h (glue_knows_right a b)).
  - intros [ha hb]. exact (glue_universal c a b ha hb).
Qed.

(** The kernel of an agent: the pairs of worlds it does not tell apart. *)
Definition ker {A : Type} (a : W -> A) (w w' : W) : Prop := a w = a w'.

(** The kernel of the glued agent is the meet of the two kernels. *)
Theorem ker_glue {A B : Type} (a : W -> A) (b : W -> B) (w w' : W) :
  ker (glue a b) w w' <-> ker a w w' /\ ker b w w'.
Proof.
  unfold ker, glue. split.
  - intro h. injection h. intros h2 h1. split; [exact h1 | exact h2].
  - intros [h1 h2]. rewrite h1, h2. reflexivity.
Qed.

(** A factorisation through c makes c know a (the converse needs choice and is the Lean statement). *)
Theorem factors_knows {C A : Type} (c : W -> C) (a : W -> A) (f : C -> A) :
  (forall w, a w = f (c w)) -> Knows c a.
Proof. intros hf w w' h. rewrite (hf w), (hf w'), h. reflexivity. Qed.

End AgentColimit.
