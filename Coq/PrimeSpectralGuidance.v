(* ================================================================== *)
(*  UMST-Formal: PrimeSpectralGuidance.v                              *)
(*  Prime-statistics-inspired guidance on auxiliary multiplicative    *)
(*  channels. Does NOT extend the four-conjunct thermodynamic gate.   *)
(* ================================================================== *)

From Coq Require Import QArith.
From Coq Require Import Qfield.
From Coq Require Import Arith.
From Coq Require Import Lia.
From Coq Require Import Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.

Open Scope Q_scope.

(* ================================================================== *)
(*  SECTION 1: Auxiliary channel (index-based for Q simplicity)       *)
(* ================================================================== *)

Record MultiplicativeChannel (n : nat) : Set := mkChannel {
  mc_values : nat -> Q
}.

Definition spectralFilter {T : nat}
  (weights : nat -> Q) (s : MultiplicativeChannel T) : MultiplicativeChannel T :=
  match s with
  | {| mc_values := old |} =>
    {| mc_values := fun i =>
         if Nat.ltb i T then weights i * old i else 0
    |}
  end.

Definition channelAt {n : nat} (ch : MultiplicativeChannel n) (i : nat) : Q :=
  match ch with {| mc_values := f |} => f i end.

Lemma spectralFilter_values : forall {T : nat} (weights : nat -> Q)
  (s : MultiplicativeChannel T) (i : nat) (Hi : (i < T)%nat),
  channelAt (spectralFilter weights s) i = (weights i) * channelAt s i.
Proof.
  intros T weights s i Hi.
  destruct s as [old].
  unfold spectralFilter, channelAt.
  simpl.
  assert (Hlt : (i <? T) = true) by (apply (proj2 (Nat.ltb_lt i T)); exact Hi).
  rewrite Hlt.
  reflexivity.
Qed.

(* perturbation bound: see Lean `spectralFilter_perturb`; omitted here due to Q_scope parsing. *)

(* von Mangoldt surrogate: see Lean `vonMangoldtWeight`; omitted in Coq Inc 1.5 core port. *)

Record GuidedState (n : nat) : Set := mkGuided {
  gs_thermo  : ThermodynamicState;
  gs_channel : MultiplicativeChannel n
}.

Definition guidedThermo {n : nat} (g : GuidedState n) : ThermodynamicState :=
  match g with {| gs_thermo := t |} => t end.

Definition guidedChannel {n : nat} (g : GuidedState n) : MultiplicativeChannel n :=
  match g with {| gs_channel := c |} => c end.

Definition gateProjection {n : nat} (g : GuidedState n) : ThermodynamicState :=
  guidedThermo g.

Definition applyChannelFilter {n : nat}
  (g : GuidedState n)
  (f : MultiplicativeChannel n -> MultiplicativeChannel n) : GuidedState n :=
  {| gs_thermo := guidedThermo g; gs_channel := f (guidedChannel g) |}.

Lemma applyChannelFilter_admissible : forall n (g1 g2 : GuidedState n)
  (h : admissible (guidedThermo g1) (guidedThermo g2))
  (f : MultiplicativeChannel n -> MultiplicativeChannel n),
  admissible (guidedThermo (applyChannelFilter g1 f))
             (guidedThermo (applyChannelFilter g2 f)).
Proof.
  intros n g1 g2 h f.
  exact h.
Qed.

Lemma guidance_preserves_admissible : forall n (old new : ThermodynamicState)
  (h : admissible old new)
  (f : MultiplicativeChannel n -> MultiplicativeChannel n),
  admissible old new.
Proof.
  intros n old new h f.
  exact h.
Qed.

Lemma applyChannelFilter_admissibleN : forall n (m : nat) (g1 g2 : GuidedState n)
  (h : admissible_N m (guidedThermo g1) (guidedThermo g2))
  (f : MultiplicativeChannel n -> MultiplicativeChannel n),
  admissible_N m (guidedThermo (applyChannelFilter g1 f))
                 (guidedThermo (applyChannelFilter g2 f)).
Proof.
  intros n m g1 g2 h f.
  exact h.
Qed.

Lemma kleisli_guidance_commute : forall n m k (g1 g2 g3 : GuidedState n)
  (h1 : admissible_N m (guidedThermo g1) (guidedThermo g2))
  (h2 : admissible_N k (guidedThermo g2) (guidedThermo g3))
  (f : MultiplicativeChannel n -> MultiplicativeChannel n),
  admissible_N (m + k)
    (guidedThermo (applyChannelFilter g1 f))
    (guidedThermo (applyChannelFilter g3 f)).
Proof.
  intros n m k g1 g2 g3 h1 h2 f.
  apply (admissible_N_compose m k (guidedThermo g1) (guidedThermo g2) (guidedThermo g3)).
  - apply applyChannelFilter_admissibleN with (f := f); exact h1.
  - apply applyChannelFilter_admissibleN with (f := f); exact h2.
Qed.
