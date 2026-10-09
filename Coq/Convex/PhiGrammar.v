(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Convex.PhiGrammar — a grammar of dissipation potentials     *)
(*  that are convex, nonnegative and zero at zero by construction (twin of *)
(*  Lean/Convex/PhiGrammar.lean).                                           *)
(*                                                                          *)
(*  Coq states the grammar over one exact rational rate: the linear maps    *)
(*  of Q are the scalings x |-> k x, a positive-semidefinite form is a x^2  *)
(*  with a >= 0, and the power and Norton exponents are p + 1 and m + 1     *)
(*  for natural p and m. Every expression denotes a potential that is zero  *)
(*  at zero, nonnegative and convex along every chord; a subgradient of it  *)
(*  pairs with the rate to a nonnegative dissipation, so a passive step is  *)
(*  a transition case of SecondLaw. Zero Axiom, Parameter or Admitted.      *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qabs Qminmax Lqa Setoid Morphisms.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope Q_scope.

(** z^k over Q. *)
Fixpoint qpow (z : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | S k' => z * qpow z k'
  end.

(** Dissipation-potential expressions over one rational rate. *)
Inductive phi_expr : Type :=
  | PQuad (a : Q) (ha : 0 <= a)                          (* a x^2, a >= 0 *)
  | PAbs                                                 (* |x| *)
  | PPow (p : nat)                                       (* |x|^(p+1) *)
  | PNorton (a : Q) (ha : 0 <= a) (m : nat)              (* a |x|^(m+1), a >= 0 *)
  | PScale (c : Q) (hc : 0 <= c) (e : phi_expr)          (* c phi, c >= 0 *)
  | PAdd (e1 e2 : phi_expr)                              (* phi1 + phi2 *)
  | PMax (e1 e2 : phi_expr)                              (* max phi1 phi2 *)
  | PPrecomp (k : Q) (e : phi_expr).                     (* phi (k x) *)

Fixpoint denote (e : phi_expr) (x : Q) : Q :=
  match e with
  | PQuad a _ => a * (x * x)
  | PAbs => Qabs x
  | PPow p => qpow (Qabs x) (S p)
  | PNorton a _ m => a * qpow (Qabs x) (S m)
  | PScale c _ e' => c * denote e' x
  | PAdd e1 e2 => denote e1 x + denote e2 x
  | PMax e1 e2 => Qmax (denote e1 x) (denote e2 x)
  | PPrecomp k e' => denote e' (k * x)
  end.

(** ** Powers *)

Lemma q_sq_nonneg (z : Q) : 0 <= z * z.
Proof.
  destruct (Qlt_le_dec z 0) as [h|h].
  - setoid_replace (z * z) with ((- z) * (- z)) by ring. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; exact h.
Qed.

Lemma qpow_wd (a b : Q) (k : nat) : a == b -> qpow a k == qpow b k.
Proof. intros h. induction k as [|k IH]; cbn [qpow denote]; [reflexivity | rewrite IH, h; reflexivity]. Qed.

Lemma qpow_nonneg (z : Q) (k : nat) : 0 <= z -> 0 <= qpow z k.
Proof.
  intros hz. induction k as [|k IH]; cbn [qpow denote]; [lra |].
  apply Qmult_le_0_compat; assumption.
Qed.

Lemma qpow_zero_succ (k : nat) : qpow 0 (S k) == 0.
Proof. cbn [qpow]. ring. Qed.

Lemma qpow_mono (a b : Q) (k : nat) : 0 <= a -> a <= b -> qpow a k <= qpow b k.
Proof.
  intros ha hab. induction k as [|k IH]; cbn [qpow denote]; [lra |].
  assert (hA : 0 <= qpow a k) by (apply qpow_nonneg; exact ha).
  assert (hB : 0 <= qpow b k) by (apply qpow_nonneg; lra).
  nra.
Qed.

(** (a - b)(a^k - b^k) >= 0 for a, b >= 0. *)
Lemma qpow_sorted (a b : Q) (k : nat) : 0 <= a -> 0 <= b -> 0 <= (a - b) * (qpow a k - qpow b k).
Proof.
  intros ha hb. destruct (Qlt_le_dec a b) as [h|h].
  - assert (qpow a k <= qpow b k) by (apply qpow_mono; lra). nra.
  - assert (qpow b k <= qpow a k) by (apply qpow_mono; lra). nra.
Qed.

(** z |-> z^(k+1) is convex along every chord of [0, oo). *)
Lemma qpow_convex (a b t : Q) (k : nat) : 0 <= a -> 0 <= b -> 0 <= t -> t <= 1 ->
  qpow (t * a + (1 - t) * b) (S k) <= t * qpow a (S k) + (1 - t) * qpow b (S k).
Proof.
  intros ha hb ht0 ht1. induction k as [|k IH].
  - cbn [qpow]. lra.
  - set (m := t * a + (1 - t) * b) in *.
    assert (hm : 0 <= m) by (unfold m; nra).
    set (A := qpow a (S k)) in *. set (B := qpow b (S k)) in *.
    change (qpow m (S (S k))) with (m * qpow m (S k)).
    change (qpow a (S (S k))) with (a * A). change (qpow b (S (S k))) with (b * B).
    assert (h1 : m * qpow m (S k) <= m * (t * A + (1 - t) * B)) by nra.
    assert (hsort : 0 <= (a - b) * (A - B)) by (apply qpow_sorted; assumption).
    assert (htt : 0 <= t * (1 - t)) by (apply Qmult_le_0_compat; lra).
    assert (hgap : 0 <= t * (1 - t) * ((a - b) * (A - B))) by (apply Qmult_le_0_compat; assumption).
    assert (hid : t * (a * A) + (1 - t) * (b * B) - m * (t * A + (1 - t) * B)
                  == t * (1 - t) * ((a - b) * (A - B))) by (unfold m; ring).
    lra.
Qed.

(** ** The three properties of every expression *)

Lemma denote_wd (e : phi_expr) (x y : Q) : x == y -> denote e x == denote e y.
Proof.
  revert x y. induction e as [a ha| |p|a ha m|c hc e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|k e IH]; intros x y h; cbn [denote].
  - rewrite h. reflexivity.
  - apply Qabs_wd. exact h.
  - apply qpow_wd. apply Qabs_wd. exact h.
  - rewrite (qpow_wd (Qabs x) (Qabs y) (S m) (Qabs_wd x y h)). reflexivity.
  - rewrite (IH x y h). reflexivity.
  - rewrite (IH1 x y h), (IH2 x y h). reflexivity.
  - rewrite (IH1 x y h), (IH2 x y h). reflexivity.
  - apply IH. rewrite h. reflexivity.
Qed.

(** Zero at zero: phi(0) = 0. *)
Theorem denote_zero (e : phi_expr) : denote e 0 == 0.
Proof.
  induction e as [a ha| |p|a ha m|c hc e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|k e IH]; cbn [qpow denote].
  - ring.
  - reflexivity.
  - change (Qabs 0) with 0. ring.
  - change (Qabs 0) with 0. ring.
  - rewrite IH. ring.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite (denote_wd e (k * 0) 0 ltac:(ring)). exact IH.
Qed.

(** Nonnegative: phi >= 0. *)
Theorem denote_nonneg (e : phi_expr) (x : Q) : 0 <= denote e x.
Proof.
  revert x. induction e as [a ha| |p|a ha m|c hc e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|k e IH]; intros x; cbn [denote].
  - apply Qmult_le_0_compat; [exact ha | apply q_sq_nonneg].
  - apply Qabs_nonneg.
  - apply qpow_nonneg. apply Qabs_nonneg.
  - apply Qmult_le_0_compat; [exact ha | apply qpow_nonneg; apply Qabs_nonneg].
  - apply Qmult_le_0_compat; [exact hc | apply IH].
  - specialize (IH1 x). specialize (IH2 x). lra.
  - specialize (IH1 x). apply (Qle_trans _ (denote e1 x)); [exact IH1 | apply Q.le_max_l].
  - apply IH.
Qed.

Lemma abs_chord (x y t : Q) : 0 <= t -> t <= 1 -> Qabs (t * x + (1 - t) * y) <= t * Qabs x + (1 - t) * Qabs y.
Proof.
  intros ht0 ht1.
  apply (Qle_trans _ (Qabs (t * x) + Qabs ((1 - t) * y))); [apply Qabs_triangle |].
  rewrite !Qabs_Qmult, (Qabs_pos t ht0), (Qabs_pos (1 - t)) by lra. lra.
Qed.

Lemma abspow_chord (x y t : Q) (k : nat) : 0 <= t -> t <= 1 ->
  qpow (Qabs (t * x + (1 - t) * y)) (S k) <= t * qpow (Qabs x) (S k) + (1 - t) * qpow (Qabs y) (S k).
Proof.
  intros ht0 ht1.
  apply (Qle_trans _ (qpow (t * Qabs x + (1 - t) * Qabs y) (S k))).
  - apply qpow_mono; [apply Qabs_nonneg | apply abs_chord; assumption].
  - apply qpow_convex; [apply Qabs_nonneg | apply Qabs_nonneg | assumption | assumption].
Qed.

(** Convex: phi(t x + (1 - t) y) <= t phi(x) + (1 - t) phi(y) for t in [0, 1]. *)
Theorem denote_convex (e : phi_expr) (x y t : Q) : 0 <= t -> t <= 1 ->
  denote e (t * x + (1 - t) * y) <= t * denote e x + (1 - t) * denote e y.
Proof.
  intros ht0 ht1. revert x y.
  induction e as [a ha| |p|a ha m|c hc e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|k e IH]; intros x y; cbn [denote].
  - assert (hgap : 0 <= a * (t * (1 - t)) * ((x - y) * (x - y))).
    { apply Qmult_le_0_compat; [apply Qmult_le_0_compat; [exact ha | apply Qmult_le_0_compat; lra] | apply q_sq_nonneg]. }
    assert (hid : t * (a * (x * x)) + (1 - t) * (a * (y * y)) - a * ((t * x + (1 - t) * y) * (t * x + (1 - t) * y))
                  == a * (t * (1 - t)) * ((x - y) * (x - y))) by ring.
    lra.
  - apply abs_chord; assumption.
  - apply abspow_chord; assumption.
  - assert (h := abspow_chord x y t m ht0 ht1).
    assert (h' : a * qpow (Qabs (t * x + (1 - t) * y)) (S m)
                 <= a * (t * qpow (Qabs x) (S m) + (1 - t) * qpow (Qabs y) (S m)))
      by nra.
    lra.
  - assert (h' : c * denote e (t * x + (1 - t) * y) <= c * (t * denote e x + (1 - t) * denote e y))
      by (specialize (IH x y); nra).
    lra.
  - specialize (IH1 x y). specialize (IH2 x y). lra.
  - specialize (IH1 x y). specialize (IH2 x y).
    assert (hx1 := Q.le_max_l (denote e1 x) (denote e2 x)). assert (hx2 := Q.le_max_r (denote e1 x) (denote e2 x)).
    assert (hy1 := Q.le_max_l (denote e1 y) (denote e2 y)). assert (hy2 := Q.le_max_r (denote e1 y) (denote e2 y)).
    apply Q.max_lub; nra.
  - rewrite (denote_wd e (k * (t * x + (1 - t) * y)) (t * (k * x) + (1 - t) * (k * y)) ltac:(ring)).
    apply IH.
Qed.

(** ** The passive second law *)

(** [g] is a subgradient of phi at [x]: phi(x) + g (y - x) <= phi(y) for every y. *)
Definition is_subgradient (e : phi_expr) (x g : Q) : Prop :=
  forall y, denote e x + g * (y - x) <= denote e y.

(** The dissipation g x dominates the potential. *)
Theorem phi_le_subgradient_power (e : phi_expr) (x g : Q) : is_subgradient e x g -> denote e x <= g * x.
Proof. intros hg. specialize (hg 0). rewrite denote_zero in hg. lra. Qed.

(** Nonnegative dissipation for every expression and subgradient. *)
Theorem subgradient_power_nonneg (e : phi_expr) (x g : Q) : is_subgradient e x g -> 0 <= g * x.
Proof.
  intros hg. apply (Qle_trans _ (denote e x)); [apply denote_nonneg | apply phi_le_subgradient_power; exact hg].
Qed.

(** Passive second law: a step that dissipates g x (g a subgradient of a grammar potential at the rate x), under
    the passive balance (psi_new - psi_old) + g x <= 0 and the mass condition, is a transition case of SecondLaw. *)
Theorem phi_expr_passive_second_law (e : phi_expr) (x g : Q) (old new : ThermodynamicState) :
  is_subgradient e x g ->
  density new - density old <= delta_mass -> density old - density new <= delta_mass ->
  (free_energy new - free_energy old) + g * x <= 0 ->
  SecondLaw transition (thermodynamic old new).
Proof.
  intros hg hm1 hm2 hb. simpl. unfold core_admissible.
  assert (hD := subgradient_power_nonneg e x g hg).
  split; [exact hm1 | split; [exact hm2 | lra]].
Qed.

(** A nonconvex potential has no expression: min(|x|, 1) is nonnegative and zero at zero but not convex. *)
Theorem no_expr_denotes_capped : ~ (exists e : phi_expr, forall x, denote e x == Qmin (Qabs x) 1).
Proof.
  intros [e he].
  assert (hc := denote_convex e 0 2 (1 # 2) ltac:(lra) ltac:(lra)).
  rewrite (he ((1 # 2) * 0 + (1 - (1 # 2)) * 2)), (he 0), (he 2) in hc.
  vm_compute in hc. apply hc. reflexivity.
Qed.
