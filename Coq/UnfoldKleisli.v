(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: UnfoldKleisli.v                                          *)
(*                                                                        *)
(*  Twin of Lean/UnfoldKleisli.lean over exact rationals: a nested solve  *)
(*  is refused or done with a value and a spend (measured energy, Landauer*)
(*  floor). L1: bind has unit as left and right identity and is           *)
(*  associative, an inner refusal is the outer refusal, an outer spend is *)
(*  the sum of the inner ones. L2: spends form a commutative monoid over  *)
(*  canonical rationals and honesty (floor <= measured) is closed under   *)
(*  addition and binding. Error propagation over rational intervals:      *)
(*  interval addition encloses sums, tolerances add along a chain, and an *)
(*  inner error within tau_in through an L-Lipschitz map with an outer    *)
(*  error within tau_out stays within tau_out + L tau_in.                 *)
(* ===================================================================== *)

From Stdlib Require Import QArith Qcanon Lqa List.
Import ListNotations.

(** ** Spends over canonical rationals (Leibniz equality). *)

Record Spend := mkSpend { measured : Qc; floor : Qc }.

Definition szero : Spend := mkSpend 0%Qc 0%Qc.

Definition sadd (s t : Spend) : Spend :=
  mkSpend (Qcplus (measured s) (measured t)) (Qcplus (floor s) (floor t)).

Lemma sadd_assoc (s t u : Spend) : sadd (sadd s t) u = sadd s (sadd t u).
Proof. destruct s, t, u. unfold sadd. simpl. f_equal; rewrite Qcplus_assoc; reflexivity. Qed.

Lemma szero_add (s : Spend) : sadd szero s = s.
Proof. destruct s. unfold sadd, szero. simpl. f_equal; apply Qcplus_0_l. Qed.

Lemma sadd_zero (s : Spend) : sadd s szero = s.
Proof. destruct s. unfold sadd, szero. simpl. f_equal; apply Qcplus_0_r. Qed.

Lemma sadd_comm (s t : Spend) : sadd s t = sadd t s.
Proof. destruct s, t. unfold sadd. simpl. f_equal; apply Qcplus_comm. Qed.

(** A spend is honest when its measured energy is at least its floor. *)
Definition honest (s : Spend) : Prop := Qcle (floor s) (measured s).

(** L2: honesty is closed under addition. *)
Theorem honest_add (s t : Spend) : honest s -> honest t -> honest (sadd s t).
Proof. unfold honest, sadd. simpl. intros hs ht. apply Qcplus_le_compat; assumption. Qed.

Lemma honest_zero : honest szero.
Proof. unfold honest, szero. simpl. apply Qcle_refl. Qed.

(** L2 for any list of spends: the sum of measured energies is at least the sum of floors. *)
Theorem honest_sum (l : list Spend) : Forall honest l -> honest (fold_right sadd szero l).
Proof.
  induction l as [| s l IH]; intro h; simpl.
  - apply honest_zero.
  - inversion h; subst. apply honest_add; auto.
Qed.

(** ** Nested solves and Kleisli bind. *)

Inductive thermo (E A : Type) : Type :=
| Refused : E -> thermo E A
| Done : A -> Spend -> thermo E A.

Arguments Refused {E A} _.
Arguments Done {E A} _ _.

Definition unit {E A : Type} (a : A) : thermo E A := Done a szero.

Definition bind {E A B : Type} (m : thermo E A) (f : A -> thermo E B) : thermo E B :=
  match m with
  | Refused e => Refused e
  | Done a s =>
    match f a with
    | Refused e => Refused e
    | Done b t => Done b (sadd s t)
    end
  end.

Definition kcomp {E A B C : Type} (f : A -> thermo E B) (g : B -> thermo E C) : A -> thermo E C :=
  fun a => bind (f a) g.

(** L1 left identity. *)
Theorem unit_bind {E A B : Type} (a : A) (f : A -> thermo E B) : bind (unit a) f = f a.
Proof. unfold bind, unit. destruct (f a) as [e | b t]; [reflexivity | rewrite szero_add; reflexivity]. Qed.

(** L1 right identity. *)
Theorem bind_unit {E A : Type} (m : thermo E A) : bind m unit = m.
Proof. destruct m as [e | a s]; [reflexivity | unfold bind, unit; rewrite sadd_zero; reflexivity]. Qed.

(** L1 associativity. *)
Theorem bind_assoc {E A B C : Type} (m : thermo E A) (f : A -> thermo E B) (g : B -> thermo E C) :
  bind (bind m f) g = bind m (fun a => bind (f a) g).
Proof.
  destruct m as [e | a s]; [reflexivity |].
  simpl. destruct (f a) as [e | b t]; [reflexivity |].
  simpl. destruct (g b) as [e | c u]; [reflexivity |].
  rewrite sadd_assoc. reflexivity.
Qed.

(** L1 Kleisli composition is associative (pointwise). *)
Theorem kcomp_assoc {E A B C D : Type} (f : A -> thermo E B) (g : B -> thermo E C) (h : C -> thermo E D) (a : A) :
  kcomp (kcomp f g) h a = kcomp f (kcomp g h) a.
Proof. unfold kcomp. apply bind_assoc. Qed.

(** A refusal of an inner solve is the outer solve's refusal. *)
Theorem bind_inner_refusal {E A B : Type} (a : A) (s : Spend) (f : A -> thermo E B) (e : E) :
  f a = Refused e -> bind (Done a s) f = Refused e.
Proof. intro h. simpl. rewrite h. reflexivity. Qed.

(** An outer solve's spend is the sum of its inner spends. *)
Theorem bind_spend {E A B : Type} (m : thermo E A) (f : A -> thermo E B) (b : B) (u : Spend) :
  bind m f = Done b u -> exists a s t, m = Done a s /\ f a = Done b t /\ u = sadd s t.
Proof.
  destruct m as [e | a s]; simpl; [discriminate |].
  destruct (f a) as [e | b' t] eqn:hf; [discriminate |].
  intro h. inversion h; subst. exists a, s, t. auto.
Qed.

(** Every spend a solve can post is honest. *)
Definition honestT {E A : Type} (m : thermo E A) : Prop := forall a s, m = Done a s -> honest s.

(** L2 under nesting: honest inner solves bind to an honest outer solve. *)
Theorem bind_honest {E A B : Type} (m : thermo E A) (f : A -> thermo E B) :
  honestT m -> (forall a, honestT (f a)) -> honestT (bind m f).
Proof.
  intros hm hf b u h.
  destruct (bind_spend m f b u h) as [a [s [t [hma [hfa hu]]]]]. subst u.
  apply honest_add; [apply (hm a s hma) | apply (hf a b t hfa)].
Qed.

(** ** Error propagation over rational intervals. *)

Open Scope Q_scope.

Record Interval := mkInterval { lo : Q; hi : Q }.

Definition mem (I : Interval) (x : Q) : Prop := lo I <= x /\ x <= hi I.

Definition iadd (I J : Interval) : Interval := mkInterval (lo I + lo J) (hi I + hi J).

Definition sym (tau : Q) : Interval := mkInterval (- tau) tau.

(** Interval addition encloses sums. *)
Theorem mem_add (I J : Interval) (x y : Q) : mem I x -> mem J y -> mem (iadd I J) (x + y).
Proof. unfold mem, iadd. simpl. intros [h1 h2] [h3 h4]. split; lra. Qed.

Definition qsum (l : list Q) : Q := fold_right Qplus 0 l.

(** Tolerance chain: errors each within their tolerance sum within the summed tolerance. *)
Theorem mem_sum_sym (l : list (Q * Q)) :
  Forall (fun p => mem (sym (snd p)) (fst p)) l -> mem (sym (qsum (map snd l))) (qsum (map fst l)).
Proof.
  induction l as [| p l IH]; intro h.
  - unfold mem, sym, qsum. simpl. split; lra.
  - inversion h as [| ? ? hp hl]; subst. pose proof (IH hl) as ih.
    unfold mem, sym, qsum in *. simpl in *. destruct hp, ih. split; lra.
Qed.

(** Error propagation: within tau_out + L tau_in. *)
Theorem error_chain (L tin tout ystar yhat z : Q) (g : Q -> Q) :
  mem (sym tin) (yhat - ystar) ->
  (forall x y, mem (sym tin) (x - y) -> mem (sym (L * tin)) (g x - g y)) ->
  mem (sym tout) (z - g yhat) -> mem (sym (tout + L * tin)) (z - g ystar).
Proof.
  intros hin hlip hout. pose proof (hlip yhat ystar hin) as hg.
  unfold mem, sym in *. simpl in *. destruct hg, hout. split; lra.
Qed.
