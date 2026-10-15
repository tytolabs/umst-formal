(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: LearningLoopLaws.v                                       *)
(*                                                                        *)
(*  Twin of Lean/LearningLoopLaws.lean: the laws the learning-loop        *)
(*  kernel of umst-adk relies on. (1) The evidence map onto the lattice   *)
(*  Unclaimed < Claimed < GuardPassed < Verified < Landed < MeterMoved    *)
(*  is monotone. (2) Outcome counts form a commutative monoid and the     *)
(*  fold is a homomorphism, so every reordering folds to the same counts. *)
(*  (3) The Beta(V+1, R+1) posterior depends on the counts alone and its  *)
(*  mean lies in (0, 1). (4) The barrier h_{k+1} >= (1 - g) h_k keeps h   *)
(*  above (1 - g)^k h_0 >= 0. (5) The clipped multiplicative step keeps   *)
(*  a distribution and moves each weight within the clip; the             *)
(*  largest-remainder apportionment keeps the total and moves each unit   *)
(*  count by less than one. (6) A verified evidence bit paid by an        *)
(*  erasure obeying SecondLaw costs at least k_B T ln 2.                  *)
(*  Counts are compared pointwise, so no extensionality axiom enters.     *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra Lia List Permutation.
Import ListNotations.
Require Import UMSTFormal.Process UMSTFormal.CostOfInformation.

Open Scope R_scope.

(* ---------------------------------------------------------------- *)
(* 1. The evidence lattice                                            *)
(* ---------------------------------------------------------------- *)

Inductive Level : Type := Unclaimed | Claimed | GuardPassed | Verified | Landed | MeterMoved.

Definition rank (l : Level) : nat :=
  match l with
  | Unclaimed => 0 | Claimed => 1 | GuardPassed => 2 | Verified => 3 | Landed => 4 | MeterMoved => 5
  end.

Inductive ClaimStatus : Type := Open | Complete | RefusedClaim.

Inductive Outcome : Type := Refused | AtLevel (l : Level).

Record Evidence : Type := mkEvidence { guard : bool; verified : bool; landed : bool; moved : bool }.

Definition evidence_le (e f : Evidence) : Prop :=
  (guard e = true -> guard f = true) /\ (verified e = true -> verified f = true) /\
  (landed e = true -> landed f = true) /\ (moved e = true -> moved f = true).

Definition completeLevel (e : Evidence) : Level :=
  if verified e then (if landed e then (if moved e then MeterMoved else Landed) else Verified)
  else if guard e then GuardPassed else Claimed.

Definition levelOf (s : ClaimStatus) (e : Evidence) : Outcome :=
  match s with
  | RefusedClaim => Refused
  | Open => AtLevel Unclaimed
  | Complete => AtLevel (completeLevel e)
  end.

Definition outcome_le (a b : Outcome) : Prop :=
  match a, b with
  | Refused, Refused => True
  | AtLevel x, AtLevel y => (rank x <= rank y)%nat
  | _, _ => False
  end.

(** Law 1: more evidence never lowers the level of a COMPLETE claim. *)
Theorem completeLevel_monotone (e f : Evidence) :
  evidence_le e f -> (rank (completeLevel e) <= rank (completeLevel f))%nat.
Proof.
  destruct e as [g v l m], f as [g' v' l' m']. unfold evidence_le, completeLevel; simpl.
  intros [hg [hv [hl hm]]].
  destruct g, v, l, m, g', v', l', m'; simpl; try lia;
    first [ discriminate (hg eq_refl) | discriminate (hv eq_refl)
          | discriminate (hl eq_refl) | discriminate (hm eq_refl) ].
Qed.

(** Law 1, for every claim status. *)
Theorem levelOf_monotone (s : ClaimStatus) (e f : Evidence) :
  evidence_le e f -> outcome_le (levelOf s e) (levelOf s f).
Proof.
  intro h. destruct s; simpl; [lia | apply completeLevel_monotone; exact h | exact I].
Qed.

(* ---------------------------------------------------------------- *)
(* 2. Outcome counts                                                  *)
(* ---------------------------------------------------------------- *)

Section Counts.

Variable K : Type.

Definition Counts := K -> nat.

Definition czero : Counts := fun _ => 0%nat.

Definition combine (a b : Counts) : Counts := fun k => (a k + b k)%nat.

Theorem combine_assoc (a b c : Counts) (k : K) : combine (combine a b) c k = combine a (combine b c) k.
Proof. unfold combine. lia. Qed.

Theorem combine_comm (a b : Counts) (k : K) : combine a b k = combine b a k.
Proof. unfold combine. lia. Qed.

Theorem zero_combine (a : Counts) (k : K) : combine czero a k = a k.
Proof. reflexivity. Qed.

Theorem combine_zero (a : Counts) (k : K) : combine a czero k = a k.
Proof. unfold combine, czero. lia. Qed.

(** The fold from the identity, left to right (OutcomeCounts::fold). *)
Definition cfold (xs : list Counts) : Counts := fold_left combine xs czero.

Lemma fold_left_combine (xs : list Counts) : forall (acc : Counts) (k : K),
  fold_left combine xs acc k = (acc k + cfold xs k)%nat.
Proof.
  induction xs as [| x xs IH]; intros acc k; [unfold cfold; simpl; unfold czero; lia |].
  unfold cfold. simpl. rewrite (IH (combine acc x)), (IH (combine czero x)). unfold combine, czero. lia.
Qed.

Theorem fold_cons (x : Counts) (xs : list Counts) (k : K) : cfold (x :: xs) k = (x k + cfold xs k)%nat.
Proof. unfold cfold at 1. simpl. rewrite fold_left_combine. reflexivity. Qed.

(** Law 2: the fold is a monoid homomorphism from lists under append. *)
Theorem fold_append (xs ys : list Counts) (k : K) : cfold (xs ++ ys) k = (cfold xs k + cfold ys k)%nat.
Proof. unfold cfold at 1. rewrite fold_left_app, fold_left_combine. reflexivity. Qed.

(** Law 2: every reordering of the rows folds to the same counts. *)
Theorem fold_perm (xs ys : list Counts) : Permutation xs ys -> forall k, cfold xs k = cfold ys k.
Proof.
  intro h. induction h as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; intro k.
  - reflexivity.
  - rewrite !fold_cons, IH. reflexivity.
  - rewrite !fold_cons. lia.
  - rewrite IH1, IH2. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* 3. The Beta posterior                                              *)
(* ---------------------------------------------------------------- *)

Definition keySum (keys : list K) (c : Counts) : nat := fold_right (fun k acc => (c k + acc)%nat) 0%nat keys.

Lemma keySum_ext (keys : list K) (c d : Counts) : (forall k, c k = d k) -> keySum keys c = keySum keys d.
Proof. intro h. induction keys as [| k ks IH]; simpl; [reflexivity | rewrite h, IH; reflexivity]. Qed.

(** The Beta(V+1, R+1) posterior mean as numerator and denominator (outcome.rs posterior). *)
Definition posterior (vKeys rKeys : list K) (c : Counts) : nat * nat :=
  ((keySum vKeys c + 1)%nat, (keySum vKeys c + keySum rKeys c + 2)%nat).

(** Law 3: the posterior of a lane is the same for every order of its rows. *)
Theorem posterior_perm (vKeys rKeys : list K) (xs ys : list Counts) :
  Permutation xs ys -> posterior vKeys rKeys (cfold xs) = posterior vKeys rKeys (cfold ys).
Proof.
  intro h. unfold posterior.
  rewrite (keySum_ext vKeys _ _ (fold_perm xs ys h)), (keySum_ext rKeys _ _ (fold_perm xs ys h)). reflexivity.
Qed.

(** Law 3: the posterior mean lies strictly between 0 and 1. *)
Theorem posterior_mean_mem (vKeys rKeys : list K) (c : Counts) :
  0 < INR (fst (posterior vKeys rKeys c)) / INR (snd (posterior vKeys rKeys c)) /\
  INR (fst (posterior vKeys rKeys c)) / INR (snd (posterior vKeys rKeys c)) < 1.
Proof.
  unfold posterior; simpl.
  set (v := keySum vKeys c). set (r := keySum rKeys c).
  assert (hn : 0 < INR (v + 1)) by (apply lt_0_INR; lia).
  assert (hd : 0 < INR (v + r + 2)) by (apply lt_0_INR; lia).
  assert (hlt : INR (v + 1) < INR (v + r + 2)) by (apply lt_INR; lia).
  split.
  - apply Rdiv_lt_0_compat; assumption.
  - apply (Rmult_lt_reg_r (INR (v + r + 2))); [exact hd |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra. exact hlt.
Qed.

End Counts.

(* ---------------------------------------------------------------- *)
(* 4. The control barrier                                             *)
(* ---------------------------------------------------------------- *)

Theorem barrier_step_nonneg (g x y : R) : g <= 1 -> 0 <= x -> (1 - g) * x <= y -> 0 <= y.
Proof. intros hg hx hs. assert (0 <= (1 - g) * x) by (apply Rmult_le_pos; lra). lra. Qed.

(** Law 4: under h (k+1) >= (1 - g) h k, h stays above the geometric floor. *)
Theorem barrier_floor (h : nat -> R) (g : R) :
  g <= 1 -> (forall k, (1 - g) * h k <= h (S k)) -> forall k, (1 - g) ^ k * h 0%nat <= h k.
Proof.
  intros hg hs k. induction k as [| k IH]; [simpl; lra |].
  simpl. rewrite Rmult_assoc.
  apply Rle_trans with ((1 - g) * h k); [apply Rmult_le_compat_l; lra | apply hs].
Qed.

(** Law 4: the safe set h >= 0 is forward invariant. *)
Theorem barrier_forward_invariant (h : nat -> R) (g : R) :
  g <= 1 -> (forall k, (1 - g) * h k <= h (S k)) -> 0 <= h 0%nat -> forall k, 0 <= h k.
Proof.
  intros hg hs h0 k. apply Rle_trans with ((1 - g) ^ k * h 0%nat).
  - apply Rmult_le_pos; [apply pow_le; lra | exact h0].
  - exact (barrier_floor h g hg hs k).
Qed.

(* ---------------------------------------------------------------- *)
(* 5. The clipped multiplicative step and the apportionment           *)
(* ---------------------------------------------------------------- *)

(** The clamp of the runtime (ppo_clipped_step.rs clamp). *)
Definition clamp (lo hi v : R) : R :=
  if Rlt_dec v lo then lo else if Rlt_dec hi v then hi else v.

Theorem clamp_mem (lo hi v : R) : lo <= hi -> lo <= clamp lo hi v <= hi.
Proof. intro h. unfold clamp. destruct (Rlt_dec v lo); [lra |]. destruct (Rlt_dec hi v); lra. Qed.

(** An arm: its weight and its clamped relative change. *)
Definition scaledW (a : R * R) : R := fst a * (1 + snd a).

Definition sumW (l : list (R * R)) : R := fold_right (fun a acc => fst a + acc) 0 l.

Definition sumScaled (l : list (R * R)) : R := fold_right (fun a acc => scaledW a + acc) 0 l.

Definition ppoStep (l : list (R * R)) : list R := map (fun a => scaledW a / sumScaled l) l.

Definition ArmsOk (clip : R) (l : list (R * R)) : Prop :=
  Forall (fun a => 0 <= fst a /\ - clip <= snd a /\ snd a <= clip) l.

(** Law 5: before renormalisation each weight moves by at most the clip times itself. *)
Theorem scaled_move (clip : R) (a : R * R) :
  0 <= fst a -> - clip <= snd a -> snd a <= clip ->
  - (clip * fst a) <= scaledW a - fst a /\ scaledW a - fst a <= clip * fst a.
Proof. intros hw hlo hhi. unfold scaledW. split; nra. Qed.

Lemma sumScaled_mem (clip : R) (l : list (R * R)) :
  ArmsOk clip l -> (1 - clip) * sumW l <= sumScaled l /\ sumScaled l <= (1 + clip) * sumW l.
Proof.
  induction l as [| a l IH]; intro h; [simpl; lra |].
  inversion h as [| ? ? [hw [hlo hhi]] hl]; subst.
  destruct (IH hl) as [ih1 ih2]. destruct (scaled_move clip a hw hlo hhi) as [hm1 hm2].
  simpl. split; nra.
Qed.

Lemma sum_map_div (l : list (R * R)) (S : R) :
  fold_right Rplus 0 (map (fun a => scaledW a / S) l) = sumScaled l / S.
Proof. induction l as [| a l IH]; simpl; [unfold Rdiv; ring | rewrite IH; unfold Rdiv; ring]. Qed.

(** Law 5: the step of a distribution is a distribution. *)
Theorem ppoStep_simplex (clip : R) (l : list (R * R)) :
  clip < 1 -> ArmsOk clip l -> sumW l = 1 ->
  Forall (fun x => 0 <= x) (ppoStep l) /\ fold_right Rplus 0 (ppoStep l) = 1.
Proof.
  intros hc h hs. destruct (sumScaled_mem clip l h) as [h1 _]. rewrite hs in h1.
  assert (hS : 0 < sumScaled l) by lra.
  split.
  - unfold ppoStep. apply Forall_map. eapply Forall_impl; [| exact h].
    intros a [hw [hlo _]]. unfold scaledW, Rdiv.
    apply Rmult_le_pos; [apply Rmult_le_pos; lra | apply Rlt_le, Rinv_0_lt_compat; exact hS].
  - unfold ppoStep. rewrite sum_map_div. field. lra.
Qed.

(** Law 5: each normalised weight stays within the ratio (1 + clip)/(1 - clip) of its predecessor. *)
Theorem ppoStep_ratio (clip : R) (l : list (R * R)) :
  clip < 1 -> ArmsOk clip l -> sumW l = 1 ->
  forall a, In a l ->
    (1 - clip) * fst a <= (1 + clip) * (scaledW a / sumScaled l) /\
    (1 - clip) * (scaledW a / sumScaled l) <= (1 + clip) * fst a.
Proof.
  intros hc h hs a ha. destruct (sumScaled_mem clip l h) as [h1 h2]. rewrite hs in h1, h2.
  assert (hS : 0 < sumScaled l) by lra.
  destruct (proj1 (Forall_forall _ l) h a ha) as [hw [hlo hhi]].
  destruct (scaled_move clip a hw hlo hhi) as [hm1 hm2].
  set (v := scaledW a / sumScaled l).
  assert (hv : 0 <= v).
  { unfold v, scaledW, Rdiv. apply Rmult_le_pos; [apply Rmult_le_pos; lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
  assert (hdef : v * sumScaled l = scaledW a) by (unfold v; field; lra).
  assert (hup : v * sumScaled l <= v * (1 + clip)) by (apply Rmult_le_compat_l; lra).
  assert (hdn : v * (1 - clip) <= v * sumScaled l) by (apply Rmult_le_compat_l; lra).
  split; nra.
Qed.

(** A unit of the apportionment: the scaled weight, its floor and whether it receives one missing unit. *)
Definition bump (b : bool) : nat := if b then 1%nat else 0%nat.

Definition apportioned (p : R * (nat * bool)) : nat := (fst (snd p) + bump (snd (snd p)))%nat.

Definition natSum (l : list nat) : nat := fold_right Nat.add 0%nat l.

Definition FloorsOk (l : list (R * (nat * bool))) : Prop :=
  Forall (fun p => INR (fst (snd p)) <= fst p /\ fst p < INR (fst (snd p)) + 1) l.

(** A bump goes only to a positive remainder (the largest-remainder order gives one). *)
Definition BumpsPositive (l : list (R * (nat * bool))) : Prop :=
  Forall (fun p => snd (snd p) = true -> INR (fst (snd p)) < fst p) l.

(** Law 5: the apportioned total is the floors' total plus the bumps. *)
Theorem apportion_sum (l : list (R * (nat * bool))) :
  natSum (map apportioned l) = (natSum (map (fun p => fst (snd p)) l) + natSum (map (fun p => bump (snd (snd p))) l))%nat.
Proof. induction l as [| p l IH]; simpl; [reflexivity | unfold apportioned at 1; rewrite IH; lia]. Qed.

(** Law 5: each apportioned count is within one of its scaled weight. *)
Theorem apportion_close (l : list (R * (nat * bool))) :
  FloorsOk l -> BumpsPositive l -> forall p, In p l -> fst p - 1 < INR (apportioned p) < fst p + 1.
Proof.
  intros hf hb p hp.
  destruct (proj1 (Forall_forall _ l) hf p hp) as [h1 h2].
  pose proof (proj1 (Forall_forall _ l) hb p hp) as hpos.
  destruct p as [x [f b]]; simpl in *. unfold apportioned; simpl. rewrite plus_INR.
  destruct b; simpl; [pose proof (hpos eq_refl); lra | lra].
Qed.

Definition sumX (l : list (R * (nat * bool))) : R := fold_right (fun p acc => fst p + acc) 0 l.

Definition sumF (l : list (R * (nat * bool))) : nat := natSum (map (fun p => fst (snd p)) l).

Lemma apportion_missing_le (l : list (R * (nat * bool))) : FloorsOk l -> sumX l - INR (sumF l) <= INR (length l).
Proof.
  induction l as [| p l IH]; intro hf; [unfold sumX, sumF; simpl; lra |].
  inversion hf as [| ? ? [h1 h2] hl]; subst. pose proof (IH hl) as ih.
  unfold sumX, sumF, natSum in *. cbn [fold_right map length] in *. rewrite plus_INR, S_INR. lra.
Qed.

(** Law 5: the missing units are fewer than the arms. *)
Theorem apportion_missing_lt (l : list (R * (nat * bool))) :
  FloorsOk l -> l <> [] -> sumX l - INR (sumF l) < INR (length l).
Proof.
  destruct l as [| p l]; intros hf hne; [contradiction |].
  inversion hf as [| ? ? [h1 h2] hl]; subst. pose proof (apportion_missing_le l hl) as ih.
  unfold sumX, sumF, natSum in *. cbn [fold_right map length] in *. rewrite plus_INR, S_INR. lra.
Qed.

(* ---------------------------------------------------------------- *)
(* 6. One verified evidence bit costs at least k_B T ln 2             *)
(* ---------------------------------------------------------------- *)

(** The bits a close counts as evidence: its claimed bits from the Verified level up. *)
Definition countedBits (s : ClaimStatus) (e : Evidence) (bits : nat) : nat :=
  match levelOf s e with
  | AtLevel l => if Nat.leb 3 (rank l) then bits else 0%nat
  | Refused => 0%nat
  end.

Lemma countedBits_le (s : ClaimStatus) (e : Evidence) (bits : nat) : (countedBits s e bits <= bits)%nat.
Proof. unfold countedBits. destruct (levelOf s e); [lia | destruct (Nat.leb 3 (rank l)); lia]. Qed.

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

(** Law 6: the counted evidence bits of a close paid by an erasure of its bits obeying SecondLaw cost at least
    k_B T ln 2 each. *)
Theorem countedBits_cost (s : ClaimStatus) (e : Evidence) (b : HeatBath) (W : R) (bits : nat)
  (hn : (0 < 2 ^ bits)%nat) :
  SecondLaw (erase (mkErasure b W)) (transformation (uniformN (2 ^ bits) hn) (diracN (2 ^ bits - 1))) ->
  INR (countedBits s e bits) * (kB * bathTemp b * ln 2) <= kB * W.
Proof.
  intro h. pose proof (bitErasure_cost b W bits hn h) as hc.
  assert (hL : 0 <= kB * bathTemp b * ln 2).
  { pose proof kB_pos. pose proof (bathTemp_pos b). pose proof ln2_pos.
    apply Rmult_le_pos; [apply Rmult_le_pos |]; lra. }
  apply Rle_trans with (INR bits * (kB * bathTemp b * ln 2)); [| exact hc].
  apply Rmult_le_compat_r; [exact hL | apply le_INR, countedBits_le].
Qed.

(** Law 6: a verified close of at least one evidence bit, paid by an erasure of its bits obeying SecondLaw, spends
    honestly (honest_spend_of_secondLaw) and pays at least one Landauer bit energy k_B T ln 2. *)
Theorem verified_bit_costs_landauer (e : Evidence) (b : HeatBath) (W : R) (bits : nat) (hn : (0 < 2 ^ bits)%nat) :
  verified e = true -> (1 <= bits)%nat ->
  SecondLaw (erase (mkErasure b W)) (transformation (uniformN (2 ^ bits) hn) (diracN (2 ^ bits - 1))) ->
  countedBits Complete e bits = bits /\ honest_spend (bathTemp b) (INR bits) (kB * W) /\
  kB * bathTemp b * ln 2 <= kB * W.
Proof.
  intros hv hbits h.
  assert (hcount : countedBits Complete e bits = bits).
  { destruct e as [g v l m]; simpl in hv; subst v. unfold countedBits; simpl.
    destruct l, m; reflexivity. }
  pose proof (honest_spend_of_secondLaw b W bits hn h) as hh.
  split; [exact hcount | split; [exact hh |]].
  unfold honest_spend in hh.
  assert (hL : 0 <= kB * bathTemp b * ln 2).
  { pose proof kB_pos. pose proof (bathTemp_pos b). pose proof ln2_pos.
    apply Rmult_le_pos; [apply Rmult_le_pos |]; lra. }
  assert (h1 : 1 <= INR bits) by (change 1 with (INR 1); apply le_INR; exact hbits).
  nra.
Qed.
