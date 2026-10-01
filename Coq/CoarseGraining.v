(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: CoarseGraining.v                                         *)
(*                                                                        *)
(*  Twin of Lean/CoarseGraining.lean: a coarse-graining map on the        *)
(*  process family, the Esposito conditions on its erase branch (work     *)
(*  preserved, coarse entropy drop at most the fine one), and fine        *)
(*  admissibility implying coarse admissibility. Coq's feedback prior     *)
(*  carries the information, not a joint distribution, so the pair lump  *)
(*  is stated by its content: for a product joint H(X,Y) = H(X) + H(Y)    *)
(*  >= H(X), so the fine erasure of the pair admits the coarse erasure.   *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra.
Require Import UMSTFormal.Process.

Open Scope R_scope.

Record CoarseGrainMap : Type := mkCoarseGrainMap {
  mapProcess : Process -> Process;
  mapPrior : Prior -> Prior
}.

Definition idCoarseGrainMap : CoarseGrainMap := mkCoarseGrainMap (fun p => p) (fun pr => pr).

(** Composition (fine to meso to macro). *)
Definition comp (g f : CoarseGrainMap) : CoarseGrainMap :=
  mkCoarseGrainMap (fun p => mapProcess g (mapProcess f p)) (fun pr => mapPrior g (mapPrior f pr)).

(** Entropy drop of an erasure to the Dirac state. *)
Definition eraseEntropyDrop (p : ProbDist2) : R := shannon2 p - shannon2 dirac0.

(** Esposito conditions (PRE 85, 041125) on the erase branch: work and bath preserved, the coarse entropy drop
    at most the fine one, and erasures mapped to erasures. *)
Record EspositoConditions (cg : CoarseGrainMap) : Prop := mkEsposito {
  erase_work_preservation : forall e e', mapProcess cg (erase e) = erase e' -> work e' = work e /\ erasureBath e' = erasureBath e;
  erase_entropy_drop_lower_bound : forall e e' p q, mapProcess cg (erase e) = erase e' ->
    mapPrior cg (erasure p) = erasure q -> eraseEntropyDrop q <= eraseEntropyDrop p;
  erase_process_image : forall e, exists e', mapProcess cg (erase e) = erase e';
  erase_erasure_prior_image : forall p, exists q, mapPrior cg (erasure p) = erasure q
}.

(** Fine erase admissibility implies coarse erase admissibility under the Esposito conditions. *)
Theorem secondLaw_coarse_from_fine (cg : CoarseGrainMap) (h : EspositoConditions cg) (e : ErasureProcess) (p : ProbDist2) :
  SecondLaw (erase e) (erasure p) -> SecondLaw (mapProcess cg (erase e)) (mapPrior cg (erasure p)).
Proof.
  intro hFine.
  destruct (erase_process_image cg h e) as [e' hP]. destruct (erase_erasure_prior_image cg h p) as [q hQ].
  destruct (erase_work_preservation cg h e e' hP) as [hW hB].
  pose proof (erase_entropy_drop_lower_bound cg h e e' p q hP hQ) as hD.
  rewrite hP, hQ. simpl in *. unfold eraseSecondLaw, eraseEntropyDrop in *. rewrite hW, hB. lra.
Qed.

Theorem espositoConditions_id : EspositoConditions idCoarseGrainMap.
Proof.
  constructor; simpl.
  - intros e e' hE. inversion hE. split; reflexivity.
  - intros e e' p q _ hQ. inversion hQ. lra.
  - intro e. exists e. reflexivity.
  - intro p. exists p. reflexivity.
Qed.

(** Coarse refusal is sound: a refused coarse erasure refuses the fine one. *)
Theorem coarse_refusal_sound_erase (cg : CoarseGrainMap) (h : EspositoConditions cg) (e : ErasureProcess) (p : ProbDist2) :
  ~ SecondLaw (mapProcess cg (erase e)) (mapPrior cg (erasure p)) -> ~ SecondLaw (erase e) (erasure p).
Proof. intros hBad hFine. exact (hBad (secondLaw_coarse_from_fine cg h e p hFine)). Qed.

(* --------------------------------------------------------------------- *)
(*  The pair lump: H(X) <= H(X, Y) for a product joint                    *)
(* --------------------------------------------------------------------- *)

Lemma xlnx_mult (a b : R) : 0 <= a -> 0 <= b -> xlnx (a * b) = a * xlnx b + b * xlnx a.
Proof.
  intros ha hb. unfold xlnx.
  destruct (Rle_dec (a * b) 0) as [hab | hab];
  destruct (Rle_dec a 0) as [ha0 | ha0]; destruct (Rle_dec b 0) as [hb0 | hb0];
  first [ assert (a = 0) by lra; subst; ring
        | assert (b = 0) by lra; subst; ring
        | exfalso; nra
        | rewrite ln_mult by lra; ring ].
Qed.

Lemma xlnx_nonpos (x : R) : x <= 1 -> xlnx x <= 0.
Proof.
  intro h1. unfold xlnx. destruct (Rle_dec x 0) as [h | h]; [lra |].
  assert (hl : ln x <= 0).
  { destruct (Req_dec x 1) as [e | ne]; [subst; rewrite ln_1; lra |].
    rewrite <- ln_1. apply Rlt_le. apply ln_increasing; lra. }
  nra.
Qed.

Lemma shannon2_nonneg (p : ProbDist2) : 0 <= shannon2 p.
Proof.
  unfold shannon2. pose proof (p0_nonneg p). pose proof (p0_le_one p).
  pose proof (xlnx_nonpos (p0 p) ltac:(lra)). pose proof (xlnx_nonpos (1 - p0 p) ltac:(lra)). lra.
Qed.

(** The product joint of two binary distributions. *)
Definition productJoint2 (p q : ProbDist2) : JointDist2.
Proof.
  refine (mkJointDist2 (p0 p * p0 q) (p0 p * (1 - p0 q)) ((1 - p0 p) * p0 q) ((1 - p0 p) * (1 - p0 q)) _ _ _ _ _);
  pose proof (p0_nonneg p); pose proof (p0_le_one p); pose proof (p0_nonneg q); pose proof (p0_le_one q);
  first [apply Rmult_le_pos; lra | ring].
Defined.

(** For a product joint the joint entropy is the sum of the marginals' entropies. *)
Theorem jointEntropy2_product (p q : ProbDist2) : jointEntropy2 (productJoint2 p q) = shannon2 p + shannon2 q.
Proof.
  unfold jointEntropy2, productJoint2, shannon2. simpl.
  pose proof (p0_nonneg p). pose proof (p0_le_one p). pose proof (p0_nonneg q). pose proof (p0_le_one q).
  rewrite !xlnx_mult by lra. ring.
Qed.

(** Lumping the pair to its first factor lowers the entropy to erase: H(X) <= H(X, Y). *)
Theorem shannon2_le_jointEntropy2_product (p q : ProbDist2) : shannon2 p <= jointEntropy2 (productJoint2 p q).
Proof. rewrite jointEntropy2_product. pose proof (shannon2_nonneg q). lra. Qed.

(** Fine admissibility of erasing the pair implies coarse admissibility of erasing its first factor. *)
Theorem lumpPair_secondLaw_coarse_from_fine_joint (e : ErasureProcess) (p q : ProbDist2) :
  jointEntropy2 (productJoint2 p q) <= work e / bathTemp (erasureBath e) -> SecondLaw (erase e) (erasure p).
Proof.
  intro hFine. simpl. unfold eraseSecondLaw. rewrite shannon2_dirac0.
  pose proof (shannon2_le_jointEntropy2_product p q). lra.
Qed.

(** The conditions are satisfiable. *)
Theorem coarse_graining_satisfiable : exists cg, EspositoConditions cg.
Proof. exists idCoarseGrainMap. exact espositoConditions_id. Qed.
