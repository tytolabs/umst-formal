(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: PredictionFeedback.v                                     *)
(*                                                                        *)
(*  Twin of Lean/PredictionFeedback.lean: a prediction-then-observation   *)
(*  turn of the learning loop is an instance of the measureFeedback case  *)
(*  of the one predicate SecondLaw, judged against the mutual information *)
(*  (nats) between prediction and outcome. A summary of receipts carrying *)
(*  no more information than the receipts (the data-processing            *)
(*  inequality, a hypothesis) admits no work the receipts refuse; the     *)
(*  gated choices err in sum by at most the prediction errors plus the   *)
(*  gate's moves.                                                         *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Require Import UMSTFormal.Process.

Open Scope R_scope.

(** One turn: the bath, the work extracted by acting on the prediction, the free-energy change, and the mutual
    information between prediction and outcome. *)
Record Turn : Type := mkTurn {
  turnBath : HeatBath;
  turnWork : R;
  turnDeltaF : R;
  turnInfo : R
}.

Definition turnProcess (t : Turn) : Process := measureFeedback (mkFeedback (turnBath t) (turnWork t) (turnDeltaF t)).

Definition turnAdmissible (t : Turn) : Prop := SecondLaw (turnProcess t) (feedback (turnInfo t)).

(** The turn is a measureFeedback instance: admissibility is the Sagawa-Ueda inequality at its information. *)
Theorem turn_admissible_iff (t : Turn) :
  turnAdmissible t <-> turnWork t <= - turnDeltaF t + kB * bathTemp (turnBath t) * turnInfo t.
Proof. unfold turnAdmissible, turnProcess. simpl. tauto. Qed.

Theorem turn_work_le (t : Turn) :
  turnAdmissible t -> turnWork t <= - turnDeltaF t + kB * bathTemp (turnBath t) * turnInfo t.
Proof. intro h. apply turn_admissible_iff. exact h. Qed.

(** A cyclic turn extracts at most k_B T times the information its prediction carries. *)
Theorem turn_cyclic_work_le (t : Turn) :
  turnAdmissible t -> turnDeltaF t = 0 -> turnWork t <= kB * bathTemp (turnBath t) * turnInfo t.
Proof. intros h hF. pose proof (turn_work_le t h) as hw. rewrite hF in hw. lra. Qed.

(** Two admissible turns at one bath add. *)
Theorem turn_pair_work_le (s t : Turn) :
  bathTemp (turnBath s) = bathTemp (turnBath t) -> turnAdmissible s -> turnAdmissible t ->
  turnWork s + turnWork t <= - (turnDeltaF s + turnDeltaF t) + kB * bathTemp (turnBath s) * (turnInfo s + turnInfo t).
Proof.
  intros hT hs ht. pose proof (turn_work_le s hs) as h1. pose proof (turn_work_le t ht) as h2.
  rewrite <- hT in h2. lra.
Qed.

(** The same turn judged against another information (the receipts', or a summary's). *)
Definition against (t : Turn) (i : R) : Turn := mkTurn (turnBath t) (turnWork t) (turnDeltaF t) i.

(** Data-processing corollary: a summary carrying no more information than the receipts admits only works the
    receipts admit. *)
Theorem summary_admitted_receipts (t : Turn) (iSummary iReceipts : R) :
  iSummary <= iReceipts -> turnAdmissible (against t iSummary) -> turnAdmissible (against t iReceipts).
Proof.
  intros hDPI h. apply turn_admissible_iff. pose proof (proj1 (turn_admissible_iff _) h) as h'.
  unfold against in *. cbn [turnBath turnWork turnDeltaF turnInfo] in *.
  pose proof kB_pos. pose proof (bathTemp_pos (turnBath t)).
  assert (0 <= kB * bathTemp (turnBath t)) by (apply Rmult_le_pos; lra).
  assert (kB * bathTemp (turnBath t) * iSummary <= kB * bathTemp (turnBath t) * iReceipts)
    by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

Theorem receipts_refused_summary (t : Turn) (iSummary iReceipts : R) :
  iSummary <= iReceipts -> ~ turnAdmissible (against t iReceipts) -> ~ turnAdmissible (against t iSummary).
Proof. intros hDPI h hs. exact (h (summary_admitted_receipts t iSummary iReceipts hDPI hs)). Qed.

(** One decision: the gated choice errs by at most the prediction's error plus the gate's move. *)
Lemma gated_error_le (p g y d : R) : Rabs (g - p) <= d -> Rabs (g - y) <= Rabs (p - y) + d.
Proof.
  intro hd. replace (g - y) with ((g - p) + (p - y)) by ring.
  pose proof (Rabs_triang (g - p) (p - y)). lra.
Qed.

(** A gated decision: prediction, gated choice, outcome and the gate's move bound. *)
Definition sumOver (f : R * R * R * R -> R) (l : list (R * R * R * R)) : R := fold_right (fun q acc => f q + acc) 0 l.

(** Separation corollary, over the loop's decisions: the summed error of the gated choices is at most the summed
    prediction error plus the summed moves. *)
Theorem gated_error_sum_le (l : list (R * R * R * R)) :
  Forall (fun q => match q with (p, g, _, d) => Rabs (g - p) <= d end) l ->
  sumOver (fun q => match q with (_, g, y, _) => Rabs (g - y) end) l <=
  sumOver (fun q => match q with (p, _, y, _) => Rabs (p - y) end) l + sumOver (fun q => match q with (_, _, _, d) => d end) l.
Proof.
  induction l as [| q l IH]; intro h; [simpl; lra |].
  inversion h as [| ? ? hq hl]; subst. destruct q as [[[p g] y] d].
  pose proof (gated_error_le p g y d hq). pose proof (IH hl). simpl in *. lra.
Qed.
