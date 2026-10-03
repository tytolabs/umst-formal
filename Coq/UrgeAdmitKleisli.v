(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: UrgeAdmitKleisli.v                                       *)
(*                                                                        *)
(*  Twin of Lean/Urge/AdmitKleisli.lean: a history move carries the gate  *)
(*  admissibility of its head move and the erasure that pays for it; the  *)
(*  move is admissible exactly when that erasure is an instance of the    *)
(*  one predicate SecondLaw (the Clausius bound: the erased entropy is    *)
(*  at most the work over the bath temperature). History head moves are   *)
(*  Kleisli arrows over thermodynamic states; their category laws hold    *)
(*  pointwise at every state. Zero Axiom, Parameter or Admitted.          *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra.
Require Import UMSTFormal.Concrete.Gate UMSTFormal.Constitutional UMSTFormal.Process.

Open Scope R_scope.

(** Content-addressed history snapshot: commit id and gate-checked head state. *)
Record HistorySnapshot : Type := mkSnapshot {
  commitId : nat;
  snapHead : ThermodynamicState
}.

(** A move of the history head and the erasure that pays for it: the head move passes the gate, and the erasure
    erases the distribution [htErased] (the information the move discards). *)
Record HistoryTransition : Type := mkHistoryTransition {
  htPrior : HistorySnapshot;
  htPost : HistorySnapshot;
  htGate : admissible (snapHead htPrior) (snapHead htPost);
  htErasure : ErasureProcess;
  htErased : ProbDist2
}.

(** A history move is admissible when its erasure is an instance of the one second law. *)
Definition admissibleHistoryTransition (t : HistoryTransition) : Prop :=
  SecondLaw (erase (htErasure t)) (erasure (htErased t)).

(** Admissibility is the Clausius bound of the erasure: the erased entropy is at most the work over the bath
    temperature. *)
Theorem admissibleHistoryTransition_iff (t : HistoryTransition) :
  admissibleHistoryTransition t <->
    shannon2 (htErased t) <= work (htErasure t) / bathTemp (erasureBath (htErasure t)).
Proof.
  unfold admissibleHistoryTransition. simpl. unfold eraseSecondLaw. rewrite shannon2_dirac0.
  split; intro h; lra.
Qed.

(** Kleisli identity on history head states. *)
Definition admitIdentity : KleisliArrow := fun s => Some s.

(** Associativity at a state. *)
Theorem kleisliComposeAssocAt (f g h : KleisliArrow) (s : ThermodynamicState) :
  kleisli_compose (kleisli_compose f g) h s = kleisli_compose f (kleisli_compose g h) s.
Proof.
  unfold kleisli_compose. destruct (f s) as [s' |]; [| reflexivity].
  destruct (g s') as [s'' |]; reflexivity.
Qed.

(** Left unit law at a state. *)
Theorem kleisliLeftUnitAt (f : KleisliArrow) (s : ThermodynamicState) :
  kleisli_compose admitIdentity f s = f s.
Proof. reflexivity. Qed.

(** Right unit law at a state. *)
Theorem kleisliRightUnitAt (f : KleisliArrow) (s : ThermodynamicState) :
  kleisli_compose f admitIdentity s = f s.
Proof. unfold kleisli_compose, admitIdentity. destruct (f s); reflexivity. Qed.
