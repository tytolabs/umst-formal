(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: SemanticSecondLaw.v                                      *)
(*                                                                        *)
(*  Twin of Lean/SemanticSecondLaw.lean: a communicative transition obeys *)
(*  the one predicate on its shared model (its entropy clause is the      *)
(*  erase instance on the model's transformation), with structural        *)
(*  consistency and mutual information preserved above a threshold.       *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra.
Require Import UMSTFormal.Process UMSTFormal.CoarseGraining.

Open Scope R_scope.

(** A communicative transition on a shared model: bath, model distributions before and after, the work it
    dissipates (units of k_B times kelvin) and a consistency defect. *)
Record CommunicativeTransition : Type := mkCommunicativeTransition {
  ctBath : HeatBath;
  ctPrior : ProbDist;
  ctPost : ProbDist;
  ctWork : R;
  ctDefect : R
}.

Definition structurallyConsistent (t : CommunicativeTransition) : Prop := ctDefect t = 0.

Definition modelUncertaintyDrop (t : CommunicativeTransition) : R := shannon (ctPrior t) - shannon (ctPost t).

(** Mutual information between proposal and outcome meets the threshold. *)
Definition miPreserved (threshold : R) (J : JointDist2) : Prop := threshold <= mutualInformation2 J.

Definition semanticSecondLaw (threshold : R) (t : CommunicativeTransition) (J : JointDist2) : Prop :=
  structurallyConsistent t /\ modelUncertaintyDrop t <= ctWork t / bathTemp (ctBath t) /\ miPreserved threshold J.

(** The semantic second law is the one predicate on the shared model, with consistency and preserved information. *)
Theorem semanticSecondLaw_iff (threshold : R) (t : CommunicativeTransition) (J : JointDist2) :
  semanticSecondLaw threshold t J <->
    structurallyConsistent t /\ SecondLaw (erase (mkErasure (ctBath t) (ctWork t))) (transformation (ctPrior t) (ctPost t)) /\
    miPreserved threshold J.
Proof. reflexivity. Qed.

(** Physical realisation of a communicative transition as a uniform-binary erasure. *)
Record PhysicalSemanticBridge : Type := mkPhysicalSemanticBridge {
  psProc : ErasureProcess;
  psTransition : CommunicativeTransition;
  psBathEq : ctBath psTransition = erasureBath psProc;
  psWorkEq : ctWork psTransition = work psProc;
  psPriorEq : ctPrior psTransition = asProbDist uniform2;
  psPostEq : ctPost psTransition = asProbDist dirac0
}.

(** The erase instance discharges the entropy clause of a physically bridged transition. *)
Theorem semantic_entropy_bound_from_physical (b : PhysicalSemanticBridge) :
  eraseSecondLaw (psProc b) uniform2 ->
  modelUncertaintyDrop (psTransition b) <= ctWork (psTransition b) / bathTemp (ctBath (psTransition b)).
Proof.
  intro h. unfold modelUncertaintyDrop.
  rewrite (psPriorEq b), (psPostEq b), (psWorkEq b), (psBathEq b), !shannon_asProbDist. exact h.
Qed.

(** Landauer bound on the understanding work of a physically bridged transition. *)
Theorem understandingCostLandauerBound (b : PhysicalSemanticBridge) :
  eraseSecondLaw (psProc b) uniform2 -> bathTemp (ctBath (psTransition b)) * ln 2 <= ctWork (psTransition b).
Proof. intro h. rewrite (psBathEq b), (psWorkEq b). exact (landauerBound (psProc b) h). Qed.

Theorem semanticSecondLaw_from_physical_bridge (threshold : R) (b : PhysicalSemanticBridge) (J : JointDist2) :
  structurallyConsistent (psTransition b) -> miPreserved threshold J -> eraseSecondLaw (psProc b) uniform2 ->
  semanticSecondLaw threshold (psTransition b) J.
Proof. intros hc hm h. split; [exact hc | split; [exact (semantic_entropy_bound_from_physical b h) | exact hm]]. Qed.

(** The consistent identity transition at 300 K, dissipating nothing. *)
Definition consistentP0Transition : CommunicativeTransition :=
  mkCommunicativeTransition (mkHeatBath 300 ltac:(lra)) (asProbDist uniform2) (asProbDist uniform2) 0 0.

Theorem consistentP0_zero_uncertainty_drop : modelUncertaintyDrop consistentP0Transition = 0.
Proof. unfold modelUncertaintyDrop. cbn [ctPrior ctPost consistentP0Transition]. ring. Qed.

Theorem consistentP0_structurallyConsistent : structurallyConsistent consistentP0Transition.
Proof. reflexivity. Qed.

(** A product joint carries no mutual information, so it meets the threshold zero. *)
Theorem productWitness_mi_zero (p q : ProbDist2) : mutualInformation2 (productJoint2 p q) = 0.
Proof.
  unfold mutualInformation2. rewrite jointEntropy2_product.
  rewrite (shannon2_ext (marginalX2 (productJoint2 p q)) p) by (simpl; ring).
  rewrite (shannon2_ext (marginalY2 (productJoint2 p q)) q) by (simpl; ring).
  ring.
Qed.

Theorem productWitness_miPreserved_at_zero (p q : ProbDist2) : miPreserved 0 (productJoint2 p q).
Proof. unfold miPreserved. rewrite productWitness_mi_zero. lra. Qed.
