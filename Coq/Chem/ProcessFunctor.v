(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Chem/ProcessFunctor.v                                  *)
(*                                                                      *)
(*  Chemistry as an instance of the one predicate SecondLaw: an update  *)
(*  is sent to the erasure that pays for it, judged against the         *)
(*  transformation of its state distribution. Updates form a category  *)
(*  (identity, composite) and the map is a functor that preserves       *)
(*  admissibility. Twin of Lean/Chem/ProcessFunctor.lean. ZERO axioms.  *)
(* ================================================================== *)

From Stdlib Require Import Reals Lra.
From UMSTFormal Require Import Process.
Require Import UMSTFormal.Chem.SecondLaw.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  The image of an update in the process family                        *)
(* ------------------------------------------------------------------ *)

(** The process an update is: the erasure that pays for it. *)
Definition tcProcess (t : ThermochemicalTransition) : Process := erase (tcErasure t).

(** The prior an update is judged against: the transformation of its state distribution. *)
Definition tcTransformation (t : ThermochemicalTransition) : Prior := transformation (tcPrior t) (tcPost t).

Theorem chemSecondLaw_iff_process (t : ThermochemicalTransition) :
  chemSecondLaw t <-> structurallyCoherent t /\ SecondLaw (tcProcess t) (tcTransformation t).
Proof. reflexivity. Qed.

(** The erasure and the entropy drop, typed through the erase case. *)
Theorem secondLaw_iff_entropyDrop (t : ThermochemicalTransition) :
  SecondLaw (erase (tcErasure t)) (transformation (tcPrior t) (tcPost t)) <->
    assemblageEntropyDrop t <= tcWork t / bathTemp (tcBath t).
Proof. reflexivity. Qed.

(** The Landauer work floor, typed through the erase case. *)
Theorem secondLaw_iff_workFloor (t : ThermochemicalTransition) :
  SecondLaw (erase (tcErasure t)) (transformation (tcPrior t) (tcPost t)) <->
    refinementWorkFloor (assemblageEntropyDrop t) (bathTemp (tcBath t)) <= tcWork t.
Proof. symmetry. exact (refinementWorkAccounted_iff t). Qed.

(* ------------------------------------------------------------------ *)
(*  The category of updates and the functor                             *)
(* ------------------------------------------------------------------ *)

(** The identity update of distribution [p] at bath [b]: no change, no work, no defect. *)
Definition tcIdAt (b : HeatBath) (p : ProbDist) : ThermochemicalTransition := mkThermochemicalTransition b p p 0 0.

(** The composite of [t1] then [t2] at the bath of [t1]: works and defects added. *)
Definition tcSeq (t1 t2 : ThermochemicalTransition) : ThermochemicalTransition :=
  mkThermochemicalTransition (tcBath t1) (tcPrior t1) (tcPost t2) (tcWork t1 + tcWork t2) (tcDefect t1 + tcDefect t2).

Theorem tcSeq_idAt_left (t : ThermochemicalTransition) : tcSeq (tcIdAt (tcBath t) (tcPrior t)) t = t.
Proof. destruct t. unfold tcSeq, tcIdAt. simpl. f_equal; ring. Qed.

Theorem tcSeq_idAt_right (t : ThermochemicalTransition) : tcSeq t (tcIdAt (tcBath t) (tcPost t)) = t.
Proof. destruct t. unfold tcSeq, tcIdAt. simpl. f_equal; ring. Qed.

Theorem tcSeq_assoc (t1 t2 t3 : ThermochemicalTransition) : tcSeq (tcSeq t1 t2) t3 = tcSeq t1 (tcSeq t2 t3).
Proof. unfold tcSeq. simpl. f_equal; ring. Qed.

(** The functor sends an identity update to the identity transformation at zero work. *)
Theorem process_idAt (b : HeatBath) (p : ProbDist) :
  tcProcess (tcIdAt b p) = erase (mkErasure b 0) /\ tcTransformation (tcIdAt b p) = transformation p p.
Proof. split; reflexivity. Qed.

(** The functor sends a composite update to the composite transformation at the summed work. *)
Theorem process_seq (t1 t2 : ThermochemicalTransition) :
  tcProcess (tcSeq t1 t2) = erase (mkErasure (tcBath t1) (tcWork t1 + tcWork t2)) /\
  tcTransformation (tcSeq t1 t2) = transformation (tcPrior t1) (tcPost t2).
Proof. split; reflexivity. Qed.

(** Admissibility of identities. *)
Theorem chemSecondLaw_idAt (b : HeatBath) (p : ProbDist) : chemSecondLaw (tcIdAt b p).
Proof. split; [reflexivity | exact (SecondLaw_transformation_id b p)]. Qed.

(** Admissibility is closed under composition. *)
Theorem chemSecondLaw_seq (t1 t2 : ThermochemicalTransition) :
  tcBath t1 = tcBath t2 -> tcPost t1 = tcPrior t2 -> chemSecondLaw t1 -> chemSecondLaw t2 ->
  chemSecondLaw (tcSeq t1 t2).
Proof.
  intros hb hp h1 h2. split.
  - unfold structurallyCoherent, tcSeq. simpl. destruct h1 as [c1 _]. destruct h2 as [c2 _].
    unfold structurallyCoherent in c1, c2. rewrite c1, c2. ring.
  - exact (chemSecondLaw_comp t1 t2 hb hp h1 h2).
Qed.

(* ------------------------------------------------------------------ *)
(*  The binary bridge transports the erase case                         *)
(* ------------------------------------------------------------------ *)

Theorem pcProcess_eq (b : PhysicalChemBridge) : tcProcess (pcTransition b) = erase (pcProc b).
Proof.
  unfold tcProcess, tcErasure. rewrite (pcBathEq b), (pcWorkEq b). destruct (pcProc b). reflexivity.
Qed.

Theorem pcTransformation_eq (b : PhysicalChemBridge) :
  tcTransformation (pcTransition b) = transformation (asProbDist uniform2) (asProbDist dirac0).
Proof. unfold tcTransformation. rewrite (pcPriorEq b), (pcPostEq b). reflexivity. Qed.

(** The bridge preserves and reflects admissibility. *)
Theorem PhysicalChemBridge_secondLaw_iff (b : PhysicalChemBridge) :
  SecondLaw (erase (pcProc b)) (erasure uniform2) <->
    SecondLaw (tcProcess (pcTransition b)) (tcTransformation (pcTransition b)).
Proof.
  rewrite pcProcess_eq, pcTransformation_eq. exact (SecondLaw_erasure_iff_transformation (pcProc b) uniform2).
Qed.

(* ------------------------------------------------------------------ *)
(*  Identity transformations and the P0 fixture                         *)
(* ------------------------------------------------------------------ *)

(** An identity transformation obeys the erase case exactly at non-negative work. *)
Theorem secondLaw_identity_iff_work_nonneg (b : HeatBath) (p : ProbDist) (W : R) :
  SecondLaw (erase (mkErasure b W)) (transformation p p) <-> 0 <= W.
Proof.
  simpl. pose proof (bathTemp_pos b) as hT.
  replace (shannon p - shannon p) with 0 by ring. split; intro h.
  - assert (hW : W = W / bathTemp b * bathTemp b) by (field; lra). rewrite hW.
    apply Rmult_le_pos; lra.
  - unfold Rdiv. apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra].
Qed.

(** Reversibility at zero work: an update and its reverse both obey the erase case at zero work exactly when the
    update removes no entropy. *)
Theorem zeroWork_reversible_iff (t : ThermochemicalTransition) :
  (SecondLaw (erase (mkErasure (tcBath t) 0)) (transformation (tcPrior t) (tcPost t)) /\
   SecondLaw (erase (mkErasure (tcBath t) 0)) (transformation (tcPost t) (tcPrior t))) <->
  assemblageEntropyDrop t = 0.
Proof.
  simpl. unfold assemblageEntropyDrop, Rdiv. rewrite Rmult_0_l.
  split; [intros [h1 h2]; lra | intro h; split; lra].
Qed.

(** The coherent P0 fixture is the identity update of the uniform bit at 300 K. *)
Theorem coherentP0_eq_idAt : coherentP0Transition = tcIdAt (tcBath coherentP0Transition) (asProbDist uniform2).
Proof. reflexivity. Qed.

Theorem coherentP0_secondLaw_iff_work_nonneg (W : R) :
  SecondLaw (erase (mkErasure (tcBath coherentP0Transition) W))
    (transformation (tcPrior coherentP0Transition) (tcPost coherentP0Transition)) <-> 0 <= W.
Proof. exact (secondLaw_identity_iff_work_nonneg _ (asProbDist uniform2) W). Qed.

Theorem coherentP0_reversible :
  SecondLaw (erase (mkErasure (tcBath coherentP0Transition) 0))
    (transformation (tcPrior coherentP0Transition) (tcPost coherentP0Transition)) /\
  SecondLaw (erase (mkErasure (tcBath coherentP0Transition) 0))
    (transformation (tcPost coherentP0Transition) (tcPrior coherentP0Transition)).
Proof. apply zeroWork_reversible_iff. exact coherentP0_zero_entropy_drop. Qed.
