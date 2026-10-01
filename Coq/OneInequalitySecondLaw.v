(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: OneInequalitySecondLaw.v                                 *)
(*                                                                        *)
(*  Twin of Lean/OneInequalitySecondLaw.lean: the second law as one free- *)
(*  energy inequality  dF <= W_in + k_B T I  (joules; I in nats). Each    *)
(*  process kind fixes which terms vanish; one chaining lemma composes    *)
(*  arbitrary mixed sequences at a common bath (the Szilard measure-then- *)
(*  erase cycle as witness). Every account is equivalent to the one       *)
(*  predicate SecondLaw of Process.v.                                     *)
(* ===================================================================== *)

From Stdlib Require Import Reals Lra QArith Qreals.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.

Open Scope R_scope.

(** One thermodynamic step: its bath, free-energy change, work in (joules) and information (nats). *)
Record Step : Type := mkStep {
  stepBath : HeatBath;
  deltaF : R;
  wIn : R;
  infoI : R
}.

(** The second law as one inequality. *)
Definition oneInequality (s : Step) : Prop := deltaF s <= wIn s + kB * bathTemp (stepBath s) * infoI s.

(** Sequential composition at the first step's bath: free energy, work and information add. *)
Definition chain (s1 s2 : Step) : Step :=
  mkStep (stepBath s1) (deltaF s1 + deltaF s2) (wIn s1 + wIn s2) (infoI s1 + infoI s2).

(** Chaining: admissible steps at a common bath temperature compose. *)
Theorem oneInequality_chain (s1 s2 : Step) :
  bathTemp (stepBath s1) = bathTemp (stepBath s2) -> oneInequality s1 -> oneInequality s2 ->
  oneInequality (chain s1 s2).
Proof.
  unfold oneInequality, chain. simpl. intros hT h1 h2. rewrite <- hT in h2.
  replace (kB * bathTemp (stepBath s1) * (infoI s1 + infoI s2))
    with (kB * bathTemp (stepBath s1) * infoI s1 + kB * bathTemp (stepBath s1) * infoI s2) by ring.
  lra.
Qed.

(** Erase (joules): I = 0, dF = k_B T (S(prior) - S(post)), W_in = k_B W. *)
Definition eraseStep (e : ErasureProcess) (p q : ProbDist) : Step :=
  mkStep (erasureBath e) (kB * bathTemp (erasureBath e) * (shannon p - shannon q)) (kB * work e) 0.

Theorem eraseStep_oneInequality_iff (e : ErasureProcess) (p q : ProbDist) :
  SecondLaw (erase e) (transformation p q) <-> oneInequality (eraseStep e p q).
Proof.
  simpl. unfold oneInequality, eraseStep. simpl.
  pose proof kB_pos as hk. pose proof (bathTemp_pos (erasureBath e)) as hT.
  assert (hkT : 0 < kB * bathTemp (erasureBath e)) by (apply Rmult_lt_0_compat; assumption).
  assert (hT0 : bathTemp (erasureBath e) <> 0) by (apply Rgt_not_eq; exact hT).
  assert (hcancel : kB * bathTemp (erasureBath e) * (work e / bathTemp (erasureBath e)) = kB * work e)
    by (field; exact hT0).
  rewrite Rmult_0_r, Rplus_0_r. split; intro h.
  - apply Rmult_le_compat_l with (r := kB * bathTemp (erasureBath e)) in h; [| apply Rlt_le; exact hkT].
    rewrite hcancel in h. exact h.
  - apply Rmult_le_reg_l with (kB * bathTemp (erasureBath e)); [exact hkT |].
    rewrite hcancel. exact h.
Qed.

(** Measurement with feedback: W_in = -W_ext, I the information acquired. *)
Definition feedbackStep (f : FeedbackProcess) (mi : R) : Step :=
  mkStep (feedbackBath f) (deltaFreeEnergy f) (- extWork f) mi.

Theorem SecondLaw_measureFeedback_oneInequality_iff (f : FeedbackProcess) (mi : R) :
  SecondLaw (measureFeedback f) (feedback mi) <-> oneInequality (feedbackStep f mi).
Proof. simpl. unfold oneInequality, feedbackStep. simpl. split; intro h; lra. Qed.

(** Passive transition at a bath: W_in = 0 and I = 0, so dF <= 0. *)
Definition transitionStepAt (b : HeatBath) (old new_ : ThermodynamicState) : Step :=
  mkStep b (Q2R (free_energy new_) - Q2R (free_energy old)) 0 0.

Theorem SecondLaw_transition_oneInequality_iff (b : HeatBath) (old new_ : ThermodynamicState) :
  SecondLaw transition (thermodynamic old new_) <->
    oneInequality (transitionStepAt b old new_) /\ core_mass_cond (density old) (density new_).
Proof.
  simpl. unfold core_admissible, core_mass_cond, oneInequality, transitionStepAt. simpl.
  rewrite Rmult_0_r, Rplus_0_r. split.
  - intros [m1 [m2 hd]]. split; [| split; assumption].
    apply Qle_Rle in hd. lra.
  - intros [hd [m1 m2]]. split; [exact m1 | split; [exact m2 |]].
    apply Rle_Qle. lra.
Qed.

(** An admissible transition followed by an admissible erase composes at the erase's bath. *)
Theorem transition_erase_chain_oneInequality (old new_ : ThermodynamicState) (e : ErasureProcess) (p q : ProbDist) :
  SecondLaw transition (thermodynamic old new_) -> SecondLaw (erase e) (transformation p q) ->
  oneInequality (chain (transitionStepAt (erasureBath e) old new_) (eraseStep e p q)).
Proof.
  intros hTr hEr. apply oneInequality_chain; [reflexivity | |].
  - exact (proj1 (proj1 (SecondLaw_transition_oneInequality_iff (erasureBath e) old new_) hTr)).
  - exact (proj1 (eraseStep_oneInequality_iff e p q) hEr).
Qed.

(** Any process with a prior of its kind packages as a step. *)
Definition stepOf (proc : Process) (prior : Prior) : option Step :=
  match proc, prior with
  | erase e, erasure p => Some (eraseStep e (asProbDist p) (asProbDist dirac0))
  | measureFeedback f, feedback mi => Some (feedbackStep f mi)
  | transition, thermodynamic old new_ => Some (transitionStepAt (mkHeatBath 1 ltac:(lra)) old new_)
  | erase e, transformation p q => Some (eraseStep e p q)
  | _, _ => None
  end.

(** Every member of the one predicate packages as a step obeying the one inequality. *)
Theorem secondLaw_implies_oneInequality (proc : Process) (prior : Prior) :
  SecondLaw proc prior -> exists s, stepOf proc prior = Some s /\ oneInequality s.
Proof.
  destruct proc; destruct prior; intro h; try (simpl in h; contradiction);
  eexists; (split; [reflexivity |]);
  first [ apply eraseStep_oneInequality_iff; apply SecondLaw_erasure_iff_transformation; exact h
        | apply SecondLaw_measureFeedback_oneInequality_iff; exact h
        | exact (proj1 (proj1 (SecondLaw_transition_oneInequality_iff _ _ _) h))
        | apply eraseStep_oneInequality_iff; exact h ].
Qed.

(** The Szilard cycle: measuring one bit then erasing it composes at the bath. *)
Theorem szilardMixedChain_oneInequality (b : HeatBath) :
  oneInequality (chain (feedbackStep (szilardEngine b) (mutualInformation2 szilardJoint))
                       (eraseStep (landauerTightErasure b) (asProbDist uniform2) (asProbDist dirac0))).
Proof.
  apply oneInequality_chain; [reflexivity | |].
  - apply SecondLaw_measureFeedback_oneInequality_iff. exact (SecondLaw_szilardEngine b).
  - apply eraseStep_oneInequality_iff. apply SecondLaw_erasure_iff_transformation. exact (landauerTight b).
Qed.
