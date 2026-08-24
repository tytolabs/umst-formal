(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/KleisliInherit.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §17.3 Kleisli inheritance layer.                 *)
(*  `kleisli_compose_preserves_admissibility` and monad laws are        *)
(*  inherited from `Constitutional`; Urge does not re-prove the         *)
(*  admissibility monad.                                                *)
(*                                                                      *)
(*  Anchored in `Chem.SecondLaw` via `AdmitKleisli` (cited, not here).  *)
(*  Excitement selection is imported — no second argmin in this crate.    *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.           *)
(* ================================================================== *)

From Coq Require Import Arith List.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.
Require Import UMSTFormal.Urge.AdmitKleisli.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Carriers (inherit from Constitutional / AdmitKleisli)   *)
(* ------------------------------------------------------------------ *)

(** Kleisli arrow over thermodynamic states (meso Urge carrier). *)
Definition InheritArrow := KleisliArrow.

(** Kleisli identity on admitted history head states. *)
Definition inheritIdentity := admitIdentity.

(** Kleisli composition (inherited bind). *)
Definition inheritCompose := kleisliCompose.

(** Fold a non-empty Kleisli chain (inherited). *)
Definition inheritFold := kleisliFold.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: compose-preserves-admissibility (inherited — not re-proved) *)
(* ------------------------------------------------------------------ *)

(** Graded Kleisli composition preserves gate admissibility. *)
Theorem kleisli_compose_preserves_admissibility (m n : nat) (f g : InheritArrow)
    (hf : well_typed_N m f) (hg : well_typed_N n g) :
  well_typed_N (m + n) (inheritCompose f g).
Proof.
  unfold inheritCompose, kleisliCompose.
  exact (kleisli_compose_well_typed_N m n f g hf hg).
Qed.

(** Single-step compose preserves admissibility (2-step graded witness). *)
Theorem kleisli_compose_preserves_admissibility_step (f g : InheritArrow)
    (hf : WellTyped f) (hg : WellTyped g) :
  well_typed_N 2 (inheritCompose f g).
Proof.
  unfold inheritCompose, kleisliCompose.
  exact (admitKleisliComposeWellTyped f g hf hg).
Qed.

(** Fold of well-typed arrows preserves graded admissibility. *)
Theorem kleisli_fold_preserves_admissibility (arrows : list InheritArrow)
    (hall : AllWellTyped arrows) :
  well_typed_N (length arrows) (inheritFold arrows).
Proof.
  unfold inheritFold, kleisliFold.
  exact (admitKleisliFoldWellTypedN arrows hall).
Qed.

(** Pointwise compose preservation at successful witnesses. *)
Theorem kleisli_compose_preserves_admissibility_at (f g : InheritArrow)
    (hf : WellTyped f) (hg : WellTyped g)
    (s s' s'' : ThermodynamicState) (hfs : f s = Some s')
    (hcs : inheritCompose f g s = Some s'') :
  admissible s s' /\ admissible s' s''.
Proof.
  split.
  - apply hf; exact hfs.
  - assert (hg' : g s' = Some s'').
    { unfold inheritCompose, kleisliCompose, kleisli_compose in hcs.
      rewrite hfs in hcs. exact hcs. }
    apply hg; exact hg'.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Monad laws (inherited — cite only, do not re-derive)    *)
(* ------------------------------------------------------------------ *)

(** Associativity at each state (inherited from `AdmitKleisli`). *)
Theorem kleisli_associativity_inherited (f g h : InheritArrow)
    (s : ThermodynamicState) :
  inheritCompose (inheritCompose f g) h s =
  inheritCompose f (inheritCompose g h) s.
Proof.
  unfold inheritCompose, kleisliCompose.
  exact (kleisliComposeAssocAt f g h s).
Qed.

(** Left unit at each state (inherited). *)
Theorem kleisli_left_unit_inherited (f : InheritArrow) (s : ThermodynamicState) :
  inheritCompose inheritIdentity f s = f s.
Proof.
  unfold inheritCompose, kleisliCompose, inheritIdentity, admitIdentity.
  exact (kleisliLeftUnitAt f s).
Qed.

(** Right unit at each state (inherited). *)
Theorem kleisli_right_unit_inherited (f : InheritArrow) (s : ThermodynamicState) :
  inheritCompose f inheritIdentity s = f s.
Proof.
  unfold inheritCompose, kleisliCompose, inheritIdentity, admitIdentity.
  exact (kleisliRightUnitAt f s).
Qed.

(** Rust parity probe: associativity inherited, not re-proved here. *)
Definition kleisli_associativity_probe_holds : bool := true.

Lemma kleisliAssociativityProbeHolds :
  kleisli_associativity_probe_holds = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Excitement import (no second argmin)                    *)
(* ------------------------------------------------------------------ *)

(** History selection composes `excitement_select` — inherited alias, not a fork. *)
Definition inheritHistorySelect (src : ThermodynamicState)
  (cands : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src cands.

Theorem inheritHistorySelect_eq_excitement_select :
  forall (src : ThermodynamicState)
         (cands : list (history_candidate src)),
  inheritHistorySelect src cands = excitement_select src cands.
Proof.
  intros. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

(** Physics GREEN unauthorized on this scaffold. *)
Definition kleisliInheritPhysicsGreen : bool := false.

Lemma kleisliInheritPhysicsGreenFalse :
  kleisliInheritPhysicsGreen = false.
Proof. reflexivity. Qed.

(** Production wiring stays open (inheritance lift only). *)
Definition kleisliInheritProductionWired : bool := false.

Lemma kleisliInheritProductionWiredFalse :
  kleisliInheritProductionWired = false.
Proof. reflexivity. Qed.

(** Catalog witness: meso Urge KleisliInherit module present. *)
Theorem kleisliInheritModuleWitness : True.
Proof. exact I. Qed.
