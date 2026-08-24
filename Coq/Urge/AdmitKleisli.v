(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/AdmitKleisli.v                                    *)
(*                                                                      *)
(*  Meso acting Urge — Kleisli admit arrow on typed history transitions. *)
(*  §2 / §16.1: second-law accounting on history moves; inherit Kleisli  *)
(*  monad laws from `Constitutional`; compose `Excitement.select`        *)
(*  conceptually (no local argmin re-derivation).                        *)
(*                                                                      *)
(*  Anchored in `Chem.SecondLaw` / Landauer lift.  ZERO new axioms.     *)
(*  Knowing fiber (EpistemicMI / LandauerBound) lives on                *)
(*  `umst-formal-double-slit` — cited, not restated here.               *)
(* ================================================================== *)

From Coq Require Import Reals Arith List.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Constitutional.
Require Import UMSTFormal.Chem.SecondLaw.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Typed history / admit carriers (meso acting layer)      *)
(* ------------------------------------------------------------------ *)

(** Content-addressed history snapshot: commit id + gate-checked head state. *)
Record HistorySnapshot : Set := {
  history_commit_id : nat;
  history_head : ThermodynamicState
}.

(** Heat bath for second-law accounting (SI temperature scale). *)
Record HeatBath : Set := {
  bath_temp : R
}.

(** Thermodynamic accounting on a history transition (acting meso layer). *)
Record HistoryTransition : Set := {
  history_prior : HistorySnapshot;
  history_post : HistorySnapshot;
  history_bath : HeatBath;
  history_dissipated_work : R;
  history_entropy_drop : R;
  history_gate_admissible : admissible history_prior.(history_head)
                              history_post.(history_head)
}.

(** Named second-law invariant on history (Prop — not a Coq Axiom). *)
Definition admitSecondLaw (t : HistoryTransition) : Prop :=
  history_entropy_drop t <=
  history_dissipated_work t / bath_temp (history_bath t).

(** Admissible history transition: gate-checked head move + second-law accounting. *)
Definition admissibleHistoryTransition (t : HistoryTransition) : Prop :=
  admitSecondLaw t.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Kleisli admit arrows (inherit monad laws — do not re-prove) *)
(* ------------------------------------------------------------------ *)

(** Kleisli arrow over thermodynamic states (history head moves). *)
Definition AdmitArrow := KleisliArrow.

(** Kleisli identity on history head states. *)
Definition admitIdentity : AdmitArrow := fun s => Some s.

(** Kleisli composition (inherited from `Constitutional`). *)
Definition kleisliCompose := kleisli_compose.

(** Fold a non-empty Kleisli chain (inherited). *)
Definition kleisliFold := kleisli_fold.

Lemma kleisliComposeAssocAt (f g h : AdmitArrow) (s : ThermodynamicState) :
  kleisliCompose (kleisliCompose f g) h s =
  kleisliCompose f (kleisliCompose g h) s.
Proof.
  unfold kleisliCompose, kleisli_compose.
  destruct (f s) as [s'|]; simpl; [| reflexivity].
  destruct (g s') as [s''|]; simpl; reflexivity.
Qed.

Lemma kleisliLeftUnitAt (f : AdmitArrow) (s : ThermodynamicState) :
  kleisliCompose admitIdentity f s = f s.
Proof.
  unfold kleisliCompose, kleisli_compose, admitIdentity.
  destruct (f s); reflexivity.
Qed.

Lemma kleisliRightUnitAt (f : AdmitArrow) (s : ThermodynamicState) :
  kleisliCompose f admitIdentity s = f s.
Proof.
  unfold kleisliCompose, kleisli_compose, admitIdentity.
  destruct (f s) as [s'|]; simpl; reflexivity.
Qed.

Theorem admitKleisliComposeWellTyped :
  forall (f g : AdmitArrow),
  WellTyped f ->
  WellTyped g ->
  well_typed_N 2 (kleisliCompose f g).
Proof.
  intros f g Hf Hg.
  unfold kleisliCompose.
  exact (kleisli_compose_well_typed f g Hf Hg).
Qed.

Theorem admitKleisliFoldWellTypedN :
  forall (arrows : list AdmitArrow),
  AllWellTyped arrows ->
  well_typed_N (length arrows) (kleisliFold arrows).
Proof.
  intros arrows Hall.
  unfold kleisliFold.
  exact (kleisli_fold_well_typed_N arrows Hall).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Excitement composition (no local argmin re-derivation)  *)
(* ------------------------------------------------------------------ *)

(** Residue tags mirroring `UMST.Excitement.Residue` (conceptual hook only). *)
Inductive excitement_residue :=
  | exc_no_candidates
  | exc_all_inadmissible
  | exc_no_strict_improvement.

(** History admit candidate (gate-checked target state). *)
Record history_candidate (src : ThermodynamicState) : Set := {
  cand_id : nat;
  cand_tgt : ThermodynamicState;
  cand_admissible : admissible src cand_tgt
}.

(** Excitement-directed selection over finite candidate lists.
    Meso Coq hook: does **not** re-derive the Lean argmin — full
    `UMST.Excitement.select` lives in `Lean/Excitement.lean`. *)
Definition excitement_select (src : ThermodynamicState)
  (cands : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  match cands with
  | nil => inr exc_no_candidates
  | c :: _ => inl c
  end.

(** History admit selection composes `excitement_select` — not a second argmin. *)
Definition admitHistorySelect (src : ThermodynamicState)
  (cands : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src cands.

Theorem admitHistorySelect_eq_excitement_select :
  forall (src : ThermodynamicState)
         (cands : list (history_candidate src)),
  admitHistorySelect src cands = excitement_select src cands.
Proof.
  intros. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Bridge to Chem.SecondLaw (derived — zero new axioms)      *)
(* ------------------------------------------------------------------ *)

(** Landauer accounting witness tying dissipated work to measurement floor.
    Full `physicalSecondLaw` discharge lives in Lean `LandauerLaw.lean`. *)
Record LandauerHistoryBridge : Set := {
  landauer_transition : HistoryTransition;
  landauer_mi_bits : R;
  landauer_bath_temp_pos : 0 < bath_temp (history_bath landauer_transition);
  landauer_work_eq :
    history_dissipated_work landauer_transition =
    chem_measurement_floor (bath_temp (history_bath landauer_transition))
      landauer_mi_bits;
  landauer_entropy_eq :
    history_entropy_drop landauer_transition = landauer_mi_bits
}.

Lemma landauer_history_bridge_floor_eq (b : LandauerHistoryBridge) :
  history_dissipated_work (landauer_transition b) =
  landauer_mi_bits b *
  chem_landauer_floor (bath_temp (history_bath (landauer_transition b))).
Proof.
  destruct b.
  rewrite landauer_work_eq.
  unfold chem_measurement_floor, chem_landauer_floor.
  reflexivity.
Qed.

Lemma admitSecondLaw_from_hypothesis (t : HistoryTransition) :
  admitSecondLaw t -> admissibleHistoryTransition t.
Proof.
  intros Hsl. exact Hsl.
Qed.

Theorem admissibleHistoryTransition_from_landauer_bridge
    (b : LandauerHistoryBridge)
    (Hsl : admitSecondLaw (landauer_transition b)) :
  admissibleHistoryTransition (landauer_transition b).
Proof.
  exact (admitSecondLaw_from_hypothesis (landauer_transition b) Hsl).
Qed.

Lemma history_landauer_floor_pos (T : R) :
  0 < T -> 0 < chem_landauer_floor T.
Proof.
  intros HT.
  exact (chem_landauer_floor_pos T HT).
Qed.

Lemma history_measurement_floor_zero (T : R) :
  chem_measurement_floor T 0 = 0.
Proof.
  exact (chem_measurement_floor_zero T).
Qed.

Lemma history_measurement_floor_scale (T k : R) :
  chem_measurement_floor T k = k * chem_landauer_floor T.
Proof.
  exact (chem_measurement_floor_scale T k).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition urge_physics_green : bool := false.

Lemma urge_physics_green_false : urge_physics_green = false.
Proof. reflexivity. Qed.

Definition admit_kleisli_production_wired : bool := false.

Lemma admit_kleisli_production_wired_false :
  admit_kleisli_production_wired = false.
Proof. reflexivity. Qed.

Theorem admit_kleisli_module_witness : True.
Proof. exact I. Qed.
