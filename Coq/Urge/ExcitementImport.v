(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ExcitementImport.v                               *)
(*                                                                      *)
(*  Meso acting Urge — §5.2 / §22.5 excitement import discipline.       *)
(*  Urge history recovery **is** `excitement_select` over admissible    *)
(*  history successors; refuse a second argmin / f64 F compare.         *)
(*                                                                      *)
(*  Sole physics axiom remains on Lean `LandauerLaw` (cited, not here). *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.           *)
(* ================================================================== *)

From Coq Require Import Arith List.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: History recovery carrier (typed successor list)         *)
(* ------------------------------------------------------------------ *)

(** Context for Urge history recovery: prior head + admissible successors. *)
Record history_recovery_ctx (src : ThermodynamicState) : Set := {
  recovery_successors : list (history_candidate src)
}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Recovery **is** excitement_select (no local argmin)     *)
(* ------------------------------------------------------------------ *)

(** Urge history recovery composes `excitement_select` — not a second argmin. *)
Definition urge_recovery (src : ThermodynamicState)
  (ctx : history_recovery_ctx src) :
  history_candidate src + excitement_residue :=
  excitement_select src (recovery_successors src ctx).

(** Alias on bare `(prior, successors)` — same selector, no re-derivation. *)
Definition urge_recovery_select (src : ThermodynamicState)
  (successors : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src successors.

(** Definitional witness: recovery API is `excitement_select`. *)
Theorem urge_recovery_eq_excitement_select :
  forall (src : ThermodynamicState) (ctx : history_recovery_ctx src),
  urge_recovery src ctx =
  excitement_select src (recovery_successors src ctx).
Proof.
  intros. reflexivity.
Qed.

Theorem urge_recovery_select_eq_excitement_select :
  forall (src : ThermodynamicState)
         (successors : list (history_candidate src)),
  urge_recovery_select src successors = excitement_select src successors.
Proof.
  intros. reflexivity.
Qed.

(** Recovery and bare select agree on identical inputs. *)
Theorem urge_recovery_eq_urge_recovery_select :
  forall (src : ThermodynamicState) (ctx : history_recovery_ctx src),
  urge_recovery src ctx =
  urge_recovery_select src (recovery_successors src ctx).
Proof.
  intros. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Imported selector properties (no local re-proof)      *)
(* ------------------------------------------------------------------ *)

(** Empty successor list → `exc_no_candidates` via imported `excitement_select`. *)
Lemma urge_recovery_empty (src : ThermodynamicState) :
  urge_recovery_select src nil = inr exc_no_candidates.
Proof.
  intros. reflexivity.
Qed.

(** Successful recovery yields an admissible step (field on `history_candidate`). *)
Lemma urge_recovery_admissible (src : ThermodynamicState)
  (successors : list (history_candidate src))
  (c : history_candidate src)
  (H : urge_recovery_select src successors = inl c) :
  admissible src (cand_tgt src c).
Proof.
  intros.
  destruct successors as [|h t]; simpl in H.
  - discriminate H.
  - injection H as Heq. subst c. exact (cand_admissible src h).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Axiom discipline + honesty flags                        *)
(* ------------------------------------------------------------------ *)

(** Physics GREEN unauthorized on this scaffold. *)
Definition urge_excitement_physics_green : bool := false.

Lemma urge_excitement_physics_green_false :
  urge_excitement_physics_green = false.
Proof. reflexivity. Qed.

(** Production wiring stays open (meso import only). *)
Definition excitement_import_production_wired : bool := false.

Lemma excitement_import_production_wired_false :
  excitement_import_production_wired = false.
Proof. reflexivity. Qed.

(** Catalog witness: meso Urge ExcitementImport module present. *)
Theorem excitement_import_module_witness : True.
Proof. exact I. Qed.

(** Recovery selector re-uses `excitement_select` — no Urge-local argmin. *)
Theorem urge_recovery_no_local_argmin :
  forall (src : ThermodynamicState) (ctx : history_recovery_ctx src),
  urge_recovery src ctx =
  excitement_select src (recovery_successors src ctx).
Proof.
  intros. reflexivity.
Qed.
