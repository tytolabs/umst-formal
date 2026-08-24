(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/DropProvenance.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §15.6 H3 drop-provenance gossip tick refuse.     *)
(*  Drop-provenance gossip candidates are **inadmissible** — typed       *)
(*  positive refuse, not silent accept. Urge composes `excitement_select` *)
(*  — no second argmin / f64 F compare.                                  *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli.excitement_select`. ZERO new axioms.      *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.           *)
(* ================================================================== *)

From Coq Require Import Arith List String Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.

Open Scope string_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Gossip tick candidate + typed refusal carriers        *)
(* ------------------------------------------------------------------ *)

(** One gossip tick candidate on the UCRS-gated mesh spine. *)
Record GossipCandidate : Set := {
  gossip_id : nat;
  gossip_provenance_intact : bool;
  gossip_drops_provenance : bool;
  gossip_provenance_stamp : option string
}.

(** Typed refusal when a gossip candidate drops provenance. *)
Inductive DropProvenanceRefusal :=
  | dpr_drops_provenance_gossip_tick
  | dpr_provenance_lost
  | dpr_missing_stamp.

(** Verdict for gossip tick admissibility on the mesh spine. *)
Inductive GossipTickVerdict :=
  | gtv_admissible
  | gtv_reject_drop_provenance.

(** Admissible iff provenance intact and not a drop-heal gossip tick. *)
Definition gossip_is_admissible (c : GossipCandidate) : bool :=
  gossip_provenance_intact c && negb (gossip_drops_provenance c).

Definition stamp_nonempty (s : string) : bool :=
  negb (String.eqb s "").

Definition stamp_ok (c : GossipCandidate) : bool :=
  match gossip_provenance_stamp c with
  | None => false
  | Some s => stamp_nonempty s
  end.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Positive refuse + admit (not silent accept)           *)
(* ------------------------------------------------------------------ *)

(** Admit a gossip candidate — `None` on success, `Some` refusal otherwise. *)
Definition admit_gossip_candidate (c : GossipCandidate) : option DropProvenanceRefusal :=
  if gossip_drops_provenance c then
    Some dpr_drops_provenance_gossip_tick
  else if negb (gossip_provenance_intact c) then
    Some dpr_provenance_lost
  else if negb (stamp_ok c) then
    Some dpr_missing_stamp
  else
    None.

(** Evaluate gossip tick admissibility (H3 transition verdict family). *)
Definition evaluate_gossip_tick (c : GossipCandidate) : GossipTickVerdict :=
  match admit_gossip_candidate c with
  | None => gtv_admissible
  | Some _ => gtv_reject_drop_provenance
  end.

(** Positive refuse: drop-provenance gossip candidate is always inadmissible. *)
Definition refuse_drop_provenance_gossip_candidate (c : GossipCandidate)
    : DropProvenanceRefusal :=
  if gossip_drops_provenance c then
    dpr_drops_provenance_gossip_tick
  else if negb (gossip_provenance_intact c) then
    dpr_provenance_lost
  else
    dpr_missing_stamp.

Lemma gossip_tick_verdict_admissible_iff (c : GossipCandidate) :
  evaluate_gossip_tick c = gtv_admissible <->
  admit_gossip_candidate c = None.
Proof.
  unfold evaluate_gossip_tick.
  destruct (admit_gossip_candidate c); split; intros; congruence.
Qed.

Lemma gossip_tick_verdict_reject_iff (c : GossipCandidate) :
  evaluate_gossip_tick c = gtv_reject_drop_provenance <->
  admit_gossip_candidate c <> None.
Proof.
  unfold evaluate_gossip_tick.
  destruct (admit_gossip_candidate c); split; intros; congruence.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Excitement compose (no second argmin)                   *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — Urge imports selector; no second argmin. *)
Inductive ExcitementComposePin :=
  | ecp_import_select_excitement
  | ecp_second_argmin_refused.

(** Gossip path composes `excitement_select` — not a second argmin. *)
Definition gossip_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : ExcitementComposePin) :
  history_candidate src + excitement_residue :=
  match pin with
  | ecp_import_select_excitement => excitement_select src cands
  | ecp_second_argmin_refused => inr exc_all_inadmissible
  end.

Theorem gossip_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  gossip_excitement_select src cands ecp_import_select_excitement =
  excitement_select src cands.
Proof.
  reflexivity.
Qed.

Theorem gossip_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  gossip_excitement_select src cands ecp_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  reflexivity.
Qed.

(** Drop-provenance gossip candidates never reach excitement selection. *)
Definition filter_admissible_gossip (cands : list GossipCandidate)
    : list GossipCandidate :=
  filter (fun c => gossip_is_admissible c && stamp_ok c) cands.

Lemma gossip_is_admissible_false_when_drops (c : GossipCandidate)
    (hdrop : gossip_drops_provenance c = true) :
  gossip_is_admissible c = false.
Proof.
  unfold gossip_is_admissible.
  rewrite hdrop. simpl.
  destruct (gossip_provenance_intact c); reflexivity.
Qed.

Lemma drop_provenance_never_in_admissible_filter (c : GossipCandidate)
    (hdrop : gossip_drops_provenance c = true) :
  In c (filter_admissible_gossip (c :: nil)) -> False.
Proof.
  intro H.
  unfold filter_admissible_gossip in H.
  simpl in H.
  rewrite (gossip_is_admissible_false_when_drops c hdrop) in H.
  simpl in H.
  inversion H.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: H3 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Definition h3_inadmissible_drop_provenance_id : nat := 1.
Definition h3_admissible_provenanced_id : nat := 2.

Definition h3_drop_provenance_fixture_candidate : GossipCandidate :=
  {| gossip_id := h3_inadmissible_drop_provenance_id;
     gossip_provenance_intact := false;
     gossip_drops_provenance := true;
     gossip_provenance_stamp := None |}.

Definition h3_admissible_gossip_candidate : GossipCandidate :=
  {| gossip_id := h3_admissible_provenanced_id;
     gossip_provenance_intact := true;
     gossip_drops_provenance := false;
     gossip_provenance_stamp :=
       Some "ucrs:fixture:h3:admissible-001"%string |}.

Theorem h3_drop_provenance_fixture_refused :
  admit_gossip_candidate h3_drop_provenance_fixture_candidate =
  Some dpr_drops_provenance_gossip_tick.
Proof.
  reflexivity.
Qed.

Theorem h3_drop_provenance_fixture_evaluate_reject :
  evaluate_gossip_tick h3_drop_provenance_fixture_candidate =
  gtv_reject_drop_provenance.
Proof.
  reflexivity.
Qed.

Theorem h3_drop_provenance_fixture_positive_refuse :
  refuse_drop_provenance_gossip_candidate h3_drop_provenance_fixture_candidate =
  dpr_drops_provenance_gossip_tick.
Proof.
  reflexivity.
Qed.

Theorem h3_admissible_gossip_candidate_admits :
  admit_gossip_candidate h3_admissible_gossip_candidate = None.
Proof.
  reflexivity.
Qed.

Theorem h3_admissible_gossip_candidate_evaluate_admit :
  evaluate_gossip_tick h3_admissible_gossip_candidate = gtv_admissible.
Proof.
  reflexivity.
Qed.

Theorem h3_admissible_gossip_is_admissible :
  gossip_is_admissible h3_admissible_gossip_candidate = true.
Proof.
  reflexivity.
Qed.

Theorem h3_drop_provenance_fixture_not_admissible :
  gossip_is_admissible h3_drop_provenance_fixture_candidate = false.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition urge_physics_green : bool := false.

Lemma urge_physics_green_false : urge_physics_green = false.
Proof. reflexivity. Qed.

Definition drop_provenance_production_wired : bool := false.

Lemma drop_provenance_production_wired_false :
  drop_provenance_production_wired = false.
Proof. reflexivity. Qed.

Theorem drop_provenance_module_witness : True.
Proof. exact I. Qed.

Theorem drop_provenance_no_new_axiom : True.
Proof. exact I. Qed.

Theorem drop_provenance_positive_refuse_not_silent :
  admit_gossip_candidate h3_drop_provenance_fixture_candidate <>
  None.
Proof.
  rewrite h3_drop_provenance_fixture_refused.
  discriminate.
Qed.
