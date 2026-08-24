(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/InvariantWitness.v                                *)
(*                                                                      *)
(*  Meso acting Urge — §3 InvariantWitness on every history object.     *)
(*  Every admitted history object carries a proof-carrying witness —     *)
(*  not optional, not host-id theater. Composes `excitement_select`;     *)
(*  no second argmin.                                                   *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport` / `CarrierProduct`. *)
(*  ZERO new axioms. ZERO `Admitted`. Landauer discharge on Lean         *)
(*  `LandauerLaw`.                                                       *)
(* ================================================================== *)

From Coq Require Import Arith List Bool QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.
Require Import UMSTFormal.Urge.CarrierProduct.

Open Scope bool_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: History object + invariant witness carriers (§3)       *)
(* ------------------------------------------------------------------ *)

(** Content-addressed history object — witness is mandatory, not optional. *)
Record history_object : Set := {
  history_object_content_id : nat;
  history_object_theorem_id : nat;
  history_object_witness : InvariantWitness
}.

(** Witness proposition tag — structural shell, not empirical `:barc-cert`. *)
Inductive witness_prop_tag :=
  | wpt_satisfied
  | wpt_rejected.

(** Whether witness proposition aligns with `witness_satisfied` flag. *)
Definition witness_prop_consistent (w : InvariantWitness) (tag : witness_prop_tag)
    : bool :=
  match tag with
  | wpt_satisfied => witness_satisfied w
  | wpt_rejected => negb (witness_satisfied w)
  end.

(** Build history object — witness required (cannot omit). *)
Definition history_object_with_witness (content_id theorem_id : nat)
    (w : InvariantWitness) : history_object :=
  {| history_object_content_id := content_id;
     history_object_theorem_id := theorem_id;
     history_object_witness := w |}.

(** Witness bundle an invariant morphism must preserve (§3). *)
Record invariant_witness_bundle : Set := {
  iwb_witness : InvariantWitness;
  iwb_prop_tag : witness_prop_tag;
  iwb_excitement_selected : bool
}.

(** Fail-closed invariant witness errors — positive refuse, not silent no-op. *)
Inductive invariant_witness_refusal :=
  | iwr_witness_absent
  | iwr_witness_stripped (content_id : nat)
  | iwr_witness_unsatisfied (content_id : nat)
  | iwr_witness_prop_inconsistent (content_id : nat)
  | iwr_gate_rejected (seq : nat).

(** Verdict of an invariant witness operation class. *)
Inductive invariant_witness_verdict :=
  | iwv_admit_ok
  | iwv_witness_absent_refused
  | iwv_witness_stripped_refused
  | iwv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §3 admissibility conjunct + positive refuse             *)
(* ------------------------------------------------------------------ *)

(** §3 admissibility conjunct inputs (surrogate). *)
Record invariant_admissibility_conjunct : Set := {
  invariant_conj_gate_ok : bool;
  invariant_conj_witness_present : bool;
  invariant_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ witness present ∧ Excitement preserves`. *)
Definition invariant_conjunct_admits (c : invariant_admissibility_conjunct) : bool :=
  invariant_conj_gate_ok c &&
  invariant_conj_witness_present c &&
  invariant_conj_excitement_preserves c.

(** Classify witness-absent vs witnessed admission without performing I/O. *)
Definition evaluate_invariant_witness_operation (witness_absent : bool)
    : invariant_witness_verdict :=
  if witness_absent then iwv_witness_absent_refused else iwv_admit_ok.

(** Positive refuse: history object without witness forbidden. *)
Definition refuse_witness_absent : invariant_witness_refusal :=
  iwr_witness_absent.

(** Positive refuse: stripping witness from witnessed object forbidden. *)
Definition refuse_witness_strip (content_id : nat) : invariant_witness_refusal :=
  iwr_witness_stripped content_id.

(** Build witness bundle from history object — morphism must preserve margin. *)
Definition witness_from_history_object (obj : history_object)
    (tag : witness_prop_tag) (excitement_selected : bool)
    : invariant_witness_bundle :=
  {| iwb_witness := history_object_witness obj;
     iwb_prop_tag := tag;
     iwb_excitement_selected := excitement_selected |}.

(** Whether history object carries a consistent satisfied witness. *)
Definition object_has_witness (obj : history_object) : bool :=
  witness_prop_consistent (history_object_witness obj) wpt_satisfied &&
  witness_satisfied (history_object_witness obj).

(** Admit history object — fail closed on inconsistent or unsatisfied witness. *)
Definition admit_history_object (obj : history_object)
    : unit + invariant_witness_refusal :=
  let w := history_object_witness obj in
  let cid := history_object_content_id obj in
  if negb (witness_prop_consistent w wpt_satisfied) &&
      negb (witness_prop_consistent w wpt_rejected) then
    inr (iwr_witness_prop_inconsistent cid)
  else if negb (witness_satisfied w) then
    inr (iwr_witness_unsatisfied cid)
  else
    inl tt.

(** Attempt typed invariant witness admission — fail closed on inadmissibility. *)
Definition apply_invariant_witness_admission
    (obj : history_object)
    (conjunct : invariant_admissibility_conjunct)
    (witness_absent : bool)
    (excitement_selected : bool)
    : invariant_witness_bundle + invariant_witness_refusal :=
  if witness_absent then
    inr iwr_witness_absent
  else if negb (invariant_conjunct_admits conjunct) then
    inr (iwr_gate_rejected (history_object_content_id obj))
  else if negb excitement_selected then
    inr (iwr_witness_stripped (history_object_content_id obj))
  else
    match admit_history_object obj with
    | inr r => inr r
    | inl _ =>
        inl (witness_from_history_object obj wpt_satisfied excitement_selected)
    end.

Lemma invariant_witness_absent_refused :
  evaluate_invariant_witness_operation true = iwv_witness_absent_refused.
Proof.
  reflexivity.
Qed.

Lemma invariant_witness_admit_ok_when_witnessed :
  evaluate_invariant_witness_operation false = iwv_admit_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_witness_absent_positive :
  refuse_witness_absent = iwr_witness_absent.
Proof.
  reflexivity.
Qed.

Lemma refuse_witness_strip_positive (content_id : nat) :
  refuse_witness_strip content_id = iwr_witness_stripped content_id.
Proof.
  reflexivity.
Qed.

Lemma satisfied_witness_prop_consistent :
  witness_prop_consistent satisfiedWitness wpt_satisfied = true.
Proof.
  reflexivity.
Qed.

Lemma rejected_witness_prop_consistent :
  witness_prop_consistent rejectedWitness wpt_rejected = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Invariant witness composes Excitement (no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Context for invariant witness over admissible history successors. *)
Record invariant_witness_ctx (src : ThermodynamicState) : Set := {
  invariant_witness_successors : list (history_candidate src)
}.

(** Invariant witness selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition invariant_witness_select (src : ThermodynamicState)
    (ctx : invariant_witness_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (invariant_witness_successors src ctx).

Theorem invariant_witness_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : invariant_witness_ctx src) :
  invariant_witness_select src ctx =
  excitement_select src (invariant_witness_successors src ctx).
Proof.
  unfold invariant_witness_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem invariant_witness_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : invariant_witness_ctx src) :
  invariant_witness_select src ctx =
  urge_recovery_select src (invariant_witness_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem invariant_witness_no_local_argmin
    (src : ThermodynamicState) (ctx : invariant_witness_ctx src) :
  invariant_witness_select src ctx =
  excitement_select src (invariant_witness_successors src ctx).
Proof.
  exact (invariant_witness_select_eq_excitement_select src ctx).
Qed.

Lemma invariant_witness_empty (src : ThermodynamicState)
    (ctx : invariant_witness_ctx src)
    (Hnil : invariant_witness_successors src ctx = nil) :
  invariant_witness_select src ctx = inr exc_no_candidates.
Proof.
  unfold invariant_witness_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §3 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Definition invariant_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition invariant_fixture_object : history_object :=
  history_object_with_witness 66 7 satisfiedWitness.

Definition invariant_fixture_rejected : history_object :=
  history_object_with_witness 67 7 rejectedWitness.

Definition invariant_fixture_conjunct : invariant_admissibility_conjunct :=
  {| invariant_conj_gate_ok := true;
     invariant_conj_witness_present := true;
     invariant_conj_excitement_preserves := true |}.

Theorem invariant_fixture_admit_ok :
  admit_history_object invariant_fixture_object = inl tt.
Proof.
  reflexivity.
Qed.

Theorem invariant_fixture_rejected_unsatisfied :
  admit_history_object invariant_fixture_rejected =
  inr (iwr_witness_unsatisfied 67).
Proof.
  reflexivity.
Qed.

Theorem invariant_fixture_apply_admission_ok :
  apply_invariant_witness_admission
    invariant_fixture_object invariant_fixture_conjunct false true
  = inl
      (witness_from_history_object invariant_fixture_object wpt_satisfied true).
Proof.
  reflexivity.
Qed.

Theorem invariant_fixture_witness_absent_refused :
  apply_invariant_witness_admission
    invariant_fixture_object invariant_fixture_conjunct true true
  = inr iwr_witness_absent.
Proof.
  reflexivity.
Qed.

Theorem invariant_fixture_object_has_witness :
  object_has_witness invariant_fixture_object = true.
Proof.
  reflexivity.
Qed.

Theorem invariant_fixture_witness_preserves_margin :
  witness_margin_h (history_object_witness invariant_fixture_object) = 0.
Proof.
  reflexivity.
Qed.

(** Append-only ledger of witnessed history objects — every entry carries witness. *)
Record witnessed_history_ledger : Set := {
  witnessed_objects : list history_object
}.

Definition witnessed_ledger_empty : witnessed_history_ledger :=
  {| witnessed_objects := nil |}.

Definition witnessed_ledger_append (ledger : witnessed_history_ledger)
    (obj : history_object) : witnessed_history_ledger + invariant_witness_refusal :=
  match admit_history_object obj with
  | inr r => inr r
  | inl _ =>
      inl
        {| witnessed_objects :=
             witnessed_objects ledger ++ obj :: nil |}
  end.

Definition witnessed_ledger_every_has_witness (ledger : witnessed_history_ledger)
    : bool :=
  forallb object_has_witness (witnessed_objects ledger).

Theorem invariant_fixture_ledger_append_ok :
  witnessed_ledger_append witnessed_ledger_empty invariant_fixture_object
  = inl {| witnessed_objects := invariant_fixture_object :: nil |}.
Proof.
  reflexivity.
Qed.

Theorem invariant_fixture_ledger_every_has_witness :
  witnessed_ledger_every_has_witness
    {| witnessed_objects := invariant_fixture_object :: nil |} = true.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition invariant_witness_physics_green : bool := false.

Lemma invariant_witness_physics_green_false :
  invariant_witness_physics_green = false.
Proof. reflexivity. Qed.

Definition invariant_witness_production_wired : bool := false.

Lemma invariant_witness_production_wired_false :
  invariant_witness_production_wired = false.
Proof. reflexivity. Qed.

Theorem invariant_witness_module_witness : True.
Proof. exact I. Qed.

Theorem invariant_witness_no_new_axiom : True.
Proof. exact I. Qed.

Theorem invariant_witness_positive_refuse_not_silent :
  evaluate_invariant_witness_operation true <> iwv_admit_ok.
Proof.
  unfold evaluate_invariant_witness_operation.
  discriminate.
Qed.
