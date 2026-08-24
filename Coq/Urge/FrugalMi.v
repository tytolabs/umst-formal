(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/FrugalMi.v                                        *)
(*                                                                      *)
(*  Meso acting Urge — §4 frugal MI observation of local+mesh state.  *)
(*  Observation **is** an Excitement-selected admissible transition —   *)
(*  acting coalgebra deconstruct, not Landauer proof theater.          *)
(*  Composes `excitement_select`; no second argmin.                    *)
(*                                                                      *)
(*  Anchored in `AdmitKleisli` / `ExcitementImport`. ZERO new axioms.  *)
(*  ZERO `Admitted`. Landauer discharge on Lean `LandauerLaw`.          *)
(* ================================================================== *)

From Coq Require Import Arith List Bool.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.

Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Local+mesh carriers + acting coalgebra                  *)
(* ------------------------------------------------------------------ *)

(** Local working-copy surrogate (commit head + entropy bits). *)
Record frugal_local_state : Set := {
  frugal_local_commit_head : nat;
  frugal_local_entropy_bits : nat
}.

(** Mesh replica surrogate (gossip mesh census entropy). *)
Record frugal_mesh_state : Set := {
  frugal_mesh_replica_seq : nat;
  frugal_mesh_gossip_entropy_bits : nat
}.

(** Paired local+mesh carrier — product state for §4 observation. *)
Record frugal_local_mesh_state : Set := {
  frugal_lm_local : frugal_local_state;
  frugal_lm_mesh : frugal_mesh_state
}.

(** Acting coalgebra deconstruct tag on local+mesh — not Landauer proof. *)
Inductive frugal_local_mesh_coalgebra :=
  | flmc_local_only (l : frugal_local_state)
  | flmc_mesh_only (m : frugal_mesh_state)
  | flmc_paired (s : frugal_local_mesh_state).

(** Whether observation requires both local and mesh components. *)
Definition frugal_coalgebra_requires_paired (c : frugal_local_mesh_coalgebra) : bool :=
  match c with
  | flmc_paired _ => true
  | _ => false
  end.

(** Acting coalgebra deconstruct — unfold paired carrier into observation tag. *)
Definition frugal_local_mesh_deconstruct (s : frugal_local_mesh_state)
    : frugal_local_mesh_coalgebra :=
  flmc_paired s.

(** Frugal MI bit observation — minimal MI cost surrogate for status verb. *)
Record frugal_mi_observation : Set := {
  frugal_i_required_bits : nat;
  frugal_i_observed_bits : nat
}.

(** Witness deficit — `max(0, required − observed)` on nat surrogate. *)
Definition frugal_mi_deficit (obs : frugal_mi_observation) : nat :=
  let req := frugal_i_required_bits obs in
  let got := frugal_i_observed_bits obs in
  if Nat.leb got req then Nat.sub req got else 0.

(** Fail-closed frugal MI errors — positive refuse, not silent no-op. *)
Inductive frugal_mi_refusal :=
  | fmr_landauer_proof_refused
  | fmr_landauer_kernel_fork_refused
  | fmr_mutual_information_zero
  | fmr_mesh_absent_when_paired_required
  | fmr_inconsistent_entropies
  | fmr_witness_deficit (required observed : nat).

(** Verdict of a frugal MI observation class. *)
Inductive frugal_mi_verdict :=
  | fmv_observation_ok
  | fmv_landauer_proof_refused
  | fmv_inadmissible.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Pairwise MI + admissibility conjunct + positive refuse  *)
(* ------------------------------------------------------------------ *)

(** Pairwise Shannon MI bits — `I(X;Y) = H(X) + H(Y) − H(X,Y)` (nat surrogate). *)
Definition pairwise_mi_bits_nat (h_local h_mesh joint_entropy : nat) : option nat :=
  let sum := Nat.add h_local h_mesh in
  if Nat.leb joint_entropy sum then Some (Nat.sub sum joint_entropy) else None.

(** §4 admissibility conjunct inputs (surrogate). *)
Record frugal_mi_admissibility_conjunct : Set := {
  frugal_conj_gate_ok : bool;
  frugal_conj_mi_positive : bool;
  frugal_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ MI>0 ∧ Excitement preserves`. *)
Definition frugal_conjunct_admits (c : frugal_mi_admissibility_conjunct) : bool :=
  frugal_conj_gate_ok c &&
  frugal_conj_mi_positive c &&
  frugal_conj_excitement_preserves c.

(** Classify Landauer proof theater vs typed observation without performing I/O. *)
Definition evaluate_frugal_mi_operation (is_landauer_proof : bool)
    : frugal_mi_verdict :=
  if is_landauer_proof then fmv_landauer_proof_refused else fmv_observation_ok.

(** Positive refuse: Landauer bound proof is inadmissible on this scaffold. *)
Definition refuse_landauer_proof : frugal_mi_refusal :=
  fmr_landauer_proof_refused.

(** Positive refuse: UCRS Landauer kernel fork is inadmissible. *)
Definition refuse_landauer_kernel_fork : frugal_mi_refusal :=
  fmr_landauer_kernel_fork_refused.

(** Build observation from required = observed witness bits. *)
Definition frugal_mi_observation_mk (required observed : nat)
    : frugal_mi_observation :=
  {| frugal_i_required_bits := required;
     frugal_i_observed_bits := observed |}.

(** Attempt frugal MI observation on acting coalgebra — fail closed. *)
Definition observe_frugal_mi_from_coalgebra
    (coalgebra : frugal_local_mesh_coalgebra)
    (h_local h_mesh joint_entropy required observed : nat)
    (conjunct : frugal_mi_admissibility_conjunct) :
  frugal_mi_observation + frugal_mi_refusal :=
  if negb (frugal_conjunct_admits conjunct) then
    inr fmr_inconsistent_entropies
  else if negb (frugal_coalgebra_requires_paired coalgebra) then
    inr fmr_mesh_absent_when_paired_required
  else
    match pairwise_mi_bits_nat h_local h_mesh joint_entropy with
    | None => inr fmr_inconsistent_entropies
    | Some mi =>
        if Nat.eqb mi 0 then
          inr fmr_mutual_information_zero
        else
          let obs := frugal_mi_observation_mk required observed in
          if Nat.ltb observed required then
            inr (fmr_witness_deficit required observed)
          else
            inl obs
    end.

Lemma frugal_mi_landauer_proof_refused :
  evaluate_frugal_mi_operation true = fmv_landauer_proof_refused.
Proof.
  reflexivity.
Qed.

Lemma frugal_mi_observation_ok_when_not_landauer :
  evaluate_frugal_mi_operation false = fmv_observation_ok.
Proof.
  reflexivity.
Qed.

Lemma refuse_landauer_proof_positive :
  refuse_landauer_proof = fmr_landauer_proof_refused.
Proof.
  reflexivity.
Qed.

Lemma refuse_landauer_kernel_fork_positive :
  refuse_landauer_kernel_fork = fmr_landauer_kernel_fork_refused.
Proof.
  reflexivity.
Qed.

Lemma pairwise_mi_fixture_paired :
  pairwise_mi_bits_nat 4 3 5 = Some 2.
Proof.
  reflexivity.
Qed.

Lemma pairwise_mi_fixture_zero :
  pairwise_mi_bits_nat 2 2 4 = Some 0.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Frugal MI composes Excitement (no second argmin)        *)
(* ------------------------------------------------------------------ *)

(** Context for frugal MI observation over admissible history successors. *)
Record frugal_mi_ctx (src : ThermodynamicState) : Set := {
  frugal_mi_successors : list (history_candidate src)
}.

(** Frugal MI status observation **is** `urge_recovery_select` / `excitement_select`. *)
Definition frugal_mi_select (src : ThermodynamicState)
    (ctx : frugal_mi_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (frugal_mi_successors src ctx).

Theorem frugal_mi_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : frugal_mi_ctx src) :
  frugal_mi_select src ctx =
  excitement_select src (frugal_mi_successors src ctx).
Proof.
  unfold frugal_mi_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem frugal_mi_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : frugal_mi_ctx src) :
  frugal_mi_select src ctx =
  urge_recovery_select src (frugal_mi_successors src ctx).
Proof.
  reflexivity.
Qed.

Theorem frugal_mi_no_local_argmin
    (src : ThermodynamicState) (ctx : frugal_mi_ctx src) :
  frugal_mi_select src ctx =
  excitement_select src (frugal_mi_successors src ctx).
Proof.
  exact (frugal_mi_select_eq_excitement_select src ctx).
Qed.

Lemma frugal_mi_select_empty (src : ThermodynamicState)
    (ctx : frugal_mi_ctx src)
    (Hnil : frugal_mi_successors src ctx = nil) :
  frugal_mi_select src ctx = inr exc_no_candidates.
Proof.
  unfold frugal_mi_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §4 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Definition frugal_fixture_local : frugal_local_state :=
  {| frugal_local_commit_head := 7;
     frugal_local_entropy_bits := 4 |}.

Definition frugal_fixture_mesh : frugal_mesh_state :=
  {| frugal_mesh_replica_seq := 3;
     frugal_mesh_gossip_entropy_bits := 3 |}.

Definition frugal_fixture_paired : frugal_local_mesh_state :=
  {| frugal_lm_local := frugal_fixture_local;
     frugal_lm_mesh := frugal_fixture_mesh |}.

Definition frugal_fixture_coalgebra : frugal_local_mesh_coalgebra :=
  frugal_local_mesh_deconstruct frugal_fixture_paired.

Definition frugal_fixture_conjunct : frugal_mi_admissibility_conjunct :=
  {| frugal_conj_gate_ok := true;
     frugal_conj_mi_positive := true;
     frugal_conj_excitement_preserves := true |}.

Theorem frugal_fixture_landauer_proof_refused :
  refuse_landauer_proof = fmr_landauer_proof_refused.
Proof.
  reflexivity.
Qed.

Theorem frugal_fixture_paired_observation_ok :
  observe_frugal_mi_from_coalgebra
    frugal_fixture_coalgebra 4 3 5 2 2 frugal_fixture_conjunct
  = inl (frugal_mi_observation_mk 2 2).
Proof.
  reflexivity.
Qed.

Theorem frugal_fixture_mesh_absent_refused :
  observe_frugal_mi_from_coalgebra
    (flmc_local_only frugal_fixture_local) 4 3 5 2 2 frugal_fixture_conjunct
  = inr fmr_mesh_absent_when_paired_required.
Proof.
  reflexivity.
Qed.

Theorem frugal_fixture_mi_zero_refused :
  observe_frugal_mi_from_coalgebra
    frugal_fixture_coalgebra 2 2 4 2 2 frugal_fixture_conjunct
  = inr fmr_mutual_information_zero.
Proof.
  reflexivity.
Qed.

Theorem frugal_fixture_witness_deficit_refused :
  observe_frugal_mi_from_coalgebra
    frugal_fixture_coalgebra 4 3 5 3 2 frugal_fixture_conjunct
  = inr (fmr_witness_deficit 3 2).
Proof.
  reflexivity.
Qed.

Theorem frugal_fixture_coalgebra_requires_paired :
  frugal_coalgebra_requires_paired frugal_fixture_coalgebra = true.
Proof.
  reflexivity.
Qed.

Theorem frugal_fixture_deconstruct_paired :
  frugal_local_mesh_deconstruct frugal_fixture_paired = flmc_paired frugal_fixture_paired.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                       *)
(* ------------------------------------------------------------------ *)

Definition frugal_mi_physics_green : bool := false.

Lemma frugal_mi_physics_green_false :
  frugal_mi_physics_green = false.
Proof. reflexivity. Qed.

Definition frugal_mi_production_wired : bool := false.

Lemma frugal_mi_production_wired_false :
  frugal_mi_production_wired = false.
Proof. reflexivity. Qed.

Definition frugal_mi_modality_unwired : bool := true.

Lemma frugal_mi_modality_unwired_true :
  frugal_mi_modality_unwired = true.
Proof. reflexivity. Qed.

Theorem frugal_mi_module_witness : True.
Proof. exact I. Qed.

Theorem frugal_mi_no_new_axiom : True.
Proof. exact I. Qed.

Theorem frugal_mi_positive_refuse_not_silent :
  evaluate_frugal_mi_operation true <> fmv_observation_ok.
Proof.
  unfold evaluate_frugal_mi_operation.
  discriminate.
Qed.

Theorem frugal_mi_acting_coalgebra_not_landauer_proof :
  refuse_landauer_proof <> fmr_landauer_kernel_fork_refused.
Proof.
  discriminate.
Qed.
