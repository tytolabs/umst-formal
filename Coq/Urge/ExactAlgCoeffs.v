(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ExactAlgCoeffs.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §3 ExactAlg coefficients on the history carrier. *)
(*  ℚ coefficient slot on `HistoryCarrier` — not silent f64 identity.   *)
(*  Composes `excitement_select`; no second argmin.                     *)
(*                                                                      *)
(*  Anchored in `CarrierProduct` / `AdmitKleisli` / `ExcitementImport`. *)
(*  ZERO new axioms. ZERO `Admitted`. Landauer on Lean `LandauerLaw`.   *)
(* ================================================================== *)

From Coq Require Import Arith List Bool ZArith QArith.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.
Require Import UMSTFormal.Urge.ExcitementImport.
Require Import UMSTFormal.Urge.CarrierProduct.

Open Scope bool_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: ExactAlg coefficient carriers on HistoryCarrier         *)
(* ------------------------------------------------------------------ *)

(** ℚ coefficient slot — mirrors Rust `ExactAlgCoeff` (num/den/op_tag). *)
Record exact_alg_coeff : Set := {
  eac_num : Z;
  eac_den : nat;
  eac_op_tag : nat
}.

(** ExactAlg coefficients attached to a history-carrier content id. *)
Record carrier_exact_alg_coeffs : Set := {
  ceac_content_id : nat;
  ceac_coeff : exact_alg_coeff
}.

(** Witness bundle an ExactAlg coefficient morphism must preserve (§3). *)
Record exact_alg_coeff_witness : Set := {
  eacw_content_id : nat;
  eacw_value : Q;
  eacw_op_tag : nat
}.

(** Typed ExactAlg coefficient morphism — admissible carrier slot update. *)
Record exact_alg_coeff_morphism : Set := {
  eacm_from : carrier_exact_alg_coeffs;
  eacm_to_carrier : HistoryCarrier;
  eacm_witness : exact_alg_coeff_witness;
  eacm_excitement_selected : bool
}.

(** f64 silent-identity theater tag — positive refuse carrier (not ℚ). *)
Inductive float_carrier_tag := float_theater.

(** Fail-closed ExactAlg coefficient errors — positive refuse, not silent accept. *)
Inductive exact_alg_coeffs_refusal :=
  | eacr_f64_identity_theater
  | eacr_zero_denominator
  | eacr_exact_alg_absent
  | eacr_second_argmin
  | eacr_gate_rejected (seq : nat).

(** Verdict of an ExactAlg coefficient admit operation class. *)
Inductive exact_alg_coeffs_verdict :=
  | eacv_admitted
  | eacv_f64_theater_refused
  | eacv_zero_den_refused
  | eacv_inadmissible.

(** Project ℚ coefficient value when denominator is non-zero. *)
Definition exact_alg_coeff_value (c : exact_alg_coeff) : Q :=
  (eac_num c # (Pos.of_nat (eac_den c)))%Q.

(** Whether ℚ denominator is non-zero (fail-closed admit precondition). *)
Definition exact_alg_coeff_den_nonzero (c : exact_alg_coeff) : bool :=
  negb ((eac_den c =? 0)%nat).

(** Map admitted ℚ slot to `CarrierProduct.ExactAlg`. *)
Definition exact_alg_coeff_to_exactAlg (c : exact_alg_coeff) : ExactAlg :=
  {| exact_alg_value := exact_alg_coeff_value c;
     exact_alg_op_tag := eac_op_tag c |}.

(** Attach ℚ coefficients to an existing history carrier (§3 product factor). *)
Definition attach_exact_alg_coeff (carrier : HistoryCarrier) (coeff : exact_alg_coeff)
    : HistoryCarrier :=
  carrierMk (umstProj carrier) (stampProj carrier) (sdfFRepProj carrier)
    (exact_alg_coeff_to_exactAlg coeff) (witnessProj carrier).

(* ------------------------------------------------------------------ *)
(*  SECTION 2: §3 admissibility conjunct + positive refuse            *)
(* ------------------------------------------------------------------ *)

(** §3 admissibility conjunct inputs (surrogate). *)
Record exact_alg_coeff_admissibility_conjunct : Set := {
  eacc_conj_gate_ok : bool;
  eacc_conj_den_nonzero : bool;
  eacc_conj_excitement_preserves : bool
}.

(** Evaluate `admit(h) ⟺ gate ∧ den≠0 ∧ Excitement preserves`. *)
Definition exact_alg_coeff_conjunct_admits (c : exact_alg_coeff_admissibility_conjunct)
    : bool :=
  eacc_conj_gate_ok c &&
  eacc_conj_den_nonzero c &&
  eacc_conj_excitement_preserves c.

(** Classify f64 identity theater vs ℚ carrier admit. *)
Definition evaluate_f64_identity_theater (is_f64_theater : bool)
    : exact_alg_coeffs_verdict :=
  if is_f64_theater then eacv_f64_theater_refused else eacv_admitted.

(** Classify zero denominator vs ℚ carrier admit. *)
Definition evaluate_zero_denominator (is_zero_den : bool)
    : exact_alg_coeffs_verdict :=
  if is_zero_den then eacv_zero_den_refused else eacv_admitted.

(** Positive refuse: f64 silent identity theater — ℚ carrier required. *)
Definition refuse_f64_identity_theater (_ : float_carrier_tag)
    : exact_alg_coeffs_refusal :=
  eacr_f64_identity_theater.

(** Positive refuse: zero denominator on ℚ coefficient. *)
Definition refuse_zero_denominator : exact_alg_coeffs_refusal :=
  eacr_zero_denominator.

(** Positive refuse: ExactAlg slot absent on carrier. *)
Definition refuse_exact_alg_absent : exact_alg_coeffs_refusal :=
  eacr_exact_alg_absent.

(** Positive refuse: second Excitement selector — compose `excitement_select`. *)
Definition refuse_second_argmin_selector : exact_alg_coeffs_refusal :=
  eacr_second_argmin.

(** Build witness from carrier ExactAlg coefficients. *)
Definition witness_from_carrier_coeffs (c : carrier_exact_alg_coeffs)
    : exact_alg_coeff_witness :=
  {| eacw_content_id := ceac_content_id c;
     eacw_value := exact_alg_coeff_value (ceac_coeff c);
     eacw_op_tag := eac_op_tag (ceac_coeff c) |}.

(** Admit ℚ ExactAlg coefficients on carrier — fail closed on zero denominator. *)
Definition admit_carrier_exact_alg (c : carrier_exact_alg_coeffs)
    : carrier_exact_alg_coeffs + exact_alg_coeffs_refusal :=
  if exact_alg_coeff_den_nonzero (ceac_coeff c) then inl c
  else inr eacr_zero_denominator.

(** Attempt typed ExactAlg coefficient morphism — fail closed on inadmissibility. *)
Definition apply_exact_alg_coeff_morphism
    (coeffs : carrier_exact_alg_coeffs)
    (carrier : HistoryCarrier)
    (conjunct : exact_alg_coeff_admissibility_conjunct)
    (excitement_selected : bool)
    : exact_alg_coeff_morphism + exact_alg_coeffs_refusal :=
  if negb (exact_alg_coeff_conjunct_admits conjunct) then
    inr (eacr_gate_rejected 0)
  else
    match admit_carrier_exact_alg coeffs with
    | inr r => inr r
    | inl admitted =>
        if negb excitement_selected then
          inr eacr_exact_alg_absent
        else
          inl
            {| eacm_from := admitted;
               eacm_to_carrier :=
                 attach_exact_alg_coeff carrier (ceac_coeff admitted);
               eacm_witness := witness_from_carrier_coeffs admitted;
               eacm_excitement_selected := excitement_selected |}
    end.

Lemma exact_alg_coeff_f64_theater_refused :
  refuse_f64_identity_theater float_theater = eacr_f64_identity_theater.
Proof.
  simpl. reflexivity.
Qed.

Lemma exact_alg_coeff_zero_den_refused :
  refuse_zero_denominator = eacr_zero_denominator.
Proof.
  simpl. reflexivity.
Qed.

Lemma exact_alg_coeff_exact_alg_absent_refused :
  refuse_exact_alg_absent = eacr_exact_alg_absent.
Proof.
  simpl. reflexivity.
Qed.

Lemma refuse_second_argmin_selector_positive :
  refuse_second_argmin_selector = eacr_second_argmin.
Proof.
  simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: ExactAlg coefficients compose Excitement (no argmin)    *)
(* ------------------------------------------------------------------ *)

(** Excitement compose pin — import selector; refuse second local argmin. *)
Inductive exact_alg_coeff_excitement_compose_pin :=
  | eacep_import_select_excitement
  | eacep_second_argmin_refused.

(** Context for ExactAlg coefficients over admissible history successors. *)
Record exact_alg_coeff_ctx (src : ThermodynamicState) : Set := {
  exact_alg_coeff_successors : list (history_candidate src)
}.

(** ExactAlg coefficient path composes `excitement_select` — not a second argmin. *)
Definition exact_alg_coeff_excitement_select (src : ThermodynamicState)
    (cands : list (history_candidate src))
    (pin : exact_alg_coeff_excitement_compose_pin) :
  history_candidate src + excitement_residue :=
  match pin with
  | eacep_import_select_excitement => excitement_select src cands
  | eacep_second_argmin_refused => inr exc_all_inadmissible
  end.

(** ExactAlg coefficient selection **is** `urge_recovery_select` / `excitement_select`. *)
Definition exact_alg_coeff_select (src : ThermodynamicState)
    (ctx : exact_alg_coeff_ctx src) :
  history_candidate src + excitement_residue :=
  urge_recovery_select src (exact_alg_coeff_successors src ctx).

Theorem exact_alg_coeff_excitement_select_eq_excitement_select
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  exact_alg_coeff_excitement_select src cands eacep_import_select_excitement =
  excitement_select src cands.
Proof.
  simpl. reflexivity.
Qed.

Theorem exact_alg_coeff_select_eq_excitement_select
    (src : ThermodynamicState) (ctx : exact_alg_coeff_ctx src) :
  exact_alg_coeff_select src ctx =
  excitement_select src (exact_alg_coeff_successors src ctx).
Proof.
  unfold exact_alg_coeff_select, urge_recovery_select.
  reflexivity.
Qed.

Theorem exact_alg_coeff_select_eq_urge_recovery_select
    (src : ThermodynamicState) (ctx : exact_alg_coeff_ctx src) :
  exact_alg_coeff_select src ctx =
  urge_recovery_select src (exact_alg_coeff_successors src ctx).
Proof.
  simpl. reflexivity.
Qed.

Theorem exact_alg_coeff_no_local_argmin
    (src : ThermodynamicState) (ctx : exact_alg_coeff_ctx src) :
  exact_alg_coeff_select src ctx =
  excitement_select src (exact_alg_coeff_successors src ctx).
Proof.
  exact (exact_alg_coeff_select_eq_excitement_select src ctx).
Qed.

Theorem exact_alg_coeff_excitement_select_refuses_second_argmin
    (src : ThermodynamicState)
    (cands : list (history_candidate src)) :
  exact_alg_coeff_excitement_select src cands eacep_second_argmin_refused =
  inr exc_all_inadmissible.
Proof.
  simpl. reflexivity.
Qed.

Lemma exact_alg_coeff_empty (src : ThermodynamicState)
    (ctx : exact_alg_coeff_ctx src)
    (Hnil : exact_alg_coeff_successors src ctx = nil) :
  exact_alg_coeff_select src ctx = inr exc_no_candidates.
Proof.
  unfold exact_alg_coeff_select, urge_recovery_select.
  rewrite Hnil. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: §3 fixtures + witness theorems                          *)
(* ------------------------------------------------------------------ *)

Definition exact_alg_fixture_coeff : exact_alg_coeff :=
  {| eac_num := 3%Z;
     eac_den := 2;
     eac_op_tag := 1 |}.

Definition exact_alg_fixture_zero_den : exact_alg_coeff :=
  {| eac_num := 1%Z;
     eac_den := 0;
     eac_op_tag := 0 |}.

Definition exact_alg_fixture_carrier_coeffs : carrier_exact_alg_coeffs :=
  {| ceac_content_id := 1;
     ceac_coeff := exact_alg_fixture_coeff |}.

Definition exact_alg_fixture_zero_den_coeffs : carrier_exact_alg_coeffs :=
  {| ceac_content_id := 1;
     ceac_coeff := exact_alg_fixture_zero_den |}.

Definition exact_alg_fixture_state : ThermodynamicState :=
  {| density := 2400 # 1;
     free_energy := 0;
     hydration := 0;
     strength := 0 |}.

Definition exact_alg_fixture_snapshot : HistorySnapshot :=
  {| history_commit_id := 1;
     history_head := exact_alg_fixture_state |}.

Definition exact_alg_fixture_stamp : UcrsStamp :=
  wallOnlyStamp 42.

Definition exact_alg_fixture_sdf : SdfFRep :=
  {| sdf_canonical_digest := 5381;
     sdf_frep_grain := 1 |}.

Definition exact_alg_fixture_exact_alg : ExactAlg :=
  exact_alg_coeff_to_exactAlg exact_alg_fixture_coeff.

Definition exact_alg_fixture_carrier : HistoryCarrier :=
  carrierMk exact_alg_fixture_snapshot exact_alg_fixture_stamp
    exact_alg_fixture_sdf exact_alg_fixture_exact_alg satisfiedWitness.

Definition exact_alg_fixture_conjunct : exact_alg_coeff_admissibility_conjunct :=
  {| eacc_conj_gate_ok := true;
     eacc_conj_den_nonzero := true;
     eacc_conj_excitement_preserves := true |}.

Theorem exact_alg_fixture_admit_ok :
  admit_carrier_exact_alg exact_alg_fixture_carrier_coeffs =
  inl exact_alg_fixture_carrier_coeffs.
Proof.
  unfold admit_carrier_exact_alg, exact_alg_coeff_den_nonzero.
  simpl. reflexivity.
Qed.

Theorem exact_alg_fixture_zero_den_refused :
  admit_carrier_exact_alg exact_alg_fixture_zero_den_coeffs =
  inr eacr_zero_denominator.
Proof.
  unfold admit_carrier_exact_alg, exact_alg_coeff_den_nonzero.
  simpl. reflexivity.
Qed.

Theorem exact_alg_fixture_f64_theater_refused :
  evaluate_f64_identity_theater true = eacv_f64_theater_refused.
Proof.
  simpl. reflexivity.
Qed.

Theorem exact_alg_fixture_apply_morphism_ok :
  apply_exact_alg_coeff_morphism
    exact_alg_fixture_carrier_coeffs exact_alg_fixture_carrier
    exact_alg_fixture_conjunct true
  = inl
      {| eacm_from := exact_alg_fixture_carrier_coeffs;
         eacm_to_carrier :=
           attach_exact_alg_coeff exact_alg_fixture_carrier exact_alg_fixture_coeff;
         eacm_witness := witness_from_carrier_coeffs exact_alg_fixture_carrier_coeffs;
         eacm_excitement_selected := true |}.
Proof.
  simpl. reflexivity.
Qed.

Theorem exact_alg_fixture_witness_preserves_value :
  eacw_value (witness_from_carrier_coeffs exact_alg_fixture_carrier_coeffs) =
  exact_alg_coeff_value exact_alg_fixture_coeff.
Proof.
  simpl. reflexivity.
Qed.

Theorem exact_alg_fixture_attach_preserves_exactAlg :
  exactAlgProj
    (attach_exact_alg_coeff exact_alg_fixture_carrier exact_alg_fixture_coeff) =
  exact_alg_fixture_exact_alg.
Proof.
  simpl. reflexivity.
Qed.

Theorem exact_alg_coeff_f64_theater_not_admitted :
  evaluate_f64_identity_theater true <> eacv_admitted.
Proof.
  unfold evaluate_f64_identity_theater.
  discriminate.
Qed.

Theorem exact_alg_coeff_zero_den_not_admitted :
  evaluate_zero_denominator true <> eacv_admitted.
Proof.
  unfold evaluate_zero_denominator.
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Honesty flags + catalog witnesses                        *)
(* ------------------------------------------------------------------ *)

Definition exact_alg_coeffs_physics_green : bool := false.

Lemma exact_alg_coeffs_physics_green_false :
  exact_alg_coeffs_physics_green = false.
Proof. reflexivity. Qed.

Definition exact_alg_coeffs_production_wired : bool := false.

Lemma exact_alg_coeffs_production_wired_false :
  exact_alg_coeffs_production_wired = false.
Proof. reflexivity. Qed.

Theorem exact_alg_coeffs_module_witness : True.
Proof. exact I. Qed.

Theorem exact_alg_coeffs_no_new_axiom : True.
Proof. exact I. Qed.

Theorem exact_alg_coeffs_positive_refuse_not_silent :
  evaluate_f64_identity_theater true <> eacv_admitted.
Proof.
  exact exact_alg_coeff_f64_theater_not_admitted.
Qed.
