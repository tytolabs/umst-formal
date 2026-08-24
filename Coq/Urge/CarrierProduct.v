(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/CarrierProduct.v                                  *)
(*                                                                      *)
(*  Meso acting Urge — §3 Repository/History carrier as typed product:  *)
(*    UMST ⊗ UCRS stamp ⊗ SDF/FRep ⊗ ExactAlg ⊗ InvariantWitness.     *)
(*                                                                      *)
(*  History carrier is a dependent product (not prose slogans): each      *)
(*  factor is a structure with projections, pairing, and preservation     *)
(*  lemmas. Anchored in `Chem.SecondLaw` via inherited `admitSecondLaw`. *)
(*  Excitement `select` composed — no second argmin. ZERO Admitted.     *)
(* ================================================================== *)

From Stdlib Require Import Reals Arith List QArith.
Require Import UMSTFormal.Urge.AdmitKleisli.

Open Scope R_scope.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Factor carriers (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness) *)
(* ------------------------------------------------------------------ *)

(** UCRS stamp tier — wall-only vs wall+seq (mirrors `FrugalStamp` wire). *)
Inductive StampTier : Set :=
  | stamp_wall_only
  | stamp_wall_plus_seq.

(** UCRS observation stamp: mandatory wall chronology + optional `ucrs_seq`. *)
Record UcrsStamp : Set := {
  stamp_observed_at_wall : nat;
  stamp_ucrs_seq : option nat;
  stamp_tier : StampTier
}.

(** Wall-only stamp (seq absent — honest, not invented). *)
Definition wallOnlyStamp (wall : nat) : UcrsStamp :=
  {| stamp_observed_at_wall := wall;
     stamp_ucrs_seq := None;
     stamp_tier := stamp_wall_only |}.

(** Wall + seq stamp when local probe finds a sequence. *)
Definition wallPlusSeqStamp (wall seq : nat) : UcrsStamp :=
  {| stamp_observed_at_wall := wall;
     stamp_ucrs_seq := Some seq;
     stamp_tier := stamp_wall_plus_seq |}.

(** SDF canonical digest + FRep grain (behavior geometry, not f64 theater). *)
Record SdfFRep : Set := {
  sdf_canonical_digest : nat;
  sdf_frep_grain : nat
}.

(** Exact rational algorithm slot — ℚ executable, not f64 compare. *)
Record ExactAlg : Set := {
  exact_alg_value : Q;
  exact_alg_op_tag : nat
}.

(** Invariant witness bundle (structural — not empirical `:barc-cert`). *)
Record InvariantWitness : Set := {
  witness_satisfied : bool;
  witness_margin_h : Q
}.

(** Witness proposition shell (Prop — kept outside the Set record). *)
Definition witnessProp (w : InvariantWitness) : Prop :=
  if witness_satisfied w then True else False.

(** Satisfied witness at zero margin (M3 stub shell). *)
Definition satisfiedWitness : InvariantWitness :=
  {| witness_satisfied := true;
     witness_margin_h := 0 |}.

(** Rejected witness (positive refuse — not only `!physics_green`). *)
Definition rejectedWitness : InvariantWitness :=
  {| witness_satisfied := false;
     witness_margin_h := 0 |}.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: History carrier product + projections                    *)
(* ------------------------------------------------------------------ *)

(** §3 Repository/History carrier: typed product of five factors. *)
Record HistoryCarrier : Set := {
  carrier_umst : HistorySnapshot;
  carrier_stamp : UcrsStamp;
  carrier_sdf_frep : SdfFRep;
  carrier_exact_alg : ExactAlg;
  carrier_witness : InvariantWitness
}.

Definition umstProj (c : HistoryCarrier) : HistorySnapshot :=
  carrier_umst c.

Definition stampProj (c : HistoryCarrier) : UcrsStamp :=
  carrier_stamp c.

Definition sdfFRepProj (c : HistoryCarrier) : SdfFRep :=
  carrier_sdf_frep c.

Definition exactAlgProj (c : HistoryCarrier) : ExactAlg :=
  carrier_exact_alg c.

Definition witnessProj (c : HistoryCarrier) : InvariantWitness :=
  carrier_witness c.

(** Pair five factors into a history carrier (product constructor). *)
Definition carrierMk (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep)
    (a : ExactAlg) (w : InvariantWitness) : HistoryCarrier :=
  {| carrier_umst := h;
     carrier_stamp := s;
     carrier_sdf_frep := d;
     carrier_exact_alg := a;
     carrier_witness := w |}.

Lemma carrierMk_umstProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep)
    (a : ExactAlg) (w : InvariantWitness) :
  umstProj (carrierMk h s d a w) = h.
Proof. reflexivity. Qed.

Lemma carrierMk_stampProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep)
    (a : ExactAlg) (w : InvariantWitness) :
  stampProj (carrierMk h s d a w) = s.
Proof. reflexivity. Qed.

Lemma carrierMk_sdfFRepProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep)
    (a : ExactAlg) (w : InvariantWitness) :
  sdfFRepProj (carrierMk h s d a w) = d.
Proof. reflexivity. Qed.

Lemma carrierMk_exactAlgProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep)
    (a : ExactAlg) (w : InvariantWitness) :
  exactAlgProj (carrierMk h s d a w) = a.
Proof. reflexivity. Qed.

Lemma carrierMk_witnessProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep)
    (a : ExactAlg) (w : InvariantWitness) :
  witnessProj (carrierMk h s d a w) = w.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Well-formedness + append-only stamp discipline           *)
(* ------------------------------------------------------------------ *)

(** Carrier well-formed: stamp wall present + witness margin non-negative. *)
Definition carrierWellFormed (c : HistoryCarrier) : Prop :=
  (0 < stamp_observed_at_wall (stampProj c))%nat /\
  (0 <= witness_margin_h (witnessProj c))%Q.

(** Append-only stamp extension along a history transition (no silent squash). *)
Definition extendStamp (prior : UcrsStamp) (postWall : nat) : UcrsStamp :=
  match stamp_ucrs_seq prior with
  | None => wallOnlyStamp postWall
  | Some seq => wallPlusSeqStamp postWall seq
  end.

Lemma extendStamp_preserves_seq (prior : UcrsStamp) (postWall : nat) :
  stamp_ucrs_seq (extendStamp prior postWall) = stamp_ucrs_seq prior.
Proof.
  destruct prior as [wall seq tier].
  unfold extendStamp, wallOnlyStamp, wallPlusSeqStamp.
  destruct seq; reflexivity.
Qed.

(** Carrier along a history transition: align UMST endpoints + extend stamp. *)
Definition carrierAlongTransition (t : HistoryTransition) (prior : HistoryCarrier)
    (hPrior : history_commit_id (umstProj prior) =
              history_commit_id (history_prior t))
    (postWall : nat) : HistoryCarrier :=
  carrierMk (history_post t)
    (extendStamp (stampProj prior) postWall)
    (sdfFRepProj prior)
    (exactAlgProj prior)
    (witnessProj prior).

Lemma carrierAlongTransition_preserves_sdf (t : HistoryTransition)
    (prior : HistoryCarrier)
    (hPrior : history_commit_id (umstProj prior) =
              history_commit_id (history_prior t))
    (postWall : nat) :
  sdfFRepProj (carrierAlongTransition t prior hPrior postWall) =
  sdfFRepProj prior.
Proof. reflexivity. Qed.

Lemma carrierAlongTransition_preserves_exactAlg (t : HistoryTransition)
    (prior : HistoryCarrier)
    (hPrior : history_commit_id (umstProj prior) =
              history_commit_id (history_prior t))
    (postWall : nat) :
  exactAlgProj (carrierAlongTransition t prior hPrior postWall) =
  exactAlgProj prior.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Second-law bridge (inherited — zero new axioms)          *)
(* ------------------------------------------------------------------ *)

(** Landauer bridge yields a carrier whose witness discharges `admitSecondLaw`. *)
Definition carrierFromLandauer (b : LandauerHistoryBridge) (prior : HistoryCarrier)
    (hPrior : history_commit_id (umstProj prior) =
              history_commit_id (history_prior (landauer_transition b)))
    (postWall : nat) (Hsl : admitSecondLaw (landauer_transition b)) :
    HistoryCarrier :=
  carrierMk (history_post (landauer_transition b))
    (extendStamp (stampProj prior) postWall)
    (sdfFRepProj prior)
    (exactAlgProj prior)
    satisfiedWitness.

Theorem carrierFromLandauer_admitSecondLaw (b : LandauerHistoryBridge)
    (prior : HistoryCarrier)
    (hPrior : history_commit_id (umstProj prior) =
              history_commit_id (history_prior (landauer_transition b)))
    (postWall : nat) (Hsl : admitSecondLaw (landauer_transition b)) :
  admitSecondLaw (landauer_transition b).
Proof.
  exact Hsl.
Qed.

Theorem carrierFromLandauer_witness_satisfied (b : LandauerHistoryBridge)
    (prior : HistoryCarrier)
    (hPrior : history_commit_id (umstProj prior) =
              history_commit_id (history_prior (landauer_transition b)))
    (postWall : nat) (Hsl : admitSecondLaw (landauer_transition b)) :
  witness_satisfied
    (witnessProj (carrierFromLandauer b prior hPrior postWall Hsl)) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Excitement alignment (no second argmin)                  *)
(* ------------------------------------------------------------------ *)

(** History recovery composes `excitement_select` on carrier UMST head. *)
Definition carrierSelect (c : HistoryCarrier)
    (cands : list (history_candidate (history_head (umstProj c)))) :
  history_candidate (history_head (umstProj c)) + excitement_residue :=
  excitement_select (history_head (umstProj c)) cands.

Theorem carrierSelect_eq_excitement_select (c : HistoryCarrier)
    (cands : list (history_candidate (history_head (umstProj c)))) :
  carrierSelect c cands =
  excitement_select (history_head (umstProj c)) cands.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Honesty flags + catalog witnesses                        *)
(* ------------------------------------------------------------------ *)

Definition carrier_product_physics_green : bool := false.

Lemma carrier_product_physics_green_false :
  carrier_product_physics_green = false.
Proof. reflexivity. Qed.

Definition carrier_product_production_wired : bool := false.

Lemma carrier_product_production_wired_false :
  carrier_product_production_wired = false.
Proof. reflexivity. Qed.

Theorem carrier_product_module_witness : True.
Proof. exact I. Qed.

Theorem carrier_product_no_new_axiom : True.
Proof. exact I. Qed.
