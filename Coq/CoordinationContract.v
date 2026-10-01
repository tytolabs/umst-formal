(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ------------------------------------------------------------------ *)
(*  UMST-Formal: CoordinationContract.v                                *)
(*                                                                     *)
(*  The contract a coordination runtime honours (umst-ucrs implements  *)
(*  it in Rust); twin of Lean/CoordinationContract.lean. The cost is   *)
(*  the Landauer cost E_Landauer_bit T * bits, nonnegative through     *)
(*  E_Landauer_bit_pos. Zero Parameter / Axiom in this module.         *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Reals Lra Lia List.
Require Import UMSTFormal.LandauerEinsteinBridge.
Import ListNotations.
Open Scope R_scope.

Definition landauer_cost (bits T : R) : R := E_Landauer_bit T * bits.

Lemma landauer_cost_nonneg (bits T : R) : 0 < T -> 0 <= bits -> 0 <= landauer_cost bits T.
Proof.
  intros HT Hb. unfold landauer_cost.
  apply Rmult_le_pos; [apply Rlt_le, E_Landauer_bit_pos, HT | exact Hb].
Qed.

Lemma landauer_cost_add (a b T : R) :
  landauer_cost (a + b) T = landauer_cost a T + landauer_cost b T.
Proof. unfold landauer_cost. ring. Qed.

(* Admission *)

Record ClockThermState := { desync_energy : R; budget : R; temperature : R; total_sync_cost : R }.

(* Admitted when the cost fits the budget and does not exceed the desync energy it resolves (Clausius-Duhem). *)
Definition admits (s : ClockThermState) (bits : R) : Prop :=
  landauer_cost bits (temperature s) <= budget s /\ landauer_cost bits (temperature s) <= desync_energy s.

Definition gated_sync (s : ClockThermState) (bits : R) : ClockThermState :=
  {| desync_energy := 0; budget := budget s; temperature := temperature s;
     total_sync_cost := total_sync_cost s + landauer_cost bits (temperature s) |}.

Theorem admitted_cost_bounded (s : ClockThermState) (bits : R) :
  0 < temperature s -> 0 <= bits -> admits s bits ->
  0 <= landauer_cost bits (temperature s) /\ landauer_cost bits (temperature s) <= budget s
  /\ landauer_cost bits (temperature s) <= desync_energy s.
Proof.
  intros HT Hb [Hbud Hdes]. repeat split; try assumption. apply landauer_cost_nonneg; assumption.
Qed.

Theorem admitted_budget_nonneg (s : ClockThermState) (bits : R) :
  0 < temperature s -> 0 <= bits -> admits s bits -> 0 <= budget s.
Proof.
  intros HT Hb [Hbud _].
  pose proof (landauer_cost_nonneg bits (temperature s) HT Hb). lra.
Qed.

Theorem gated_sync_second_law (s : ClockThermState) (bits : R) :
  0 < temperature s -> 0 <= bits -> admits s bits ->
  desync_energy (gated_sync s bits) <= desync_energy s /\ total_sync_cost s <= total_sync_cost (gated_sync s bits).
Proof.
  intros HT Hb [_ Hdes]. pose proof (landauer_cost_nonneg bits (temperature s) HT Hb).
  simpl. split; lra.
Qed.

(* Clock drift *)

Record ClockState := { tick : nat; drift : R }.

Definition clock_step (c : ClockState) (d : R) : ClockState :=
  {| tick := S (tick c); drift := drift c + d |}.

Definition clock_run (c : ClockState) (ds : list R) : ClockState := fold_left clock_step ds c.

Theorem clock_run_monotone (ds : list R) : forall c : ClockState,
  Forall (fun d => 0 <= d) ds ->
  drift c <= drift (clock_run c ds) /\ tick (clock_run c ds) = (tick c + length ds)%nat.
Proof.
  unfold clock_run. induction ds as [| d ds IH]; intros c H; simpl.
  - split; [lra | lia].
  - inversion H as [| d' ds' Hd Hds]; subst.
    destruct (IH (clock_step c d) Hds) as [Hdrift Htick].
    simpl in Hdrift, Htick. split; [lra | rewrite Htick; lia].
Qed.

(* Byzantine isolation *)

Record Participant := { pid : nat; credit : R; faulty : bool }.

Definition honest_credits (ps : list Participant) : list R :=
  map credit (filter (fun p => negb (faulty p)) ps).

Theorem honest_credits_append_faulty (ps fs : list Participant) :
  Forall (fun p => faulty p = true) fs -> honest_credits (ps ++ fs) = honest_credits ps.
Proof.
  intros H. unfold honest_credits. rewrite filter_app.
  assert (Hf : filter (fun p => negb (faulty p)) fs = []).
  { induction H as [| p fs' Hp _ IH]; simpl; [reflexivity |]. rewrite Hp. exact IH. }
  rewrite Hf, app_nil_r. reflexivity.
Qed.

Corollary honest_credits_faulty_only (fs : list Participant) :
  Forall (fun p => faulty p = true) fs -> honest_credits fs = [].
Proof. intros H. exact (honest_credits_append_faulty [] fs H). Qed.

(* Wire order *)

Record WireStamp := { seq : nat }.

Definition wire_next (w : WireStamp) : WireStamp := {| seq := S (seq w) |}.

Fixpoint wire_iter (n : nat) (w : WireStamp) : WireStamp :=
  match n with O => w | S k => wire_iter k (wire_next w) end.

Theorem wire_iter_seq (n : nat) : forall w : WireStamp, seq (wire_iter n w) = (seq w + n)%nat.
Proof. induction n as [| n IH]; intros w; simpl; [lia | rewrite IH; simpl; lia]. Qed.
