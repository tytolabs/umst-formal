(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ===================================================================== *)
(*  UMST-Formal: UnfoldTermination.v                                      *)
(*                                                                        *)
(*  Twin of Lean/UnfoldTermination.lean over exact rationals (law L-E):   *)
(*  spends each at least eps > 0 summing to at most B number n with       *)
(*  n eps <= B, so n <= floor (B / eps); a step erasing at least b bits   *)
(*  at a cost of at least bits * kT * l with l >= l_lo spends at least    *)
(*  b * kT * l_lo, l_lo = 6931471803 / 10^10 the lower end of the         *)
(*  enclosure of ln 2.                                                    *)
(* ===================================================================== *)

From Stdlib Require Import QArith Qround Lqa List ZArith Lia.
Import ListNotations.

Open Scope Q_scope.

Definition qsum (l : list Q) : Q := fold_right Qplus 0 l.

Definition qlen (l : list Q) : Q := inject_Z (Z.of_nat (length l)).

Lemma qlen_cons (d : Q) (ds : list Q) : qlen (d :: ds) == 1 + qlen ds.
Proof. unfold qlen. simpl length. rewrite Nat2Z.inj_succ, <- Z.add_1_l, inject_Z_plus. reflexivity. Qed.

(** L-E: n eps <= B. *)
Theorem steps_mul_le (eps B : Q) (l : list Q) : Forall (fun w => eps <= w) l -> qsum l <= B -> qlen l * eps <= B.
Proof.
  intros hf hB. enough (key : qlen l * eps <= qsum l) by (eapply Qle_trans; eassumption). clear hB.
  induction l as [| w l IH].
  - unfold qlen, qsum. simpl length. change (inject_Z (Z.of_nat 0)) with 0. rewrite Qmult_0_l. apply Qle_refl.
  - inversion hf as [| ? ? hw hl]; subst. rewrite qlen_cons. pose proof (IH hl) as ih. unfold qsum in *. simpl.
    setoid_replace ((1 + qlen l) * eps) with (eps + qlen l * eps) by ring. apply Qplus_le_compat; assumption.
Qed.

(** L-E as a step count: n <= floor (B / eps). *)
Theorem steps_le_floor (eps B : Q) (l : list Q) :
  0 < eps -> Forall (fun w => eps <= w) l -> qsum l <= B -> (Z.of_nat (length l) <= Qfloor (B / eps))%Z.
Proof.
  intros he hf hB. pose proof (steps_mul_le eps B l hf hB) as h.
  assert (hd : qlen l <= B / eps).
  { apply Qle_shift_div_l; assumption. }
  pose proof (Qlt_floor (B / eps)) as hfl.
  assert (hlt : qlen l < inject_Z (Qfloor (B / eps) + 1)) by exact (Qle_lt_trans _ _ _ hd hfl).
  unfold qlen in hlt. rewrite <- Zlt_Qlt in hlt. lia.
Qed.

(** The lower end of the enclosure of ln 2. *)
Definition ln2Lower : Q := 6931471803 # 10000000000.

(** The Landauer floor enclosed from below: bits >= b and l >= ln2Lower give b kT ln2Lower <= bits kT l. *)
Theorem erase_spend_ge_enclosure (kT l W : Q) (b bits : nat) :
  0 <= kT -> ln2Lower <= l -> (b <= bits)%nat -> inject_Z (Z.of_nat bits) * (kT * l) <= W ->
  inject_Z (Z.of_nat b) * (kT * ln2Lower) <= W.
Proof.
  intros hk hl hb hc.
  assert (hbb : inject_Z (Z.of_nat b) <= inject_Z (Z.of_nat bits)) by (rewrite <- Zle_Qle; lia).
  assert (h0 : 0 <= inject_Z (Z.of_nat b)) by (change 0 with (inject_Z 0); rewrite <- Zle_Qle; lia).
  assert (hlo : 0 <= ln2Lower) by (unfold ln2Lower, Qle; simpl; lia).
  assert (hbits : 0 <= inject_Z (Z.of_nat bits)) by (change 0 with (inject_Z 0); rewrite <- Zle_Qle; lia).
  assert (h1 : inject_Z (Z.of_nat b) * (kT * ln2Lower) <= inject_Z (Z.of_nat bits) * (kT * ln2Lower))
    by (apply Qmult_le_compat_r; [exact hbb | apply Qmult_le_0_compat; assumption]).
  assert (h2 : kT * ln2Lower <= kT * l)
    by (setoid_replace (kT * ln2Lower) with (ln2Lower * kT) by ring;
        setoid_replace (kT * l) with (l * kT) by ring; apply Qmult_le_compat_r; assumption).
  assert (h3 : inject_Z (Z.of_nat bits) * (kT * ln2Lower) <= inject_Z (Z.of_nat bits) * (kT * l))
    by (setoid_replace (inject_Z (Z.of_nat bits) * (kT * ln2Lower)) with ((kT * ln2Lower) * inject_Z (Z.of_nat bits)) by ring;
        setoid_replace (inject_Z (Z.of_nat bits) * (kT * l)) with ((kT * l) * inject_Z (Z.of_nat bits)) by ring;
        apply Qmult_le_compat_r; assumption).
  exact (Qle_trans _ _ _ h1 (Qle_trans _ _ _ h3 hc)).
Qed.
