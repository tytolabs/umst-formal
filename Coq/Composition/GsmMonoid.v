(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ======================================================================== *)
(*  UMSTFormal.Composition.GsmMonoid — the composition law of GSM atoms     *)
(*  and the glue fraction (twin of Lean/Composition/GsmMonoid.lean, W-44).  *)
(*                                                                          *)
(*  Coq carries a GSM potential over the rationals in supporting-line form: *)
(*  phi with a slope dphi such that phi x + dphi x (y - x) <= phi y for all *)
(*  x, y (convexity with a subgradient), phi >= 0 and phi 0 = 0. The power  *)
(*  at rate x is D = x * dphi x, and the supporting line at x through 0     *)
(*  gives D >= phi x >= 0.                                                  *)
(*                                                                          *)
(*  Potentials and atoms (a convex psi with a potential) form commutative   *)
(*  monoids under pointwise sum and cones under non-negative scaling, up to *)
(*  pointwise equality; the power is additive and homogeneous (a monoid     *)
(*  homomorphism to the non-negative rationals); the atoms passing one      *)
(*  passive step are closed under sum, scaling and the empty composite, and *)
(*  the composite step is a transition case of SecondLaw. A convex glue     *)
(*  term keeps admissibility; an arbitrary glue term needs its own witness. *)
(*  Zero Axiom, Parameter or Admitted.                                      *)
(* ======================================================================== *)

From Stdlib Require Import QArith Qabs Lqa List.
Require Import UMSTFormal.Compat.Gate UMSTFormal.Process.
Import ListNotations.

Open Scope Q_scope.

(* Every obligation below is discharged by its own script, never by the default obligation tactic. *)
#[local] Obligation Tactic := intros; cbv beta.

(* ------------------------------------------------------------------------ *)
(*  Potentials                                                              *)
(* ------------------------------------------------------------------------ *)

(** A GSM dissipation potential in supporting-line form. *)
Record GsmPotential := mkPot {
  phi : Q -> Q;
  dphi : Q -> Q;
  support : forall x y, phi x + dphi x * (y - x) <= phi y;
  phi_nonneg : forall x, 0 <= phi x;
  phi_zero : phi 0 == 0
}.

(** Dissipation power at rate x. *)
Definition power (P : GsmPotential) (x : Q) : Q := x * dphi P x.

(** The supporting line at x through 0: phi x <= x * dphi x. *)
Lemma phi_le_power (P : GsmPotential) (x : Q) : phi P x <= power P x.
Proof.
  unfold power. pose proof (support P x 0) as h. pose proof (phi_zero P) as h0.
  setoid_replace (dphi P x * (0 - x)) with (- (x * dphi P x)) in h by ring. lra.
Qed.

(** Non-negative dissipation from a convex, non-negative potential pinned at zero. *)
Theorem power_nonneg (P : GsmPotential) (x : Q) : 0 <= power P x.
Proof. pose proof (phi_le_power P x). pose proof (phi_nonneg P x). lra. Qed.

Program Definition pot_zero : GsmPotential := mkPot (fun _ => 0) (fun _ => 0) _ _ _.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed.
Next Obligation. reflexivity. Qed.

Program Definition pot_add (P R : GsmPotential) : GsmPotential :=
  mkPot (fun x => phi P x + phi R x) (fun x => dphi P x + dphi R x) _ _ _.
Next Obligation.
  pose proof (support P x y). pose proof (support R x y).
  setoid_replace ((dphi P x + dphi R x) * (y - x)) with (dphi P x * (y - x) + dphi R x * (y - x)) by ring. lra.
Qed.
Next Obligation. pose proof (phi_nonneg P x). pose proof (phi_nonneg R x). lra. Qed.
Next Obligation. rewrite (phi_zero P), (phi_zero R). reflexivity. Qed.

Program Definition pot_scale (c : Q) (hc : 0 <= c) (P : GsmPotential) : GsmPotential :=
  mkPot (fun x => c * phi P x) (fun x => c * dphi P x) _ _ _.
Next Obligation.
  pose proof (support P x y) as h.
  setoid_replace (c * phi P x + c * dphi P x * (y - x)) with (c * (phi P x + dphi P x * (y - x))) by ring.
  nra.
Qed.
Next Obligation. pose proof (phi_nonneg P x). nra. Qed.
Next Obligation. rewrite (phi_zero P). ring. Qed.

(** Pointwise equality of potentials. *)
Definition pot_eq (P R : GsmPotential) : Prop :=
  forall x, phi P x == phi R x /\ dphi P x == dphi R x.

Theorem pot_add_assoc (P R S : GsmPotential) : pot_eq (pot_add (pot_add P R) S) (pot_add P (pot_add R S)).
Proof. intro x; simpl; split; ring. Qed.

Theorem pot_add_comm (P R : GsmPotential) : pot_eq (pot_add P R) (pot_add R P).
Proof. intro x; simpl; split; ring. Qed.

Theorem pot_zero_add (P : GsmPotential) : pot_eq (pot_add pot_zero P) P.
Proof. intro x; simpl; split; ring. Qed.

Theorem pot_scale_one (P : GsmPotential) (h : 0 <= 1) : pot_eq (pot_scale 1 h P) P.
Proof. intro x; simpl; split; ring. Qed.

Theorem pot_scale_mul (a b : Q) (ha : 0 <= a) (hb : 0 <= b) (hab : 0 <= a * b) (P : GsmPotential) :
  pot_eq (pot_scale (a * b) hab P) (pot_scale a ha (pot_scale b hb P)).
Proof. intro x; simpl; split; ring. Qed.

Theorem pot_scale_add (c : Q) (hc : 0 <= c) (P R : GsmPotential) :
  pot_eq (pot_scale c hc (pot_add P R)) (pot_add (pot_scale c hc P) (pot_scale c hc R)).
Proof. intro x; simpl; split; ring. Qed.

Theorem pot_add_scale (a b : Q) (ha : 0 <= a) (hb : 0 <= b) (hab : 0 <= a + b) (P : GsmPotential) :
  pot_eq (pot_scale (a + b) hab P) (pot_add (pot_scale a ha P) (pot_scale b hb P)).
Proof. intro x; simpl; split; ring. Qed.

(** The power is a monoid homomorphism into the non-negative rationals: zero, additive, homogeneous. *)
Theorem power_zero (x : Q) : power pot_zero x == 0.
Proof. unfold power; simpl; ring. Qed.

Theorem power_add (P R : GsmPotential) (x : Q) : power (pot_add P R) x == power P x + power R x.
Proof. unfold power; simpl; ring. Qed.

Theorem power_scale (c : Q) (hc : 0 <= c) (P : GsmPotential) (x : Q) :
  power (pot_scale c hc P) x == c * power P x.
Proof. unfold power; simpl; ring. Qed.

(* ------------------------------------------------------------------------ *)
(*  Atoms and the admissible cone                                           *)
(* ------------------------------------------------------------------------ *)

(** A GSM atom: a free energy psi convex in supporting-line form, with a potential. *)
Record GsmAtom := mkAtom {
  psi : Q -> Q;
  dpsi : Q -> Q;
  psi_support : forall x y, psi x + dpsi x * (y - x) <= psi y;
  pot : GsmPotential
}.

Program Definition atom_zero : GsmAtom := mkAtom (fun _ => 0) (fun _ => 0) _ pot_zero.
Next Obligation. lra. Qed.

Program Definition atom_add (A B : GsmAtom) : GsmAtom :=
  mkAtom (fun x => psi A x + psi B x) (fun x => dpsi A x + dpsi B x) _ (pot_add (pot A) (pot B)).
Next Obligation.
  pose proof (psi_support A x y). pose proof (psi_support B x y).
  setoid_replace ((dpsi A x + dpsi B x) * (y - x)) with (dpsi A x * (y - x) + dpsi B x * (y - x)) by ring. lra.
Qed.

Program Definition atom_scale (c : Q) (hc : 0 <= c) (A : GsmAtom) : GsmAtom :=
  mkAtom (fun x => c * psi A x) (fun x => c * dpsi A x) _ (pot_scale c hc (pot A)).
Next Obligation.
  pose proof (psi_support A x y) as h.
  setoid_replace (c * psi A x + c * dpsi A x * (y - x)) with (c * (psi A x + dpsi A x * (y - x))) by ring.
  nra.
Qed.

(** A passive step of an atom: internal variable s -> s' at rate r with Delta psi + D <= 0. *)
Definition PassiveStep (s s' r : Q) (A : GsmAtom) : Prop :=
  (psi A s' - psi A s) + power (pot A) r <= 0.

Theorem passive_zero (s s' r : Q) : PassiveStep s s' r atom_zero.
Proof. unfold PassiveStep, power; simpl. lra. Qed.

Theorem passive_add (s s' r : Q) (A B : GsmAtom) :
  PassiveStep s s' r A -> PassiveStep s s' r B -> PassiveStep s s' r (atom_add A B).
Proof.
  unfold PassiveStep. intros hA hB. simpl. rewrite power_add. lra.
Qed.

Theorem passive_scale (s s' r c : Q) (hc : 0 <= c) (A : GsmAtom) :
  PassiveStep s s' r A -> PassiveStep s s' r (atom_scale c hc A).
Proof.
  unfold PassiveStep. intros hA. simpl. rewrite power_scale.
  setoid_replace (c * psi A s' - c * psi A s + c * power (pot A) r)
    with (c * (psi A s' - psi A s + power (pot A) r)) by ring.
  nra.
Qed.

(** The composite of a list of atoms (each already scaled by its non-negative coefficient). *)
Definition atom_sum (As : list GsmAtom) : GsmAtom := fold_right atom_add atom_zero As.

(** **Composition law (W-44)**: a composite of atoms that each pass the step passes it. *)
Theorem passive_sum (s s' r : Q) (As : list GsmAtom) :
  Forall (PassiveStep s s' r) As -> PassiveStep s s' r (atom_sum As).
Proof.
  induction 1 as [| A As hA _ ih]; simpl.
  - apply passive_zero.
  - apply passive_add; assumption.
Qed.

(** The composite's dissipation is the sum of the atoms' dissipations. *)
Theorem power_sum (As : list GsmAtom) (r : Q) :
  power (pot (atom_sum As)) r == fold_right (fun A acc => power (pot A) r + acc) 0 As.
Proof.
  induction As as [| A As ih]; simpl.
  - apply power_zero.
  - rewrite power_add. rewrite ih. reflexivity.
Qed.

(** A passive atom step whose free energies are the states' free energies is a transition case of SecondLaw. *)
Theorem passiveStep_secondLaw (A : GsmAtom) (s s' r rho rho' : Q) :
  rho' - rho <= delta_mass -> rho - rho' <= delta_mass -> PassiveStep s s' r A ->
  SecondLaw transition (thermodynamic (mkState rho (psi A s) 0 0) (mkState rho' (psi A s') 0 0)).
Proof.
  intros h1 h2 hs. simpl. unfold core_admissible. simpl.
  unfold PassiveStep in hs. pose proof (power_nonneg (pot A) r).
  split; [exact h1 | split; [exact h2 | lra]].
Qed.

(** The composite step of passing atoms satisfies the second law. *)
Theorem combination_secondLaw (As : list GsmAtom) (s s' r rho rho' : Q) :
  rho' - rho <= delta_mass -> rho - rho' <= delta_mass -> Forall (PassiveStep s s' r) As ->
  SecondLaw transition
    (thermodynamic (mkState rho (psi (atom_sum As) s) 0 0) (mkState rho' (psi (atom_sum As) s') 0 0)).
Proof. intros h1 h2 h. apply passiveStep_secondLaw with (r := r); [exact h1 | exact h2 | apply passive_sum, h]. Qed.

(* ------------------------------------------------------------------------ *)
(*  Glue                                                                    *)
(* ------------------------------------------------------------------------ *)

(** Glue fraction |D_glue| / D_total with D_total = D_atoms + D_glue (Q division by zero is zero). *)
Definition glue_fraction (dAtoms dGlue : Q) : Q := Qabs dGlue / (dAtoms + dGlue).

(** A convex glue term is an atom with zero free energy. *)
Program Definition glue_atom (G : GsmPotential) : GsmAtom := mkAtom (fun _ => 0) (fun _ => 0) _ G.
Next Obligation. lra. Qed.

(** Convex glue keeps admissibility: D_glue >= 0 and the composite with the glue atom passes the step. *)
Theorem convexGlue_secondLaw (A : GsmAtom) (G : GsmPotential) (s s' r rho rho' : Q) :
  rho' - rho <= delta_mass -> rho - rho' <= delta_mass ->
  (psi A s' - psi A s) + (power (pot A) r + power G r) <= 0 ->
  0 <= power G r /\
  SecondLaw transition
    (thermodynamic (mkState rho (psi (atom_add A (glue_atom G)) s) 0 0)
                   (mkState rho' (psi (atom_add A (glue_atom G)) s') 0 0)).
Proof.
  intros h1 h2 hb. split; [apply power_nonneg |].
  apply passiveStep_secondLaw with (r := r); [exact h1 | exact h2 |].
  unfold PassiveStep. simpl. rewrite power_add. simpl. lra.
Qed.

(** An arbitrary glue term with a witness 0 <= D_total is admissible. *)
Theorem glued_secondLaw_of_witness (dAtoms dGlue rho rho' psi0 psi1 : Q) :
  rho' - rho <= delta_mass -> rho - rho' <= delta_mass -> 0 <= dAtoms + dGlue ->
  (psi1 - psi0) + (dAtoms + dGlue) <= 0 ->
  SecondLaw transition (thermodynamic (mkState rho psi0 0 0) (mkState rho' psi1 0 0)).
Proof. intros h1 h2 hw hb. simpl. unfold core_admissible. simpl. split; [exact h1 | split; [exact h2 | lra]]. Qed.

(** Without a witness, a negative total under the passive equality balance is refused. *)
Theorem glued_refused_of_negative_total (dAtoms dGlue rho rho' psi0 psi1 : Q) :
  dAtoms + dGlue < 0 -> (psi1 - psi0) + (dAtoms + dGlue) == 0 ->
  ~ SecondLaw transition (thermodynamic (mkState rho psi0 0 0) (mkState rho' psi1 0 0)).
Proof. intros hn hb h. simpl in h. unfold core_admissible in h. simpl in h. destruct h as [_ [_ hd]]. lra. Qed.

(** An arbitrary glue term is not closed under the law. *)
Theorem arbitrary_glue_not_closed :
  exists dAtoms dGlue psi0 psi1 : Q,
    0 <= dAtoms /\ (psi1 - psi0) + (dAtoms + dGlue) == 0 /\
    ~ SecondLaw transition (thermodynamic (mkState 0 psi0 0 0) (mkState 0 psi1 0 0)).
Proof.
  exists 0, (-1), 0, 1. split; [lra | split; [reflexivity |]].
  apply (glued_refused_of_negative_total 0 (-1)); [reflexivity | reflexivity].
Qed.

(** A convex glue fraction lies in [0, 1]. *)
Theorem glueFraction_mem_unit (dAtoms dGlue : Q) :
  0 <= dAtoms -> 0 <= dGlue -> 0 <= glue_fraction dAtoms dGlue /\ glue_fraction dAtoms dGlue <= 1.
Proof.
  intros hA hG. unfold glue_fraction. rewrite Qabs_pos by exact hG.
  destruct (Qeq_dec (dAtoms + dGlue) 0) as [h0 | hne].
  - assert (hg0 : dGlue == 0) by lra. rewrite h0, hg0. unfold Qdiv. simpl. split; discriminate.
  - assert (hT : 0 < dAtoms + dGlue) by (destruct (Qle_lt_or_eq 0 (dAtoms + dGlue)) as [h|h]; lra).
    split.
    + apply Qle_shift_div_l; [exact hT | lra].
    + apply Qle_shift_div_r; [exact hT | lra].
Qed.

(** The glue fraction vanishes exactly when the glue dissipation does (for a non-zero total). *)
Theorem glueFraction_eq_zero_iff (dAtoms dGlue : Q) :
  ~ dAtoms + dGlue == 0 -> (glue_fraction dAtoms dGlue == 0 <-> dGlue == 0).
Proof.
  intros hT. unfold glue_fraction. split.
  - intros h.
    assert (hq : Qabs dGlue == 0).
    { setoid_replace (Qabs dGlue) with (Qabs dGlue / (dAtoms + dGlue) * (dAtoms + dGlue)) by (field; exact hT).
      rewrite h. ring. }
    destruct (Qlt_le_dec dGlue 0) as [hn | hp].
    + rewrite Qabs_neg in hq by lra. lra.
    + rewrite Qabs_pos in hq by exact hp. exact hq.
  - intros h. rewrite h. reflexivity.
Qed.

(** A glue fraction above one signals a negative glue term (with non-negative atom dissipation). *)
Theorem glue_neg_of_fraction_gt_one (dAtoms dGlue : Q) :
  0 <= dAtoms -> 1 < glue_fraction dAtoms dGlue -> dGlue < 0.
Proof.
  intros hA h. destruct (Qlt_le_dec dGlue 0) as [hn | hp]; [exact hn |].
  exfalso. destruct (glueFraction_mem_unit dAtoms dGlue hA hp) as [_ hle]. lra.
Qed.
