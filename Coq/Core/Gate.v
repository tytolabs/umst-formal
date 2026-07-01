(* ================================================================== *)
(*  UMSTFormal.Core.Gate — universal thermodynamic bounds.            *)
(* ================================================================== *)

From Coq Require Import QArith.
From Coq Require Import Qfield.

Open Scope Q_scope.

(** Mass conservation tolerance (kg/m³); SSOT across Agda / Coq / Lean / Rust. *)
Definition delta_mass : Q := 100 # 1.

(** Core 1-step admissibility: metric ball + free-energy descent. *)
Definition core_admissible (rho_old rho_new psi_old psi_new : Q) : Prop :=
  (rho_new - rho_old <= delta_mass) /\
  (rho_old - rho_new <= delta_mass) /\
  (psi_new <= psi_old).

Definition core_mass_cond (rho_old rho_new : Q) : Prop :=
  (rho_new - rho_old <= delta_mass) /\
  (rho_old - rho_new <= delta_mass).

Definition core_dissip_cond (psi_old psi_new : Q) : Prop :=
  psi_new <= psi_old.

Lemma core_admissible_iff_mass_dissip :
  forall rho_old rho_new psi_old psi_new : Q,
  core_admissible rho_old rho_new psi_old psi_new <->
  core_mass_cond rho_old rho_new /\ core_dissip_cond psi_old psi_new.
Proof.
  intros. unfold core_admissible, core_mass_cond, core_dissip_cond. tauto.
Qed.
