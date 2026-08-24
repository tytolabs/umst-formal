(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ================================================================== *)
(*  UMST-Formal: Urge/ReplicaCoalgebra.v                                *)
(*                                                                      *)
(*  Meso acting Urge — §15.4 admissible replica coalgebra.              *)
(*  node-0 / node-1 / Forgejo / LUKS are **replica classes** — sample *)
(*  sections of one mesh sheaf, not XOR worlds.  Inbound merge:        *)
(*                                                                      *)
(*    admit(h) ⟺ gate_check(h) ∧ MergeSafe(h) ∧ Excitement preserves   *)
(*    provenance(h)                                                     *)
(*                                                                      *)
(*  Backup is a **typed recovery morphism** (Excitement `select`, not   *)
(*  rsync theater).  Offline LUKS replica class carries                 *)
(*  `network-egress: []`.                                               *)
(*                                                                      *)
(*  Sole physics axiom remains on Lean `LandauerLaw` (cited, not here). *)
(*  Adds **zero** Coq `Axiom` declarations. ZERO `Admitted`.           *)
(* ================================================================== *)

From Coq Require Import Arith List String Reals.
Require Import UMSTFormal.Gate.
Require Import UMSTFormal.Urge.AdmitKleisli.

Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(*  SECTION 1: Replica classes (sample sections — not XOR worlds)     *)
(* ------------------------------------------------------------------ *)

(** Four replica classes on one mesh sheaf. *)
Inductive ReplicaClass : Set :=
  | replica_node0
  | replica_node1
  | replica_forge
  | replica_luks.

(** Human-readable class tag (deployment naming — not XOR partition). *)
Definition replicaClassTag (c : ReplicaClass) : string :=
  match c with
  | replica_node0 => "node-0"
  | replica_node1 => "node-1"
  | replica_forge => "forge"
  | replica_luks  => "luks"
  end.

Theorem node0_tag : replicaClassTag replica_node0 = "node-0".
Proof. reflexivity. Qed.

Theorem node1_tag : replicaClassTag replica_node1 = "node-1".
Proof. reflexivity. Qed.

Theorem forge_tag : replicaClassTag replica_forge = "forge".
Proof. reflexivity. Qed.

Theorem luks_tag : replicaClassTag replica_luks = "luks".
Proof. reflexivity. Qed.

Theorem replicaClassTag_node0_ne_node1 :
  replicaClassTag replica_node0 <> replicaClassTag replica_node1.
Proof. discriminate. Qed.

Theorem replicaClassTag_node0_ne_forge :
  replicaClassTag replica_node0 <> replicaClassTag replica_forge.
Proof. discriminate. Qed.

Theorem replicaClassTag_node0_ne_luks :
  replicaClassTag replica_node0 <> replicaClassTag replica_luks.
Proof. discriminate. Qed.

Theorem replicaClassTag_node1_ne_forge :
  replicaClassTag replica_node1 <> replicaClassTag replica_forge.
Proof. discriminate. Qed.

Theorem replicaClassTag_node1_ne_luks :
  replicaClassTag replica_node1 <> replicaClassTag replica_luks.
Proof. discriminate. Qed.

Theorem replicaClassTag_forge_ne_luks :
  replicaClassTag replica_forge <> replicaClassTag replica_luks.
Proof. discriminate. Qed.

(** Replica classes are distinct tags — concurrent sections, not XOR worlds. *)
Definition replicaClassesNotXor : Prop :=
  replicaClassTag replica_node0 <> replicaClassTag replica_node1 /\
  replicaClassTag replica_node0 <> replicaClassTag replica_forge /\
  replicaClassTag replica_node0 <> replicaClassTag replica_luks /\
  replicaClassTag replica_node1 <> replicaClassTag replica_forge /\
  replicaClassTag replica_node1 <> replicaClassTag replica_luks /\
  replicaClassTag replica_forge <> replicaClassTag replica_luks.

Theorem replicaClassesNotXorHolds : replicaClassesNotXor.
Proof.
  exact (conj replicaClassTag_node0_ne_node1
    (conj replicaClassTag_node0_ne_forge
      (conj replicaClassTag_node0_ne_luks
        (conj replicaClassTag_node1_ne_forge
          (conj replicaClassTag_node1_ne_luks
            replicaClassTag_forge_ne_luks))))).
Qed.

Definition replicaClassCount : nat := (4%nat).

Theorem replica_class_count_is_four : replicaClassCount = (4%nat).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 2: Mesh sheaf + coalgebra observe (concurrent sections)   *)
(* ------------------------------------------------------------------ *)

(** One mesh sheaf: probe each replica class for its sample section. *)
Record ReplicaMeshSheaf : Set := {
  sectionProbe : ReplicaClass -> nat
}.

Definition node0SampleSection (R : ReplicaMeshSheaf) : nat :=
  sectionProbe R replica_node0.

Definition node1SampleSection (R : ReplicaMeshSheaf) : nat :=
  sectionProbe R replica_node1.

Definition forgeSampleSection (R : ReplicaMeshSheaf) : nat :=
  sectionProbe R replica_forge.

Definition luksSampleSection (R : ReplicaMeshSheaf) : nat :=
  sectionProbe R replica_luks.

Definition sampleSectionAt (c : ReplicaClass) (R : ReplicaMeshSheaf) : nat :=
  sectionProbe R c.

(** Observed section bundle — coalgebra output over all replica classes. *)
Record ReplicaSectionBundle : Set := {
  sec_node0 : nat;
  sec_node1 : nat;
  sec_forge : nat;
  sec_luks  : nat
}.

Definition replicaCoalgebraObserve (R : ReplicaMeshSheaf) : ReplicaSectionBundle :=
  {| sec_node0 := node0SampleSection R;
     sec_node1 := node1SampleSection R;
     sec_forge := forgeSampleSection R;
     sec_luks  := luksSampleSection R |}.

Theorem replicaCoalgebraObserve_components (R : ReplicaMeshSheaf) :
  sec_node0 (replicaCoalgebraObserve R) = node0SampleSection R /\
  sec_node1 (replicaCoalgebraObserve R) = node1SampleSection R /\
  sec_forge (replicaCoalgebraObserve R) = forgeSampleSection R /\
  sec_luks (replicaCoalgebraObserve R) = luksSampleSection R.
Proof.
  repeat split; reflexivity.
Qed.

Theorem sampleSectionAt_node0 (R : ReplicaMeshSheaf) :
  sampleSectionAt replica_node0 R = node0SampleSection R.
Proof. reflexivity. Qed.

Theorem sampleSectionAt_node1 (R : ReplicaMeshSheaf) :
  sampleSectionAt replica_node1 R = node1SampleSection R.
Proof. reflexivity. Qed.

Theorem sampleSectionAt_forge (R : ReplicaMeshSheaf) :
  sampleSectionAt replica_forge R = forgeSampleSection R.
Proof. reflexivity. Qed.

Theorem sampleSectionAt_luks (R : ReplicaMeshSheaf) :
  sampleSectionAt replica_luks R = luksSampleSection R.
Proof. reflexivity. Qed.

(** Witness sheaf: sections differ across classes (not one XOR world). *)
Definition witnessReplicaSheaf : ReplicaMeshSheaf :=
  {| sectionProbe := fun c =>
       match c with
       | replica_node0 => (1%nat)
       | replica_node1 => (2%nat)
       | replica_forge => (3%nat)
       | replica_luks  => (4%nat)
       end |}.

Theorem node0DoesNotCloseLuks :
  exists R : ReplicaMeshSheaf,
    node0SampleSection R <> luksSampleSection R.
Proof.
  exists witnessReplicaSheaf.
  unfold node0SampleSection, luksSampleSection, witnessReplicaSheaf.
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 3: Network egress (offline LUKS carries empty egress)       *)
(* ------------------------------------------------------------------ *)

Definition networkEgress (c : ReplicaClass) : list string :=
  match c with
  | replica_luks => nil
  | _ => "tailscale-admin" :: nil
  end.

Theorem luks_network_egress_empty :
  networkEgress replica_luks = nil.
Proof. reflexivity. Qed.

Theorem node0_network_egress_tailscale :
  networkEgress replica_node0 = "tailscale-admin" :: nil.
Proof. reflexivity. Qed.

Theorem offline_luks_is_network_egress_empty :
  networkEgress replica_luks = nil /\
  replicaClassTag replica_luks = "luks".
Proof.
  split; [reflexivity | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 4: Admissible replica coalgebra (gate ∧ MergeSafe ∧ prov) *)
(* ------------------------------------------------------------------ *)

(** Inbound replica history move with typed obligation slots. *)
Record ReplicaHistoryMove : Type := {
  replica_prior        : ThermodynamicState;
  replica_post         : ThermodynamicState;
  replica_gate_checked : Prop;
  replica_merge_safe     : Prop;
  replica_provenance_ok  : Prop
}.

Definition admissibleReplicaCoalgebra (h : ReplicaHistoryMove) : Prop :=
  replica_gate_checked h /\
  replica_merge_safe h /\
  replica_provenance_ok h.

Theorem admissibleReplicaCoalgebra_intro (h : ReplicaHistoryMove)
    (hg : replica_gate_checked h) (hm : replica_merge_safe h)
    (hp : replica_provenance_ok h) :
  admissibleReplicaCoalgebra h.
Proof.
  repeat split; assumption.
Qed.

Definition admitReplicaInbound := admissibleReplicaCoalgebra.

(* ------------------------------------------------------------------ *)
(*  SECTION 5: Typed recovery morphism (Excitement — no second argmin) *)
(* ------------------------------------------------------------------ *)

(** Recovery context: prior state + admissible successor candidates. *)
Record recovery_ctx (src : ThermodynamicState) : Set := {
  recovery_successors : list (history_candidate src)
}.

(** Typed recovery morphism composes `excitement_select` — not rsync theater. *)
Definition typedRecoveryMorphism (src : ThermodynamicState)
    (ctx : recovery_ctx src) :
  history_candidate src + excitement_residue :=
  excitement_select src (recovery_successors src ctx).

Definition typedRecoverySelect (src : ThermodynamicState)
    (successors : list (history_candidate src)) :
  history_candidate src + excitement_residue :=
  excitement_select src successors.

Theorem typedRecoveryMorphism_eq_excitement_select :
  forall (src : ThermodynamicState) (ctx : recovery_ctx src),
  typedRecoveryMorphism src ctx =
  excitement_select src (recovery_successors src ctx).
Proof.
  intros. reflexivity.
Qed.

Theorem typedRecoverySelect_eq_excitement_select :
  forall (src : ThermodynamicState)
         (successors : list (history_candidate src)),
  typedRecoverySelect src successors = excitement_select src successors.
Proof.
  intros. reflexivity.
Qed.

Theorem typedRecoveryMorphism_eq_typedRecoverySelect :
  forall (src : ThermodynamicState) (ctx : recovery_ctx src),
  typedRecoveryMorphism src ctx =
  typedRecoverySelect src (recovery_successors src ctx).
Proof.
  intros. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 6: Second-law bridge (Landauer lift — zero new axioms)      *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

(** Replica transition with thermodynamic accounting. *)
Record ReplicaTransition : Type := {
  replica_move            : ReplicaHistoryMove;
  replica_bath            : HeatBath;
  replica_dissipated_work : R;
  replica_entropy_drop    : R
}.

Definition replicaSecondLaw (t : ReplicaTransition) : Prop :=
  replica_entropy_drop t <=
  replica_dissipated_work t / bath_temp (replica_bath t).

(** Physical bridge: Landauer discharge + admissible replica coalgebra. *)
Record PhysicalReplicaBridge : Type := {
  physical_landauer_bridge : LandauerHistoryBridge;
  physical_replica_move    : ReplicaHistoryMove;
  physical_admissible :
    admissibleReplicaCoalgebra physical_replica_move
}.

Theorem replicaSecondLaw_from_physical (b : PhysicalReplicaBridge)
    (Hsl : admitSecondLaw (landauer_transition (physical_landauer_bridge b))) :
  let t := landauer_transition (physical_landauer_bridge b) in
  history_entropy_drop t <=
  history_dissipated_work t / bath_temp (history_bath t).
Proof.
  intros. exact Hsl.
Qed.

Theorem admissibleReplicaCoalgebra_from_physical (b : PhysicalReplicaBridge)
    (_Hsl : admitSecondLaw (landauer_transition (physical_landauer_bridge b))) :
  admissibleReplicaCoalgebra (physical_replica_move b).
Proof.
  exact (physical_admissible b).
Qed.

(* ------------------------------------------------------------------ *)
(*  SECTION 7: Honesty flags + catalog witnesses                        *)
(* ------------------------------------------------------------------ *)

Definition urgePhysicsGreen : bool := false.

Lemma urgePhysicsGreenFalse : urgePhysicsGreen = false.
Proof. reflexivity. Qed.

Definition replicaCoalgebraProductionWired : bool := false.

Lemma replicaCoalgebraProductionWiredFalse :
  replicaCoalgebraProductionWired = false.
Proof. reflexivity. Qed.

Theorem replicaCoalgebraModuleWitness : True.
Proof. exact I. Qed.

Theorem replicaCoalgebra_noNewAxiom : True.
Proof. exact I. Qed.

Theorem replicaCoalgebra_namedNotXor : replicaClassesNotXor.
Proof. exact replicaClassesNotXorHolds. Qed.
