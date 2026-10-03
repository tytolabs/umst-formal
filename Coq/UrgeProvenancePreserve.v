(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* ===================================================================== *)
(*  UMST-Formal: UrgeProvenancePreserve.v                                 *)
(*                                                                        *)
(*  Twin of Lean/Urge/ProvenancePreserve.lean: provenance is a stamp      *)
(*  chain, an admitted DAG commit and a second-law witness slot. A move   *)
(*  preserves provenance when the post chain extends the prior chain by   *)
(*  the prior commit, the DAG endpoints align with the move, the witness  *)
(*  is retained and a held witness is the admissibility of the move       *)
(*  under the one second law. An admissible move from the prior commit    *)
(*  preserves provenance. Zero Axiom, Parameter or Admitted.              *)
(* ===================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
Require Import UMSTFormal.UrgeAdmitKleisli.

(** Typed provenance: stamp chain, admitted DAG commit and second-law witness slot. *)
Record Provenance : Type := mkProvenance {
  ucrsChain : list nat;
  dagCommit : nat;
  landauerWitness : Prop
}.

(** Preservation: the post extends the stamp chain, aligns the DAG endpoints, retains the witness. *)
Definition preserves (t : HistoryTransition) (prior post : Provenance) : Prop :=
  dagCommit prior = commitId (htPrior t) /\
  dagCommit post = commitId (htPost t) /\
  ucrsChain post = ucrsChain prior ++ [dagCommit prior] /\
  (landauerWitness prior -> landauerWitness post) /\
  (landauerWitness post -> admissibleHistoryTransition t).

Theorem preserves_chain_append (t : HistoryTransition) (prior post : Provenance) :
  preserves t prior post -> ucrsChain post = ucrsChain prior ++ [dagCommit prior].
Proof. intros [_ [_ [h _]]]. exact h. Qed.

Theorem preserves_witness_retained (t : HistoryTransition) (prior post : Provenance) :
  preserves t prior post -> landauerWitness prior -> landauerWitness post.
Proof. intros [_ [_ [_ [h _]]]]. exact h. Qed.

(** The provenance after a move: the stamp chain extended by the prior commit, the DAG at the move's target. *)
Definition postProvenance (t : HistoryTransition) (prior : Provenance) : Provenance :=
  mkProvenance (ucrsChain prior ++ [dagCommit prior]) (commitId (htPost t)) True.

(** An admissible move from the prior's commit preserves provenance; the second law discharges the witness. *)
Theorem postProvenance_preserves (t : HistoryTransition) (prior : Provenance) :
  dagCommit prior = commitId (htPrior t) -> admissibleHistoryTransition t ->
  preserves t prior (postProvenance t prior).
Proof.
  intros hPrior hSL. unfold preserves, postProvenance. simpl.
  split; [exact hPrior |]. split; [reflexivity |]. split; [reflexivity |]. split; [intros _; exact I | intros _; exact hSL].
Qed.
