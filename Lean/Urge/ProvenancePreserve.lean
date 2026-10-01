-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ProvenancePreserve.lean

  Meso acting Urge — §17.4 provenance as a type (not prose).
  `Provenance` = UCRS stamp chain + admitted Kleisli DAG head + Landauer witnesses.
  `preserves : Transition → Provenance → Provenance → Prop` — Excitement `select`
  must respect this by construction (obligation named here; wiring stays open).

  The witness obligation is the admissibility of the move under the one second law.
  Adds **zero** Lean `axiom` declarations.
-/

import Urge.AdmitKleisli
import LandauerLaw
import Excitement

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.AdmitKleisli

namespace UMST.Urge.ProvenancePreserve

/-- Meso transition carrier (history move with second-law accounting). -/
abbrev Transition := HistoryTransition

/-- Typed provenance: stamp chain + admitted DAG commit + second-law witness slot. -/
structure Provenance where
  ucrsChain     : List Nat
  dagCommit     : Nat
  landauerWitness : Prop

/-- Empty provenance at genesis commit (no prior stamps). -/
def genesisProvenance (commitId : Nat) : Provenance where
  ucrsChain := []
  dagCommit := commitId
  landauerWitness := True

/-- §17.4 preservation: post extends stamp chain, aligns DAG endpoints, retains witness. -/
def preserves (t : Transition) (prior post : Provenance) : Prop :=
  prior.dagCommit = t.prior.commitId ∧
  post.dagCommit = t.post.commitId ∧
  post.ucrsChain = prior.ucrsChain ++ [prior.dagCommit] ∧
  (∀ _ : prior.landauerWitness, post.landauerWitness) ∧
  (post.landauerWitness → admissibleHistoryTransition t)

theorem preserves_chain_append (t : Transition) (prior post : Provenance)
    (h : preserves t prior post) :
    post.ucrsChain = prior.ucrsChain ++ [prior.dagCommit] :=
  h.2.2.1

theorem preserves_witness_retained (t : Transition) (prior post : Provenance)
    (h : preserves t prior post) (hw : prior.landauerWitness) :
    post.landauerWitness :=
  h.2.2.2.1 hw

/-- The provenance after a move: the stamp chain extended by the prior commit, the DAG at the move's target. -/
def postProvenance (t : Transition) (prior : Provenance) : Provenance where
  ucrsChain := prior.ucrsChain ++ [prior.dagCommit]
  dagCommit := t.post.commitId
  landauerWitness := True

/-- An admissible move from the prior's commit preserves provenance; the second law discharges the witness. -/
theorem postProvenance_preserves (t : Transition) (prior : Provenance)
    (hPrior : prior.dagCommit = t.prior.commitId) (hSL : admissibleHistoryTransition t) :
    preserves t prior (postProvenance t prior) :=
  ⟨hPrior, rfl, rfl, fun _ => trivial, fun _ => hSL⟩

end UMST.Urge.ProvenancePreserve
