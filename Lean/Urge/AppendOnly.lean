-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/AppendOnly.lean

  Meso acting Urge — §17.6 append-only admitted history invariant.
  Admitted history is append-only; silent rewrite refused as a `Prop`.
  Self-healing adds an Excitement arrow; it does not mutate prior admitted objects.

  Anchored in `LandauerLaw.physicalSecondLaw` via `Urge.AdmitKleisli` physical bridge.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Urge.AdmitKleisli
import Excitement
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli

namespace UMST.Urge.AppendOnly

/-- Monotone commit-id move: prior strictly before post (append-only head). -/
def appendOnlyCommitMove (t : HistoryTransition) : Prop :=
  t.prior.commitId < t.post.commitId

/-- §17.6 append-only invariant on a single admitted transition. -/
def appendOnlyInvariant (t : HistoryTransition) : Prop :=
  appendOnlyCommitMove t

/-- Silent rewrite: post does not strictly extend prior commit id. -/
def silentRewrite (t : HistoryTransition) : Prop :=
  t.post.commitId ≤ t.prior.commitId

/-- Admitted history transition with append-only discipline (§17.6). -/
def appendOnlyAdmittedTransition (t : HistoryTransition) : Prop :=
  admissibleHistoryTransition t ∧ appendOnlyInvariant t

/-- Every transition in a chain respects append-only commit moves. -/
def appendOnlyHistoryChain (ts : List HistoryTransition) : Prop :=
  ∀ t ∈ ts, appendOnlyCommitMove t

/-- Recovery snapshot must strictly extend prior commit id (new arrow, not rewrite). -/
def recoveryAppendOnly (prior post : HistorySnapshot) : Prop :=
  prior.commitId < post.commitId

/-- Silent rewrite on bare snapshots (no thermodynamic accounting). -/
def silentRewriteSnapshots (prior post : HistorySnapshot) : Prop :=
  post.commitId ≤ prior.commitId

/-- Recovery append-only refuses silent rewrite on snapshots. -/
theorem recoveryAppendOnly_refusesSilentRewrite (prior post : HistorySnapshot)
    (h : recoveryAppendOnly prior post) :
    ¬ silentRewriteSnapshots prior post := by
  unfold recoveryAppendOnly silentRewriteSnapshots at *
  omega

/-- Self-heal discipline: recovery transition obeys append-only when modeled as HistoryTransition. -/
def selfHealAppendOnly (t : HistoryTransition) : Prop :=
  recoveryAppendOnly t.prior t.post

end UMST.Urge.AppendOnly
