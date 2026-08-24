-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/AppendOnly.lean

  Meso acting Urge — §17.6 append-only admitted history invariant.
  Admitted history is append-only; silent rewrite refused as a `Prop`.
  Self-healing adds an Excitement arrow; it does not mutate prior admitted objects.

  Anchored in `LandauerLaw.physicalSecondLaw` via `Urge.AdmitKleisli` physical bridge.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
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

/-- Silent rewrite refused when append-only discipline holds. -/
theorem silentRewriteRefused (t : HistoryTransition) (h : appendOnlyCommitMove t) :
    ¬ silentRewrite t := by
  unfold appendOnlyCommitMove silentRewrite at *
  omega

/-- Append-only and silent rewrite are mutually exclusive. -/
theorem appendOnly_not_silentRewrite (t : HistoryTransition) :
    appendOnlyCommitMove t ↔ ¬ silentRewrite t := by
  constructor
  · exact silentRewriteRefused t
  · unfold appendOnlyCommitMove silentRewrite
    omega

/-- Admitted history transition with append-only discipline (§17.6). -/
def appendOnlyAdmittedTransition (t : HistoryTransition) : Prop :=
  admissibleHistoryTransition t ∧ appendOnlyInvariant t

/-- Every transition in a chain respects append-only commit moves. -/
def appendOnlyHistoryChain (ts : List HistoryTransition) : Prop :=
  ∀ t ∈ ts, appendOnlyCommitMove t

/-- Chain append-only ⇒ no transition in the chain is a silent rewrite. -/
theorem appendOnlyHistoryChain_refusesSilentRewrite (ts : List HistoryTransition)
    (h : appendOnlyHistoryChain ts) (t : HistoryTransition) (ht : t ∈ ts) :
    ¬ silentRewrite t :=
  silentRewriteRefused t (h t ht)

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

theorem selfHealAppendOnly_eq_appendOnlyInvariant (t : HistoryTransition) :
    selfHealAppendOnly t = appendOnlyInvariant t :=
  rfl

/-- Self-heal transition refuses snapshot-level silent rewrite. -/
theorem selfHeal_not_silentRewrite (t : HistoryTransition) (h : selfHealAppendOnly t) :
    ¬ silentRewriteSnapshots t.prior t.post :=
  recoveryAppendOnly_refusesSilentRewrite t.prior t.post h

/-- Physically bridged transition is append-only admitted. -/
theorem appendOnlyAdmitted_from_physical (b : PhysicalHistoryBridge)
    (hAppend : appendOnlyCommitMove b.transition)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    appendOnlyAdmittedTransition b.transition := by
  refine ⟨admissibleHistoryTransition_from_physical b hSL, ?_⟩
  exact hAppend

/-- Physical bridge forbids silent rewrite on the bridged transition. -/
theorem silentRewriteRefused_from_physical (b : PhysicalHistoryBridge)
    (hAppend : appendOnlyCommitMove b.transition)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    ¬ silentRewrite b.transition :=
  silentRewriteRefused b.transition hAppend

/-- Physics GREEN unauthorized on this scaffold. -/
def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

/-- Production wiring stays open (meso lift only). -/
def appendOnlyProductionWired : Bool := false

theorem appendOnlyProductionWiredFalse : appendOnlyProductionWired = false := rfl

/-- Catalog witness: meso Urge AppendOnly module present. -/
theorem appendOnlyModuleWitness : True := trivial

/-- §17.6 named obligation: admitted history append-only; silent rewrite refused. -/
theorem appendOnly_silentRewrite_refused (t : HistoryTransition) :
    appendOnlyInvariant t → ¬ silentRewrite t :=
  silentRewriteRefused t

end UMST.Urge.AppendOnly
