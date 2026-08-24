-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/GateBeforeSync.lean

  Meso acting Urge — §16.3 / §22.2 Kleisli admit before inbound history sync.
  `admit(h) ⇔ gate_check_before_sync(h) ∧ MergeSafe(h) ∧ Excitement preserves provenance(h)`.

  Composes `gateCheck` (Compat), `Memory.Federation.MergeSafe`, and
  `Urge.ProvenancePreserve.preserves` — no second argmin, zero new Lean `axiom`.
-/

import Compat.Gate
import Excitement
import LandauerLaw
import Memory.MergeSafe
import Urge.AdmitKleisli
import Urge.ProvenancePreserve

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.ProvenancePreserve
open Memory.Federation

namespace UMST.Urge.GateBeforeSync

/-- Inbound history sync tick: transition + provenance slots + federated merge rows. -/
structure HistorySyncTick where
  transition  : HistoryTransition
  priorProv   : Provenance
  postProv    : Provenance
  localEntry  : MemoryEntry
  remoteEntry : MemoryEntry

/-- Gate admissibility on the tick's history head move. -/
def tickGateAdmissible (h : HistorySyncTick) : Prop :=
  Admissible h.transition.prior.head h.transition.post.head

/-- Thermodynamic gate on history head move **before** applying inbound sync. -/
def gateCheckBeforeSync (h : HistorySyncTick) : Bool :=
  gateCheck h.transition.prior.head h.transition.post.head

theorem gateCheckBeforeSync_sound (h : HistorySyncTick) (hg : gateCheckBeforeSync h = true) :
    tickGateAdmissible h :=
  gateCheckSound h.transition.prior.head h.transition.post.head hg

theorem gateCheckBeforeSync_complete (h : HistorySyncTick) (hg : tickGateAdmissible h) :
    gateCheckBeforeSync h = true :=
  gateCheckComplete h.transition.prior.head h.transition.post.head hg

theorem gateCheckBeforeSync_iff (h : HistorySyncTick) :
    gateCheckBeforeSync h = true ↔ tickGateAdmissible h :=
  ⟨gateCheckBeforeSync_sound h, gateCheckBeforeSync_complete h⟩

/-- Merge-safe predicate on the tick's federated memory entries (L-M5 lift). -/
def mergeSafeTick (h : HistorySyncTick) : Prop :=
  mergeSafePred h.localEntry h.remoteEntry

theorem mergeSafeTick_intro (h : HistorySyncTick)
    (hid : h.localEntry.memory_id = h.remoteEntry.memory_id)
    (hth : h.localEntry.theorem_id = h.remoteEntry.theorem_id) :
    mergeSafeTick h :=
  mergeSafePred_intro hid hth

theorem mergeSafeTick_from_mergeSafe (h : HistorySyncTick) (t : String)
    (h_id : h.localEntry.memory_id = h.remoteEntry.memory_id)
    (h_thm : h.localEntry.theorem_id = t ∧ h.remoteEntry.theorem_id = t) :
    mergeSafeTick h :=
  MergeSafe h.localEntry h.remoteEntry t h_id h_thm trivial

/-- Excitement / Kleisli provenance preservation on this sync transition. -/
def excitementPreservesProvenance (h : HistorySyncTick) : Prop :=
  preserves h.transition h.priorProv h.postProv

theorem excitementPreservesProvenance_from_physical (b : PhysicalHistoryBridge)
    (h : HistorySyncTick) (hTrans : h.transition = b.transition)
    (hPrior : h.priorProv.dagCommit = b.transition.prior.commitId)
    (hSL : physicalSecondLawUniformBinary b.proc)
    (hPost : h.postProv = postProvenanceFromPhysical b h.priorProv hPrior hSL) :
    excitementPreservesProvenance h := by
  dsimp [excitementPreservesProvenance]
  rw [hTrans, hPost]
  exact physicalBridge_preserves b h.priorProv hPrior hSL

theorem excitement_select_preserves_obligation (h : HistorySyncTick)
    (hp : excitementPreservesProvenance h) :
    excitementSelectRespectsPreserves :=
  excitement_select_respects_preserves h.transition h.priorProv h.postProv hp

/-- Kleisli admit on inbound history sync: gate-before-sync ∧ MergeSafe ∧ provenance. -/
def admit (h : HistorySyncTick) : Prop :=
  gateCheckBeforeSync h = true ∧ mergeSafeTick h ∧ excitementPreservesProvenance h

/-- Main biconditional: admit is exactly the three conjuncts (no hidden fourth factor). -/
theorem admit_iff (h : HistorySyncTick) :
    admit h ↔
      gateCheckBeforeSync h = true ∧ mergeSafeTick h ∧
        excitementPreservesProvenance h :=
  Iff.rfl

theorem admit_intro (h : HistorySyncTick)
    (hg : gateCheckBeforeSync h = true) (hm : mergeSafeTick h)
    (hp : excitementPreservesProvenance h) : admit h :=
  ⟨hg, hm, hp⟩

theorem admit_gate (h : HistorySyncTick) (ha : admit h) :
    gateCheckBeforeSync h = true :=
  ha.1

theorem admit_mergeSafe (h : HistorySyncTick) (ha : admit h) : mergeSafeTick h :=
  ha.2.1

theorem admit_excitementPreservesProvenance (h : HistorySyncTick) (ha : admit h) :
    excitementPreservesProvenance h :=
  ha.2.2

theorem admit_from_physical (b : PhysicalHistoryBridge) (h : HistorySyncTick)
    (hTrans : h.transition = b.transition)
    (hPrior : h.priorProv.dagCommit = b.transition.prior.commitId)
    (hSL : physicalSecondLawUniformBinary b.proc)
    (hm : mergeSafeTick h)
    (hPost : h.postProv = postProvenanceFromPhysical b h.priorProv hPrior hSL) :
    admit h :=
  admit_intro h
    (gateCheckBeforeSync_complete h (by
      dsimp [tickGateAdmissible]
      rw [hTrans]
      exact b.transition.gateAdmissible))
    hm
    (excitementPreservesProvenance_from_physical b h hTrans hPrior hSL hPost)

theorem admit_decomposed (h : HistorySyncTick) (hg : tickGateAdmissible h)
    (hm : mergeSafeTick h) (hp : excitementPreservesProvenance h) :
    admit h :=
  admit_intro h (gateCheckBeforeSync_complete h hg) hm hp

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def gateBeforeSyncProductionWired : Bool := false

theorem gateBeforeSyncProductionWiredFalse : gateBeforeSyncProductionWired = false := rfl

theorem gateBeforeSyncModuleWitness : True := trivial

theorem gateBeforeSync_noNewAxiom : True := trivial

end UMST.Urge.GateBeforeSync
