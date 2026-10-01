-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/KleisliFetch.lean

  Meso acting Urge — §16.7 operator verb `fetch` as Kleisli arrow.
  Blueprint row: `fetch` → `gate_check_before_sync` inbound · entity check `remote class`.
  Composes `UMST.Excitement.select`; no second argmin.

  Anchored in `AdmitKleisli` / `GateBeforeSync`. Sole physical law (the `SecondLaw` predicate) remains
  `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Compat.Gate
import Excitement
import ExcitementProofs
import LandauerLaw
import Urge.AdmitKleisli
import Urge.GateBeforeSync

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement
open UMST.Urge.AdmitKleisli UMST.Urge.GateBeforeSync

namespace UMST.Urge.KleisliFetch

-- ================================================================
-- SECTION 1: Remote class + inbound gate carriers (§16.7)
-- ================================================================

/-- Operator verb surface tag — §16.7 Kleisli table row `fetch`. -/
inductive FetchOperatorVerb where
  | fetch
  deriving DecidableEq, Repr

/-- Remote entity class for fetch entity check (§16.7). -/
inductive FetchRemoteClass where
  | entityRemote
  | refusedUpstream
  | unclassified
  deriving DecidableEq, Repr

/-- Whether remote class admits fetch Kleisli arrow. -/
def fetchRemoteAdmissible (c : FetchRemoteClass) : Bool :=
  match c with
  | .entityRemote => true
  | .refusedUpstream | .unclassified => false

/-- Inbound gate posture — `gate_check_before_sync` before applying refs. -/
inductive FetchInboundGate where
  | admitted
  | refused
  | bypassAttempted
  deriving DecidableEq, Repr

/-- Whether inbound gate admits fetch morphism. -/
def fetchGateAdmits (g : FetchInboundGate) : Bool :=
  match g with
  | .admitted => true
  | .refused | .bypassAttempted => false

/-- Classify remote host surrogate into entity check class (§16.7). -/
def classifyFetchRemote (host : String) : FetchRemoteClass :=
  if host == "forge.entity" then .entityRemote
  else if host == "github.com" then .refusedUpstream
  else if host == "origin.cursor.com" then .refusedUpstream
  else .unclassified

/-- Kleisli arrow witness for operator verb `fetch`. -/
structure FetchKleisliArrow where
  fetchVerb         : FetchOperatorVerb
  fetchGate         : FetchInboundGate
  fetchRemote       : FetchRemoteClass
  fetchObjectCount  : Nat

/-- Fetch morphism outcome — admitted only when gate ∧ remote class pass. -/
inductive FetchVerdict where
  | admitted
  | gateRefused
  | remoteClassRefused
  | productionWiredRefused
  | gateBypassRefused
  deriving DecidableEq, Repr

/-- Fail-closed fetch errors — positive refuse, not silent no-op. -/
inductive FetchError where
  | gateRefused
  | remoteClassRefused (c : FetchRemoteClass)
  | productionWiredRefused
  | gateBypassRefused
  deriving Repr

-- ================================================================
-- SECTION 2: §16.7 Kleisli evaluation + positive refuse
-- ================================================================

/-- Evaluate fetch as Kleisli arrow — §16.7 gate + remote class. -/
def evaluateFetchKleisli (arrow : FetchKleisliArrow) : FetchVerdict ⊕ FetchError :=
  if fetchGateAdmits arrow.fetchGate then
    if fetchRemoteAdmissible arrow.fetchRemote then
      Sum.inl FetchVerdict.admitted
    else
      Sum.inr (.remoteClassRefused arrow.fetchRemote)
  else
    match arrow.fetchGate with
    | .bypassAttempted => Sum.inr .gateBypassRefused
    | _ => Sum.inr .gateRefused

/-- Positive refuse: gate bypass on inbound fetch. -/
def refuseGateBypassFetch : FetchError := .gateBypassRefused

/-- Construct fetch Kleisli arrow from gate + remote host surrogate. -/
def fetchKleisliArrowFromHost (gate : FetchInboundGate) (remoteHost : String)
    (objectCount : Nat) : FetchKleisliArrow :=
  { fetchVerb := .fetch
    fetchGate := gate
    fetchRemote := classifyFetchRemote remoteHost
    fetchObjectCount := objectCount }

/-- Whether fetch arrow is admissible under §16.7 (gate ∧ remote class). -/
def fetchKleisliAdmissible (arrow : FetchKleisliArrow) : Bool :=
  fetchGateAdmits arrow.fetchGate && fetchRemoteAdmissible arrow.fetchRemote

theorem fetchKleisliAdmissible_spec (arrow : FetchKleisliArrow) :
    fetchKleisliAdmissible arrow = true ↔
      evaluateFetchKleisli arrow = Sum.inl FetchVerdict.admitted := by
  unfold fetchKleisliAdmissible evaluateFetchKleisli
  cases arrow.fetchGate <;> cases arrow.fetchRemote <;> simp [fetchGateAdmits, fetchRemoteAdmissible]

theorem evaluateFetchGateRefused (arrow : FetchKleisliArrow)
    (Hg : arrow.fetchGate = .refused) :
    evaluateFetchKleisli arrow = Sum.inr FetchError.gateRefused := by
  dsimp [evaluateFetchKleisli, fetchGateAdmits]
  rw [Hg]
  rfl

theorem evaluateFetchRemoteRefused (arrow : FetchKleisliArrow)
    (Hg : arrow.fetchGate = .admitted) (Hr : arrow.fetchRemote = .refusedUpstream) :
    evaluateFetchKleisli arrow = Sum.inr (.remoteClassRefused .refusedUpstream) := by
  dsimp [evaluateFetchKleisli, fetchGateAdmits, fetchRemoteAdmissible]
  rw [Hg, Hr]
  rfl

theorem evaluateFetchGateBypassRefused (arrow : FetchKleisliArrow)
    (Hg : arrow.fetchGate = .bypassAttempted) :
    evaluateFetchKleisli arrow = Sum.inr FetchError.gateBypassRefused := by
  dsimp [evaluateFetchKleisli, fetchGateAdmits]
  rw [Hg]
  rfl

-- ================================================================
-- SECTION 3: gate_check_before_sync inbound (GateBeforeSync bridge)
-- ================================================================

/-- Inbound fetch head move uses `gateCheck` — same predicate as sync tick. -/
def fetchGateCheckBeforeSync (prior post : ThermodynamicState) : Bool :=
  gateCheck prior post

theorem fetchGateCheckBeforeSync_sound (prior post : ThermodynamicState)
    (Hg : fetchGateCheckBeforeSync prior post = true) :
    Admissible prior post :=
  gateCheckSound prior post Hg

theorem fetchGateCheckBeforeSync_eq_tick (h : HistorySyncTick) :
    fetchGateCheckBeforeSync h.transition.prior.head h.transition.post.head =
      gateCheckBeforeSync h :=
  rfl

/-- Lift admitted inbound gate to fetch gate enum. -/
def fetchInboundGateFromSync (h : HistorySyncTick) : FetchInboundGate :=
  if gateCheckBeforeSync h then .admitted else .refused

theorem fetchInboundGateFromSync_admitted (h : HistorySyncTick)
    (Hg : gateCheckBeforeSync h = true) :
    fetchInboundGateFromSync h = .admitted := by
  simp [fetchInboundGateFromSync, Hg]

-- ================================================================
-- SECTION 4: Fetch composes Excitement.select (no second argmin)
-- ================================================================

/-- Kleisli fetch compose pin — import selector; refuse second argmin. -/
inductive FetchExcitementPin where
  | importSelectExcitement
  | secondArgminRefused
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 5: §16.7 fixtures + witness theorems
-- ================================================================

def fetchFixtureState : ThermodynamicState := ⟨2400, 0, 0, 0⟩

def fetchFixtureAdmittedArrow : FetchKleisliArrow :=
  fetchKleisliArrowFromHost .admitted "forge.entity" 3

def fetchFixtureGateRefusedArrow : FetchKleisliArrow :=
  fetchKleisliArrowFromHost .refused "forge.entity" 0

def fetchFixtureRemoteRefusedArrow : FetchKleisliArrow :=
  fetchKleisliArrowFromHost .admitted "github.com" 0

theorem fetchFixture_admitted_ok :
    evaluateFetchKleisli fetchFixtureAdmittedArrow = Sum.inl FetchVerdict.admitted := rfl

theorem fetchFixture_gate_refused :
    evaluateFetchKleisli fetchFixtureGateRefusedArrow = Sum.inr FetchError.gateRefused := rfl

theorem fetchFixture_remote_refused :
    evaluateFetchKleisli fetchFixtureRemoteRefusedArrow =
      Sum.inr (.remoteClassRefused .refusedUpstream) := rfl

theorem fetchFixture_classify_forge_entity :
    classifyFetchRemote "forge.entity" = .entityRemote := rfl

theorem fetchFixture_classify_github_refused :
    classifyFetchRemote "github.com" = .refusedUpstream := rfl

theorem fetchFixture_kleisli_admissible :
    fetchKleisliAdmissible fetchFixtureAdmittedArrow = true := rfl

theorem fetchPositiveRefuse_not_silent :
    evaluateFetchKleisli fetchFixtureGateRefusedArrow ≠ Sum.inl FetchVerdict.admitted := by
  simp [fetchFixture_gate_refused]

end UMST.Urge.KleisliFetch
