-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/Transport.lean

  Meso acting Urge — BP II §5.3 / §13.05 transport seam channel set.
  Mirrors Rust `Transport` + `admit_carry` Offline refuse. Channel-agnostic above.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Zero Lean `axiom`. Zero sorry. `physics_green` false.
-/

import Urge.AppendOnly
import LandauerLaw

namespace UMST.Urge.Transport

set_option linter.dupNamespace false

/-- Channel set above which identity/reconcile stay transport-agnostic. -/
inductive Transport where
  | local
  | git
  | mesh
  | remote
  | offline
  deriving DecidableEq, Repr

/-- Offline cannot carry live bytes. -/
def canCarry : Transport → Bool
  | .offline => false
  | _ => true

/-- Positive refuse when Offline is asked to carry. -/
inductive TransportError where
  | offlineCannotCarry
  deriving DecidableEq, Repr

/-- Admit a carry on `channel` — Offline refuses. -/
def admitCarry (t : Transport) : Except TransportError Unit :=
  if canCarry t then .ok () else .error .offlineCannotCarry

theorem local_can_carry : canCarry .local = true := rfl
theorem offline_cannot_carry : canCarry .offline = false := rfl

theorem admit_local_ok : admitCarry .local = .ok () := rfl
theorem admit_offline_refuses :
    admitCarry .offline = .error .offlineCannotCarry := rfl

/-- Closed channel census. -/
def channelSet : List Transport :=
  [.local, .git, .mesh, .remote, .offline]

theorem channelSet_len : channelSet.length = 5 := rfl

def transportPhysicsGreen : Bool := false
theorem transportPhysicsGreen_false : transportPhysicsGreen = false := rfl

end UMST.Urge.Transport
