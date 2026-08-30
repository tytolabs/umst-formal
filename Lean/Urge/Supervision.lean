-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/Supervision.lean — BP II §6 supervision loop pin.
  Phases observe→reconcile→heal→verify→record. Local-only. Zero sorry/axiom.
-/

import Urge.Transport
import LandauerLaw

namespace UMST.Urge.Supervision

open UMST.Urge.Transport

inductive SupervisionPhase where
  | observe | reconcile | selfHeal | verify | record
  deriving DecidableEq, Repr

inductive SupervisionTier where
  | fast | slow
  deriving DecidableEq, Repr

def budgetUs : SupervisionTier → Nat
  | .fast => 100000
  | .slow => 1000000

def phaseOrder : List SupervisionPhase :=
  [.observe, .reconcile, .selfHeal, .verify, .record]

theorem phaseOrder_len : phaseOrder.length = 5 := rfl

/-- Local cycle admissible when channel can carry. -/
def localCycleAdmissible (ch : Transport) : Bool :=
  canCarry ch

theorem local_admissible : localCycleAdmissible .local = true := rfl
theorem offline_inadmissible : localCycleAdmissible .offline = false := rfl

def supervisionPhysicsGreen : Bool := false
theorem supervisionPhysicsGreen_false : supervisionPhysicsGreen = false := rfl

end UMST.Urge.Supervision
