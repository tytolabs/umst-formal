-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/AdmitKleisli.lean

  Meso acting Urge — Kleisli admit arrow on typed history transitions.
  §2 / §16.1: second-law accounting on history moves; inherit Kleisli monad laws
  from `Compat.Constitutional`; compose `UMST.Excitement.select` (no local argmin).

  Anchored in `LandauerLaw.physicalSecondLaw` via a physical bridge.
  Adds **zero** Lean `axiom` declarations.  Knowing fiber (EpistemicMI / LandauerBound)
  lives on `umst-formal-double-slit` — cited, not restated here.
-/

import Compat.Constitutional
import Excitement
import LandauerLaw
import Process

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.AdmitKleisli

-- ================================================================
-- SECTION 1: Typed history / admit carriers (meso acting layer)
-- ================================================================

/-- Content-addressed history snapshot: commit id + gate-checked head state. -/
structure HistorySnapshot where
  commitId : Nat
  head     : ThermodynamicState

/-- A move of the history head and the erasure that pays for it: the head move passes the gate, and `erasure`
    erases the distribution `erased` (the information the move discards). -/
structure HistoryTransition where
  prior          : HistorySnapshot
  post           : HistorySnapshot
  gateAdmissible : Admissible prior.head post.head
  erasure        : ErasureProcess
  erased         : ProbDist 2

/-- A history move is admissible when its erasure is an instance of the one second law. -/
def admissibleHistoryTransition (t : HistoryTransition) : Prop :=
  UMST.ProcessFamily.SecondLaw (.erase t.erasure) (.erasure t.erased)

/-- Admissibility is the Clausius bound of the erasure: the erased entropy is at most the work over the bath
    temperature. -/
theorem admissibleHistoryTransition_iff (t : HistoryTransition) :
    admissibleHistoryTransition t ↔
      shannonEntropy t.erased ≤ t.erasure.work / t.erasure.bath.bathTemp.val := by
  simp [admissibleHistoryTransition, UMST.ProcessFamily.SecondLaw, eraseSecondLaw, eraseSecondLawStep,
    diracEntropy_zero LandauerLaw.two_pos]

-- ================================================================
-- SECTION 2: Kleisli admit arrows (inherit monad laws — do not re-prove)
-- ================================================================

/-- Kleisli arrow over thermodynamic states (history head moves). -/
abbrev AdmitArrow := KleisliArrow

/-- Kleisli identity on history head states. -/
def admitIdentity : AdmitArrow := fun s => some s

/-- Kleisli composition (inherited). -/
abbrev kleisliCompose := UMST.kleisliCompose

/-- Fold a non-empty Kleisli chain (inherited). -/
abbrev kleisliFold := UMST.kleisliFold

/-- Associativity at a state (inherited from `Compat.Constitutional`). -/
theorem kleisliComposeAssocAt (f g h : AdmitArrow) (s : ThermodynamicState) :
    kleisliCompose (kleisliCompose f g) h s = kleisliCompose f (kleisliCompose g h) s := by
  simpa using congrArg (fun k => k s) (UMST.kleisliComposeAssoc f g h)

/-- Left unit law at a state (inherited). -/
theorem kleisliLeftUnitAt (f : AdmitArrow) (s : ThermodynamicState) :
    kleisliCompose admitIdentity f s = f s := by
  simpa [admitIdentity] using congrArg (fun k => k s) (UMST.kleisliLeftUnit f)

/-- Right unit law at a state (inherited). -/
theorem kleisliRightUnitAt (f : AdmitArrow) (s : ThermodynamicState) :
    kleisliCompose f admitIdentity s = f s := by
  simpa [admitIdentity] using congrArg (fun k => k s) (UMST.kleisliRightUnit f)

end UMST.Urge.AdmitKleisli
