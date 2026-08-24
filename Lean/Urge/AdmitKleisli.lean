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

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.AdmitKleisli

-- ================================================================
-- SECTION 1: Typed history / admit carriers (meso acting layer)
-- ================================================================

/-- Content-addressed history snapshot: commit id + gate-checked head state. -/
structure HistorySnapshot where
  commitId : Nat
  head     : ThermodynamicState

/-- Thermodynamic accounting on a history transition (acting meso layer). -/
structure HistoryTransition where
  prior           : HistorySnapshot
  post            : HistorySnapshot
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ
  gateAdmissible  : Admissible prior.head post.head

/-- Named second-law invariant on history (Prop — not a Lean axiom). -/
def admitSecondLaw (t : HistoryTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

/-- Admissible history transition: gate-checked head move + second-law accounting. -/
def admissibleHistoryTransition (t : HistoryTransition) : Prop :=
  admitSecondLaw t

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

/-- Global Kleisli associativity (inherited). -/
theorem kleisliComposeAssoc (f g h : AdmitArrow) :
    kleisliCompose (kleisliCompose f g) h = kleisliCompose f (kleisliCompose g h) :=
  UMST.kleisliComposeAssoc f g h

/-- Left unit law at a state (inherited). -/
theorem kleisliLeftUnitAt (f : AdmitArrow) (s : ThermodynamicState) :
    kleisliCompose admitIdentity f s = f s := by
  simpa [admitIdentity] using congrArg (fun k => k s) (UMST.kleisliLeftUnit f)

/-- Right unit law at a state (inherited). -/
theorem kleisliRightUnitAt (f : AdmitArrow) (s : ThermodynamicState) :
    kleisliCompose f admitIdentity s = f s := by
  simpa [admitIdentity] using congrArg (fun k => k s) (UMST.kleisliRightUnit f)

/-- Graded composition preserves well-typing (inherited). -/
theorem kleisliComposeWellTypedN (m n : ℕ) (f g : AdmitArrow)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (kleisliCompose f g) :=
  UMST.kleisliComposeWellTypedN m n f g hf hg

-- ================================================================
-- SECTION 3: Excitement composition (no local argmin re-derivation)
-- ================================================================

/-- History admit selection composes `UMST.Excitement.select` — not a second argmin. -/
noncomputable def admitHistorySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    Cand (K := ℚ) src ⊕ Residue :=
  select src cands

/-- Alias witness: local selection API is definitionally `Excitement.select`. -/
theorem admitHistorySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (src : S) (cands : List (Cand (K := ℚ) src)) :
    admitHistorySelect src cands = select src cands :=
  rfl

-- ================================================================
-- SECTION 4: Bridge to physicalSecondLaw (derived — zero new axioms)
-- ================================================================

/-- Physical realization of a binary history erasure (uniform → Dirac accounting). -/
structure PhysicalHistoryBridge where
  proc : ErasureProcess
  transition : HistoryTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))

/-- `physicalSecondLaw` discharges history second-law admissibility. -/
theorem admitSecondLaw_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition := by
  unfold admitSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

/-- **Admit morphism axiom discipline**: history second-law admissibility discharges from
    the sole project axiom `physicalSecondLaw` — zero new Lean `axiom` declarations. -/
theorem admitMorphism_noNewAxiom (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition :=
  admitSecondLaw_from_physical b hSL

/-- Physically bridged transition is an admissible history transition. -/
theorem admissibleHistoryTransition_from_physical (b : PhysicalHistoryBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleHistoryTransition b.transition :=
  admitSecondLaw_from_physical b hSL

-- ================================================================
-- SECTION 5: Honesty flags + catalog witnesses
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

/-- Production wiring stays open (meso lift only). -/
def admitKleisliProductionWired : Bool := false

theorem admitKleisliProductionWiredFalse : admitKleisliProductionWired = false := rfl

/-- Catalog witness: meso Urge AdmitKleisli module present. -/
theorem admitKleisliModuleWitness : True := trivial

end UMST.Urge.AdmitKleisli
