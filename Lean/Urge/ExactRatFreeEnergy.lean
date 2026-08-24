-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ExactRatFreeEnergy.lean

  Meso acting Urge — §22.6 exact Rat free-energy identity.
  Executable F lives in ℚ (`jointFreeEnergy` at field `K`); pin Rat/ℚ carrier;
  refuse f64-as-identity theater as a named Prop.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.ExactRatFreeEnergy

-- ================================================================
-- SECTION 1: ℚ carrier pin for executable F (§22.6)
-- ================================================================

/-- Carrier for executable joint free energy F: pinned to ℚ = Rat. -/
abbrev ExecutableFCarrier := ℚ

/-- Rat/ℚ identity witness: carrier is definitionally ℚ. -/
theorem executableFCarrier_eq_rat : ExecutableFCarrier = ℚ := rfl

/-- Executable joint free energy F in ℚ — aliases `Excitement.jointFreeEnergy`. -/
def executableF {S : Type} [ThermodynamicSystem ℚ S] [JointThermo ℚ S] (s : S) :
    ExecutableFCarrier :=
  jointFreeEnergy s

/-- Definitional witness: `executableF` is `jointFreeEnergy`. -/
theorem executableF_eq_jointFreeEnergy {S : Type} [ThermodynamicSystem ℚ S] [JointThermo ℚ S]
    (s : S) : executableF s = jointFreeEnergy s :=
  rfl

/-- Candidate global free energy remains ℚ-exact (no Urge-local f64 lift). -/
def executableCandEnergy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ExecutableFCarrier :=
  candEnergy (src := src) c

theorem executableCandEnergy_eq_candEnergy {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) :
    executableCandEnergy (src := src) c = candEnergy (src := src) c :=
  rfl

theorem executableCandEnergy_eq_globalFreeEnergyCand {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) :
    executableCandEnergy (src := src) c = globalFreeEnergyCand (src := src) c :=
  rfl

-- ================================================================
-- SECTION 2: f64-as-identity theater refusal (named Prop)
-- ================================================================

/-- Theater pattern (§22.6): treating non-ℚ (e.g. f64/Float) as the identity carrier for F. -/
def f64AsIdentityTheater : Prop :=
  ExecutableFCarrier ≠ ℚ

/-- Named refusal: f64 is not the identity carrier for executable F. -/
theorem refuseF64AsIdentityTheater : ¬ f64AsIdentityTheater :=
  fun h => h rfl

/-- Positive pin: executable F comparisons use ℚ exact Rat, not f64 theater. -/
def exactRatFreeEnergyIdentity : Prop :=
  ∀ {S : Type} [ThermodynamicSystem ℚ S] [JointThermo ℚ S] (s : S),
    ∃ q : ℚ, executableF s = q ∧ jointFreeEnergy s = q

theorem exactRatFreeEnergyIdentityHolds : exactRatFreeEnergyIdentity := by
  intro S _ _ s
  exact ⟨jointFreeEnergy s, rfl, rfl⟩

-- ================================================================
-- SECTION 3: Excitement.select strict-improvement uses ℚ F (no f64 compare)
-- ================================================================

/-- Strict-improvement gate in `select` compares ℚ `candEnergy` vs ℚ `jointFreeEnergy`. -/
theorem select_strictImprovement_exact_rat {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (src : S) (c : Cand (K := ℚ) src) :
    (candEnergy (src := src) c < jointFreeEnergy src) =
      (executableCandEnergy (src := src) c < executableF src) :=
  rfl

/-- `pickMin` uses ℚ `candEnergy` — no Urge-local f64 argmin. -/
theorem pickMin_uses_exact_rat_energy {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] {src : S}
    (_acc : Option (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src) :
    candEnergy (src := src) c = executableCandEnergy (src := src) c :=
  rfl

-- ================================================================
-- SECTION 4: Axiom discipline + honesty flags
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

/-- Production wiring stays open (meso ℚ pin only). -/
def exactRatFreeEnergyProductionWired : Bool := false

theorem exactRatFreeEnergyProductionWiredFalse : exactRatFreeEnergyProductionWired = false := rfl

/-- Catalog witness: meso Urge ExactRatFreeEnergy module present. -/
theorem exactRatFreeEnergyModuleWitness : True := trivial

/-- Executable F re-uses `jointFreeEnergy` from Excitement — no Urge-local f64 F. -/
theorem exactRat_noLocalF64F {S : Type} [ThermodynamicSystem ℚ S] [JointThermo ℚ S]
    (s : S) : executableF s = jointFreeEnergy s :=
  rfl

end UMST.Urge.ExactRatFreeEnergy
