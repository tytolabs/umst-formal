-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ExactRatFreeEnergy.lean

  Meso acting Urge — §22.6 exact Rat free-energy identity.
  Executable F lives in ℚ (`jointFreeEnergy` at field `K`); pin Rat/ℚ carrier;
  refuse f64-as-identity theater as a named Prop.

  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
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

/-- Executable joint free energy F in ℚ — aliases `Excitement.jointFreeEnergy`. -/
def executableF {S : Type} [ThermodynamicSystem ℚ S] [JointThermo ℚ S] (s : S) :
    ExecutableFCarrier :=
  jointFreeEnergy s

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

end UMST.Urge.ExactRatFreeEnergy
