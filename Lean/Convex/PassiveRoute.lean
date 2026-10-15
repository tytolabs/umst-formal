-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  `Convex.PassiveRoute` — the passive route into the `.transition` case of `UMST.ProcessFamily.SecondLaw`.

  A passive step supplies no power: its free energy changes by Δψ = ψ_new − ψ_old and it dissipates D, with the
  energy balance Δψ + D = 0 and the mass condition of the gate. On such a step the transition case of `SecondLaw`
  holds exactly when D ≥ 0 (`passive_secondLaw_iff`). Every dissipative statement of the repository enters the law
  through this one statement:

  * forward, a convex dissipation potential φ with φ ≥ 0 and φ(0) = 0 makes D = ṡ·φ′(ṡ) ≥ 0, so the passive balance
    is a `SecondLaw` step (`ConvexPhiDissipation.gsmCartridge_passive_secondLaw`, and through it the grammar of
    `Convex.PhiGrammar` and the composition law of `Composition.GsmMonoid`);
  * backward, a `SecondLaw` step whose dissipation is written in a constitutive form (c·q, η·ṙ²·dt, a released
    stored energy, the kinetic energy an impact loses) has D ≥ 0, and that bounds the coefficient
    (`dissipation_nonneg_of_secondLaw`, used by the `second_law_bound.*` statements).

  `passive_inequality_secondLaw` is the inequality form Δψ + D ≤ 0 with D ≥ 0; it passes through the equality form
  with the released free energy ψ_old − ψ_new ≥ D as the dissipation.

  Zero Lean axioms, no `sorry`.
-/

import Process

open UMST.ProcessFamily UMST.Core UMST.Real

namespace UMST.Convex.PassiveRoute

/-- **Passive balance** of one step dissipating `D`: the mass condition of the gate and Δψ + D = 0 (no supplied
    power). -/
structure PassiveBalance (D : ℝ) (old new : RealThermodynamicState) : Prop where
  mass : CoreMassCond ℝ RealThermodynamicState old new
  balance : (new.freeEnergy - old.freeEnergy) + D = 0

/-- **The passive route**: on a passive balance the `.transition` case of `SecondLaw` holds exactly when the
    dissipation is non-negative. -/
theorem passive_secondLaw_iff {D : ℝ} {old new : RealThermodynamicState} (h : PassiveBalance D old new) :
    SecondLaw .transition (.thermodynamic old new) ↔ 0 ≤ D := by
  have hb := h.balance
  constructor
  · intro hs
    have hd : new.freeEnergy ≤ old.freeEnergy := hs.2
    linarith
  · intro hD
    exact ⟨h.mass, by
      show new.freeEnergy ≤ old.freeEnergy
      linarith⟩

/-- The released free energy ψ_old − ψ_new is the dissipation of a passive balance on any step within the mass
    ball. -/
theorem passiveBalance_released {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new) :
    PassiveBalance (old.freeEnergy - new.freeEnergy) old new :=
  ⟨hm, by ring⟩

/-- **Bounds through the passive route**: a `SecondLaw` step whose energy balance Δψ + D = 0 names its dissipation
    has D ≥ 0. -/
theorem dissipation_nonneg_of_secondLaw {D : ℝ} {old new : RealThermodynamicState}
    (h : SecondLaw .transition (.thermodynamic old new))
    (hb : (new.freeEnergy - old.freeEnergy) + D = 0) : 0 ≤ D :=
  (passive_secondLaw_iff ⟨h.1, hb⟩).1 h

/-- A step from free energy `ψ` that dissipates `d` (ψ_new = ψ − d) obeys the second law only with `d ≥ 0`. -/
theorem step_dissipation_nonneg {ρ ρ' ψ d : ℝ}
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', ψ - d⟩)) : 0 ≤ d :=
  dissipation_nonneg_of_secondLaw h (by dsimp only; ring)

/-- A passive relaxation from a stored free energy `ψ` to the natural state (free energy zero) dissipates `ψ`; it
    obeys the second law only with `ψ ≥ 0`. -/
theorem relaxation_stored_nonneg {ρ ρ' ψ : ℝ}
    (h : SecondLaw .transition (.thermodynamic ⟨ρ, ψ⟩ ⟨ρ', 0⟩)) : 0 ≤ ψ :=
  dissipation_nonneg_of_secondLaw h (by dsimp only; ring)

/-- **Inequality form**: Δψ + D ≤ 0 with D ≥ 0 and the mass condition is a `SecondLaw` step; the released free
    energy, at least D, is the dissipation of the passive balance. -/
theorem passive_inequality_secondLaw {D : ℝ} {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new) (hD : 0 ≤ D)
    (hb : (new.freeEnergy - old.freeEnergy) + D ≤ 0) :
    SecondLaw .transition (.thermodynamic old new) :=
  (passive_secondLaw_iff (passiveBalance_released hm)).2 (by linarith)

/-- **Refusal through the passive route**: a step whose energy balance Δψ + D = 0 names a negative dissipation is
    refused. -/
theorem passive_refused_of_neg {D : ℝ} {old new : RealThermodynamicState}
    (hb : (new.freeEnergy - old.freeEnergy) + D = 0) (hD : D < 0) :
    ¬ SecondLaw .transition (.thermodynamic old new) :=
  fun hs => absurd (dissipation_nonneg_of_secondLaw hs hb) (not_le.2 hD)

end UMST.Convex.PassiveRoute
