-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Constants/SecondLawElectromagnetic.lean

  Four electromagnetic constants of `Constants.SI` bounded by the second law. Each statement takes the `.transition`
  case of `UMST.ProcessFamily.SecondLaw` (free energy does not rise in a passive step) and states, for a coefficient,
  exactly when the law admits every passive step of its kind; the exact SI value is then shown to lie inside.

  * Stored field energy. A region of vacuum holding an electric field `E` stores ½·ε·E² per unit volume; holding a
    magnetic flux density `B` it stores B²/(2μ). Released, the field relaxes passively to zero (free energy zero).
    `electricRelaxation_secondLaw_iff`: every such relaxation is admitted exactly when `ε ≥ 0`;
    `magneticRelaxation_secondLaw_iff`: for `μ ≠ 0`, exactly when `μ > 0`.
  * Joule dissipation. A two-terminal conductance `G` at voltage `V` for a time `dt > 0` dissipates G·V²·dt out of
    the free energy; a resistance `R` carrying current `I` dissipates R·I²·dt.
    `conductanceDissipation_secondLaw_iff`: every such step is admitted exactly when `G ≥ 0`;
    `resistanceDissipation_secondLaw_iff`: exactly when `R ≥ 0`.

  The SI instances `vacuumPermittivity_relaxation_secondLaw`, `vacuumPermeability_relaxation_secondLaw`,
  `conductanceQuantum_dissipation_secondLaw` and `vonKlitzing_dissipation_secondLaw` state that the law admits every
  step at the exact values ε₀, μ₀, G₀ = 2e²/h and R_K = h/e². Each result is a bound (a sign), never a value: the
  value stays fixed by the SI definitions and the CODATA 2022 fine-structure constant. Zero Lean axioms; physics
  enters only as the `SecondLaw` hypothesis.
-/

import Process
import Constants.SI

open UMST.ProcessFamily UMST.Real

namespace UMST.Constants.SecondLawElectromagnetic

/-- A passive step of the vacuum at density `ρ` from free energy `ψ` to `ψ'`. -/
def passiveStep (ρ ψ ψ' : ℝ) : Prior := .thermodynamic ⟨ρ, ψ⟩ ⟨ρ, ψ'⟩

/-- A passive step at fixed density is admitted exactly when the free energy does not rise. -/
theorem passiveStep_secondLaw_iff (ρ ψ ψ' : ℝ) : SecondLaw .transition (passiveStep ρ ψ ψ') ↔ ψ' ≤ ψ := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    show |ρ - ρ| ≤ UMST.Core.ThermodynamicScalar.δMass (K := ℝ)
    rw [sub_self, abs_zero]
    exact UMST.Core.ThermodynamicScalar.δMass_nonneg

/-- **Electric field energy**: the relaxation of every field `E` from ½·ε·E² to zero is admitted exactly when
    `ε ≥ 0`. -/
theorem electricRelaxation_secondLaw_iff (ε : ℝ) :
    (∀ ρ E : ℝ, SecondLaw .transition (passiveStep ρ (1 / 2 * ε * E ^ 2) 0)) ↔ 0 ≤ ε := by
  simp only [passiveStep_secondLaw_iff]
  constructor
  · intro h
    have h1 := h 0 1
    linarith
  · intro hε ρ E
    positivity

/-- **Magnetic field energy**: for `μ ≠ 0`, the relaxation of every flux density `B` from B²/(2μ) to zero is
    admitted exactly when `μ > 0`. -/
theorem magneticRelaxation_secondLaw_iff {μ : ℝ} (hμ : μ ≠ 0) :
    (∀ ρ B : ℝ, SecondLaw .transition (passiveStep ρ (B ^ 2 / (2 * μ)) 0)) ↔ 0 < μ := by
  simp only [passiveStep_secondLaw_iff]
  constructor
  · intro h
    have h1 : (0 : ℝ) ≤ 1 ^ 2 / (2 * μ) := h 0 1
    rcases lt_or_gt_of_ne hμ with hneg | hpos
    · have : (1 : ℝ) ^ 2 / (2 * μ) < 0 := div_neg_of_pos_of_neg (by norm_num) (by linarith)
      linarith
    · exact hpos
  · intro hμ' ρ B
    positivity

/-- **Conductance**: every Joule step dissipating G·V²·dt (`dt > 0`) is admitted exactly when `G ≥ 0`. -/
theorem conductanceDissipation_secondLaw_iff (G : ℝ) :
    (∀ ρ ψ V dt : ℝ, 0 < dt → SecondLaw .transition (passiveStep ρ ψ (ψ - G * V ^ 2 * dt))) ↔ 0 ≤ G := by
  simp only [passiveStep_secondLaw_iff]
  constructor
  · intro h
    have h1 := h 0 0 1 1 one_pos
    linarith
  · intro hG ρ ψ V dt hdt
    have : 0 ≤ G * V ^ 2 * dt := by positivity
    linarith

/-- **Resistance**: every Joule step dissipating R·I²·dt (`dt > 0`) is admitted exactly when `R ≥ 0`. -/
theorem resistanceDissipation_secondLaw_iff (R : ℝ) :
    (∀ ρ ψ I dt : ℝ, 0 < dt → SecondLaw .transition (passiveStep ρ ψ (ψ - R * I ^ 2 * dt))) ↔ 0 ≤ R :=
  conductanceDissipation_secondLaw_iff R

/-- The vacuum permittivity ε₀ = e²/(2αhc) lies inside the second-law bound: every field relaxation is admitted. -/
theorem vacuumPermittivity_relaxation_secondLaw (ρ E : ℝ) :
    SecondLaw .transition (passiveStep ρ (1 / 2 * (UMST.Constants.SI.vacuumPermittivity : ℝ) * E ^ 2) 0) :=
  (electricRelaxation_secondLaw_iff _).2
    (by rw [UMST.Constants.SI.vacuumPermittivity_value]; norm_num) ρ E

/-- The vacuum permeability μ₀ = 2αh/(e²c) lies inside the second-law bound: every field relaxation is admitted. -/
theorem vacuumPermeability_relaxation_secondLaw (ρ B : ℝ) :
    SecondLaw .transition (passiveStep ρ (B ^ 2 / (2 * (UMST.Constants.SI.vacuumPermeability : ℝ))) 0) := by
  have hpos : (0 : ℝ) < (UMST.Constants.SI.vacuumPermeability : ℝ) := by
    rw [UMST.Constants.SI.vacuumPermeability_value]; norm_num
  exact (magneticRelaxation_secondLaw_iff hpos.ne').2 hpos ρ B

/-- The conductance quantum G₀ = 2e²/h lies inside the second-law bound: every Joule step is admitted. -/
theorem conductanceQuantum_dissipation_secondLaw (ρ ψ V dt : ℝ) (hdt : 0 < dt) :
    SecondLaw .transition
      (passiveStep ρ ψ (ψ - (UMST.Constants.SI.conductanceQuantum : ℝ) * V ^ 2 * dt)) :=
  (conductanceDissipation_secondLaw_iff _).2
    (by rw [UMST.Constants.SI.conductanceQuantum_value]; norm_num) ρ ψ V dt hdt

/-- The von Klitzing constant R_K = h/e² lies inside the second-law bound: every Joule step is admitted. -/
theorem vonKlitzing_dissipation_secondLaw (ρ ψ I dt : ℝ) (hdt : 0 < dt) :
    SecondLaw .transition (passiveStep ρ ψ (ψ - (UMST.Constants.SI.vonKlitzing : ℝ) * I ^ 2 * dt)) :=
  (resistanceDissipation_secondLaw_iff _).2
    (by rw [UMST.Constants.SI.vonKlitzing_value]; norm_num) ρ ψ I dt hdt

end UMST.Constants.SecondLawElectromagnetic
