-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  `ConvexPhiChannels` — several convex dissipation channels on one state, an inequality energy balance,
  Prony viscoelastic arms, and passive restitution, each closed through the passive `.transition` case of
  `UMST.ProcessFamily.SecondLaw`.

  * `GsmMultiPotential n` holds `n` scalar-rate channels; the total dissipation power is the sum of the
    per-channel powers and is nonnegative channel by channel (`multi_dissipation_nonneg`).
  * `PassiveGsmEnergyInequality` states Δψ + D ≤ 0 with D ≥ 0 (no supplied power); `inequality_secondLaw`
    derives free-energy descent. `supplied_inequality_secondLaw` admits a supplied power `P` that the
    dissipation covers (P ≤ D), the open case that still descends.
  * `pronyPotential E τ` is one Maxwell arm with viscosity η = E·τ and φ(x) = ½·η·x²;
    `prony_dissipation_nonneg` is the nonnegative total power of any finite set of arms.
  * `restitution_le_one`: a passive impact whose free energy is ½·μ·v² before and ½·μ·(e·v)² after
    satisfies e ≤ 1 for any e ≥ 0.

  Zero Lean axioms; physics enters only as the `SecondLaw` hypothesis shape.
-/

import ConvexPhiDissipation

open Real Set UMST.ProcessFamily UMST.Core UMST.Real UMST.ConvexPhiDissipation

local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.ConvexPhiChannels

/-- `n` scalar-rate dissipation channels on one state. -/
structure GsmMultiPotential (n : ℕ) where
  ch : Fin n → GsmDissipationPotential

/-- Total dissipation power: the sum of the per-channel powers ṡᵢ·φᵢ′(ṡᵢ). -/
noncomputable def multiDissipationPower {n : ℕ} (M : GsmMultiPotential n) (sDot : Fin n → ℝ) : ℝ :=
  ∑ i, dissipationPower (M.ch i) (sDot i)

/-- Every channel is convex, nonnegative and pinned at zero, so the total power is nonnegative. -/
theorem multi_dissipation_nonneg {n : ℕ} (M : GsmMultiPotential n) (sDot : Fin n → ℝ) :
    0 ≤ multiDissipationPower M sDot :=
  Finset.sum_nonneg fun i _ => convex_phi_dissipation_nonneg (M.ch i) (sDot i)

/-- Passive inequality energy balance: Δψ + D ≤ 0 with a nonnegative dissipation D. -/
structure PassiveGsmEnergyInequality (D : ℝ) (old new : RealThermodynamicState) : Prop where
  mass : CoreMassCond ℝ RealThermodynamicState old new
  dNonneg : 0 ≤ D
  balance : (new.freeEnergy - old.freeEnergy) + D ≤ 0

/-- The passive inequality balance is a `.transition` instance of the second law. -/
theorem inequality_secondLaw {D : ℝ} {old new : RealThermodynamicState}
    (h : PassiveGsmEnergyInequality D old new) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  ⟨h.mass, by
    show new.freeEnergy ≤ old.freeEnergy
    linarith [h.dNonneg, h.balance]⟩

/-- Supplied power `P` with Δψ + D ≤ P and P ≤ D still descends: the dissipation covers the supply. -/
theorem supplied_inequality_secondLaw {D P : ℝ} {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hb : (new.freeEnergy - old.freeEnergy) + D ≤ P) (hcover : P ≤ D) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  ⟨hm, by
    show new.freeEnergy ≤ old.freeEnergy
    linarith [hb, hcover]⟩

/-- Several channels under the passive inequality balance satisfy the second law. -/
theorem multi_secondLaw {n : ℕ} (M : GsmMultiPotential n) {old new : RealThermodynamicState}
    {sDot : Fin n → ℝ} (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hb : (new.freeEnergy - old.freeEnergy) + multiDissipationPower M sDot ≤ 0) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  inequality_secondLaw ⟨hm, multi_dissipation_nonneg M sDot, hb⟩

/-- One Maxwell (Prony) arm with modulus `E ≥ 0` and relaxation time `τ ≥ 0`:
    viscosity η = E·τ and dissipation potential φ(x) = ½·η·x² in the arm's viscous strain rate x. -/
noncomputable def pronyPotential (E τ : ℝ) (hE : 0 ≤ E) (hτ : 0 ≤ τ) : GsmDissipationPotential where
  φ x := (1 / 2 * (E * τ)) * x ^ 2
  convex := by
    have hη : 0 ≤ 1 / 2 * (E * τ) := by positivity
    have hsq : ConvexOn ℝ univ fun x : ℝ => x ^ 2 := Even.convexOn_pow (𝕜 := ℝ) even_two
    simpa [smul_eq_mul] using hsq.smul hη
  nonneg x := by
    have := mul_nonneg hE hτ
    positivity
  zero := by simp
  diff := by fun_prop

/-- The arm's dissipation power is η·x², the classical viscous dashpot power. -/
theorem prony_dissipationPower_eq (E τ : ℝ) (hE : 0 ≤ E) (hτ : 0 ≤ τ) (x : ℝ) :
    dissipationPower (pronyPotential E τ hE hτ) x = E * τ * x ^ 2 := by
  have hd : deriv (fun y : ℝ => (1 / 2 * (E * τ)) * y ^ 2) x = (1 / 2 * (E * τ)) * (2 * x) := by
    have h := ((hasDerivAt_pow 2 x).const_mul (1 / 2 * (E * τ))).deriv
    simp at h
    simp [h]
  show x * deriv (fun y : ℝ => (1 / 2 * (E * τ)) * y ^ 2) x = E * τ * x ^ 2
  rw [hd]
  ring

/-- A finite Prony series: arm moduli `E i ≥ 0` and relaxation times `τ i ≥ 0`. -/
noncomputable def pronySeries {n : ℕ} (E τ : Fin n → ℝ) (hE : ∀ i, 0 ≤ E i) (hτ : ∀ i, 0 ≤ τ i) :
    GsmMultiPotential n where
  ch i := pronyPotential (E i) (τ i) (hE i) (hτ i)

/-- **Prony dissipation is nonnegative**: Σᵢ ηᵢ·xᵢ² ≥ 0 for ηᵢ = Eᵢ·τᵢ ≥ 0. -/
theorem prony_dissipation_nonneg {n : ℕ} (E τ : Fin n → ℝ) (hE : ∀ i, 0 ≤ E i) (hτ : ∀ i, 0 ≤ τ i)
    (x : Fin n → ℝ) :
    0 ≤ ∑ i, E i * τ i * x i ^ 2 := by
  have h := multi_dissipation_nonneg (pronySeries E τ hE hτ) x
  simpa [multiDissipationPower, pronySeries, prony_dissipationPower_eq] using h

/-- A viscoelastic step with Prony arms under the passive inequality balance satisfies the second law. -/
theorem prony_secondLaw {n : ℕ} (E τ : Fin n → ℝ) (hE : ∀ i, 0 ≤ E i) (hτ : ∀ i, 0 ≤ τ i)
    (x : Fin n → ℝ) {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hb : (new.freeEnergy - old.freeEnergy) + ∑ i, E i * τ i * x i ^ 2 ≤ 0) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  inequality_secondLaw ⟨hm, prony_dissipation_nonneg E τ hE hτ x, hb⟩

/-- **Passive restitution**: with free energy ½·μ·v² before the impact and ½·μ·(e·v)² after, a
    `.transition` second-law step forces e ≤ 1 for any e ≥ 0 (μ·v² > 0). -/
theorem restitution_le_one {ρ ρ' μ v e : ℝ} (he : 0 ≤ e) (hpos : 0 < μ * v ^ 2)
    (h : SecondLawₚ .transition
      (.thermodynamic ⟨ρ, 1 / 2 * μ * v ^ 2⟩ ⟨ρ', 1 / 2 * μ * (e * v) ^ 2⟩)) :
    e ≤ 1 := by
  have hd : 1 / 2 * μ * (e * v) ^ 2 ≤ 1 / 2 * μ * v ^ 2 := h.2
  have h2 : (μ * v ^ 2) * e ^ 2 ≤ (μ * v ^ 2) * 1 := by nlinarith [hd]
  exact (sq_le_one_iff₀ he).1 (le_of_mul_le_mul_left h2 hpos)

/-- The energy split of a passive impact: the kinetic energy lost, ½·μ·v²·(1 − e²), is nonnegative
    whenever the step satisfies the second law. -/
theorem restitution_energy_loss_nonneg {ρ ρ' μ v e : ℝ}
    (h : SecondLawₚ .transition
      (.thermodynamic ⟨ρ, 1 / 2 * μ * v ^ 2⟩ ⟨ρ', 1 / 2 * μ * (e * v) ^ 2⟩)) :
    0 ≤ 1 / 2 * μ * v ^ 2 * (1 - e ^ 2) := by
  have hd : 1 / 2 * μ * (e * v) ^ 2 ≤ 1 / 2 * μ * v ^ 2 := h.2
  nlinarith [hd]

end UMST.ConvexPhiChannels
