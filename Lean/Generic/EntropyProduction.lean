-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  C-GENERIC (W-37): `Generic.EntropyProduction` — the GENERIC form of a nonequilibrium evolution and its
  entropy-production theorem.

  GENERIC (Grmela and Öttinger, Phys. Rev. E 56, 6620 and 6633 (1997)) writes an evolution on the state space
  `Fin n → ℝ` as ẋ = L·∇E + M·∇S with a Poisson operator L that is antisymmetric (Lᵀ = −L), a friction operator
  M that is symmetric and positive semidefinite, and the degeneracy conditions L·∇S = 0 and M·∇E = 0.

  * `energy_rate_zero` and `entropy_rate_nonneg`: at one state, ⟨∇E, ẋ⟩ = 0 and ⟨∇S, ẋ⟩ = ∇Sᵀ·M·∇S ≥ 0.
  * `generic_energy_const` and `generic_entropy_monotone`: along a differentiable trajectory whose velocity is the
    GENERIC vector field and whose E and S have the stated gradients, E is constant and S is nondecreasing.
  * `generic_secondLaw`: the bridge to the `.transition` case of `UMST.ProcessFamily.SecondLaw`. GENERIC describes an
    isolated system and states no free energy and no density, so the bridge names two extra hypotheses: a
    reservoir temperature T ≥ 0 that identifies the free energy ψ = E − T·S, and the mass condition
    `CoreMassCond` on the two endpoint states. Under them ψ does not rise from t₀ to t₁ ≥ t₀.

  Zero Lean axioms, no `sorry`.
-/

import Process
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Matrix UMST.ProcessFamily UMST.Core UMST.Real

local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.Generic

/-- The state space of `n` coordinates. -/
abbrev State (n : ℕ) := Fin n → ℝ

/-- The GENERIC vector field L·∇E + M·∇S. -/
def genericField {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℝ) (dE dS : State n) : State n :=
  L *ᵥ dE + M *ᵥ dS

/-- The GENERIC operator conditions at one state with energy gradient `dE` and entropy gradient `dS`. -/
structure GenericAt {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℝ) (dE dS : State n) : Prop where
  /-- The Poisson operator is antisymmetric. -/
  antisymm : Lᵀ = -L
  /-- The friction operator is symmetric. -/
  symm : Mᵀ = M
  /-- The friction operator is positive semidefinite. -/
  psd : ∀ v : State n, 0 ≤ v ⬝ᵥ (M *ᵥ v)
  /-- Degeneracy: the reversible part leaves the entropy unchanged. -/
  degenL : L *ᵥ dS = 0
  /-- Degeneracy: the irreversible part leaves the energy unchanged. -/
  degenM : M *ᵥ dE = 0

/-- Moving a matrix across the pairing: u·(A·w) = (Aᵀ·u)·w. -/
theorem pair_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u w : State n) :
    u ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ u) ⬝ᵥ w := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- An antisymmetric operator pairs every vector with itself to zero. -/
theorem antisymm_pair_self {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ} (hL : Lᵀ = -L) (v : State n) :
    v ⬝ᵥ (L *ᵥ v) = 0 := by
  have h := pair_transpose L v v
  rw [hL, neg_mulVec, neg_dotProduct, dotProduct_comm (L *ᵥ v) v] at h
  linarith

/-- **Energy conservation**: the GENERIC rate of the energy, ⟨∇E, ẋ⟩, is zero. -/
theorem energy_rate_zero {n : ℕ} {L M : Matrix (Fin n) (Fin n) ℝ} {dE dS : State n}
    (h : GenericAt L M dE dS) : dE ⬝ᵥ genericField L M dE dS = 0 := by
  rw [genericField, dotProduct_add, antisymm_pair_self h.antisymm, pair_transpose M, h.symm, h.degenM,
    zero_dotProduct, add_zero]

/-- The GENERIC rate of the entropy is the friction pairing ∇Sᵀ·M·∇S. -/
theorem entropy_rate_eq {n : ℕ} {L M : Matrix (Fin n) (Fin n) ℝ} {dE dS : State n}
    (h : GenericAt L M dE dS) : dS ⬝ᵥ genericField L M dE dS = dS ⬝ᵥ (M *ᵥ dS) := by
  rw [genericField, dotProduct_add, pair_transpose L, h.antisymm, neg_mulVec, h.degenL, neg_zero,
    zero_dotProduct, zero_add]

/-- **Entropy production**: the GENERIC rate of the entropy, ⟨∇S, ẋ⟩, is nonnegative. -/
theorem entropy_rate_nonneg {n : ℕ} {L M : Matrix (Fin n) (Fin n) ℝ} {dE dS : State n}
    (h : GenericAt L M dE dS) : 0 ≤ dS ⬝ᵥ genericField L M dE dS := by
  rw [entropy_rate_eq h]
  exact h.psd dS

/-- The gradient `g` as the continuous linear functional v ↦ g·v. -/
noncomputable def gradCLM {n : ℕ} (g : State n) : State n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => g ⬝ᵥ v
      map_add' := fun v w => dotProduct_add g v w
      map_smul' := fun c v => dotProduct_smul c g v }

theorem gradCLM_apply {n : ℕ} (g v : State n) : gradCLM g v = g ⬝ᵥ v := rfl

/-- A GENERIC system on `Fin n → ℝ`: energy and entropy with their gradients, and operators at every state that
    satisfy the GENERIC conditions there. -/
structure GenericSystem (n : ℕ) where
  E : State n → ℝ
  S : State n → ℝ
  gradE : State n → State n
  gradS : State n → State n
  L : State n → Matrix (Fin n) (Fin n) ℝ
  M : State n → Matrix (Fin n) (Fin n) ℝ
  hasGradE : ∀ x, HasFDerivAt E (gradCLM (gradE x)) x
  hasGradS : ∀ x, HasFDerivAt S (gradCLM (gradS x)) x
  generic : ∀ x, GenericAt (L x) (M x) (gradE x) (gradS x)

/-- A trajectory of a GENERIC system: ẋ(t) = L·∇E + M·∇S at x(t), for every t. -/
structure GenericTrajectory {n : ℕ} (G : GenericSystem n) where
  x : ℝ → State n
  flow : ∀ t, HasDerivAt x (genericField (G.L (x t)) (G.M (x t)) (G.gradE (x t)) (G.gradS (x t))) t

theorem energy_hasDerivAt {n : ℕ} {G : GenericSystem n} (γ : GenericTrajectory G) (t : ℝ) :
    HasDerivAt (G.E ∘ γ.x) 0 t := by
  have h := (G.hasGradE (γ.x t)).comp_hasDerivAt t (γ.flow t)
  rwa [gradCLM_apply, energy_rate_zero (G.generic (γ.x t))] at h

theorem entropy_hasDerivAt {n : ℕ} {G : GenericSystem n} (γ : GenericTrajectory G) (t : ℝ) :
    HasDerivAt (G.S ∘ γ.x) ((G.gradS (γ.x t)) ⬝ᵥ
      genericField (G.L (γ.x t)) (G.M (γ.x t)) (G.gradE (γ.x t)) (G.gradS (γ.x t))) t := by
  have h := (G.hasGradS (γ.x t)).comp_hasDerivAt t (γ.flow t)
  rwa [gradCLM_apply] at h

/-- **Energy is conserved** along every GENERIC trajectory. -/
theorem generic_energy_const {n : ℕ} {G : GenericSystem n} (γ : GenericTrajectory G) (t₀ t₁ : ℝ) :
    G.E (γ.x t₁) = G.E (γ.x t₀) := by
  have hd : Differentiable ℝ (G.E ∘ γ.x) := fun t => (energy_hasDerivAt γ t).differentiableAt
  have hc := is_const_of_deriv_eq_zero hd fun t => (energy_hasDerivAt γ t).deriv
  exact hc t₁ t₀

/-- **Entropy does not decrease** along every GENERIC trajectory. -/
theorem generic_entropy_monotone {n : ℕ} {G : GenericSystem n} (γ : GenericTrajectory G) :
    Monotone (G.S ∘ γ.x) := by
  have hd : Differentiable ℝ (G.S ∘ γ.x) := fun t => (entropy_hasDerivAt γ t).differentiableAt
  refine monotone_of_deriv_nonneg hd fun t => ?_
  rw [(entropy_hasDerivAt γ t).deriv]
  exact entropy_rate_nonneg (G.generic (γ.x t))

/-- The free energy ψ = E − T·S at reservoir temperature `T`. -/
def freeEnergyAt {n : ℕ} (G : GenericSystem n) (T : ℝ) (x : State n) : ℝ := G.E x - T * G.S x

/-- At a reservoir temperature T ≥ 0 the free energy E − T·S does not rise along a GENERIC trajectory. -/
theorem generic_freeEnergy_descent {n : ℕ} {G : GenericSystem n} (γ : GenericTrajectory G) {T : ℝ}
    (hT : 0 ≤ T) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) :
    freeEnergyAt G T (γ.x t₁) ≤ freeEnergyAt G T (γ.x t₀) := by
  have hE := generic_energy_const γ t₀ t₁
  have hS : G.S (γ.x t₀) ≤ G.S (γ.x t₁) := generic_entropy_monotone γ ht
  unfold freeEnergyAt
  nlinarith [mul_le_mul_of_nonneg_left hS hT]

/-- **Bridge to the second law**: a GENERIC step from t₀ to t₁ ≥ t₀, read at a reservoir temperature T ≥ 0 with the
    free energy E − T·S and endpoint densities that meet the mass condition, is a `.transition` instance of
    `SecondLaw`. The temperature and the mass condition are the two hypotheses GENERIC itself does not supply. -/
theorem generic_secondLaw {n : ℕ} {G : GenericSystem n} (γ : GenericTrajectory G) {T : ℝ} (hT : 0 ≤ T)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (ρ₀ ρ₁ : ℝ)
    (hm : CoreMassCond ℝ RealThermodynamicState ⟨ρ₀, freeEnergyAt G T (γ.x t₀)⟩
      ⟨ρ₁, freeEnergyAt G T (γ.x t₁)⟩) :
    SecondLawₚ .transition
      (.thermodynamic ⟨ρ₀, freeEnergyAt G T (γ.x t₀)⟩ ⟨ρ₁, freeEnergyAt G T (γ.x t₁)⟩) :=
  ⟨hm, generic_freeEnergy_descent γ hT ht⟩

end UMST.Generic
