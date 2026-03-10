/-
  UMST-Formal: Helmholtz.lean
  Lean 4 — Concrete Helmholtz free-energy model and SDF interpretation.

  Mirrors Agda/Helmholtz.agda.  Imports Gate for ThermodynamicState and
  the abstract psiAntitone axiom; provides the concrete arithmetic witness
  for that axiom when the free-energy function is ψ(α) = −Q_hyd · α.

  Proof status: ALL theorems fully proved.  Zero sorry.

  Correspondence:
    HelmholtzState         │ Agda: HelmholtzState
    ψAntitoneHelmholtz      │ Agda: ψ-antitone-helmholtz
    helmholtzLinear        │ Agda: helmholtz-linear (postulate there, proved here)
    helmholtzGradientConst │ Agda: helmholtz-gradient-const (postulate, proved here)
-/

import UMST.Gate

namespace UMST

-- ================================================================
-- SECTION 1: HelmholtzState — States Satisfying the Concrete Model
-- ================================================================

/-- A ThermodynamicState "satisfies the Helmholtz model" if its
    freeEnergy field equals ψ(α) = −Q_hyd · α.
    This holds for states produced by `from_mix` in the Rust kernel. -/
def HelmholtzState (s : ThermodynamicState) : Prop :=
  s.freeEnergy = helmholtz s.hydration

-- ================================================================
-- SECTION 2: Concrete Witness for psiAntitone
-- ================================================================

/-- For Helmholtz-consistent states, forward hydration implies
    decreasing free energy.

    This is the concrete arithmetic witness for the abstract axiom
    `psiAntitone` in Gate.lean.  It shows the axiom is not arbitrary:
    it follows from the specific model ψ = −Q_hyd · α.

    Physical meaning: cement hydration is exothermic — each increment
    in α releases Q_hyd J/kg of heat, lowering ψ.  The gate's
    Clausius-Duhem check captures this exactly. -/
theorem ψAntitoneHelmholtz
    (s₁ s₂ : ThermodynamicState)
    (h₁ : HelmholtzState s₁)
    (h₂ : HelmholtzState s₂)
    (hα  : s₁.hydration ≤ s₂.hydration) :
    s₂.freeEnergy ≤ s₁.freeEnergy := by
  rw [h₂, h₁]
  exact helmholtzAntitone s₁.hydration s₂.hydration hα

-- ================================================================
-- SECTION 3: Helmholtz States are Admissible Under Forward Hydration
-- ================================================================

/-- For two Helmholtz-consistent states: if hydration advances and
    mass is conserved, the transition is admissible.
    The Clausius-Duhem condition follows from ψAntitoneHelmholtz;
    strength monotonicity requires the abstract fcMonotone axiom. -/
theorem helmholtzStateAdmissible
    (old new : ThermodynamicState)
    (ho  : HelmholtzState old)
    (hn  : HelmholtzState new)
    (hα  : old.hydration ≤ new.hydration)
    (hm  : |new.density - old.density| ≤ δMass) :
    Admissible old new :=
  ⟨hm, ψAntitoneHelmholtz old new ho hn hα, hα, fcMonotone old new hα⟩

-- ================================================================
-- SECTION 4: Linearity and Gradient (SDF / Eikonal Properties)
-- ================================================================
-- These correspond to the two postulates in Agda/Helmholtz.agda §6.
-- In Lean 4, both follow from `ring` since ψ is linear by definition.

/-- ψ is additive (ℚ-linear):
    ψ(α₁ + α₂) = ψ(α₁) + ψ(α₂).
    This is the formal statement that ψ is a group homomorphism
    (ℚ, +) → (ℚ, +), i.e., a linear signed distance function. -/
theorem helmholtzLinear (α₁ α₂ : ℚ) :
    helmholtz (α₁ + α₂) = helmholtz α₁ + helmholtz α₂ :=
  helmholtzAdditive α₁ α₂

/-- Discrete gradient of ψ is constant:
    ψ(α + ε) − ψ(α) = −Q_hyd · ε.

    SDF / Eikonal interpretation:
    ψ is a 1D signed distance function in hydration state space with
    constant gradient magnitude Q_hyd = 450 J/kg.  The Eikonal
    condition |∂ψ/∂α| = Q_hyd holds everywhere.

    Proof: direct from helmholtzGradient (proved in Gate.lean by ring). -/
theorem helmholtzGradientConst (α ε : ℚ) :
    helmholtz (α + ε) - helmholtz α = -(Q_hyd * ε) :=
  helmholtzGradient α ε

-- ================================================================
-- SECTION 5: Eikonal Condition — Gradient Direction and Admissibility
-- ================================================================

/-- The admissible transition direction is exactly the
    negative-gradient direction of ψ.

    ψ_new ≤ ψ_old
    ⟺  −Q_hyd · α_new ≤ −Q_hyd · α_old
    ⟺  α_old ≤ α_new    (since Q_hyd > 0)

    This shows the Clausius-Duhem condition and the hydration
    irreversibility condition are equivalent under the Helmholtz model. -/
theorem admissibleDirIsNegGrad
    (old new : ThermodynamicState)
    (ho : HelmholtzState old)
    (hn : HelmholtzState new) :
    new.freeEnergy ≤ old.freeEnergy ↔ old.hydration ≤ new.hydration := by
  rw [ho, hn]
  unfold helmholtz Q_hyd
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end UMST
