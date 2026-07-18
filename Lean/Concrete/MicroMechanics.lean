/-
  UMST-Formal: MicroMechanics.lean
  Lean 4 — B1 continuum L1b: scalar Mori–Tanaka elastic-base witness.

  Mirrors `energy.rs` `psi_elastic_base_domain` (slice-1 scalar ℚ reduction):
    E_eff = E₀ · (1 − d)²          (`effective_modulus_pa`)
    ψ_elastic_base = −½ · E_eff · ε²

  Model choice **A_MT_scalar:** the `(1 − d)²` degradation law is declared here as the
  B1 scalar reduction — not derived from tensor Mori–Tanaka homogenization.
  E₀ provenance (`blended_youngs_pa`) is external until L1c `VinetPartition`.

  Proof status (L1b D1–D7): core definitions, monotonicity lemmas, `MicroMechanicsState`
  witness + gate fragment.  Zero sorry.  No `[proved]` catalog export without operator.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic
import Compat.Gate

namespace UMST

open Rat

-- ================================================================
-- SECTION 1: Rust-aligned damage domain
-- ================================================================

/-- Maximum damage scalar (matches Rust `DAMAGE_D_MAX = 0.99`). -/
def damageDMax : ℚ := 99 / 100

lemma damageDMax_pos : 0 < damageDMax := by norm_num [damageDMax]

lemma damageDMax_le_one : damageDMax ≤ 1 := by norm_num [damageDMax]

/-- Validated damage interval d ∈ [0, `damageDMax`] — mirrors `PsiElDomain` clamp. -/
def damageAdmissible (d : ℚ) : Prop :=
  0 ≤ d ∧ d ≤ damageDMax

lemma damageAdmissible_zero : damageAdmissible 0 := by
  constructor <;> norm_num [damageDMax]

lemma damageAdmissible_one_sub_nonneg {d : ℚ} (hd : damageAdmissible d) :
    0 ≤ 1 - d := by
  linarith [hd.2, damageDMax_le_one]

lemma damageAdmissible_one_sub_le_one {d : ℚ} (hd : damageAdmissible d) :
    1 - d ≤ 1 := by linarith [hd.1]

-- ================================================================
-- SECTION 2: Effective modulus — E₀ · (1 − d)²  (A_MT_scalar)
-- ================================================================

/-- Scalar effective modulus — mirrors Rust `effective_modulus_pa`. -/
noncomputable def e_eff_mt (e0 d : ℚ) : ℚ :=
  e0 * (1 - d) ^ 2

/-- MT-1: effective modulus is non-negative when E₀ ≥ 0 and damage is admissible. -/
theorem e_eff_mt_nonneg {e0 d : ℚ} (he0 : 0 ≤ e0) (_hd : damageAdmissible d) :
    0 ≤ e_eff_mt e0 d := by
  unfold e_eff_mt
  exact mul_nonneg he0 (sq_nonneg (1 - d))

/-- MT-3: intact material recovers E₀ at zero damage. -/
theorem e_eff_mt_at_zero (e0 : ℚ) : e_eff_mt e0 0 = e0 := by
  unfold e_eff_mt
  simp

/-- Effective modulus at maximum admissible damage. -/
theorem e_eff_mt_at_max (e0 : ℚ) :
    e_eff_mt e0 damageDMax = e0 * (1 / 100) ^ 2 := by
  unfold e_eff_mt damageDMax
  norm_num

/-- Key softening factor: (1 − d₂)² ≤ (1 − d₁)² when d₁ ≤ d₂ on the admissible box. -/
private lemma one_sub_sq_antitone {d₁ d₂ : ℚ}
    (_hd₁ : damageAdmissible d₁) (hd₂ : damageAdmissible d₂) (hd : d₁ ≤ d₂) :
    (1 - d₂) ^ 2 ≤ (1 - d₁) ^ 2 := by
  have hsub : 1 - d₂ ≤ 1 - d₁ := by linarith
  exact pow_le_pow_left₀ (damageAdmissible_one_sub_nonneg hd₂) hsub 2

/-- MT-2: effective modulus is antitone in damage at fixed E₀ ≥ 0. -/
theorem e_eff_mt_antitone_in_d {e0 d₁ d₂ : ℚ}
    (he0 : 0 ≤ e0) (hd₁ : damageAdmissible d₁) (hd₂ : damageAdmissible d₂)
    (hd : d₁ ≤ d₂) :
    e_eff_mt e0 d₂ ≤ e_eff_mt e0 d₁ := by
  unfold e_eff_mt
  exact mul_le_mul_of_nonneg_left (one_sub_sq_antitone hd₁ hd₂ hd) he0

-- ================================================================
-- SECTION 3: ψ_elastic_base — M1-negative elastic summand
-- ================================================================

/-- `ψ_elastic_base` on validated scalar domain — mirrors `psi_elastic_base_domain`. -/
noncomputable def psi_elastic_base (epsilon d e0 : ℚ) : ℚ :=
  -((1 / 2) * e_eff_mt e0 d * epsilon ^ 2)

private lemma psi_elastic_base_factor_nonneg {epsilon d e0 : ℚ}
    (he0 : 0 ≤ e0) (hd : damageAdmissible d) :
    0 ≤ (1 / 2) * e_eff_mt e0 d * epsilon ^ 2 := by
  have heff := e_eff_mt_nonneg (e0 := e0) (d := d) he0 hd
  exact mul_nonneg (mul_nonneg (by norm_num) heff) (sq_nonneg epsilon)

/-- MT-4: M1-negative convention — ψ ≤ 0 when E₀ ≥ 0 and damage is admissible. -/
theorem psi_elastic_base_nonpos {epsilon d e0 : ℚ}
    (he0 : 0 ≤ e0) (hd : damageAdmissible d) :
    psi_elastic_base epsilon d e0 ≤ 0 := by
  unfold psi_elastic_base
  exact neg_nonpos.mpr (psi_elastic_base_factor_nonneg (epsilon := epsilon) (d := d) (e0 := e0) he0 hd)

/-- ψ vanishes at zero strain regardless of damage. -/
theorem psi_elastic_base_eq_zero_at_zero_strain (d e0 : ℚ) :
    psi_elastic_base 0 d e0 = 0 := by
  unfold psi_elastic_base
  simp

/-- ψ recovers the intact elastic energy density at zero damage. -/
theorem psi_elastic_base_at_zero_damage {epsilon e0 : ℚ} :
    psi_elastic_base epsilon 0 e0 = -(1 / 2) * e0 * epsilon ^ 2 := by
  unfold psi_elastic_base
  simp [e_eff_mt_at_zero]

/-- MT-5: elastic stored energy softens with damage at fixed ε, E₀ ≥ 0
    (|ψ| antitone in d; ψ monotone toward 0 since ψ ≤ 0). -/
theorem psi_elastic_base_antitone_in_d {epsilon d₁ d₂ e0 : ℚ}
    (he0 : 0 ≤ e0) (hd₁ : damageAdmissible d₁) (hd₂ : damageAdmissible d₂)
    (hd : d₁ ≤ d₂) :
    psi_elastic_base epsilon d₁ e0 ≤ psi_elastic_base epsilon d₂ e0 := by
  unfold psi_elastic_base
  have heff := e_eff_mt_antitone_in_d (e0 := e0) (d₁ := d₁) (d₂ := d₂) he0 hd₁ hd₂ hd
  have hfactor_nonneg : 0 ≤ (1 / 2) * epsilon ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg epsilon)
  have hinner :
      (1 / 2) * e_eff_mt e0 d₂ * epsilon ^ 2 ≤ (1 / 2) * e_eff_mt e0 d₁ * epsilon ^ 2 := by
    calc
      (1 / 2) * e_eff_mt e0 d₂ * epsilon ^ 2
          = (1 / 2) * epsilon ^ 2 * e_eff_mt e0 d₂ := by ring
      _ ≤ (1 / 2) * epsilon ^ 2 * e_eff_mt e0 d₁ :=
        mul_le_mul_of_nonneg_left heff hfactor_nonneg
      _ = (1 / 2) * e_eff_mt e0 d₁ * epsilon ^ 2 := by ring
  exact neg_le_neg hinner

/-- Combined Helmholtz + elastic-base free energy at scalar damage. -/
noncomputable def microMechanicsEnergy (epsilon d e0 α : ℚ) : ℚ :=
  helmholtz α + psi_elastic_base epsilon d e0

/-- Elastic-base contribution softens when damage advances at fixed ε, E₀, α. -/
theorem microMechanicsEnergy_softens_in_damage {epsilon d₁ d₂ e0 α : ℚ}
    (he0 : 0 ≤ e0) (hd₁ : damageAdmissible d₁) (hd₂ : damageAdmissible d₂)
    (hd : d₁ ≤ d₂) :
    microMechanicsEnergy epsilon d₁ e0 α ≤ microMechanicsEnergy epsilon d₂ e0 α := by
  unfold microMechanicsEnergy
  exact add_le_add_left (psi_elastic_base_antitone_in_d (epsilon := epsilon) (d₁ := d₁)
    (d₂ := d₂) (e0 := e0) he0 hd₁ hd₂ hd) _

-- ================================================================
-- SECTION 4: MicroMechanicsState — gate witness (MT-6–MT-7)
-- ================================================================

/-- A state satisfies the micro-mechanics elastic-base model at parameters `(e0, ε, d)`
    if its free energy equals the Helmholtz base plus the elastic-base summand.
    Damage `d` is carried as an external parameter (not in `ThermodynamicState`). -/
def MicroMechanicsState (s : ThermodynamicState) (e0 epsilon d : ℚ) : Prop :=
  s.freeEnergy = helmholtz s.hydration + psi_elastic_base epsilon d e0

/-- For micro-mechanics-consistent states, forward damage implies the elastic summand
    softens (ψ antitone in d) — scalar witness for continuum damage mechanics. -/
theorem ψSofteningMicroMechanics
    (_s₁ _s₂ : ThermodynamicState) (e0 epsilon d₁ d₂ : ℚ)
    (_h₁ : MicroMechanicsState _s₁ e0 epsilon d₁)
    (_h₂ : MicroMechanicsState _s₂ e0 epsilon d₂)
    (he0 : 0 ≤ e0)
    (hd₁ : damageAdmissible d₁)
    (hd₂ : damageAdmissible d₂)
    (hd : d₁ ≤ d₂) :
    psi_elastic_base epsilon d₁ e0 ≤ psi_elastic_base epsilon d₂ e0 :=
  psi_elastic_base_antitone_in_d (epsilon := epsilon) (d₁ := d₁) (d₂ := d₂) (e0 := e0)
    he0 hd₁ hd₂ hd

/-- Gate fragment: micro-mechanics-consistent states admit a transition when mass,
    hydration, strength, and global dissipation hypotheses hold (as in `PowersState`).
    Full Clausius–Duhem closure with coupled `ψ_damage_release` is **L1d**. -/
theorem microMechanicsStateAdmissible
    (old new : ThermodynamicState) (e0 epsilon d_old d_new : ℚ)
    (_ho : MicroMechanicsState old e0 epsilon d_old)
    (_hn : MicroMechanicsState new e0 epsilon d_new)
    (hα : old.hydration ≤ new.hydration)
    (hm : |new.density - old.density| ≤ δMass)
    (h_psi : old.hydration ≤ new.hydration → new.freeEnergy ≤ old.freeEnergy)
    (h_fc : old.hydration ≤ new.hydration → old.strength ≤ new.strength) :
    Admissible old new :=
  Admissible.mk old new hm (h_psi hα) hα (h_fc hα)

end UMST
