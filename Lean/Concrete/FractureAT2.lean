-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
/-
  UMST-Formal: Concrete/FractureAT2.lean

  AT2 fracture at a material point (Bourdin, Francfort and Marigo 2000; Miehe, Hofacker and Welschinger 2010; Pham
  and Marigo) as instances of the one predicate `SecondLaw`, with the crack-surface density as dissipation:

    stored energy        ψ(ε, φ) = g(φ) ψ_e(ε),   g(φ) = (1 − φ)²,   ψ_e ≥ 0
    crack energy spent   D_crack(φ → φ') = (G_c / (2 l)) (φ'² − φ²)
    total energy         E(ε, φ) = ψ(ε, φ) + (G_c / (2 l)) φ²

  `G_c` and `l` enter only through `c = G_c / l > 0`. `E` is convex in `φ` at fixed strain and convex in `ε` when
  `ψ_e` is, but not jointly convex, so `ConvexPhiDissipation.gsmCartridge_passive_secondLaw` does not apply; the passive
  route (`Convex.PassiveRoute`) needs no convexity, only `Δψ + D ≤ 0` with `D ≥ 0`, and that is what a damage step
  gives:

  * the irreversible alternate-minimisation step at fixed strain, `φ' = max(φ, φ*)` with
    `φ* = 2 ψ_e / (2 ψ_e + c)`, stays in `[0, 1]` and minimises `E(ε, ·)` over `[φ, 1]` (`at2_damage_update`);
  * `E` does not increase on the whole domain `[0, 1]`, with no cut-off at `(3 − √3)/6` (`at2_energy_nonincreasing`);
  * the step is a `SecondLaw` `.transition` through the passive route, the stored part `g(φ) ψ_e` falling and the crack
    energy `D_crack ≥ 0` (by irreversibility) spent (`at2_damage_step_secondLaw`);
  * for any irreversible step the degraded elastic energy released, `ψ_e (g(φ) − g(φ'))`, is non-negative, and the
    passive inequality `Δψ + D_crack ≤ 0` holds exactly when that release covers the crack energy created: the Griffith
    criterion (`at2_degradation_release_nonneg`, `at2_griffith_iff`).

  The two readings agree: `Δψ + D_crack = E(ε, φ') − E(ε, φ)`, so the passive inequality with the crack energy spent is
  the total energy not rising (`at2_balance_eq_total`).

  **Typed absence: the loading step.** A step that raises the strain energy at fixed damage, with work supplied by the
  load, raises the stored energy; the `.transition` case carries no input-work term and refuses it
  (`at2_loading_refused`). The missing term is the supplied power `W_in` of `ΔF ≤ W_in + k_B T I`; a loading step is a
  powered transition, which this module does not state.

  Zero `axiom`, zero `sorry`.
-/

import Convex.PassiveRoute

open UMST.ProcessFamily UMST.Core UMST.Real UMST.Convex.PassiveRoute

namespace UMST.Concrete.FractureAT2

section Field

variable {α : Type*} [LinearOrderedField α]

/-- The AT2 degradation `g(φ) = (1 − φ)²`. -/
def degradation (φ : α) : α := (1 - φ) ^ 2

/-- The stored energy `g(φ) ψ_e`. -/
def stored (ψe φ : α) : α := degradation φ * ψe

/-- The crack energy spent by a damage step: `(c/2)(φ'² − φ²)`, `c = G_c / l`. -/
def crackSpent (c φ φ' : α) : α := c / 2 * (φ' ^ 2 - φ ^ 2)

/-- The total energy `E = g(φ) ψ_e + (c/2) φ²`. -/
def total (c ψe φ : α) : α := stored ψe φ + c / 2 * φ ^ 2

/-- The unconstrained minimiser `φ* = 2 ψ_e / (2 ψ_e + c)`. -/
def damageTarget (c ψe : α) : α := 2 * ψe / (2 * ψe + c)

/-- The irreversible alternate-minimisation damage step at fixed strain. -/
def damageUpdate (c ψe φ : α) : α := max φ (damageTarget c ψe)

theorem damageTarget_mem {c ψe : α} (hc : 0 < c) (hψ : 0 ≤ ψe) :
    0 ≤ damageTarget c ψe ∧ damageTarget c ψe < 1 := by
  have hd : 0 < 2 * ψe + c := by linarith
  unfold damageTarget
  refine ⟨div_nonneg (by linarith) hd.le, ?_⟩
  rw [div_lt_one hd]; linarith

/-- `E` is a parabola in `φ` with vertex `φ*`: `E(x) = E(φ*) + (ψ_e + c/2)(x − φ*)²`. -/
theorem total_vertex {c ψe : α} (hc : 0 < c) (hψ : 0 ≤ ψe) (x : α) :
    total c ψe x = total c ψe (damageTarget c ψe) + (ψe + c / 2) * (x - damageTarget c ψe) ^ 2 := by
  have hd : (2 * ψe + c) ≠ 0 := by linarith
  unfold total stored degradation damageTarget
  field_simp
  ring

/-- **The damage step** stays in `[0, 1]`, never heals, and minimises `E(ε, ·)` over `[φ, 1]`. -/
theorem at2_damage_update {c ψe φ : α} (hc : 0 < c) (hψ : 0 ≤ ψe) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    φ ≤ damageUpdate c ψe φ ∧ 0 ≤ damageUpdate c ψe φ ∧ damageUpdate c ψe φ ≤ 1 ∧
      ∀ x, φ ≤ x → x ≤ 1 → total c ψe (damageUpdate c ψe φ) ≤ total c ψe x := by
  obtain ⟨ht0, ht1⟩ := damageTarget_mem hc hψ
  have ha : 0 ≤ ψe + c / 2 := by linarith
  refine ⟨le_max_left _ _, le_trans h0 (le_max_left _ _), max_le h1 ht1.le, ?_⟩
  intro x hx _
  rw [total_vertex hc hψ x, total_vertex hc hψ (damageUpdate c ψe φ)]
  have key : (damageUpdate c ψe φ - damageTarget c ψe) ^ 2 ≤ (x - damageTarget c ψe) ^ 2 := by
    unfold damageUpdate
    rcases le_total φ (damageTarget c ψe) with hφ | hφ
    · rw [max_eq_right hφ, sub_self]; nlinarith [sq_nonneg (x - damageTarget c ψe)]
    · rw [max_eq_left hφ]
      have h1' : 0 ≤ φ - damageTarget c ψe := by linarith
      have h2' : φ - damageTarget c ψe ≤ x - damageTarget c ψe := by linarith
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key ha]

/-- **The total energy does not increase** on the whole domain `[0, 1]`. -/
theorem at2_energy_nonincreasing {c ψe φ : α} (hc : 0 < c) (hψ : 0 ≤ ψe) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    total c ψe (damageUpdate c ψe φ) ≤ total c ψe φ :=
  (at2_damage_update hc hψ h0 h1).2.2.2 φ le_rfl h1

/-- The two readings agree: the passive balance with the crack energy spent is the change of total energy. -/
theorem at2_balance_eq_total (c ψe φ φ' : α) :
    (stored ψe φ' - stored ψe φ) + crackSpent c φ φ' = total c ψe φ' - total c ψe φ := by
  unfold total crackSpent; ring

/-- The crack energy of an irreversible step is spent, never recovered. -/
theorem crackSpent_nonneg {c φ φ' : α} (hc : 0 < c) (h0 : 0 ≤ φ) (hφ : φ ≤ φ') : 0 ≤ crackSpent c φ φ' := by
  unfold crackSpent
  have : φ ^ 2 ≤ φ' ^ 2 := by nlinarith
  have hc2 : 0 ≤ c / 2 := by linarith
  nlinarith

/-- **Release of degraded elastic energy** by any irreversible step in `[0, 1]`: `ψ_e (g(φ) − g(φ')) ≥ 0`. -/
theorem at2_degradation_release_nonneg {ψe φ φ' : α} (hψ : 0 ≤ ψe) (hφ : φ ≤ φ') (h1 : φ' ≤ 1) :
    0 ≤ stored ψe φ - stored ψe φ' := by
  unfold stored degradation
  have : (1 - φ') ^ 2 ≤ (1 - φ) ^ 2 := by nlinarith
  nlinarith

/-- **Griffith**: the passive inequality with the crack energy spent holds exactly when the released elastic energy
    covers the crack energy created. -/
theorem at2_griffith_iff (c ψe φ φ' : α) :
    (stored ψe φ' - stored ψe φ) + crackSpent c φ φ' ≤ 0 ↔ crackSpent c φ φ' ≤ stored ψe φ - stored ψe φ' := by
  constructor <;> intro h <;> linarith

end Field

/-- **The damage step is a `SecondLaw` transition** through the passive route: at unchanged density the stored energy
    falls by at least the crack energy spent, which is non-negative. -/
theorem at2_damage_step_secondLaw {c ψe φ ρ : ℝ} (hc : 0 < c) (hψ : 0 ≤ ψe) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    SecondLaw .transition
      (.thermodynamic ⟨ρ, stored ψe φ⟩ ⟨ρ, stored ψe (damageUpdate c ψe φ)⟩) := by
  have hm : CoreMassCond ℝ RealThermodynamicState ⟨ρ, stored ψe φ⟩ ⟨ρ, stored ψe (damageUpdate c ψe φ)⟩ := by
    show |ρ - ρ| ≤ δMass (K := ℝ)
    rw [sub_self, abs_zero]
    exact ThermodynamicScalar.δMass_nonneg
  have hD := crackSpent_nonneg hc h0 (at2_damage_update hc hψ h0 h1).1
  refine passive_inequality_secondLaw hm hD ?_
  show (stored ψe (damageUpdate c ψe φ) - stored ψe φ) + crackSpent c φ (damageUpdate c ψe φ) ≤ 0
  rw [at2_balance_eq_total]
  linarith [at2_energy_nonincreasing hc hψ h0 h1]

/-- **Typed absence, the loading step**: raising the strain energy at fixed damage below full damage raises the stored
    energy, which the `.transition` case refuses; the missing term is the supplied power `W_in`. -/
theorem at2_loading_refused {ψe ψe' φ ρ ρ' : ℝ} (h1 : φ < 1) (hload : ψe < ψe') :
    ¬ SecondLaw .transition (.thermodynamic ⟨ρ, stored ψe φ⟩ ⟨ρ', stored ψe' φ⟩) := by
  intro hs
  have hf : stored ψe' φ ≤ stored ψe φ := hs.2
  unfold stored degradation at hf
  have hg : 0 < (1 - φ) ^ 2 := by have : 0 < 1 - φ := by linarith
                                  positivity
  nlinarith

end UMST.Concrete.FractureAT2
