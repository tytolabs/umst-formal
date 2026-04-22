/-
  UMST-Formal: EtaCog.lean

  MI-per-Joule frugality scalar **η_cog** (cockpit metric schema, COCKPIT_DESIGN_BRIEF §5;
  egoffplan §14bis.b row N3), dignity-weighted with a **single-bit Landauer floor** in the
  denominator (encoding **(i)**):

  `η_cog d c = d.value * c.delta_mi_bits / (c.delta_energy_j + landauer_joules_per_bit c.T)`.

  **Denominator choice (i) vs (ii).** We use **(i)** `ΔE + k_B T ln 2` (one floor quantum per step
  in the denominator), **not** `ΔE + (k_B T ln 2) * ΔMI`, so the formula matches the published
  cockpit line `η_cog = dignity · ΔMI / (ΔE + k_B T ln 2)`. Large `ΔMI` with tiny `ΔE` can make
  η_cog large in principle; the **dignity** layer (N3-FPD-a) is the primary guard against treating
  sub-Landauer-per-claimed-bit work as epistemically productive — see `eta_cog_frozen_under_dishonest_claim`.

  **Parametricity (operator Q4).** Every `theorem` below is generic over `d : Dignity` and uses
  only `d.value`, `d.nonneg`, `d.bounded` — **no** literal `10` / `d_max` in theorem *statements*.

  Imports: `Dignity` (Landauer-gated step + claims), `LandauerEinsteinBridge` only transitively
  via `Dignity` for the floor; double-slit `LandauerBound.lean` is not in this lake closure —
  PROOF-STATUS cross-references it narratively as the ecosystem anchor for the same SI scale.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Dignity

set_option linter.dupNamespace false

open Classical

namespace UMST.Formal.EtaCog

open UMST.Formal.Dignity

/-- One cockpit step: nonnegative MI and energy budgets, positive temperature for the floor. -/
structure EtaCogClaim where
  /-- Bath / device temperature (K) for the Landauer denominator term. -/
  T              : ℝ
  hT             : 0 < T
  delta_mi_bits  : ℝ
  delta_energy_j : ℝ
  hmi            : 0 ≤ delta_mi_bits
  he             : 0 ≤ delta_energy_j

/-- Denominator `ΔE + k_B T ln 2` (case **(i)**). -/
noncomputable def etaDenom (c : EtaCogClaim) : ℝ :=
  c.delta_energy_j + landauer_joules_per_bit c.T

lemma etaDenom_pos (c : EtaCogClaim) : 0 < etaDenom c := by
  have hL : 0 < landauer_joules_per_bit c.T := landauer_joules_per_bit_pos c.hT
  exact add_pos_of_nonneg_of_pos c.he hL

/-- η_cog = dignity · ΔMI / (ΔE + Landauer floor). -/
noncomputable def eta_cog (d : Dignity) (c : EtaCogClaim) : ℝ :=
  d.value * c.delta_mi_bits / etaDenom c

theorem eta_cog_nonneg (d : Dignity) (c : EtaCogClaim) : 0 ≤ eta_cog d c := by
  unfold eta_cog
  have hd : 0 ≤ d.value := d.nonneg
  have hmi : 0 ≤ c.delta_mi_bits := c.hmi
  have hnum : 0 ≤ d.value * c.delta_mi_bits := mul_nonneg hd hmi
  exact div_nonneg hnum (le_of_lt (etaDenom_pos c))

theorem eta_cog_bounded_when_delta_energy_zero (d : Dignity) (c : EtaCogClaim)
    (he : c.delta_energy_j = 0) :
    eta_cog d c = d.value * c.delta_mi_bits / landauer_joules_per_bit c.T := by
  simp [eta_cog, etaDenom, he]

theorem eta_cog_monotone_in_dignity (d₁ d₂ : Dignity) (c : EtaCogClaim) (hd : d₁.value ≤ d₂.value) :
    eta_cog d₁ c ≤ eta_cog d₂ c := by
  unfold eta_cog
  have hden : 0 < etaDenom c := etaDenom_pos c
  have hmi : 0 ≤ c.delta_mi_bits := c.hmi
  have h₁ : d₁.value * c.delta_mi_bits ≤ d₂.value * c.delta_mi_bits :=
    mul_le_mul_of_nonneg_right hd hmi
  exact div_le_div_of_nonneg_right h₁ (le_of_lt hden)

theorem eta_cog_monotone_in_mi (d : Dignity) (c₁ c₂ : EtaCogClaim) (hT : c₁.T = c₂.T)
    (hmi : c₁.delta_mi_bits ≤ c₂.delta_mi_bits) (he : c₁.delta_energy_j = c₂.delta_energy_j) :
    eta_cog d c₁ ≤ eta_cog d c₂ := by
  have hL : landauer_joules_per_bit c₁.T = landauer_joules_per_bit c₂.T := by rw [hT]
  have hden : etaDenom c₁ = etaDenom c₂ := by simp [etaDenom, he, hL]
  have hpos : 0 < etaDenom c₂ := etaDenom_pos c₂
  suffices h : d.value * c₁.delta_mi_bits / etaDenom c₂ ≤ d.value * c₂.delta_mi_bits / etaDenom c₂ by
    simpa [eta_cog, hden] using h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmi d.nonneg) (le_of_lt hpos)

theorem eta_cog_antitone_in_energy (d : Dignity) (c₁ c₂ : EtaCogClaim) (hT : c₁.T = c₂.T)
    (hmi : c₁.delta_mi_bits = c₂.delta_mi_bits) (he : c₂.delta_energy_j ≤ c₁.delta_energy_j) :
    eta_cog d c₁ ≤ eta_cog d c₂ := by
  unfold eta_cog etaDenom
  have hL : landauer_joules_per_bit c₁.T = landauer_joules_per_bit c₂.T := by rw [hT]
  rw [hmi]
  have hden_le : etaDenom c₂ ≤ etaDenom c₁ := by
    unfold etaDenom
    calc
      c₂.delta_energy_j + landauer_joules_per_bit c₂.T
          ≤ c₁.delta_energy_j + landauer_joules_per_bit c₂.T := add_le_add_right he _
      _ = c₁.delta_energy_j + landauer_joules_per_bit c₁.T := by rw [← hL]
  have ha : 0 ≤ d.value * c₂.delta_mi_bits := mul_nonneg d.nonneg c₂.hmi
  have hv₁ : 0 < etaDenom c₁ := etaDenom_pos c₁
  have hv₂ : 0 < etaDenom c₂ := etaDenom_pos c₂
  exact (div_le_div_iff₀ hv₁ hv₂).mpr (mul_le_mul_of_nonneg_left hden_le ha)

theorem eta_cog_frozen_under_dishonest_claim {T : ℝ} (hT : 0 < T) (d : Dignity) (dc : DignityClaim)
    (hh : ¬ honest_spend T dc) (ec : EtaCogClaim) (_hTe : ec.T = T) :
    eta_cog (dignity_step T hT d dc) ec = eta_cog d ec := by
  have hf : dignity_step T hT d dc = d := dignity_step_dishonest_eq hT d dc hh
  simp [eta_cog, hf]

theorem eta_cog_list_sum_nonneg (pairs : List (Dignity × EtaCogClaim)) :
    0 ≤ (List.map (fun p : Dignity × EtaCogClaim => eta_cog p.1 p.2) pairs).sum := by
  refine List.sum_nonneg ?_
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨⟨d, c⟩, -, rfl⟩ := hy
  exact eta_cog_nonneg d c

/-- Expected-value / mean over a nonempty list is well-defined and nonnegative. -/
theorem eta_cog_list_mean_nonneg (pairs : List (Dignity × EtaCogClaim)) (hn : pairs ≠ []) :
    0 ≤ (List.map (fun p => eta_cog p.1 p.2) pairs).sum / (pairs.length : ℝ) := by
  have hs : 0 ≤ (List.map (fun p => eta_cog p.1 p.2) pairs).sum := eta_cog_list_sum_nonneg pairs
  have hl : 0 < (pairs.length : ℝ) := by
    have h0 : 0 < pairs.length := List.length_pos_of_ne_nil hn
    exact_mod_cast h0
  exact div_nonneg hs (le_of_lt hl)

end UMST.Formal.EtaCog
