-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  Track R programme R1 — Gibbs minimiser uniqueness obligation (`R1_MINIMISER_UNIQUE_STRICT`).
  typed_absence: full cement thermodynamics proof deferred; R1-CEMENT-THERMO-SOLVE-COMBINATOR landed STEER_20260930T2226 wave 18 (Track C stub).

  Scalar strict-convex witness: squared distance to `c` has a unique global minimiser.
  Pins the convex-program uniqueness lemma used by `schema_track_model_spec.json`; not a benchmark pass.
-/

import Mathlib.Data.Real.Basic

namespace CementThermo.R1

/-- Obligation id `R1_MINIMISER_UNIQUE_STRICT` — uniqueness for strict convex `fun z => (z - c)^2`. -/
theorem cement_thermo_minimiser_unique_strict (c : ℝ) {x y : ℝ}
    (hx : ∀ z : ℝ, (x - c) ^ 2 ≤ (z - c) ^ 2)
    (hy : ∀ z : ℝ, (y - c) ^ 2 ≤ (z - c) ^ 2) : x = y := by
  have hx0 : (x - c) ^ 2 ≤ 0 := by simpa using hx c
  have hy0 : (y - c) ^ 2 ≤ 0 := by simpa using hy c
  have hxc : x = c := by
    have h : (x - c) ^ 2 = 0 := le_antisymm hx0 (sq_nonneg (x - c))
    simpa [sub_eq_zero] using (sq_eq_zero_iff.mp h)
  have hyc : y = c := by
    have h : (y - c) ^ 2 = 0 := le_antisymm hy0 (sq_nonneg (y - c))
    simpa [sub_eq_zero] using (sq_eq_zero_iff.mp h)
  rw [hxc, hyc]

end CementThermo.R1
