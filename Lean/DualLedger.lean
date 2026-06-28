/-
  UMST-Formal: DualLedger.lean
  Lean 4 — Dual energy ledger non-negativity (foundation Phase: dual ledger).

  Index: `PROOF-STATUS.md` § Lean 4 Layer Summary.

  Runtime correspondence:
    `umst-manifold/src/runtime/gate/cold_wire.rs` — `SpineEventCost { compute_j, material_j }`
    with axiom anchor `physicalSecondLaw`. The runtime asserts both rails ≥ 0 on
    sampled values (`spine_event_dual_ledger_axiom_anchor`). This file proves the
    invariant *constructively* from the physical model:

      - Compute rail (Landauer): cost = (k_B·T·ln2) · bits, a product of
        non-negative factors ⇒ ≥ 0.
      - Material rail (Clausius–Duhem): D_int = ρ · (ψ_old − ψ_new), non-negative
        when ρ ≥ 0 and the gate's Clausius–Duhem condition ψ_new ≤ ψ_old holds.
      - Total ledger = compute + material ≥ 0.

  This moves "dual-ledger ≥ 0" from RUNTIME-ONLY to PROVEN(Lean).
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace UMST

-- ================================================================
-- SECTION 1: Compute rail (Landauer)
-- ================================================================

/-- Landauer compute cost: `(k_B · T · ln2) · bits`.
    `kT_ln2` packs the non-negative `k_B·T·ln2` prefactor (joules/bit). -/
def landauerComputeCost (kT_ln2 bits : ℚ) : ℚ := kT_ln2 * bits

/-- The compute rail is non-negative for non-negative prefactor and bit count. -/
theorem landauerComputeCost_nonneg {kT_ln2 bits : ℚ}
    (hk : 0 ≤ kT_ln2) (hb : 0 ≤ bits) :
    0 ≤ landauerComputeCost kT_ln2 bits := by
  unfold landauerComputeCost
  exact mul_nonneg hk hb

-- ================================================================
-- SECTION 2: Material rail (Clausius–Duhem dissipation)
-- ================================================================

/-- Internal dissipation `D_int = ρ · (ψ_old − ψ_new)` (host joule units). -/
def materialDissipation (ρ ψ_old ψ_new : ℚ) : ℚ := ρ * (ψ_old - ψ_new)

/-- The material rail is non-negative under non-negative density and the
    gate's Clausius–Duhem condition `ψ_new ≤ ψ_old` (free energy non-increasing). -/
theorem materialDissipation_nonneg {ρ ψ_old ψ_new : ℚ}
    (hρ : 0 ≤ ρ) (hcd : ψ_new ≤ ψ_old) :
    0 ≤ materialDissipation ρ ψ_old ψ_new := by
  unfold materialDissipation
  have hΔ : 0 ≤ ψ_old - ψ_new := by linarith
  exact mul_nonneg hρ hΔ

-- ================================================================
-- SECTION 3: Dual ledger
-- ================================================================

/-- Dual energy ledger: distinct compute and material rails (mirrors the runtime
    `SpineEventCost`). -/
structure DualLedger where
  computeJ : ℚ
  materialJ : ℚ
  deriving Repr

/-- Total ledger cost = compute rail + material rail. -/
def DualLedger.total (l : DualLedger) : ℚ := l.computeJ + l.materialJ

/-- **Dual-ledger non-negativity (rails).** Both rails ≥ 0 ⇒ total ≥ 0. -/
theorem dualLedger_total_nonneg (l : DualLedger)
    (hc : 0 ≤ l.computeJ) (hm : 0 ≤ l.materialJ) :
    0 ≤ l.total := by
  unfold DualLedger.total
  linarith

/-- **Dual-ledger non-negativity (constructive).** Built from the physical model:
    a non-negative Landauer compute rail and a Clausius–Duhem material rail give a
    ledger whose total is non-negative — the `physicalSecondLaw` anchor. -/
theorem dualLedger_nonneg_of_physical
    {kT_ln2 bits ρ ψ_old ψ_new : ℚ}
    (hk : 0 ≤ kT_ln2) (hb : 0 ≤ bits)
    (hρ : 0 ≤ ρ) (hcd : ψ_new ≤ ψ_old) :
    0 ≤ (DualLedger.mk (landauerComputeCost kT_ln2 bits)
                       (materialDissipation ρ ψ_old ψ_new)).total :=
  dualLedger_total_nonneg _
    (landauerComputeCost_nonneg hk hb)
    (materialDissipation_nonneg hρ hcd)

end UMST
