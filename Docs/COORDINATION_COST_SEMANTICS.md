# Coordination Cost — lower-bound semantics (Landauer floor)

**Status:** A7 formal scaffold @ 2026-07-18 — definitions + algebraic lemmas only.  
**Lean module:** [`Lean/CoordinationCost.lean`](../Lean/CoordinationCost.lean)  
**Rust SSOT:** `umst-arcs/crates/umst-arcs/src/coordination_cost.rs`

---

## 1. Reporting identity (not realized energy)

The MTP-Arc **Coordination Cost Identity** reports:

\[
\text{CoordCost}(A,B; T) = k_B \, T \, \ln 2 \cdot I(A{:}B)
\]

where \(I(A{:}B)\) is mutual information in **bits** and \(T\) is bath temperature in kelvin.

In Lean this is `UMST.CoordinationCost.coordinationSavingJoules`. In Rust it is
`coordination_saving_joules`. The quantity is a **Landauer floor projection** for honest
performance accounting — **not**:

- measured dissipation on a device,
- wall-clock speedup,
- a Core `gate<R>` admissibility witness,
- a business or decision outcome.

Label every UI / cert string that surfaces this number as **projection** or **floor**, never
**witness** (egoff `CoordinationReport` policy).

---

## 2. Layer alignment

| Layer | Artifact | Role |
|-------|----------|------|
| **Definitions** | `coordinationSavingJoules`, `landauerCostJoules` | SI joule reporting functor |
| **Bit / nat bridge** | `mutualInformationBits` | \(I_\text{bits} = I_\text{nats} / \ln 2\) |
| **Classical MI link** | `classical_measurement_floor_agrees` | Same floor as `ClassicalMeasurementCost.measurementEnergyLowerBound` |
| **Landauer bit scale** | `landauerBitEnergy` (`LandauerEinsteinBridge`) | One-bit floor at temperature \(T\) |
| **Thermodynamic bound** | `landauerBound` (`LandauerLaw`) | Erasure work ≥ \(T \ln 2\) (uses sole project axiom `physicalSecondLaw`) |
| **Operational orthogonality** | `kleisli_compose_preserves_admissibility` tests (Rust) | `coordination_saving` does not alter `gate<R>` |

---

## 3. What is proved in the scaffold

All of the following are machine-checked without new axioms or `sorry`:

- `coordinationSaving_eq_landauerCost` — alias coherence
- `coordinationSaving_zero` — zero MI ⇒ zero saving
- `coordinationSaving_linear` — linear in MI (bits)
- `coordinationSaving_one_bit` — one bit = `landauerBitEnergy T`
- `coordinationSaving_temp_scaling` — linear in \(T\)
- `zero_mi_zero_saving` — product joint ⇒ zero saving
- `classical_measurement_floor_agrees` — nats vs bits convention bridge

---

## 4. Open obligations (`OpenObligation`)

Indexed in Lean; **not** discharged with placeholder proofs.

| Constructor | Meaning | Blocked by |
|-------------|---------|------------|
| `joint_erasure_sub_additive` | Joint erasure of correlated registers cheaper than independent sum | Full erasure-process model + second-law packaging for composed registers |
| `finite_time_excess_bound` | Document excess dissipation above isothermal floor | Finite-time Landauer literature; engineering `excess_dissipation` field (A7-3+) |
| `epistemic_mi_witness` | Semantic / L10 MI separate from physical MI | `EpistemicCoordinationDraft` type split (A7-4) |

---

## 5. Honest boundary (cross-arc)

- **Physical MI fixtures only** until epistemic channel is type-split.
- **No M4 / executive % bump** on coordination joules alone.
- Money and decision arcs remain heuristic until gate-checked response families exist
  (`umst-arcs/FORMAL_ANCHOR.md`).

---

## 6. Verify

```bash
cd egoff/umst-formal/Lean && lake build UMST.CoordinationCost
```

Full closure: `lake build` (module registered in `lakefile.lean` roots).

---

*Semantics doc: `Docs/COORDINATION_COST_SEMANTICS.md` · spawn `i-coord-lean-1144` · no push*
