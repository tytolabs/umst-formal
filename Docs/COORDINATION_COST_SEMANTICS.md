# Coordination Cost — lower-bound semantics (Landauer floor)

**Status:** A7-4 n-ary scaffold @ 2026-07-18 13:27 — `multiInformationBits` + global floor lemmas; pairwise SSOT preserved.  
**Lean module:** [`Lean/CoordinationCost.lean`](../Lean/CoordinationCost.lean)  
**Rust SSOT:** `umst-arcs/crates/umst-arcs/src/coordination_cost.rs` (+ planned `coordination_cost_global.rs`)

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
| **Definitions** | `coordinationSavingJoules`, `landauerCostJoules`, `coordinationMassEquivalentKg` | SI joule + kg reporting functors |
| **Bit / nat bridge** | `mutualInformationBits` | \(I_\text{bits} = I_\text{nats} / \ln 2\) |
| **Classical MI link** | `classical_measurement_floor_agrees`, `physical_channel_floor_agrees` | Same floor as `ClassicalMeasurementCost.measurementEnergyLowerBound` |
| **Landauer bit scale** | `landauerBitEnergy`, `landauerEnergyAt` | One-bit floor at temperature \(T\) (`landauerBitEnergy_eq_landauerEnergyAt`) |
| **Independent−joint delta** | `independentMinusJointDelta`, `independent_minus_joint_eq_mi_delta` | Algebraic form of Rust `coordination_cost_identity_independent_minus_joint` |
| **A7-4 n-ary** | `multiInformationBits`, `multiInformationNats`, `coordinationSavingGlobalJoules` | Total correlation `I_n = Σᵢ H(Xᵢ) − H(joint)` in bits |
| **A7-4 channel split** | `PhysicalMultiInfoChannel`, `EpistemicMultiInfoDraft`, `PhysicalMiChannel`, `EpistemicMiDraft` | N-ary + pairwise physical vs epistemic (no epistemic→thermo slip) |
| **n=2 reduction** | `multiInformationBits_pair_eq_mutualInformationBits`, `global_floor_pair_agrees` | Global scalar reduces to pairwise SSOT on `JointDist` |
| **Thermodynamic bound** | `landauerBound` (`LandauerLaw`) | Erasure work ≥ \(T \ln 2\) (uses sole project axiom `physicalSecondLaw`) |
| **Operational orthogonality** | `kleisli_compose_preserves_admissibility` tests (Rust) | `coordination_saving` does not alter `gate<R>` |

---

## 3. What is proved in the scaffold

All of the following are machine-checked without new axioms or `sorry` (42 theorems):

- `coordinationSaving_eq_landauerCost` — alias coherence
- `landauerBitEnergy_eq_landauerEnergyAt` — SI bridge alignment
- `coordinationSaving_eq_landauerEnergyAt` — joule scale via `landauerEnergyAt`
- `coordinationSaving_zero` — zero MI ⇒ zero saving
- `coordinationSaving_linear` / `coordinationSaving_additive` — linear / additive in MI (bits)
- `coordinationSaving_one_bit` — one bit = `landauerBitEnergy T`
- `coordinationSaving_temp_scaling` — linear in \(T\)
- `coordinationSaving_nonneg` / `coordinationSaving_pos` — sign witnesses (hypothesised MI, T)
- `coordinationMassEquivalent_eq_div` / `coordinationMassEquivalent_temp_scaling` — egoff `mass_equiv_kg` bridge
- `independent_minus_joint_eq_mi_delta` — independent−joint parity identity
- `globalCoordinationSaving_eq_pairwise` — A7-4 global alias reduces to pairwise
- `multiInformationBits_pair_eq_mutualInformationBits` — n=2 total correlation = pairwise MI
- `multiInformationBits_pair_product_zero` — independent product joint ⇒ zero multi-info
- `multiInformationBits_nonneg` — nonnegativity when `joint ≤ Σ marginals` (hypothesis)
- `coordinationSavingGlobal_eq_pairwise` / `global_floor_pair_agrees` — global joule floor
- `physicalMultiInfoBits_pair_eq` — `PhysicalMultiInfoChannel` pairwise bridge
- `physical_channel_floor_agrees` — `PhysicalMiChannel` floor witness
- `zero_mi_zero_saving` — product joint ⇒ zero saving
- `classical_measurement_floor_agrees` — nats vs bits convention bridge
- `mkReport_*` — `CoordinationReport` projection fields (joules + kg)

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

## 7. P6 extension crosswalk (F25-B06)

A7 physical floor semantics are **frozen** in this doc. P6 semantic/L10 prep lives in
[`COORDINATION_COST_P6_SPINE.md`](COORDINATION_COST_P6_SPINE.md) and
[`Lean/CoordinationCostP6.lean`](../Lean/CoordinationCostP6.lean) (**13 thm · 0 sorry**).

| A7 concept | P6 stub | Honest rule |
|------------|---------|-------------|
| `coordinationSavingJoules` | `physicalUnderstandingFloorJoules` | Same functor on physical bridge |
| `EpistemicMiDraft` | `EpistemicMiDeficitDraft` | Bits only until bridge |
| `mkReport` | `FixtureGridRow` | Lean-bridge grid pin (no `JointDist`) |
| `CoordinationReport` | `SemanticFloorReport` | `isPhysicalProjection` flag |

**Not claimed:** epistemic auto-projection · `SemanticResponse` gate · cert Proved.

---

*Semantics doc: `Docs/COORDINATION_COST_SEMANTICS.md` · F25-B06 deepen · no push*
