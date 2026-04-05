<!--
SPDX-License-Identifier: MIT
-->

# SAFETY-LIMITS — Meso-scale Economic layer (Wave 6.5.2)

## Scope

`Lean/Economic/` proves **classical** inequalities and typings over the gate carrier, Shannon/Landauer
bookkeeping, and Kleisli composition. It does **not** import the quantum double-slit package.

**Classification** (checked / surrogate / shell): [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md). **Quantum RCC / which-path formalism:** sibling artifact [**Thermodynamic Cost of Knowing**](https://doi.org/10.5281/zenodo.19159660) (`umst-formal-double-slit`); scope and assumptions live there as **`Docs/ASSUMPTIONS-DOUBLE-SLIT.md`** (not repeated in this meso-layer repo).

## Non-claims

- **“Hallucination” / “lie” / “RCC”** in file names denote **explicit predicates** (thresholds, margins).
  They are not trained detectors and not the RCC formalism in `umst-formal-double-slit`.
- No result here certifies **deployment safety** for ML systems or market agents.
- **Dynamic ε calibration** (`DynamicEpsilonCalibration.lean`) is a **functional shell**: a user-supplied
  `f : ℝ → ℝ`; no data pipeline ships with the proof.

## Axioms

The only physical `axiom` in `umst-formal/Lean` remains **`LandauerLaw.physicalSecondLaw`** (see
`FORMAL_FOUNDATIONS.md`). The Economic layer adds **no** new physics axioms.

## Build

Default `lake build` covers registered roots only. Optional scratch modules are excluded from roots
by design (`lakefile.lean` comment block).
