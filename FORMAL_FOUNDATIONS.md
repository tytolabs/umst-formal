# Formal foundations — `umst-formal`

**Version:** Wave 6.5.2 — **2026-04-04** (Lean declaration totals refreshed **2026-04-22** — FPD roots + snapshot; see audit table)

## Single physical axiom (Lean `axiom`)

| Location | Name | Role |
|----------|------|------|
| `Lean/LandauerLaw.lean` | `physicalSecondLaw` | Second law input for the Landauer / erasure bound (`T_LandauerLaw`). |

No other `axiom` declarations remain under `umst-formal/Lean/`.

## Domain constraints (not axioms)

| Location | Mechanism | Role |
|----------|-----------|------|
| `Lean/Convergence.lean` | `HydrationInUnitInterval s` as an explicit hypothesis; bundled into `ConstitutionalStream` | Hydration in `[0,1]` for streams and Helmholtz bounds. |

## Semantics tier (DIB)

| Location | Mechanism | Role |
|----------|-----------|------|
| `Lean/DIBKleisli.lean` | `DIBArtifactSemantics`, `artifactSemanticStep`, `dib_semantic_step_admissible`, `dibArtifactGateCheck`, `dibArtifactGateCheck_eq_true` | **Non-identity** dissipative step on ψ; lawful link to executable `gateCheck`. Full Field/Core functor story is **future work**; witness is minimal but **non-vacuous**. |

Opaque: `DIBState`, `discover`, `invent`, `build`.

## Witness module

`lake build FormalFoundations` imports `Gate`, `DIBKleisli`, `Convergence`, `LandauerLaw` and defines `UMST.umst_formal_complete`.

## Build

```bash
cd Lean && lake build
```

## Build scope

Default `lake build` covers **all** registered `lakefile.lean` `roots` (**45** modules, including `Lean/Economic/*` and **Formal-First** cockpit mirrors: `CreditGreedyOptimal`, `Dignity`, `EtaCog`, `RhoEstimator`, `MedianConvergence`, `OrderStatisticsBand`). Scratch / debug files such as `_check_ext.lean` are **excluded** from that closure. They have been **manually grep-checked** for tactic `sorry` and stray project `axiom` declarations. **Count methodology:** [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md); regenerate via `python3 scripts/lean_declaration_stats.py`.

## Paper Claims ↔ Formal Lemmas

Index of **major published themes** (five-paper programme) to **in-repo** anchors. This is a **manual** map, not machine-checked against PDFs.

| Theme | Claim (informal) | Formal anchor(s) |
|--------|------------------|------------------|
| **I. Clausius–Duhem / rational gate** | Transitions satisfy mass, dissipation (ψ), hydration monotone, strength monotone | `Gate.Admissible`, fields `massDensity` … `strengthMono`; `helmholtz`, `helmholtzAntitone` |
| **II. 100% admissibility for checked steps** | Any transition accepted by the boolean gate satisfies `Admissible` | `Gate.gateCheckSound` |
| **III. Graded compositional safety** | Multi-step mass budget composes (triangle inequality); Kleisli lifting | `Gate.admissibleN_compose`; `Constitutional` lemmas citing it |
| **IV. Landauer / observation / erasure** | Erasure obeys second-law input → Landauer-style bound | `LandauerLaw.physicalSecondLaw` (only project `axiom`); `LandauerExtension`, `MeasurementCost` |
| **V. Double-slit, TMI, epistemic layer** | Complementarity, fringe visibility bound, dephasing, trajectory MI | Package **`umst-formal-double-slit`**: `GeneralVisibility.fringeVisibility_n_le_one`, `LindbladDynamics.dephasingSolution_tendsto_diagonal`, `EpistemicMI` / `EpistemicTrajectoryMI` |
| **VI. Classical economic / burden layer (meso)** | Shannon–Landauer “economic temperature”, burden steps vs `Admissible`, stochastic drift, classical surrogates for exploration cost | **`Lean/Economic/`** (17 named modules + `EconomicDomain`); **no** new physics axioms; surrogates and shells classified in [`Docs/FALSIFIABILITY_DASHBOARD.md`](Docs/FALSIFIABILITY_DASHBOARD.md) and [`SAFETY-LIMITS.md`](SAFETY-LIMITS.md) |

## Wave 6.5 verification audit (closure pass)

| Check | Result |
|--------|--------|
| `lake build` (all `lakefile` roots) | **Succeeded** (verified in workspace) |
| `^axiom ` in `Lean/*.lean` (excluding `.lake`) | **1** — `LandauerLaw.physicalSecondLaw` only |
| Tactic `sorry` / `admit` / `Admitted` in `Lean/*.lean` | **None** (the word “sorry” appears only in **comments** in: `Gate.lean`, `Helmholtz.lean`, `Naturality.lean`, `Activation.lean`, `DIBKleisli.lean`, `FormalFoundations.lean`) |
| `theorem` / `lemma` in **`lakefile` roots only** (45 modules; excludes `_check_ext.lean`) | **221** `theorem`, **17** `lemma` (total **238**) — lines starting with `theorem ` / `lemma `; excludes `example` / `def` / proof `instance` |
| Modules **not** in `lakefile` roots | `_check_ext.lean` — **not** part of `lake build` |

### Cold rebuild (audit)

Procedure: `rm -rf .lake && lake build` under `Lean/` (fresh Mathlib checkout + full compile). **Result:** `Build completed successfully.` **Stderr/stdout:** no lines matching `warning:` or `error:` (entire captured log was dependency `info:` clones + success line).

## Logical / physical alignment (informal cross-check)

| Topic | Formal anchor | Note |
|--------|----------------|------|
| Clausius–Duhem / gate | `Gate.Admissible`, `clausiusDuhem` field, `gateCheckSound` / `gateCheckComplete` | Predicate is the conjunction of four inequalities; **100%** of *checked* transitions satisfy it by **definition** of `gateCheck`; constitutive closure uses explicit hypotheses (e.g. `forwardHydrationAdmissible`). |
| Graded composition | `Gate.admissibleN_compose`, `Constitutional` Kleisli lemmas | Replaces removed `admissibleTrans`; proved (triangle inequality), not axiomatized. |
| Landauer / observation cost | `LandauerLaw`, `MeasurementCost`, extensions | **Single** project `axiom`: `physicalSecondLaw` (Clausius inequality input). |
| Hydration | `Convergence.HydrationInUnitInterval`, `ConstitutionalStream` | Hypothesis-driven; no hydration axiom. |
| DIB ↔ gate | `dib_semantic_step_admissible`, `dibArtifactGateCheck_eq_true` | **Non-identity** `artifactSemanticStep` (ψ decreases); `gateCheck` always **true** on the interpreted step. Opaque `discover`/`invent`/`build` still unlinked from concrete thermo traces. |

**Papers:** the five publications are **not** in-repo; alignment with prose claims is **manual** (this table maps code to themes only). **Mathlib** contributes its **own** axioms under every import (`#print axioms` on a theorem lists them).

## Planned (engineering): AutoExperimenter — invariants and scope

**Status:** design note only — **no** Lean module or automation ships here yet. When a Rust/TS experiment harness exists (`MaOS-Core` probes, governor metrics), this section records **what formal review must not allow** to change without an explicit law pass.

| Boundary | Requirement |
|:---------|:------------|
| **Non-bypass** | Any automated “experiment” that mutates slot wiring, env defaults, or gate thresholds must **not** introduce a path where the thermodynamic gate is skipped or UI shows ACCEPT when the kernel would REJECT (see `MaOS-Config/docs/AGENTS.md` functor language). |
| **Oracle** | Proposed config deltas should be **gated** by the same executables humans trust today (`cargo test`, `npm run continuum:registry:static`, smoke probes) before merge; no silent self-apply to production env. Phase **3** ordering is in `MaOS-Core/docs/CONTINUUM_GAP_REMEDIATION_PLAN.md` §16. Automatable subset: `npm run continuum:ci:oracle` in MaOS-Core (tests + static probe); full harness needs a running `vla_server` (Σ weights). Optional `lake build`: `umst-formal/.github/workflows/ci.yml`. |
| **Human gate (Phase 2)** | Advisory JSON + unified diffs only; **no** auto-commit, auto-merge, or secret writes — see §16 Phase 2 schema sketch in the same doc. |
| **Scope** | AutoExperimenter concerns **cartridge / env / harness** evidence — **not** new constitutive physics inside universal Layer 1 without a separate proof obligation. |
| **Lean linkage** | Non-root placeholder: [`Lean/experiments/AutoExperimenterPlaceholder.lean`](Lean/experiments/AutoExperimenterPlaceholder.lean) (excluded from `lakefile.lean`). A real **gated experiment monad** root belongs only after the **Rust harness + policy** are frozen; until then, this file’s **Green-flag** Lean closure is unchanged. |

**Related (repo prose):** `MaOS-Core/docs/CONTINUUM_GAP_REMEDIATION_PLAN.md` §§16–17 (truth probes + **typed morphism** breakdown of Θ / Σ / splat / CI backlog), `MaOS-Core/docs/ARCHITECTURE_CONTINUUM.md` (presentation vs kernel).

## Green-flag status

**GREEN FLAG – closure criteria (Wave 6.5.2)**

| Gate | Mechanism |
|:-----|:----------|
| Lean default roots | `lake build UMST` — 45 modules in `lakefile.lean` |
| Tactic gaps | **Zero** `sorry` / `admit` in `Lean/**/*.lean` (excl. `.lake`); CI: `scripts/check_lean_sorry.sh` |
| Project axiom | Exactly **`LandauerLaw.physicalSecondLaw`**; CI: `scripts/check_lean_axioms.py` |
| Declaration drift | Totals match `scripts/expected_lean_declaration_snapshot.json`; CI: `lean_declaration_stats.py --verify-snapshot` |
| Coq / Agda / Haskell | CI jobs per `.github/workflows/ci.yml` (see `Docs/PROOF-REPLAY.md`) |
| Docs style | `markdownlint` on curated paths (CI **Docs lint** job) |
| Doc link integrity | `scripts/check-markdown-links.sh` (curated Markdown; sibling `MaOS-Core` path ignored in CI; in-file `#` anchors ignored) |

**Cold `lake build` audit:** `rm -rf Lean/.lake && lake build` under `Lean/` completed successfully with no `error:` lines in the captured log (Mathlib may emit `warning:` from upstream; team policy is to treat new project-local warnings as regressions).

Wave **6.5.2** ships the full `Lean/Economic/` meso-layer, doc-stack alignment (`PROOF-STATUS`, `Docs/FALSIFIABILITY_DASHBOARD.md`, `SAFETY-LIMITS.md`), the non-identity DIB witness, and CI gates above. Opaque DIB phases remain future functor work.
