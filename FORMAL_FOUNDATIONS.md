# Formal foundations — `umst-formal`

**Version:** Wave 6.5.1 — **2026-04-04**

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

Default `lake build` covers the **core formal layer** only (modules listed in `lakefile.lean` `roots`). Scratch / debug files such as `_check_ext.lean` are **excluded** from that closure. They have been **manually grep-checked** for tactic `sorry` and stray project `axiom` declarations. **Count methodology:** [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md); regenerate via `python3 scripts/lean_declaration_stats.py`.

## Paper Claims ↔ Formal Lemmas

Index of **major published themes** (five-paper programme) to **in-repo** anchors. This is a **manual** map, not machine-checked against PDFs.

| Theme | Claim (informal) | Formal anchor(s) |
|--------|------------------|------------------|
| **I. Clausius–Duhem / rational gate** | Transitions satisfy mass, dissipation (ψ), hydration monotone, strength monotone | `Gate.Admissible`, fields `massDensity` … `strengthMono`; `helmholtz`, `helmholtzAntitone` |
| **II. 100% admissibility for checked steps** | Any transition accepted by the boolean gate satisfies `Admissible` | `Gate.gateCheckSound` |
| **III. Graded compositional safety** | Multi-step mass budget composes (triangle inequality); Kleisli lifting | `Gate.admissibleN_compose`; `Constitutional` lemmas citing it |
| **IV. Landauer / observation / erasure** | Erasure obeys second-law input → Landauer-style bound | `LandauerLaw.physicalSecondLaw` (only project `axiom`); `LandauerExtension`, `MeasurementCost` |
| **V. Double-slit, TMI, epistemic layer** | Complementarity, fringe visibility bound, dephasing, trajectory MI | Package **`umst-formal-double-slit`**: `GeneralVisibility.fringeVisibility_n_le_one`, `LindbladDynamics.dephasingSolution_tendsto_diagonal`, `EpistemicMI` / `EpistemicTrajectoryMI` |

## Wave 6.5 verification audit (closure pass)

| Check | Result |
|--------|--------|
| `lake build` (all `lakefile` roots) | **Succeeded** (verified in workspace) |
| `^axiom ` in `Lean/*.lean` (excluding `.lake`) | **1** — `LandauerLaw.physicalSecondLaw` only |
| Tactic `sorry` / `admit` / `Admitted` in `Lean/*.lean` | **None** (the word “sorry” appears only in **comments** in: `Gate.lean`, `Helmholtz.lean`, `Naturality.lean`, `Activation.lean`, `DIBKleisli.lean`, `FormalFoundations.lean`) |
| `theorem` / `lemma` in **`lakefile` roots only** (24 modules; excludes `_check_ext.lean`) | **154** `theorem`, **13** `lemma` (total **167**) — lines starting with `theorem ` / `lemma `; excludes `example` / `def` / proof `instance` |
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

## Green-flag status

**GREEN FLAG – Fully Complete** for: default `lake` roots, **zero** tactic `sorry` / `admit` / `Admitted`, **one** project-authored `axiom` (`physicalSecondLaw`), and **cold** `lake build` success **without** `warning:`/`error:` in captured output.

Wave **6.5.1** closed documentation residuals (gate header, lakefile scope comments, `FORMAL_FOUNDATIONS` build scope + paper map, non-identity DIB witness). Opaque DIB phases remain future functor work.
