# Documentation coverage plan — exhaustive sorry-free corpus

**Purpose:** Maintainer checklist so every machine-checked claim in `umst-formal` is **accounted for** in the right document, with cross-links among canonical indices (`PROOF-STATUS.md`, `FORMAL_FOUNDATIONS.md`, `Docs/*`). **Not** linked from `README.md` by design (entry point stays short; depth lives in those files). Re-verify **zero** tactic `sorry` / `admit` in default Lean roots in Layer 0 before each release.

**Definition of “exhaustive” (pragmatic):**

1. **Mechanical closure:** Every default `lake` root and every Agda/Coq/Haskell artifact that carries proofs/tests is listed in at least one **authoritative index** (`PROOF-STATUS.md` or language-specific section).
2. **Semantic closure:** Every **module** (Lean root or top-level Agda/Coq file) has a **one-line role** plus **1–3 flagship identifiers** (theorem / QC property names) somewhere in the doc stack—not necessarily every one of 221 theorems spelled out in the README.
3. **Honesty closure:** Every **axiom**, **postulate**, **opaque**, and **surrogate predicate** is classified in `FORMAL_FOUNDATIONS.md`, `PROOF-STATUS.md`, `SAFETY-LIMITS.md`, or `FALSIFIABILITY_DASHBOARD.md` as appropriate.
4. **Navigation closure:** `README.md` points readers to the correct **next click** for depth (never a dead end that implies “nothing else exists”).

---

## Authority stack (do not fork silently)

| Priority | Document | Role |
|:--------:|----------|------|
| A | `Lean/lakefile.lean` | **Ground truth** for Lean build scope (`roots`). |
| B | `scripts/lean_declaration_stats.py` | **Ground truth** for theorem/lemma counts per root; regenerate after root changes. |
| C | `PROOF-STATUS.md` | **Master cross-layer index** (Agda, Coq, Lean, Haskell, FFI). |
| D | `FORMAL_FOUNDATIONS.md` | **Constitutional** summary: axioms, DIB semantics, paper-claim map, audit table. |
| E | `Docs/COUNT-METHODOLOGY.md` | Counting rules—cite when numbers disagree with intuition. |
| F | `README.md` | **Entry point** + narrative; must **link** to C/D/E, not duplicate them incorrectly. |
| G | Other `Docs/*.md` | Thematic depth (falsifiability, replay, roadmap). **This plan** is optional internal QA. |

**Rule:** If README and `PROOF-STATUS` disagree, **fix README** (or add “abbreviated—see PROOF-STATUS”).

---

## Layer 0 — Mechanical “sorry-free / error-free” verification

Repeat before marking any documentation wave “closed.”

- [x] **Lean:** `cd Lean && lake build` — success (verified 2026-04-03).
- [x] **Lean:** `rg '^\s*(sorry|admit)\b' Lean --glob '*.lean'` — empty in default closure (re-run before release).
- [x] **Lean:** `rg '^axiom ' Lean --glob '*.lean'` — `physicalSecondLaw` only (`LandauerLaw.lean`).
- [x] **Coq:** `cd Coq && make` — success; `rg 'Admitted' Coq --glob '*.v'` — empty (re-run before release).
- [x] **Agda:** `cd Agda && make check` — success (re-run before release); `--safe` policy in `PROOF-STATUS`.
- [x] **Haskell:** `cd Haskell && cabal test umst-properties -f -with-ffi` — pass (re-run before release); optional FFI suite for Rust parity.
- [x] **Stats:** `python3 scripts/lean_declaration_stats.py` — 45 roots, 221 thm / 17 lemma / 238 total; aligned with `PROOF-STATUS` / `FORMAL_FOUNDATIONS` (verified 2026-04-22).

---

## Layer 1 — Machine-readable inventory (single export)

Goal: one script or documented command sequence that lists **all** accountable artifacts.

- [x] **Lean:** `lean_declaration_stats.py` emits per-root `theorem`/`lemma` counts; documented in `Docs/COUNT-METHODOLOGY.md`.
- [x] **Theorem-name export:** `python3 scripts/lean_declaration_stats.py --theorem-names` (JSON per root).
- [x] **Haskell:** **62** `quickCheck` obligations in `test/Test.hs` `main` (gate, SDF, InfoTheory, Landauer, monoidal, Economic, FPD mirrors); `landauer-einstein-sanity`; `Haskell/README.md` + `PROOF-STATUS.md`.
- [x] **Agda / Coq:** `PROOF-STATUS.md` + `Makefile` inputs; file-level notes in cross-layer tables.

---

## Layer 2 — `PROOF-STATUS.md` (exhaustive index target)

This file should be the **only** place that attempts **per-layer theorem tables** at full width.

### 2.1 Lean — all 45 roots

For **each** `UMST.*` root in `lakefile.lean`:

- [x] Row exists in **Lean 4 Layer Summary** table with correct `theorem` / `lemma` counts (regenerate from script).
- [x] **Source path** column matches actual file (`Lean/...` or `Lean/Economic/...`).
- [x] At least **one flagship name** or parenthetical hint for non-obvious modules (`PROOF-STATUS.md`).
- [x] **Economic surrogate** modules cross-reference `SAFETY-LIMITS.md` / `FALSIFIABILITY_DASHBOARD.md`.

**Checklist by root (45 modules — verified 2026-04-22):**

- [x] `Gate` … `Economic.CreativeExplorationTolerance` (all roots listed in `lakefile.lean` ↔ `PROOF-STATUS` table)

### 2.2 Haskell QuickCheck

- [x] Property table / narrative includes **62** QuickCheck obligations in `umst-properties` (`Test.hs` `main`).
- [x] `landauer-einstein-sanity` documented (`PROOF-STATUS`, `Haskell/README.md`, `PROOF-REPLAY.md`).
- [x] Count matches `Test.hs` `main` (`rg quickCheck test/Test.hs` → 62).

### 2.3 Agda / Coq / FFI

- [x] Default-build files indexed in `PROOF-STATUS.md` (including postulate / traceability notes).
- [x] FFI / `UMST_PROTO_REPO` scope documented in `PROOF-REPLAY.md` and `PROOF-STATUS.md`.

---

## Layer 3 — `FORMAL_FOUNDATIONS.md`

- [x] **Version / wave** — 6.5.2.
- [x] **Single axiom** — `physicalSecondLaw` only.
- [x] **Paper Claims ↔ Formal Lemmas** — row **VI** + double-slit external package.
- [x] **Wave verification audit** — 45 roots, 221/17/238, matches script.
- [x] **DIB** — matches `DIBKleisli.lean`.
- [x] Cross-links to `Docs/FALSIFIABILITY_DASHBOARD.md` and `SAFETY-LIMITS.md`.

---

## Layer 4 — `Docs/` thematic documents

### 4.1 `FALSIFIABILITY_DASHBOARD.md`

- [x] Full **Economic** grid + core L₀ + Haskell/Agda/Coq + out-of-repo rows; links to `PROOF-STATUS`, `FORMAL_FOUNDATIONS`, `SAFETY-LIMITS`.

### 4.2 `SAFETY-LIMITS.md`

- [x] Economic scope + non-claims; link to `FALSIFIABILITY_DASHBOARD.md`.

### 4.3 `COUNT-METHODOLOGY.md`

- [x] Roots, line-start counts, **`.lake` exclusion**; points at `lean_declaration_stats.py`.

### 4.4 `PROOF-REPLAY.md`

- [x] Stages 8–9: `make lean-stats`, `make visuals`; evidence table rows added.

### 4.5 `COMPREHENSIVE-FORMAL-PLAN.md` / roadmaps

- [x] Status banner + pointer to `FORMAL_FOUNDATIONS.md` (dated audit retained).

### 4.6 `Architecture-Invariants.md`

- [x] Linked from `README.md` scope; unchanged in this pass.

---

## Layer 5 — `README.md` (entry point, not encyclopedia)

**Goal:** Correct **story**, **counts**, **links**; avoid duplicating full theorem lists. **This plan is not linked from README** (maintainers open `Docs/DOCUMENTATION-COVERAGE-PLAN.md` directly when needed).

- [x] **Hero / stats** line matches `lean_declaration_stats.py` (via `PROOF-STATUS` / `FORMAL_FOUNDATIONS`).
- [x] **Economic** table + **Lean core (non-Economic)** roles + flagship hints (re-verify on each Economic edit).
- [x] **Architecture tree:** 45 roots, `lakefile.lean`, full Agda/Coq/Haskell/Docs listing.
- [x] **Agda / Coq** trees include InfoTheory / MeasurementCost / LandauerEinsteinTrace as applicable.
- [x] **Haskell:** **62** QuickCheck obligations + `landauer-einstein-sanity` + `Haskell/README.md`.
- [x] **Docs hub:** `FORMAL_FOUNDATIONS`, `PROOF-STATUS`, `COUNT-METHODOLOGY`, `FALSIFIABILITY`, `SAFETY-LIMITS`, `PROOF-REPLAY` — **no** link to this file.

---

## Layer 6 — Per-module file headers (optional depth)

For maintainers who open source first:

- [x] **High-traffic roots:** `Gate.lean`, `Constitutional.lean` (graded Kleisli; refutation pointer), `LandauerLaw.lean`, `EnrichedAdmissibility.lean`, `FormalFoundations.lean`, `Economic/EconomicDomain.lean` — role text + `PROOF-STATUS` / `FORMAL_FOUNDATIONS` where needed; remaining roots optional on touch.
- [x] **Economic/** surrogates already cite `SAFETY-LIMITS.md` in-file where names are loaded (`HallucinationDetector`, `LowEntropyLieDetector`, etc.).

---

## Layer 7 — Automation & drift control

- [x] **Declaration snapshot:** CI runs `lean_declaration_stats.py --verify-snapshot scripts/expected_lean_declaration_snapshot.json` (update JSON in the same commit as intentional root/count changes).
- [x] **Single-axiom gate:** CI runs [`scripts/check_lean_axioms.py`](../scripts/check_lean_axioms.py).
- [x] **Sorry/admit gate:** [`scripts/check_lean_sorry.sh`](../scripts/check_lean_sorry.sh) after `lake build`.
- [x] **Markdown link check:** [`scripts/check-markdown-links.sh`](../scripts/check-markdown-links.sh) + [`scripts/markdown-link-check.json`](../scripts/markdown-link-check.json) in the **Docs lint + Markdown links** CI job (`../../MaOS-Core` ignored in isolated checkout; in-file `#` anchors ignored).

---

## Rust / Continuum engineering (out of `lake` closure — honesty)

This repository’s **default Lean/Agda/Coq/Haskell** artifacts do **not** machine-check `MaOS-Core` (`vla_server`, swarm fusion, Θ/Σ backends). Treat that code as a **sibling functor** in the workspace: evidence is **tests, probes, and operator runbooks**, not `lake build`.

**Decomposition / planning (typed morphisms, Θ recon, splat, Σ VarBuilder, CI boot):** sibling doc **[`MaOS-Core/docs/CONTINUUM_GAP_REMEDIATION_PLAN.md`](../../MaOS-Core/docs/CONTINUUM_GAP_REMEDIATION_PLAN.md) §17**. **AutoExperimenter / oracle policy:** same file §16 + [`FORMAL_FOUNDATIONS.md`](../FORMAL_FOUNDATIONS.md) (Planned: AutoExperimenter).

**Rule:** Do not imply in `README` or `PROOF-STATUS` that a theorem here **proves** a Continuum HTTP contract; cross-link §17 when discussing “alignment” between formal gate language and deployed swarm behavior.

---

## Cross-link matrix (fill as you complete work)

| From → To | `README` | `PROOF-STATUS` | `FORMAL_FOUNDATIONS` | `FALSIFIABILITY` | `SAFETY-LIMITS` | `COUNT-METHODOLOGY` | `PROOF-REPLAY` |
|-----------|:--------:|:--------------:|:--------------------:|:----------------:|:---------------:|:-------------------:|:--------------:|
| `README` | — | ✓ required | ✓ required | ✓ for surrogates | ✓ for Economic | ✓ for counts | ✓ for build |
| `PROOF-STATUS` | optional | — | ✓ | ✓ | ✓ | ✓ | ✓ |
| `FORMAL_FOUNDATIONS` | optional | ✓ | — | ✓ | ✓ | ✓ | optional |

**Note:** `PROOF-STATUS.md` links to **this file** for maintainer QA only (2026-04-05); `README.md` does not.

---

## Execution order (recommended)

1. **Layer 0** (mechanical green)  
2. **Layer 1** + regenerate stats  
3. **Layer 2.1** Lean table completeness (biggest gap vs README today)  
4. **Layer 3** `FORMAL_FOUNDATIONS` audit row  
5. **Layer 4** falsifiability + safety alignment  
6. **Layer 5** README hub + non-Economic mini-table + tree fixes  
7. **Layer 6** optional module docs  
8. **Layer 7** automation as needed  

---

## Completion criteria (sign-off)

- [x] Layer 0 green on verified checkout (2026-04-03); re-run before each release.
- [x] `PROOF-STATUS.md` Lean table: **45** roots, script-aligned counts.
- [x] `README.md` reflects full root set + Economic layer.
- [x] Economic surrogates / shells in `FALSIFIABILITY_DASHBOARD.md` + `SAFETY-LIMITS.md`.
- [x] **No** README link to this plan (by product choice).

**Maintainer note:** After each wave touching Lean roots, run **Layer 0 → 2.1 → 3 → 5 stats line** as minimum.

---

## Execution log

| Date | Notes |
|------|--------|
| 2026-04-03 | Layer 0: `lake build` OK; `Agda/make check`, `Coq/make`, `cabal test umst-properties` OK; `rg sorry` empty in `Lean/`; `lean_declaration_stats.py` → 39 roots, 189 decls, 1 axiom. Expanded `FALSIFIABILITY_DASHBOARD.md`, `COUNT-METHODOLOGY` (`.lake`), `SAFETY-LIMITS` ↔ dashboard, `Haskell/README.md`, `PROOF-REPLAY` stages 8–9, `FORMAL_FOUNDATIONS` wave 6.5.2 green-flag text, `lakefile.lean` header, `PROOF-STATUS` flagship hints, README `Naturality` identifiers. README **does not** link this plan. |
| 2026-04-05 | `PROOF-STATUS` maintainer pointer; Rust/Continuum §. CI: `check_lean_sorry.sh`, `check_lean_axioms.py`, `--verify-snapshot`, **`check-markdown-links.sh`**. `Constitutional.lean` header corrected. `--theorem-names`. README tone pass; module index lines. `FORMAL_FOUNDATIONS` green-flag table + link-check Layer 7 closed. |
| 2026-04-22 | **Lean / Haskell doc parity pass:** regenerated `expected_lean_declaration_snapshot.json` (**45** roots · **221**/**17**/**238**); `README.md`, `FORMAL_FOUNDATIONS.md`, this plan, `Haskell/README.md` aligned with `python3 scripts/lean_declaration_stats.py` + `rg quickCheck test/Test.hs` (**62** obligations). FPD roots (`CreditGreedyOptimal`, `Dignity`, `EtaCog`, `RhoEstimator`, `MedianConvergence`, `OrderStatisticsBand`) reflected in README build-scope sentence. |
