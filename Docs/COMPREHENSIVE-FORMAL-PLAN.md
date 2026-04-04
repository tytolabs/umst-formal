# Comprehensive Formal Plan: Grounding Claims, Closing Gaps, and Extending L₀

**Date:** 2026-03-19
**Scope:** Complete gap analysis, error identification, logical fallacy audit, end-condition proof plan, and phased theory extensions for `umst-formal`.
**Perspective:** Functional programming, lambda calculus, category theory, type theory, graph theory.

**Status note (post-snapshot):** The refutable `admissibleTrans` / `admissible_trans` axiom has been **removed** from Lean and Coq and replaced by **graded** admissibility (`AdmissibleN`, `admissibleN_compose`) and N-step Kleisli theorems. **Authoritative counts, module list, and axiom inventory:** `PROOF-STATUS.md`. This file remains a **dated audit** for reasoning about remaining gaps (e.g. `fcMonotone` witness, ℚ↔f64); treat the `admissibleTrans` “CRITICAL open” narrative below as **historical context**, not the current proof state.

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Current L₀ Signature Inventory](#2-current-l₀-signature-inventory)
3. [CRITICAL: Identified Inconsistency (admissibleTrans)](#3-critical-identified-inconsistency)
4. [Axiom Audit: Gaps vs Interface Specifications](#4-axiom-audit)
5. [End-Condition Proofs Pending](#5-end-condition-proofs-pending)
6. [Category-Theoretic Completions](#6-category-theoretic-completions)
7. [Graph-Theoretic Properties](#7-graph-theoretic-properties)
8. [Theory Extensions (T_ext)](#8-theory-extensions)
9. [ℚ vs f64 Correspondence](#9-rational-vs-float-correspondence)
10. [Implementation Sequencing](#10-implementation-sequencing)
11. [Proof Dependency DAG](#11-proof-dependency-dag)
12. [File-Level Impact Map](#12-file-level-impact-map)

---

## 1. Executive Summary

### Findings (ordered by severity)

| # | Finding | Severity | Status |
|---|---------|----------|--------|
| 1 | `admissibleTrans` is **refutable** from existing definitions | **CRITICAL** | **Resolved in repo:** axiom removed; graded `AdmissibleN` + `admissibleN_compose` (see `PROOF-STATUS.md`) |
| 2 | `fcMonotone` is over-quantified (no w/c ratio) and has **no concrete witness** | HIGH | Logical overcommitment |
| 3 | No convergence/termination proofs for constitutional sequences | HIGH | **Partial:** `Lean/Convergence.lean` (hydration/free-energy limits, Lyapunov); broader “all protocols” termination still not claimed |
| 4 | `psiAntitone` is over-quantified (applies beyond Helmholtz states) | MEDIUM | Stronger than witness |
| 5 | Naturality proofs are trivially true on discrete category | MEDIUM | Not a strong claim |
| 6 | DIB monad proves only State-monad tautologies (no physical content) | MEDIUM | Informationally vacuous |
| 7 | No formal ℚ ↔ f64 correspondence | MEDIUM | Semantic gap |
| 8 | Monoidal structure claimed but unformalised | LOW | Commentary only |
| 9 | Sheaf structure trivial on discrete topology | LOW | Vacuously true |
| 10 | Target claims (Landauer law, Jacobson, etc.) not well-formed in L₀ | KNOWN | Documented in DERIVATION-PLAN |

### Contamination Scope of admissibleTrans *(historical — pre-fix)*

Before the axiom was removed, every theorem downstream of `admissibleTrans` was **formally vacuous** (provable from False), including:
- `kleisliComposeWellTyped` (Lean, Coq)
- `kleisliFoldWellTyped` (Lean, Coq)
- `sequentialCompositionSafe` (Lean, Coq)

**Current repo:** those results are superseded or reframed by **graded** theorems (`kleisliComposeWellTypedN`, `kleisliFoldWellTypedN`, etc.); see `PROOF-STATUS.md`. The `ConstitutionalSeq` / `kleisliAdmissibility` / `subjectReduction` chain did not depend on `admissibleTrans` and was always sound.

---

## 2. Current L₀ Signature Inventory

### Sorts

| Sort | Layer | Classification |
|------|-------|----------------|
| `ThermodynamicState` | Agda/Coq/Lean | Record: `{density, freeEnergy, hydration, strength : ℚ}` |
| `Admissible old new` | Agda/Coq/Lean | Prop: 4-fold conjunction |
| `MaterialClass` | Agda/Lean | Inductive: 5 constructors (OPC, RAC, Geopolymer, Lime, Earth) |
| `Engine` | Lean | Inductive: 8 constructors |
| `EngineSet` | Lean | `Engine → Bool` |
| `ActivatedUMST M` | Lean | Sigma: `{engines // engines = activation M}` |
| `ConstitutionalSeq` | Lean/Coq | Inductive: well-typed state list |
| `KleisliArrow` | Lean/Coq | `ThermodynamicState → Option ThermodynamicState` |
| `M A` (DIB) | Agda/Lean | State monad: `DIBState → (A × DIBState)` |
| `DIBState` | Agda/Lean | Opaque/postulate |
| `Observation, Insight, Design, Artifact` | Agda/Lean | Opaque/postulate/axiom |

### Constants

| Constant | Value | Layer |
|----------|-------|-------|
| `δMass` / `delta_mass` | 100 (kg/m³) | All |
| `Q_hyd` | 450 (J/kg) | All |
| `helmholtz α` | `-(Q_hyd * α)` | All |
| `kBoltzmannSI` | 1.380649 × 10⁻²³ (J/K, exact SI) | Lean |
| `speedOfLightSI` | 299792458 (m/s, exact SI) | Lean |
| `landauerBitEnergy T` | `kB * T * ln 2` | Lean/Coq |
| `massEquivalent T` | `landauerBitEnergy T / c²` | Lean/Coq |

### Axioms (Complete Inventory)

| Axiom | Type | Classification | Witness? |
|-------|------|----------------|----------|
| `psiAntitone` | `∀ s₁ s₂, s₁.hydration ≤ s₂.hydration → s₂.freeEnergy ≤ s₁.freeEnergy` | Physical (over-quantified) | Partial: `ψAntitoneHelmholtz` (conditioned on `HelmholtzState`) |
| `fcMonotone` | `∀ s₁ s₂, s₁.hydration ≤ s₂.hydration → s₁.strength ≤ s₂.strength` | Physical (over-quantified) | **NONE** |
| `admissibleTrans` | *(removed)* was `Admissible s s' → Admissible s' s'' → Admissible s s''` | Composition | **Was REFUTABLE** — **removed**; use graded `admissibleN_compose` (see §3, `PROOF-STATUS.md`) |
| `funext` | Function extensionality | Standard meta-axiom | Theorem in Lean 4 |
| `kB_SI_pos`, `c_SI_pos`, `ln2_pos` | Positivity of parameters | Coq only | N/A (parameter axioms) |

---

## 3. CRITICAL: Identified Inconsistency (admissibleTrans)

*Live codebase:* the axiom is **removed** and Kleisli composition uses graded theorems (`PROOF-STATUS.md`). This section records **why** it had to go (the counterexample), for audit traceability.

### 3.1 The Refutation

The former `admissibleTrans` axiom was **provably false** under the definition of `Admissible` with `δMass = 100`.

**Counterexample construction:**

```
s   = { density := 0,   freeEnergy := 0,    hydration := 0,   strength := 0 }
s'  = { density := 99,  freeEnergy := -225,  hydration := 1/2, strength := 50 }
s'' = { density := 198, freeEnergy := -450,  hydration := 1,   strength := 100 }
```

**Verification:**
- `Admissible s s'`: `|99 - 0| = 99 ≤ 100` ✓, `ψ' ≤ ψ` ✓, `α' ≥ α` ✓, `fc' ≥ fc` ✓
- `Admissible s' s''`: `|198 - 99| = 99 ≤ 100` ✓, `ψ'' ≤ ψ'` ✓, `α'' ≥ α'` ✓, `fc'' ≥ fc'` ✓
- `Admissible s s''`: `|198 - 0| = 198 > 100 = δMass` **FAIL**

Yet `admissibleTrans` would derive `Admissible s s''`, from which we extract `|198 - 0| ≤ 100`, i.e., `198 ≤ 100` in ℚ — **False**.

### 3.2 Why This Happens

The `Admissible` predicate conjoins four conditions. Three are order-theoretic (transitive by `≤`-transitivity):
- `freeEnergy new ≤ freeEnergy old` (Clausius-Duhem)
- `old.hydration ≤ new.hydration` (hydration monotone)
- `old.strength ≤ new.strength` (strength monotone)

The fourth is **metric** (NOT transitive):
- `|new.density - old.density| ≤ δMass` (mass conservation)

The triangle inequality gives `|s''.density - s.density| ≤ 2δMass`, not `≤ δMass`.

### 3.3 Three Repair Strategies

**Strategy A — Graded Admissibility (Recommended)**

Replace the single `Admissible` with a step-indexed version:

```lean
structure AdmissibleN (n : Nat) (old new : ThermodynamicState) : Prop where
  massDensity   : |new.density - old.density| ≤ n * δMass
  clausiusDuhem : new.freeEnergy ≤ old.freeEnergy
  hydrationMono : old.hydration ≤ new.hydration
  strengthMono  : old.strength ≤ new.strength
```

Then composition is **provable** (not axiomatic):

```lean
theorem admissibleN_compose :
    AdmissibleN m s s' → AdmissibleN n s' s'' → AdmissibleN (m + n) s s''
```

The existing `Admissible` becomes `AdmissibleN 1`. Kleisli composition of N arrows gives `AdmissibleN N`. This is a **graded monad** / **indexed monad** structure.

**Strategy B — Weaken WellTyped**

Change `WellTyped` to require only consecutive admissibility, dropping end-to-end:

```lean
def WellTypedLocal (f : KleisliArrow) : Prop :=
  ∀ s s', f s = some s' → Admissible s s'
-- No claim about composed arrows reaching beyond one step
```

This preserves the existing `Admissible` definition but weakens the composition theorem.

**Strategy C — Endpoint Mass Check**

Keep single-step `Admissible` for consecutive pairs, add an endpoint invariant separately:

```lean
def SafeExecution (init final : ThermodynamicState) (path : List ThermodynamicState) : Prop :=
  ConstitutionalSeq (init :: path ++ [final]) ∧
  |final.density - init.density| ≤ δMass
```

### 3.4 Recommended Action

**Strategy A** is recommended because it:
- Preserves all existing theorems (single-step = `AdmissibleN 1`)
- Makes the mass accumulation explicit in the type
- Is the mathematically natural structure (graded monad / Lawvere metric enrichment)
- Allows the bound to be checked at any granularity

---

## 4. Axiom Audit

### 4.1 fcMonotone — No Concrete Witness (HIGH)

**Problem:** The axiom quantifies over ALL `ThermodynamicState` pairs, but the Powers model `fc = S · x³` where `x = 0.68α / (0.32α + w/c)` is monotone in α only at **fixed w/c ratio**. Since `ThermodynamicState` does not carry `w/c`, the axiom asserts monotonicity even across states with different water-cement ratios — **physically false**.

**Repair plan:**

1. Add `waterCementRatio : ℚ` to `ThermodynamicState` (or parameterise the gate).
2. Define `PowersState s` analogous to `HelmholtzState s`:
   ```lean
   def PowersState (s : ThermodynamicState) (wc : ℚ) : Prop :=
     s.strength = S_intrinsic * ((0.68 * s.hydration) / (0.32 * s.hydration + wc)) ^ 3
   ```
3. Prove `powersMonotone` as a concrete witness:
   ```lean
   theorem powersMonotone (s₁ s₂ : ThermodynamicState) (wc : ℚ)
       (hp₁ : PowersState s₁ wc) (hp₂ : PowersState s₂ wc)
       (hwc : 0 < wc) (hα : s₁.hydration ≤ s₂.hydration) :
       s₁.strength ≤ s₂.strength
   ```
4. Narrow `fcMonotone` to carry `PowersState` hypotheses (or keep as interface spec with documented scope limitation).

### 4.2 psiAntitone — Over-Quantified (MEDIUM)

**Problem:** The axiom asserts `∀ s₁ s₂, hydration s₁ ≤ hydration s₂ → freeEnergy s₂ ≤ freeEnergy s₁` for ALL states, but the concrete witness `ψAntitoneHelmholtz` is conditioned on `HelmholtzState s₁ ∧ HelmholtzState s₂`.

**The gap:** States where `freeEnergy` is unrelated to `hydration` (e.g., manually constructed with arbitrary field values) satisfy the axiom vacuously. The axiom is consistent but **physically overbroad**.

**Repair plan:**

1. Parameterise the gate over a free-energy model typeclass:
   ```lean
   class FreeEnergyModel where
     freeEnergyOf : ℚ → ℚ  -- hydration → free energy
     antitone : ∀ α₁ α₂, α₁ ≤ α₂ → freeEnergyOf α₂ ≤ freeEnergyOf α₁
   ```
2. Or: narrow the axiom to states satisfying a model constraint:
   ```lean
   axiom psiAntitone (s₁ s₂ : ThermodynamicState)
       (h₁ : ValidFreeEnergy s₁) (h₂ : ValidFreeEnergy s₂) :
       s₁.hydration ≤ s₂.hydration → s₂.freeEnergy ≤ s₁.freeEnergy
   ```

### 4.3 Opaque DIB Types — Informationally Vacuous (MEDIUM)

**Historical note (pre–Wave 6.5):** This paragraph referred to an early DIB layer where phase carriers were fully opaque and a removed `gateIsTotal` stub. **Current tree:** `Observation` … `Artifact` are `structure`s; `DIBState` / `discover` / `invent` / `build` remain opaque; artifact semantics use `artifactSemanticStep` + `dibArtifactGateCheck_eq_true` (see `FORMAL_FOUNDATIONS.md`). The monad laws still abstract over `DIBState`.

**Problem (audit framing):** Kleisli laws carry no domain-specific thermo content until linked to `gateCheck`; the remaining gap is a full Field/Core functor from `M Artifact` to traced thermo states.

**Assessment:** The DIB module is a **methodology model**, not a physical model. Its monad laws prove compositional coherence of the pipeline, which is the correct property for a one-pass pipeline. This is not an error, but it should be honestly documented as carrying no physical content beyond the structural guarantee.

**No repair needed** — but documentation should note that the DIB module adds categorical structure without domain-specific theorems.

### 4.4 Naturality — Trivially True (MEDIUM)

**Problem:** `gateMaterialAgnostic` (Lean) returns `rfl`. `naturalitySquare` reduces to `rfl` after pattern-matching on the identity morphism of the discrete category. These are tautologies, not non-trivial categorical results.

**Assessment:** The naturality claim is accurate but weak. The gate IS material-agnostic (it doesn't inspect the material label), but proving this on a discrete category is trivially true for ANY function that takes states as inputs.

**Repair plan:** The stronger claim would be naturality on a **non-discrete** category of materials (e.g., with sub-class morphisms like CEM-I → CEM-II). This would require non-trivial proof. See §6.

---

## 5. End-Condition Proofs Pending

### 5.1 Constitutional Sequence Convergence

**Gap:** Constitutional sequences are well-typed but unbounded. No proof that hydration reaches equilibrium.

**Theorem to prove:**

```lean
theorem hydrationConverges
    (seq : Nat → ThermodynamicState)
    (hadm : ∀ n, Admissible (seq n) (seq (n+1)))
    (hbound : ∀ n, 0 ≤ (seq n).hydration ∧ (seq n).hydration ≤ 1) :
    ∃ α_star, Filter.Tendsto (fun n => (seq n).hydration) Filter.atTop (nhds α_star)
```

**Proof strategy:** Monotone Convergence Theorem. The hydration sequence is:
- Monotonically non-decreasing (from `hydrationMono` in `Admissible`)
- Bounded above by 1 (physical axiom to add)

Mathlib provides `tendsto_of_monotone` + `BddAbove` → convergence.

**Required new axioms:**
```lean
axiom hydration_bounded : ∀ s : ThermodynamicState, 0 ≤ s.hydration ∧ s.hydration ≤ 1
axiom strength_bounded : ∀ s : ThermodynamicState, s.strength ≤ S_intrinsic
```

### 5.2 Lyapunov Function

**Gap:** The Helmholtz free energy `ψ` is a natural Lyapunov function (monotonically decreasing, bounded below by `-Q_hyd`), but no formal convergence proof uses it.

**Theorem to prove:**

```lean
theorem lyapunovConvergence
    (seq : Nat → ThermodynamicState)
    (hadm : ∀ n, Admissible (seq n) (seq (n+1)))
    (hHelm : ∀ n, HelmholtzState (seq n)) :
    ∃ ψ_star, Filter.Tendsto (fun n => (seq n).freeEnergy) Filter.atTop (nhds ψ_star) ∧
              -Q_hyd ≤ ψ_star
```

### 5.3 Fixed Point Characterisation

**Gap:** No proof that the equilibrium state exists, is unique, or is attracting.

**Theorem to prove:**

```lean
theorem equilibriumExists
    (propose : ThermodynamicState → ThermodynamicState)
    (hPhys : PhysicallyReasonable propose) :
    ∃ s_eq : ThermodynamicState,
      propose s_eq = s_eq ∧ Admissible s_eq s_eq ∧
      s_eq.hydration = 1 ∧ s_eq.freeEnergy = helmholtz 1
```

The second conjunct is trivial (`admissibleRefl`). The first requires a fixpoint theorem or explicit construction.

### 5.4 Accumulated Mass Bound

**Gap:** No proof that N-step sequences have bounded mass drift.

**Theorem to prove (replaces admissibleTrans):**

```lean
theorem accumulatedMassBound
    (seq : List ThermodynamicState)
    (hseq : ConstitutionalSeq seq)
    (hlen : seq.length = N + 1) :
    |(seq.getLast hne).density - (seq.head hne).density| ≤ N * δMass
```

**Proof:** Induction on N, using triangle inequality at each step.

### 5.5 Completeness of the Four Invariants

**Gap:** Are four invariants sufficient? Can unphysical transitions pass?

**Positive result to prove (isothermal correspondence):**

```lean
theorem isothermalClausiusDuhemCorrespondence :
    -- Under isothermal, mechanically quiescent conditions,
    -- the full Clausius-Duhem inequality reduces to ψ_new ≤ ψ_old
    IsothermalQuiescent s₁ s₂ →
    (fullClausiusDuhem s₁ s₂ ↔ DissipCond s₁ s₂)
```

**Negative result (false positive counterexample):**

A transition where all four invariants pass but the state is unphysical (e.g., negative w/c ratio, impossible stoichiometry). This demonstrates the gate is **necessary but not sufficient**.

---

## 6. Category-Theoretic Completions

### 6.1 Enriched Category (Lawvere Metric Space)

**What:** Formalize the admissibility relation as a category enriched over `([0,∞], ≥, +)`.

**Why:** The mass condition is metric (not order-theoretic). The Lawvere perspective makes the non-transitivity explicit and motivates the graded monad repair from §3.

**Implementation:**
```lean
-- New file: EnrichedAdmissibility.lean
def massDistance (s₁ s₂ : ThermodynamicState) : ℚ :=
  |s₂.density - s₁.density|

theorem massDistance_self (s : ThermodynamicState) : massDistance s s = 0 := by
  simp [massDistance, sub_self, abs_zero]

theorem massDistance_triangle (s₁ s₂ s₃ : ThermodynamicState) :
    massDistance s₁ s₃ ≤ massDistance s₁ s₂ + massDistance s₂ s₃ := by
  -- From abs_sub_abs_le_abs_sub in Mathlib
  sorry -- standard triangle inequality on rationals
```

**Difficulty:** Medium | **Value:** High

### 6.2 Fibration (ActivatedUMST)

**What:** Formalize `ActivatedUMST` as a fibration `p : E → MaterialClass` using Mathlib's `CategoryTheory.FiberedCategory`.

**Why:** Sets up the path toward non-trivial sheaf structure when `MaterialClass` gets subclass ordering.

**Implementation:**
```lean
-- New file: FiberedActivation.lean
def TotalActivation := (m : MaterialClass) × ActivatedUMST m
def projMat : TotalActivation → MaterialClass := Sigma.fst

-- Fibers are singletons (engines uniquely determined by material)
theorem fiber_subsingleton (M : MaterialClass) :
    ∀ a b : ActivatedUMST M, a = b := by
  intro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  have : e₁ = e₂ := by rw [h₁, h₂]
  subst this; rfl
```

**Difficulty:** Low-Medium | **Value:** Medium

### 6.3 Monoidal Structure

**What:** Define tensor product on `ThermodynamicState` via volume-weighted averaging.

**Why:** Mass conservation is claimed as monoidal coherence (Naturality.agda §8), but nothing is formalized.

**Key negative result to prove:**
```lean
-- The gate is NOT monoidal in general
theorem gate_not_monoidal :
    ∃ (old₁ new₁ old₂ new₂ : ThermodynamicState) (v : VolumeFraction),
      Admissible old₁ new₁ ∧ Admissible old₂ new₂ ∧
      ¬ Admissible (tensorState v old₁ old₂) (tensorState v new₁ new₂)
```

**Difficulty:** Medium-High | **Value:** High (negative results clarify scope)

### 6.4 Galois Connection

**What:** The four gate conditions form a Galois connection between the lattice of condition-subsets and the lattice of transition-pair predicates.

**Implementation:**
```lean
-- New file: GaloisGate.lean
def conditionMeet (S : Finset (Fin 4)) : ThermodynamicState → ThermodynamicState → Prop :=
  fun old new => (0 ∈ S → MassCond old new) ∧ (1 ∈ S → DissipCond old new) ∧
                 (2 ∈ S → HydratCond old new) ∧ (3 ∈ S → StrengthCond old new)

def conditionExtract (P : ThermodynamicState → ThermodynamicState → Prop) : Finset (Fin 4) :=
  Finset.filter (fun i => ∀ old new, P old new → conditionMeet {i} old new) Finset.univ

-- Galois connection: conditionMeet ⊣ conditionExtract
theorem galois_connection :
    GaloisConnection conditionMeet conditionExtract := by sorry
```

**Difficulty:** Low | **Value:** High

### 6.5 Non-Discrete Naturality (Future)

**What:** Extend `MaterialClass` to a poset with subclass morphisms (e.g., `CEM_I ≤ CEM_II`). Prove non-trivial naturality.

**Why:** The current naturality proof is `rfl`. A non-discrete category would require proving that the gate commutes with material refinement functors — a genuinely non-trivial claim.

**Difficulty:** High | **Value:** Very High (but future work)

---

## 7. Graph-Theoretic Properties

### 7.1 Admissibility Graph Structure

The admissibility relation defines a directed graph `G = (V, E)`:
- `V = ThermodynamicState` (infinite, over ℚ⁴)
- `(s, s') ∈ E ⟺ Admissible s s'`

**Properties:**
| Property | Mass | Clausius-Duhem | Hydration | Strength | Full `Admissible` |
|----------|------|---------------|-----------|----------|-------------------|
| Reflexive | ✓ | ✓ | ✓ | ✓ | ✓ (proved) |
| Symmetric | ✓ | ✗ | ✗ | ✗ | ✗ |
| Transitive | **✗** | ✓ | ✓ | ✓ | **✗** |
| Antisymmetric | ✗ | ✓ | ✓ | ✓ | ✗ |

### 7.2 Mass Non-Transitivity (Formal Counterexample)

```lean
-- New file: GraphProperties.lean
theorem mass_not_transitive :
    ∃ s₁ s₂ s₃ : ThermodynamicState,
      MassCond s₁ s₂ ∧ MassCond s₂ s₃ ∧ ¬ MassCond s₁ s₃ := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨99, 0, 0, 0⟩, ⟨198, 0, 0, 0⟩, ?_, ?_, ?_⟩
  · -- |99 - 0| = 99 ≤ 100
    simp [MassCond, δMass]; norm_num
  · -- |198 - 99| = 99 ≤ 100
    simp [MassCond, δMass]; norm_num
  · -- |198 - 0| = 198 > 100
    simp [MassCond, δMass]; norm_num; linarith
```

### 7.3 Hydration DAG Property

```lean
theorem hydration_acyclic (s s' : ThermodynamicState)
    (h : Admissible s s') (hstrict : s.hydration < s'.hydration) :
    ¬ Admissible s' s := by
  intro h_rev
  have := h_rev.hydrationMono  -- s'.hydration ≤ s.hydration
  linarith
```

### 7.4 Order-Dimension Transitivity

```lean
theorem dissipCond_transitive : ∀ s₁ s₂ s₃,
    DissipCond s₁ s₂ → DissipCond s₂ s₃ → DissipCond s₁ s₃ :=
  fun _ _ _ h₁ h₂ => le_trans h₂ h₁

theorem hydratCond_transitive : ∀ s₁ s₂ s₃,
    HydratCond s₁ s₂ → HydratCond s₂ s₃ → HydratCond s₁ s₃ :=
  fun _ _ _ h₁ h₂ => le_trans h₁ h₂

theorem strengthCond_transitive : ∀ s₁ s₂ s₃,
    StrengthCond s₁ s₂ → StrengthCond s₂ s₃ → StrengthCond s₁ s₃ :=
  fun _ _ _ h₁ h₂ => le_trans h₁ h₂
```

---

## 8. Theory Extensions (T_ext)

### 8.0 Dependency Graph

```
L₀ (gate + Landauer-Einstein algebra)
  │
  ├─► T_LandauerLaw   = L₀ + processes + entropy + second law     [INDEPENDENT]
  ├─► T_GR             = L₀ + Lorentzian geometry + Einstein eqs
  │       ├─► T_Jacobson   (horizon thermodynamics + Clausius)
  │       ├─► T_Bekenstein (entropy + energy conditions)
  │       └─► T_Friedmann  (FLRW + T_μν + EOS)
  └─► T_Interpretation  = explicit maps from "information" to T_μν
```

### 8.1 T_LandauerLaw (Priority 1 — Self-Contained)

**Target theorem (schematic):**

```lean
-- ∀ erasure process ε in class 𝒞, average work ≥ k_B T ln 2
theorem landauer_bound (n : Nat) (proc : ErasureProcess n)
    (prior : Fin n → ℝ) (hprior : IsProbDist prior)
    (hSecondLaw : SecondLawAxiom) :
    avgWork proc prior ≥ kBoltzmannSI * proc.bathTemp.val * Real.log 2
```

**ΔL required:**

| New Type | Purpose |
|----------|---------|
| `ErasureProcess n` | Stochastic kernel / CPTP map on `Fin n` |
| `LogIrreversible` | Channel is not injective on distinguishable states |
| `GibbsEntropy` | `S(p) = -∑ pᵢ log pᵢ` |
| `SecondLawAxiom` | Total entropy non-decreasing (**axiom**) |
| `IsothermalFirstLaw` | Work = ΔF + T·ΔS_bath |

**Proof pattern:** Data-processing inequality for KL divergence. Standard in quantum thermodynamics.

**L₀ theorems that lift:** `landauerBitEnergy_pos`, `massEquivalent_pos`, `massEquivalent_linear`, 300K brackets.

**Estimated effort:** 1 new file `LandauerLaw.lean` (~300-400 lines). Depends on Mathlib `MeasureTheory.Measure` and `Analysis.SpecialFunctions.Log.Basic` (already imported).

### 8.2 T_GR (Priority 2 — Foundation for Others)

**Target:** Minimal Lorentzian geometry to express Einstein field equations.

**ΔL required:**

| New Type | Purpose | Mathlib Status |
|----------|---------|----------------|
| `LorentzianManifold` | Smooth 4-manifold with (-,+,+,+) metric | **Not in Mathlib** (Riemannian only) |
| `StressEnergyTensor` | Symmetric (0,2)-tensor field | Requires tensor bundle |
| `EinsteinTensor` | `G_μν = R_μν - ½Rg_μν` | Requires Ricci, scalar curvature |
| `LeviCivitaConnection` (pseudo-Riem) | Covariant derivative | Partial in Mathlib (Riemannian) |
| `G_Newton : ℝ` | Newton's constant (SI) | Definition |

**Critical gap:** Mathlib has `SmoothManifoldWithCorners` and tangent bundles but NO Lorentzian signature, NO curvature tensors on pseudo-Riemannian manifolds.

**Pragmatic approach:** Axiomatize curvature tensors initially; replace with Mathlib constructions as they become available.

**Estimated effort:** 2-3 new files (~800-1200 lines). Heavy axiom load.

### 8.3 T_Jacobson (Priority 3)

**Target:** Derive Einstein equations from horizon thermodynamics.

**ΔL required (beyond T_GR):**
- `LocalRindlerHorizon` — null surface + acceleration parameter
- `unruhTemp a = ℏa / (2πk_Bc)` — definition
- `clausius_on_horizons` — **axiom**: δQ = T·δS on horizons
- `entropy_area_proportionality` — **axiom**: S = A/(4Gℏ)

**Proof structure:** Following Jacobson (1995):
1. Any point p, any null vector k → construct local Rindler horizon
2. Clausius: δQ = T_Unruh · δS
3. δQ = ∫ T_μν k^μ dΣ^ν (heat flux definition)
4. δS = δA / (4Gℏ) (Bekenstein-Hawking)
5. δA → R_μν k^μ k^ν via Raychaudhuri equation (geometric identity, derivable)
6. Combine: R_μν k^μ k^ν = 8πG T_μν k^μ k^ν for all null k
7. Algebraic → G_μν + Λg_μν = 8πG T_μν

**Estimated effort:** 1 file `Jacobson.lean` (~400 lines).

### 8.4 T_Bekenstein (Priority 4)

**Target:** Entropy bound S ≤ A/(4Gℏ).

**ΔL:** Null energy condition, area functional on horizons, entropy definition (ideally quantum — von Neumann — but classical Gibbs is a tractable first pass).

**Estimated effort:** 1 file `BekensteinBound.lean` (~200 lines, mostly axiomatic).

### 8.5 T_Friedmann (Priority 5)

**Target:** FLRW ODEs from Einstein equations + cosmological symmetry.

**ΔL:** `FLRWAnsatz` (scale factor + curvature parameter), `FluidComponent` (ρ, p, w), stress-energy decomposition.

**Where information density enters:** As one `FluidComponent` with ρ_info derived from `massEquivalent`:
```lean
def informationFluid (bitDensity : ℝ → ℝ) (T : ℝ) : FluidComponent where
  rho := fun t => bitDensity t * massEquivalent T
  w := w_info  -- equation of state (MODEL CHOICE, must be axiom)
```

**Estimated effort:** 1 file `Friedmann.lean` (~500 lines). The FLRW computation is mechanical but lengthy.

---

## 9. Rational vs Float Correspondence

### 9.1 The Gap

All proofs are over ℚ. The Rust kernel uses `f64` with `1e-6` tolerances. `f64` arithmetic is NOT a field (associativity fails). The FFI bridge (`ffi-bridge/src/lib.rs`) uses explicit `f64` comparisons.

Key discrepancies:
- Formal: `|ρ_new - ρ_old| ≤ 100` (exact ℚ)
- Rust: `(new_density - old_density).abs() < 100.0` (f64, strict inequality, tolerance)
- Formal: `ψ_new ≤ ψ_old` (exact ℚ)
- Rust: `d_int >= -1e-6` (f64, with tolerance)

### 9.2 Repair Plan

**Theorem to prove:**

```lean
-- If the rational gate accepts, the f64 gate also accepts
-- (given machine-epsilon representability)
theorem f64_soundness
    (old new : ThermodynamicState)
    (h : gateCheck old new = true)
    (h_repr : ∀ field, |f64_encode (field old) - field old| ≤ ε_machine * |field old|) :
    f64_gateCheck (f64_encode old) (f64_encode new) = true
```

**Approach options:**
1. **Coq + Flocq** — mature IEEE 754 formalization. Labor-intensive but achievable.
2. **Pen-and-paper + axiom** — derive error bounds analytically, encode as axiom. Pragmatic.
3. **Interval arithmetic** — define `FloatInterval` tracking error bounds. Clean but requires new infrastructure.

**Priority:** MEDIUM-HIGH | **Difficulty:** HIGH

---

## 10. Implementation Sequencing

### Phase 0: Critical Repair (admissibleTrans)

| Task | File | Difficulty | Blocks |
|------|------|-----------|--------|
| Prove `mass_not_transitive` counterexample | `GraphProperties.lean` (new) | Low | Nothing |
| Define `AdmissibleN` graded structure | `Gate.lean` (extend) | Medium | Phase 1 |
| Prove `admissibleN_compose` | `Gate.lean` | Medium | Phase 1 |
| Refactor `kleisliComposeWellTyped` | `Constitutional.lean` | Medium | N/A |
| Remove `admissibleTrans` axiom | `Constitutional.lean` | Low | Phase 0 tasks above |
| Mirror in Coq: `Constitutional.v` | `Constitutional.v` | Medium | N/A |
| Mirror in Agda (if applicable) | N/A (Agda uses DIB monad) | N/A | N/A |
| Update `PROOF-STATUS.md` | `PROOF-STATUS.md` | Low | N/A |

### Phase 1: Close Existing Gaps

| Task | File | Priority | Difficulty |
|------|------|----------|-----------|
| Prove `powersMonotone` (witness for `fcMonotone`) | `Helmholtz.lean` or new `Powers.lean` | HIGH | Medium |
| Add `hydration_bounded` axiom | `Gate.lean` | HIGH | Low |
| Prove `hydrationConverges` | New `Convergence.lean` | HIGH | Medium |
| Prove `lyapunovConvergence` | `Convergence.lean` | HIGH | Medium |
| Prove `accumulatedMassBound` | `GraphProperties.lean` | HIGH | Low |
| Prove order-dimension transitivity | `GraphProperties.lean` | MEDIUM | Low |
| Prove `hydration_acyclic` | `GraphProperties.lean` | MEDIUM | Low |
| Prove `isothermalClausiusDuhemCorrespondence` | New `ClausiusDuhem.lean` | MEDIUM | Low-Medium |

### Phase 2: Category-Theoretic Foundations

| Task | File | Priority | Difficulty |
|------|------|----------|-----------|
| Galois connection for gate conditions | New `GaloisGate.lean` | HIGH | Low |
| Enriched admissibility (Lawvere metric) | New `EnrichedAdmissibility.lean` | HIGH | Medium |
| Fibered activation (Grothendieck construction) | New `FiberedActivation.lean` | MEDIUM | Low-Medium |
| Monoidal structure + negative result | New `MonoidalState.lean` | MEDIUM | Medium-High |

### Phase 3: Theory Extensions

| Task | File | Priority | Difficulty |
|------|------|----------|-----------|
| T_LandauerLaw | New `LandauerLaw.lean` | Priority 1 | Medium |
| T_GR skeleton | New `LorentzianManifold.lean`, `StressEnergy.lean` | Priority 2 | High |
| T_Jacobson | New `Jacobson.lean` | Priority 3 | High |
| T_Bekenstein | New `BekensteinBound.lean` | Priority 4 | Medium |
| T_Friedmann | New `Friedmann.lean` | Priority 5 | Medium-High |

### Phase 4: Bridge & Polish

| Task | File | Priority | Difficulty |
|------|------|----------|-----------|
| ℚ vs f64 error bound analysis | New `FloatBridge.lean` or Coq+Flocq | MEDIUM-HIGH | HIGH |
| Non-discrete naturality (MaterialClass poset) | Extend `Naturality.lean` | LOW | HIGH |
| Damage context indexing | Extend `Gate.lean` | MEDIUM | Medium |
| Cross-prover constant alignment (Coq ↔ Lean) | Policy doc update | LOW | Low |

---

## 11. Proof Dependency DAG

```
ThermodynamicState ← δMass, Q_hyd, helmholtz
       │
       ├── Admissible ← psiAntitone*, fcMonotone*
       │       │
       │       ├── gateCheck ← gateCheckSound, gateCheckComplete
       │       │       │
       │       │       └── ConstitutionalSeq ← subjectReduction
       │       │               │
       │       │               └── kleisliAdmissibility ← sequentialCompositionSafe†
       │       │
       │       ├── forwardHydrationAdmissible ← gate-accepts-forward
       │       │
       │       ├── admissibleRefl ← identityWellTyped, kleisliFoldWellTyped†
       │       │
       │       ├── admissibleTrans† ← kleisliComposeWellTyped†, kleisliFoldWellTyped†
       │       │                       (REFUTABLE — contaminated subtree)
       │       │
       │       └── admissibleIffCSG (CSG decomposition)
       │
       ├── HelmholtzState ← ψAntitoneHelmholtz, helmholtzStateAdmissible
       │
       ├── MaterialClass ← stateFor, activation, ActivatedUMST
       │       │
       │       ├── gateMaterialAgnostic, naturalitySquare
       │       │
       │       └── activationTotal, engine witnesses, negative proofs
       │
       ├── M (DIB monad) ← pureM, bindM, leftUnit, rightUnit, assocM
       │       │
       │       └── dib, dibAssoc, kleisliAssoc [DISCONNECTED from gate layer]
       │
       └── massEquivalent ← kBoltzmannSI, speedOfLightSI, landauerBitEnergy
               │
               ├── massEquivalent_pos, massEquivalent_linear
               │
               └── massEquivalent_three_hundred_interval[_tight]

Legend: * = physical axiom (interface spec)
        † = contaminated by admissibleTrans
```

---

## 12. File-Level Impact Map

| File | Changes Needed | Phase |
|------|---------------|-------|
| `Lean/Gate.lean` | Add `AdmissibleN`, `hydration_bounded`, narrow `psiAntitone`/`fcMonotone` | 0, 1 |
| `Lean/Constitutional.lean` | Remove `admissibleTrans`, refactor Kleisli with graded types | 0 |
| `Lean/Helmholtz.lean` | Add Lyapunov convergence, Powers model witness | 1 |
| `Coq/Constitutional.v` | Mirror `admissibleTrans` removal | 0 |
| `Coq/Gate.v` | Mirror graded admissibility if desired | 0 |
| `PROOF-STATUS.md` | Update axiom inventory, add new theorem rows | 0, 1, 2, 3 |
| `Docs/FORMAL-PHYSICS-DERIVATION-PLAN.md` | Update with precise T_ext signatures | 3 |
| `Lean/lakefile.lean` | Register new module roots | 1, 2, 3 |
| **New files:** | |
| `Lean/GraphProperties.lean` | Mass counterexample, DAG, transitivity | 0, 1 |
| `Lean/Convergence.lean` | Hydration convergence, Lyapunov, fixpoint | 1 |
| `Lean/GaloisGate.lean` | Galois connection for conditions | 2 |
| `Lean/EnrichedAdmissibility.lean` | Lawvere metric structure | 2 |
| `Lean/FiberedActivation.lean` | Grothendieck construction | 2 |
| `Lean/MonoidalState.lean` | Tensor product + negative result | 2 |
| `Lean/Powers.lean` | Powers gel-space model + monotonicity | 1 |
| `Lean/LandauerLaw.lean` | Full Landauer bound theorem | 3 |
| `Lean/LorentzianManifold.lean` | T_GR types | 3 |
| `Lean/StressEnergy.lean` | T_GR + interpretation map | 3 |
| `Lean/Jacobson.lean` | T_Jacobson theorem | 3 |
| `Lean/BekensteinBound.lean` | T_Bekenstein | 3 |
| `Lean/Friedmann.lean` | T_Friedmann | 3 |

---

## Appendix A: Claims That Must Remain Axioms

These are physically motivated but NOT derivable within any reasonable T_ext:

| Claim | Why It's an Axiom |
|-------|-------------------|
| Second Law of Thermodynamics (in T_LandauerLaw) | Derivation requires full statistical mechanics / microscopic dynamics |
| Clausius relation on horizons (in T_Jacobson) | Founding physical postulate of Jacobson program |
| Entropy-area proportionality (in T_Bekenstein) | Bekenstein-Hawking formula; derivable only in quantum gravity |
| Equation of state for information (w_info in T_Friedmann) | Physical model choice, not logically determined |
| FLRW symmetry ansatz | Assumption about the universe, not derivable from Einstein equations |
| Lorentzian signature | Global property of spacetime, not derivable from topology |

## Appendix B: Claims That Should Become Theorems (Currently Axioms)

| Current Axiom | Can Be Proved From | Action |
|---------------|-------------------|--------|
| `admissibleTrans` | **REFUTABLE** — must be removed or replaced | Replace with `admissibleN_compose` |
| `psiAntitone` (universal) | `ψAntitoneHelmholtz` + model constraint | Narrow to `HelmholtzState` or parameterise |
| `fcMonotone` (universal) | Powers formula at fixed w/c | Add `PowersState` + prove `powersMonotone` |
| `helmholtz-linear` (Agda) | Already proved in Coq/Lean | Port proof to Agda |
| `helmholtz-gradient-const` (Agda) | Already proved in Coq/Lean | Port proof to Agda |
