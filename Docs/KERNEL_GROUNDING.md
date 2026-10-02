<!-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar -->
<!-- SPDX-License-Identifier: MIT -->

# Kernel Grounding

Design proposal. It changes no code. It specifies the machine-checked statements that ground the two development kernels, `umst-adk` and `umst-gdk` (both under `umst/umst-meta/crates/`), where those statements live in this repository, how the kernels cite them at zero run-time cost, and the ordered cells that build them.

The ecosystem has one physical predicate, `UMST.ProcessFamily.SecondLaw : Process → Prior → Prop` (`Lean/Process.lean`). The kernels are mostly combinatorial and algebraic programs. Two of their invariants are instances of the predicate and one more is conditional on an interpretation. Section 3 states which. The remaining invariants receive proofs of their own, in the same four languages and under the same parity contract, with no physical reading attached.

## 1. Verified ground

Each item below was read in the working tree on 2026-10-03. Items 1 to 5 constrain the design. Items 6 to 11 are findings the proofs will force into the open; each becomes a cell in section 6.

1. **The parity budget is spent.** `formal_parity.json` has 80 statements and 15 absent language entries against `max_absent` 15 (`scripts/check_formal_parity.py --summary`). Every new row therefore carries a Lean, a Coq, an Agda and a Haskell entry. Statements that need a real logarithm or exponential are stated over an abstract exponential field (K6) or over bits (K10), which Agda states without a real analysis library.
2. **A contract module admits only declarations that have rows.** The checker flags every `theorem`, `lemma`, `def`, `abbrev`, `structure`, `inductive` and `class` of a `contract_modules` entry that appears in no statement (private ones included). Helper lemmas live in `Lean/Kernel/Support/` modules, which are outside the contract; contract modules hold statements and the definitions those statements mention.
3. **Typed Lean references exist on a local branch.** `Derivation::Theorem { decl: LeanDecl { module, name }, expected_value }` and `umst-math/tests/theorem_derivations_resolve.rs` are in umst-manifold commits `007f8482` and `13d4ff8d` (branch `docs/reorganize-readme`). The checked-out `main` has `Derivation::Theorem { theorem_id: &str, .. }` and no resolver test. The resolver reads `artifacts/upstream_catalog.json`, the composed export pinned by `catalog.lock.json`; the catalog of this repository is `artifacts/catalog.json` (`modules[].module` such as `Core.Constitutional`, `modules[].declarations` keyed by kind). The design below builds the typed reference in this repository, so the kernels do not wait on that branch.
4. **`umst-gdk` already grounds a claim in the catalog.** `verify_catalog_pin` (`umst-gdk/src/evidence.rs:59`) accepts a `Pinned` tag when a module of `umst/umst-formal/artifacts/catalog.json` matches the source path, has `content_sha256` equal to `pin_sha256`, and lists `pin_decl`. `scripts/check_catalog_fresh.py` keeps that catalog equal to the tracked Lean sources (SHA-256 and declaration set per file). The two checks together form the grounding chain used in K12.
5. **Constants already have a zero-cost generated crate.** `scripts/gen_constants.py` writes `constants-rs` (`umst-constants`, `#![no_std]`, `const` items). Policy rows carry a `reason` and a `range` of two other rows, proved in each language (`constants/constants.json`). The kernel pins follow this pattern.
6. **`check_holds` is strict in `all` (K2).** `compile.rs:168` collects `Option<bool>` over the conjuncts, so one unmeasurable conjunct yields `None` even when another conjunct is `Some(false)`. `cell_met` (`compile.rs:183`) then falls back to the receipt, and E8 (`compile.rs:427`) tests `cell_check == Some(false)`. A cell `all[failing check, metric check]` is met by a COMPLETE receipt. The worklist has 8 `all` cells and 5 `metric` checks, and no cell mixes them today (counted from `workspace/ops/UMST_WORKLIST.json`), so the gap is latent.
7. **"Committed content" has two sources (K2).** `committed_count` reads `HEAD` through `git grep ... HEAD` (`compile.rs:118`); `committed_exists` reads the index through `git ls-files --error-unmatch` (`compile.rs:132`). A staged, uncommitted file satisfies `file_exists` and `rg_present`'s tracked-ness conjunct while its content is read from `HEAD`.
8. **`TokenMeter::merge` takes `alpha` from the left operand (K10).** `energy.rs:111` makes `merge` additive in `energy()` only for equal `alpha`; token counts use `saturating_add`. Fold sums per-cell surrogates (`sum_landauer_nats`, `energy.rs:157`) and is additive by construction.
9. **The end-to-end priority is not monotone in drift (K8).** `learn` passes the advantage through a peak normalisation, a coupled trust-region scale, and the CBF projection (`learn.rs:509-552`). Only the advantage is antitone in the drift rate. The Lean statement is at the advantage; a property test covers the end-to-end claim until the code adds a monotone envelope.
10. **`refusals` is empty for a non-COMPLETE receipt (K1).** `evidence.rs:473` returns early. Admission is `status = COMPLETE ∧ refusals = ∅`, as `receipt_evidenced` computes (`compile.rs:109`).
11. **Duplicate cell ids break the allocator's contract (K3).** `ConflictGraph::from_cells` (`conflict.rs:102`) builds edges between positions and writes the pair of ids; equal ids give a self-loop or a duplicate output. The proofs take `Nodup` ids as a hypothesis, which the Rust side checks at the boundary.

## 2. Kernel invariants

Each invariant states its source, its value, the typed model, and the theorem statements in Lean. Statements are given without proofs; each module is proved in its cell. Names are final unless a cell reports a clash.

### K1 Receipt admission is monotone on an evidence lattice

Source: `steer/evidence.rs:3-23` (rule list), `:245` (E5), `:298` (E6), `:367` (E7), `:411` (drift), `:472-512` (`refusals`); `steer/compile.rs:109-115` (`receipt_evidenced`), `:424-433` (E8 in `claim_fields`).

Value: a COMPLETE receipt that passes at one time of writing passes under every earlier rule set, and adding evidence never revokes an admission. The steer compiler can then credit receipts without re-judging history.

Model. Evidence splits into witnesses (E1 a proof command executes, E3 changed code is reached, E6 a cited commit exists and touches a delta path, E7 a proof scope meets a changed repository) and offences (E2 a selected test is named by provenance, E5 a delta lies outside the write set). The order raises witnesses and lowers offences. The rule set grows with time: E5 to E7 apply from `ANCHOR_CUTOVER` (`evidence.rs:209`, `anchor_due` at `:276`).

```lean
namespace UMST.Kernel.Receipt

inductive Status | complete | failed | refused
inductive Witness | executes | changesReachedCode | anchoredCommit | scopedProof
  deriving DecidableEq
inductive Offence | provenanceNamedTest | deltaOutsideWriteSet
  deriving DecidableEq

structure Obs where
  witnesses : Finset Witness
  offences  : Finset Offence

/-- More witnesses and fewer offences. -/
def Obs.le (a b : Obs) : Prop := a.witnesses ⊆ b.witnesses ∧ b.offences ⊆ a.offences

/-- Rules in force at time `t`; `cutover` is the anchor cutover. -/
def required (cutover t : ℕ) : Finset Witness :=
  if cutover ≤ t then {.executes, .changesReachedCode, .anchoredCommit, .scopedProof}
  else {.executes, .changesReachedCode}

def active (cutover t : ℕ) : Finset Offence :=
  if cutover ≤ t then {.provenanceNamedTest, .deltaOutsideWriteSet} else {.provenanceNamedTest}

def Admit (cutover t : ℕ) (s : Status) (o : Obs) : Prop :=
  s = .complete ∧ required cutover t ⊆ o.witnesses ∧ o.offences ∩ active cutover t = ∅

theorem admit_mono_obs {a b : Obs} (h : Obs.le a b) :
    Admit c t s a → Admit c t s b

theorem admit_antitone_time {t t' : ℕ} (h : t ≤ t') :
    Admit c t' s o → Admit c t s o

theorem admit_requires_complete : Admit c t s o → s = .complete

/-- The kernel's `refusals` is the failing-rule set; admission is its emptiness together with COMPLETE. -/
theorem admit_iff_refusals_empty :
    Admit c t s o ↔ s = .complete ∧ refusals c t o = ∅

end UMST.Kernel.Receipt
```

E7 holds vacuously when the proof names no path or package (`evidence.rs:384-386`). The model treats `scopedProof` as present in that case, which keeps `admit_mono_obs` true, and a Rust property test covers the extraction.

Rust twin. `refusals` maps a receipt to `Obs` by a total extraction function `obs_of(&Value, root) -> (Status, Obs)`; the property test generates receipts, applies `obs_of`, and compares `refusals(r).is_empty()` with `Admit`.

### K2 A cell is met by its own check, with receipts as the fallback for unmeasurable kinds

Source: `steer/compile.rs:109-115`, `:118-145` (committed reads), `:147-181` (`compare`, `check_holds`), `:183-185` (`cell_met`), `:424-433` (E8); tests `:1236-1276`.

Value: the tracker's meaning of "done" is a decision procedure over committed content, and E8 refuses a COMPLETE claim beside a failing check. A proved evaluator makes the guarantee "a receipt never meets a cell whose check fails" a theorem.

Model. `Check` is the worklist check language (`pool`, `phase_check`, `file_exists`, `rg_present`, `rg_absent`, `rg_count`, `cell_complete`, `all`, and a kernel-unmeasurable `metric`). A `Snapshot` has two committed components, the `HEAD` blob counts and the tracked set of the index, and a tracker state. `denote` is the specification; `eval` is the three-valued evaluator that the kernel computes.

```lean
namespace UMST.Kernel.CellCheck

inductive Cmp | lt | gt | ge | eq | le

inductive Check
  | pool (pool shard : String) (op : Cmp) (v : ℚ)
  | phase (name : String)
  | fileExists (path : String)
  | rgPresent (pat : String) (paths : List String)
  | rgAbsent (pat : String) (paths : List String)
  | rgCount (pat : String) (paths : List String) (op : Cmp) (v : ℚ)
  | cellComplete (cells : List String)
  | metric (name : String)
  | all (cs : List Check)

structure Snapshot where
  headCount : String → String → ℕ      -- occurrences of a fixed pattern in HEAD content under a path
  tracked   : String → Prop            -- membership in the index
  poolShard : String → String → ℚ
  phaseOk   : String → Prop
  evidenced : String → Prop            -- receipt_evidenced of a cell id (K1)

def denote (S : Snapshot) : Check → Option Prop      -- none: the kernel cannot measure this kind
def eval   (S : Snapshot) : Check → Option Bool      -- Kleene conjunction in `all`

/-- Soundness and completeness of the evaluator against the specification. -/
theorem eval_sound (S : Snapshot) (c : Check) (b : Bool) :
    eval S c = some b → (b = true ↔ ∃ p, denote S c = some p ∧ p)

/-- A failing conjunct decides `all` whatever the other conjuncts are. -/
theorem all_false_absorbs (S : Snapshot) (cs : List Check) (c : Check) (h : c ∈ cs) :
    eval S c = some false → eval S (.all cs) = some false

/-- A cell is met by its check when the kernel measures it, by its receipt otherwise. -/
def cellMet (S : Snapshot) (ck : Option Check) (cellId : String) : Prop :=
  match ck.bind (eval S) with
  | some b => b = true
  | none   => S.evidenced cellId

theorem receipt_never_meets_failing_check (S : Snapshot) (c : Check) (id : String) :
    eval S c = some false → ¬ cellMet S (some c) id

/-- Evaluation reads only the two committed components and the tracker. -/
theorem eval_factors_through_commit (S S' : Snapshot)
    (hh : S.headCount = S'.headCount) (ht : S.tracked = S'.tracked)
    (hp : S.poolShard = S'.poolShard) (hk : S.phaseOk = S'.phaseOk) (he : S.evidenced = S'.evidenced) :
    ∀ c, eval S c = eval S' c

end UMST.Kernel.CellCheck
```

Findings 6 and 7 enter here. `all_false_absorbs` fails on the present kernel (strict `collect`), and `eval_factors_through_commit` needs `tracked` as an explicit component because the kernel reads the index for tracked-ness and `HEAD` for counts. Cell KG-3 writes the failing Rust test first, then changes `check_holds` to Kleene conjunction and aligns `committed_exists` with `HEAD` (`git cat-file -e HEAD:<path>`).

### K3 Allocation is a maximal independent set of the conflict graph

Source: `conflict.rs:70-86` (`paths_conflict`), `:102-114` (`from_cells`), `:159-169` (`is_independent_set`), `:186-235` (`allocate_antichain_with_distances`); `hilbert_allocate.rs:86-100` (`hilbert_sort`, `hilbert_sort_preserves_antichain`).

Value: concurrent lanes never share a write path, the output is deterministic in the input as a set, and the locality sort never changes the allocation. The source records the claim level itself (`CONFLICT_NON_CLAIM`, `conflict.rs:13`): greedy, not exact MIS. The theorems state exactly that level.

Model. A path is a list of components with the trailing separator stripped. Two write sets conflict when some pair of paths has one as a component prefix of the other (equal paths included). Cells conflict when their write sets conflict. The selection order is priority descending, then degree ascending, then id ascending; the id tie-break makes the order total on `Nodup` ids.

```lean
namespace UMST.Kernel.Antichain

abbrev Path := List String

def PathConflict (x y : Path) : Prop := x <+: y ∨ y <+: x
def SetConflict (a b : List Path) : Prop := ∃ x ∈ a, ∃ y ∈ b, PathConflict x y

structure Cell (ι : Type) where
  id : ι
  writeSet : List Path
  priority : ℤ

def Conflict {ι} (c d : Cell ι) : Prop := SetConflict c.writeSet d.writeSet

/-- Greedy selection by (priority desc, degree asc, id asc), at most `budget` cells. -/
def allocate {ι} [LinearOrder ι] (budget : ℕ) (cells : List (Cell ι)) : List ι

theorem pathConflict_symm : PathConflict x y → PathConflict y x
theorem setConflict_symm : SetConflict a b → SetConflict b a

theorem allocate_independent [LinearOrder ι] (hn : (cells.map Cell.id).Nodup) :
    ∀ c ∈ cells, ∀ d ∈ cells, c.id ∈ allocate b cells → d.id ∈ allocate b cells →
      c.id ≠ d.id → ¬ Conflict c d

theorem allocate_length_le : (allocate b cells).length ≤ b
theorem allocate_subset : ∀ i ∈ allocate b cells, i ∈ cells.map Cell.id

/-- With budget to spare the selection is maximal: every other cell conflicts with a selected one. -/
theorem allocate_maximal (hn : (cells.map Cell.id).Nodup) (hb : (allocate b cells).length < b) :
    ∀ c ∈ cells, c.id ∈ allocate b cells ∨ ∃ d ∈ cells, d.id ∈ allocate b cells ∧ Conflict c d

/-- The result depends on the set of cells. The Hilbert sort is a permutation, so it never changes it. -/
theorem allocate_perm (hn : (cells.map Cell.id).Nodup) (hp : cells ~ cells') :
    allocate b cells = allocate b cells'

end UMST.Kernel.Antichain
```

Bridge to existing Lean: `Urge/AntichainIndependent.lean` carries `ConflictGraph`, `canonicalConflictEdge` and `isIndependentSet` over `Nat` ids with a zone/suffix path surrogate. `Kernel/Antichain.lean` adds the lemma `isIndependent_iff_pairwise`, which identifies `isIndependentSet` (at `ι = ℕ`) with the pairwise form above, so the two modules share one notion of independence.

Composition with `Excitement.select` is not claimed: `select` minimises global free energy over evidence-tagged candidates, and `allocate` orders by priority. `priority_from_sdf_distance` (`conflict.rs:237`) converts a surrogate distance to an integer, and no theorem relates that integer to a free energy.

### K4 Identity-plan typing is a prefix-closed regular language

Source: `hilbert_allocate.rs:110-141` (step codes, `allocate_identity_plan_well_typed`), `:349-360` (`allocate_antichain_after_identity_plan`), `:102-111` (the two `const fn` refusals).

Value: a plan the allocator refuses can never be extended into one it accepts, and an ill-typed plan yields the empty selection. The refusal constants (`allocate_is_kleisli_compose() = false`) change only when a proved interpretation lands.

Model. Steps are `material | acceptLow | acceptHigh | propagate | creditTransfer | other n` (codes above 4 pass). A plan is ill-typed when it has at least two steps and contains `creditTransfer`, or when `propagate` follows `acceptHigh` anywhere.

```lean
namespace UMST.Kernel.Plan

inductive Step | material | acceptLow | acceptHigh | propagate | creditTransfer | other (n : ℕ)
  deriving DecidableEq

def WellTypedPlan : List Step → Prop

instance : DecidablePred WellTypedPlan

/-- A three-state automaton with a length counter accepts the same language. -/
theorem wellTypedPlan_iff_dfa : ∀ p, WellTypedPlan p ↔ dfaAccepts p

theorem wellTypedPlan_prefix : WellTypedPlan (p ++ q) → WellTypedPlan p
theorem wellTypedPlan_singleton_credit : WellTypedPlan [.creditTransfer]

/-- The gate: an ill-typed plan selects nothing. -/
theorem allocateAfterPlan_ill : ¬ WellTypedPlan p → allocateAfterPlan p b cells = []
theorem allocateAfterPlan_well : WellTypedPlan p → allocateAfterPlan p b cells = Antichain.allocate b cells

end UMST.Kernel.Plan
```

`wellTypedPlan_singleton_credit` records behaviour the present code has (a lone `creditTransfer` passes, `hilbert_allocate.rs:126`); the statement keeps that behaviour visible.

### K5 Learned priorities are bounded and move by at most two

Source: `steer/learn.rs:42-45` (`bounded_priority`), `:545-552` (final map).

Value: no steer can drive a class outside `[1, 10]` or move it more than two units from its base.

```lean
namespace UMST.Kernel.LearnBounds

def boundedPriority (v : ℝ) : ℤ          -- round to nearest, clamp to [1, 10]
def learnedPriority (b v : ℝ) : ℤ := boundedPriority (b + max (-2) (min 2 (v - b)))

theorem boundedPriority_mem (v : ℝ) : 1 ≤ boundedPriority v ∧ boundedPriority v ≤ 10
theorem boundedPriority_int (k : ℤ) (hk : 1 ≤ k ∧ k ≤ 10) : boundedPriority k = k
theorem boundedPriority_mono : Monotone boundedPriority
theorem learnedPriority_displacement (b : ℤ) (hb : 1 ≤ b ∧ b ≤ 10) (v : ℝ) :
    |learnedPriority b v - b| ≤ 2

end UMST.Kernel.LearnBounds
```

The Rust property test feeds NaN and infinities: the range holds (a NaN maps to 10, `learn.rs:44`). A total-order refinement that maps NaN to the base priority is an optional cell; the Lean statement covers real inputs.

### K6 The policy step stays in the trust region

Source: `steer/learn.rs:429-468` (`softmax`, `clipped_policy_step`), test `:761`.

Value: one steer changes each class's selection probability by a factor in `[1/(1+ε), 1+ε]`. The code searches the scale by bisection.

Model. The statement is parametric in an exponential field, which Lean instantiates at `ℝ` with `Real.exp` and Agda states over a record of laws.

```lean
namespace UMST.Kernel.TrustRegion

class ExpField (K : Type) [LinearOrderedField K] where
  exp : K → K
  exp_add : ∀ a b, exp (a + b) = exp a * exp b
  exp_pos : ∀ a, 0 < exp a
  exp_mono : Monotone exp

def softmax [ExpField K] (τ : K) (θ : ι → K) (c : ι) : K
def Within [ExpField K] (ε τ : K) (θ θ' : ι → K) : Prop :=
  ∀ c, 1 / (1 + ε) ≤ softmax τ θ' c / softmax τ θ c ∧ softmax τ θ' c / softmax τ θ c ≤ 1 + ε

/-- The bisection keeps `Within` at its lower end for every iteration count. -/
theorem bisect_within (hε : 0 ≤ ε) (n : ℕ) : Within ε τ θ (θ + (bisect n).lo • (step • unit))

theorem bisect_width (n : ℕ) : (bisect n).hi - (bisect n).lo = 1 / 2 ^ n
theorem step_displacement (hu : ∀ c, |unit c| ≤ 1) : ∀ c, |(bisect n).lo * step * unit c| ≤ |step|

end UMST.Kernel.TrustRegion
```

The log-ratio of a class is concave in the scale, so `Within` holds on an interval around 0 for its lower side and need not be an interval for its upper side. The theorem therefore guarantees safety (`Within` at the returned scale) and a width-`2⁻ⁿ` bracket whose upper end violates it; the doc comment "largest step scale" (`learn.rs:434`) describes the bracket, and the cell corrects the comment to match.

### K7 The evidence barrier and its single-constraint projection

Source: `steer/learn.rs:384-413` (`Barrier`, `barrier`), `:416-425` (`cbf_project`), tests `:749`.

Value: the projection returns the closest priorities that satisfy the evidence constraint, and a sequence that obeys the discrete barrier condition from a safe start stays safe forever.

```lean
namespace UMST.Kernel.Barrier

variable {ι : Type} [Fintype ι]

def cbfProject (p a : ι → ℝ) : ι → ℝ :=
  if 0 ≤ ∑ c, p c * a c ∨ ∑ c, a c ^ 2 = 0 then p
  else fun c => p c + (-(∑ c', p c' * a c') / ∑ c', a c' ^ 2) * a c

theorem cbfProject_feasible : 0 ≤ ∑ c, a c * cbfProject p a c
theorem cbfProject_idempotent : cbfProject (cbfProject p a) a = cbfProject p a
theorem cbfProject_minimal (q : ι → ℝ) (hq : 0 ≤ ∑ c, a c * q c) :
    ∑ c, (cbfProject p a c - p c) ^ 2 ≤ ∑ c, (q c - p c) ^ 2

/-- Share of evidenced claims minus the floor `ρ`. -/
def h (ρ : ℝ) (evidenced claims : ℕ) : ℝ := (evidenced : ℝ) / claims - ρ

theorem safe_iff (hc : 0 < claims) : 0 ≤ h ρ e claims ↔ ρ ≤ (e : ℝ) / claims

/-- Discrete control barrier: `h_{k+1} ≥ (1-γ) h_k` from `h_0 ≥ 0` keeps every `h_k ≥ 0`. -/
theorem barrier_invariant (h : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ ∧ γ ≤ 1)
    (h0 : 0 ≤ h 0) (hstep : ∀ k, (1 - γ) * h k ≤ h (k + 1)) : ∀ k, 0 ≤ h k

theorem barrier_lower_bound (h : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ ∧ γ ≤ 1)
    (hstep : ∀ k, (1 - γ) * h k ≤ h (k + 1)) : ∀ k, (1 - γ) ^ k * h 0 ≤ h k

end UMST.Kernel.Barrier
```

The kernel measures the barrier condition and responds to a violation with recovery actions (`learn.rs:565-574`). The invariance theorem holds for any history in which the measured condition holds at every step, which is the statement the `Barrier.condition_holds` field reports on the last two steers. The Rust twin asserts the projection properties on random vectors against a rational oracle.

### K8 Evidence, hollowness and drift form a small algebra

Source: `steer/learn.rs:50-66` (`Verdict::refutes`), `:99-118` (`evidenced`, `hollow`, `drifted`), `:160-195` (rates), `:203-222` (`observe`), `:545-` (advantage at `:524-533`), tests `:788`, `:809`.

Value: an audit that refutes a COMPLETE claim lowers its class's evidence rate and raises its hollow and drift rates, and an honest failure costs nothing. This is the signal structure the learner trusts.

```lean
namespace UMST.Kernel.Evidence

structure Row where
  claimed : Bool
  moved : Option Bool
  refusalsEmpty : Bool
  refuted : Bool          -- verdict ∈ {drift, incompleteAsComplete}
  flagged : Bool          -- a D1 or D2 drift signal

def Row.evidenced (r : Row) : Bool := r.moved = some true ∧ r.refusalsEmpty ∧ ¬ r.refuted
def Row.hollow (r : Row) : Bool := r.claimed ∧ (¬ r.refusalsEmpty ∨ r.refuted)
def Row.drifted (r : Row) : Bool := r.flagged ∨ r.refuted

theorem evidenced_hollow_exclusive (r : Row) : r.claimed = true → ¬ (r.evidenced ∧ r.hollow)
theorem refute_effect (r : Row) :
    (r.refute).evidenced = false ∧ (r.claimed = true → (r.refute).hollow = true) ∧ (r.refute).drifted = true

/-- Laplace-smoothed evidence rate lies strictly between 0 and 1. -/
def evidenceRate (evidenced claims : ℕ) : ℚ := (evidenced + 1) / (max claims evidenced + 2)
theorem evidenceRate_mem (e c : ℕ) : 0 < evidenceRate e c ∧ evidenceRate e c < 1

theorem refute_lowers_rate (rs : List Row) (r : Row) (h : r ∈ rs) :
    evidenceRate' (rs.map Row.refute_at r) ≤ evidenceRate' rs
theorem refute_raises_hollow_drift : hollowRate' (refute_at rs r) ≥ hollowRate' rs ∧ driftRate' (refute_at rs r) ≥ driftRate' rs

/-- The advantage of a class is antitone in its hollow and drift rates. -/
def advantage (φ overclaim hollow drift w₁ w₂ w₃ : ℝ) : ℝ := φ - w₁ * max overclaim 0 - w₂ * hollow - w₃ * drift
theorem advantage_antitone (h₁ : 0 ≤ w₂) (h₂ : 0 ≤ w₃) :
    hollow ≤ hollow' → drift ≤ drift' → advantage φ o hollow drift w₁ w₂ w₃ ≥ advantage φ o hollow' drift' w₁ w₂ w₃

end UMST.Kernel.Evidence
```

The learner's observation `I(claim; moved)` (`learn.rs:137`) is the plug-in mutual information of a `JointDist 2 2` built from the four counts. Kernel code and `InfoTheory.mutualInformation` (`Lean/InfoTheory.lean:48`) share that definition, so `mutualInformation_product_zero` (`:131`) and the nonnegativity and `≤ log 2` bounds apply to `claim_information_bits`. The learner has no bath or work, so the feedback instance of `SecondLaw` is not instantiated (section 3).

End-to-end claim (finding 9). The Lean statement is `advantage_antitone`. The end-to-end property "an audited DRIFT never raises its class's final priority" is a proptest over random histories (`learn.rs:788` is its single-case ancestor). If the proptest finds a counterexample, the cell adds `priority' := min priority priority_without_drift` as a monotone envelope, which makes the end-to-end claim a theorem.

### K9 HodgeRank is an orthogonal decomposition on a clique complex

Source: `steer/learn.rs:234-256` (`HodgeRank`, `inconsistency`), `:259-290` (conjugate gradients), `:292-368` (`hodge_rank`), tests `:717`, `:734`.

Value: the potential `φ` and the inconsistency share are well defined: the three energies add up, the share lies in `[0, 1]`, and it is zero exactly when a global ranking explains every comparison. `Lean/DEC.lean` proves `Δ₀` symmetric, `B₁B₂ = 0` and the discrete Stokes identity on one oriented triangle over `ℚ`; K9 states them for every finite graph.

```lean
namespace UMST.Kernel.Hodge

structure Complex (V E T : Type) [Fintype V] [Fintype E] [Fintype T] where
  d0 : Matrix E V ℚ
  d1 : Matrix T E ℚ
  d1_d0 : d1 * d0 = 0

/-- The clique complex of a simple graph ordered by index: the orientation the kernel uses. -/
def cliqueComplex (G : SimpleGraph V) [LinearOrder V] : Complex V (Edges G) (Triangles G)

theorem cliqueComplex_dd (G) : (cliqueComplex G).d1 * (cliqueComplex G).d0 = 0

/-- Weighted energy and the normal-equation potential. -/
def energy (W : E → ℚ) (f : E → ℚ) : ℚ := ∑ e, W e * f e ^ 2
def IsPotential (K : Complex V E T) (W f) (φ : V → ℚ) : Prop := K.d0ᵀ *ᵥ (W • (f - K.d0 *ᵥ φ)) = 0

theorem pythagoras (hW : ∀ e, 0 < W e) (hφ : IsPotential K W f φ) :
    energy W f = energy W (K.d0 *ᵥ φ) + energy W (f - K.d0 *ᵥ φ)
theorem inconsistency_mem_Icc : 0 ≤ inconsistency ∧ inconsistency ≤ 1
theorem inconsistency_zero_iff (hW) (hφ) : inconsistency = 0 ↔ f = K.d0 *ᵥ φ

/-- A posteriori bound for the conjugate-gradient result: a small normal-equation residual bounds the energy error. -/
theorem cg_certificate (hW) (r : V → ℚ) (hr : r = K.d0ᵀ *ᵥ (W • (f - K.d0 *ᵥ φ))) :
    energy W (K.d0 *ᵥ (φ - φ★)) ≤ (rnorm r) ^ 2 / λ₂

end UMST.Kernel.Hodge
```

All counts and weights are rationals, so the statements live over `ℚ` and the Agda twin states them without a real analysis library. The Rust solver is floating point; its property test compares the potential with an exact rational solve on small graphs and asserts the `cg_certificate` residual bound on larger ones (a spectral-gap constant `λ₂` of the weighted Laplacian is computed per component and checked).

### K10 The fold's energy sum is additive on a common alpha

Source: `energy.rs:19-35`, `:111-128` (`merge`, `energy`), `:157-166` (`sum_landauer_nats`, `landauer_nats_from_meter`); `fold.rs:108-128` (`sum_gate_deltas`), `:194` (`fold_statuses`).

Value: the fold prior's total equals the sum over its cells, so a wave's Landauer-surrogate figure does not depend on how cells are grouped.

```lean
namespace UMST.Kernel.Energy

structure Meter where
  tokensIn tokensOut : ℕ
  α : ℚ                          -- bits per token

def Meter.bits (m : Meter) : ℚ := (m.tokensIn + m.tokensOut) * m.α
def Meter.merge (a b : Meter) : Meter := ⟨a.tokensIn + b.tokensIn, a.tokensOut + b.tokensOut, a.α⟩

theorem merge_bits (h : a.α = b.α) : (a.merge b).bits = a.bits + b.bits
theorem merge_assoc (a b c : Meter) : (a.merge b).merge c = a.merge (b.merge c)
theorem merge_comm_of_alpha (h : a.α = b.α) : a.merge b = b.merge a
theorem merge_bits_counterexample : ∃ a b : Meter, (a.merge b).bits ≠ a.bits + b.bits

/-- A fold over cells is a monoid homomorphism into the rationals. -/
theorem sumBits_append (xs ys : List Meter) : sumBits (xs ++ ys) = sumBits xs + sumBits ys

end UMST.Kernel.Energy
```

The kernel's `nats = bits · ln 2` (`energy.rs:121`) is the image of `bits` under a scalar `c = log 2`. The theorems are stated in bits and in an arbitrary positive scalar `c`, so all four languages state them with no analysis library; section 3 composes the scalar with `SecondLaw`. The counterexample theorem is the statement behind finding 8, and the Rust cell either makes `merge` reject unequal alphas or states the precondition in its type.

### K11 Every pin site is a lawful lens onto one target

Source: `formal_pins.rs:73-190` (`SITES`), `:222-300` (`read`, `render`), `:326` (`current`), `:397-413` (`check`), `:419-448` (`bump`); tests `:456-` (round trip, locality, absent form, currency).

Value: after `umst-adk formal-pins bump` every site pins its repository's target, a second bump changes nothing, and rendering one site leaves every other pin and every other byte of the file alone.

Model. A site is a partial lens: `read` extracts the commit, `render` writes one, and both return `none` when the file lacks the site's form. Regex details stay in the Rust and Haskell instances; the family theorems quantify over any lawful lens family.

```lean
namespace UMST.Kernel.PinLens

structure Lens (Text Sha : Type) where
  read   : Text → Option Sha
  render : Text → Sha → Option Text
  get_put : ∀ t s t', render t s = some t' → read t' = some s
  put_put : ∀ t s s' t', render t s = some t' → render t' s' = render t s'
  absent  : ∀ t s, read t = none ↔ render t s = none

structure Family (Text Sha Repo : Type) where
  sites : List (Text × Lens Text Sha × Repo)    -- file content, its lens, the repository it pins
  nodup : (sites.map (fun s => (s.1, s.2.2))).Nodup
  independent : ∀ s ∈ sites, ∀ s' ∈ sites, s.2.2 ≠ s'.2.2 → s.1 = s'.1 →
    ∀ t sha t', s.2.1.render t sha = some t' → s'.2.1.read t' = s'.2.1.read t

theorem bump_sound  : ∀ site, read (bump F target) site = some (target site.repo)
theorem bump_idem   : bump F target (bump F target) = bump F target
theorem check_after_bump : stale (check F target (bump F target)) = 0

/-- A pin written abbreviated is current when it is a nonempty prefix of the target. -/
def Current (pinned target : String) : Prop := pinned ≠ "" ∧ pinned.isPrefixOf target
theorem current_of_render (sha : String) : Current sha sha ∨ sha = ""

end UMST.Kernel.PinLens
```

Instance obligations (the six `SiteKind` forms obey the lens laws, `independent` holds for the sites that share a file) are checked by the Haskell QuickCheck lens (the same six regular expressions) and by the Rust tests, which share golden fixtures (section 4). `nodup` becomes a Rust `const` assertion (section 4).

### K12 GDK admission is a meet of independent gates

Source: `umst-gdk/src/admit.rs:233-310` (`gdk_admits_with`), `evidence.rs:116-150` (`try_new`), `:59-100` (`verify_catalog_pin`), `schema_lint.rs:30-55`, `hygiene.rs:40-52` (`HygieneReport::is_clean`).

Value: a document is admitted when every tag passes every gate and the file passes the file gate; adding a gate or a tag can only narrow admission; tag sets compose by union. The first failing gate names the refusal.

Model. A gate is a decidable predicate on a tag. `Admit` requires a nonempty tag list (`UntaggedConstant`, `admit.rs:240`), all tag gates for each tag, and the file gate. The function computes the verdict as a fold in `Except GdkRefusal`, which is Kleisli composition over the error monad, the `Option` case of `Core.Constitutional.kleisliCompose` with a label on the failure.

```lean
namespace UMST.Kernel.Admit

structure Tag where
  claimId kind source method observedAt uncertainty : String
  pinDecl pinSha : Option String

abbrev Gate := Tag → Prop

def TagAdmit (gs : List Gate) (t : Tag) : Prop := ∀ g ∈ gs, g t
def Admit (fileGate : Prop) (gs : List Gate) (tags : List Tag) : Prop :=
  tags ≠ [] ∧ (∀ t ∈ tags, TagAdmit gs t) ∧ fileGate

theorem admit_antitone_gates (h : gs ⊆ gs') : Admit f gs' tags → Admit f gs tags
theorem admit_perm_gates (h : gs ~ gs') : Admit f gs tags ↔ Admit f gs' tags
theorem admit_append (h₁ : t₁ ≠ []) (h₂ : t₂ ≠ []) :
    Admit f gs (t₁ ++ t₂) ↔ Admit f gs t₁ ∧ Admit f gs t₂

/-- The label of a refusal is the first failing gate in the fixed order. -/
theorem refusal_is_first_failure (gs : List (Gate × GdkRefusal)) (t : Tag) :
    runGates gs t = (gs.find? (fun g => ¬ g.1 t)).map Prod.snd |>.elim (.ok ()) .error

/-- A pinned claim that the kernel admits names a declaration of a Lean file with the pinned digest. -/
theorem pinned_grounded (cat : Catalog) (hfresh : CatalogFresh cat repo) (t : Tag)
    (hp : PinnedOk cat t) : ∃ m ∈ cat.modules, m.sha = t.pinSha.get! ∧ t.pinDecl.get! ∈ m.declarations

end UMST.Kernel.Admit
```

`pinned_grounded` composes the kernel check with `scripts/check_catalog_fresh.py`, whose Lean model is `CatalogFresh` (each tracked Lean file appears with its current digest and declaration set). `verify_catalog_pin` matches a module by string suffix (`source.ends_with(p)`, `evidence.rs:76`) and returns the verdict of the first match. No two paths of the present catalog are suffixes of each other, so the first match is unique today; the theorem requires path-component suffix matching, and the cell changes the match to components so uniqueness becomes a property of the matcher.

## 3. Composition over the one predicate

The table lists each invariant's relation to `SecondLaw`.

| Invariant | Relation to `SecondLaw` | Mechanism |
|---|---|---|
| K10 energy, with the chain below | Instance of the erase/transformation case | Clausius form and `SecondLaw_transformation_comp` |
| K4 plan typing | Kleisli composite of `transition` instances, conditional on an interpretation | `kleisliFoldWellTypedN`, `WellTyped` at `CoreAdmissible` |
| K8 `I(claim; moved)` | Shares the definition `mutualInformation` with the feedback case | No instance: the learner measures no work or bath |
| K9 | Generalises `DEC.lean` from one triangle to every clique complex | Chain-complex algebra; no `Process` or `Prior` appears |
| K7 | CBF as a half-space projection and a discrete barrier on evidence share | Epistemic accounting; no `Process` or `Prior` appears |
| K1, K2, K3, K5, K6, K11, K12 | Combinatorial or algebraic | Statements mention no `Process` and no `Prior` |

### K10 over the erase instance

The kernel's surrogate is the left side of the Clausius inequality for the bits it meters. A chain of transformations `p₀ → p₁ → … → p_k` at one bath obeys the law with the sum of the step works, by induction on `SecondLaw_transformation_comp` and `SecondLaw_transformation_id` (`Lean/Process.lean:190-206`).

```lean
namespace UMST.Kernel.Energy

open UMST.ProcessFamily

inductive Chain (b : HeatBath) {n : ℕ} : ProbDist n → ProbDist n → ℝ → Prop
  | refl (p) : Chain b p p 0
  | step (p q r W₁ W₂) :
      SecondLaw (.erase ⟨b, W₁⟩) (.transformation p q) → Chain b q r W₂ → Chain b p r (W₁ + W₂)

theorem chain_secondLaw (h : Chain b p r W) :
    SecondLaw (.erase ⟨b, W⟩) (.transformation p r)

/-- A metered chain: each step erases entropy equal to its meter's bits times `c`. The floor on the chain's work
    is the sum of the surrogates, which is the fold's total. -/
theorem metered_floor (c : ℝ) (ms : List Meter) (ps : List (ProbDist n))
    (hsteps : StepsMatch c ms ps) (hl : SecondLaw (.erase ⟨b, W⟩) (.transformation (ps.head) (ps.getLast)))  :
    c * (sumBits ms : ℝ) ≤ W / b.bathTemp.val

end UMST.Kernel.Energy
```

At `c = Real.log 2` the left side is `sum_landauer_nats`. The Rust figure carries `ENERGY_NON_CLAIM`: surrogate bit-equivalents, no measured work. The theorem states the floor that any physical realisation of the metered erasures obeys; it does not assert that a realisation exists, and `physics_green` stays `false` in the kernels' fences. The Coq twin states the chain over `Process.v`; the Agda twin states it over rational entropies, the form `Agda/Process.agda` already uses for the transformation case.

### K4 over Kleisli composition

`Core.Constitutional` proves `kleisliFoldWellTypedN`: a list of well-typed Kleisli arrows folds to a `WellTypedN` composite whose length is the list length, with associativity and unit laws (`kleisliComposeAssoc`, `kleisliLeftUnit`, `kleisliRightUnit`). K4 supplies the missing interface. An interpretation maps each `Step` to a `KleisliArrow S`; the hypothesis `PlanSound interp` says that well-typed plans interpret to lists of well-typed arrows.

```lean
namespace UMST.Kernel.Plan

open UMST.Core

def PlanSound {S} [ThermodynamicSystem ℝ S] [AdmissibleSystem ℝ S] (interp : Step → KleisliArrow S) : Prop :=
  ∀ p, WellTypedPlan p → AllWellTyped (p.map interp)

theorem plan_composes (hs : PlanSound interp) (hp : WellTypedPlan p) :
    WellTypedN p.length (kleisliFold (p.map interp))

/-- At `S = RealThermodynamicState` a well-typed arrow is a family of `SecondLaw` transitions. -/
theorem wellTyped_iff_secondLaw (f : KleisliArrow RealThermodynamicState) :
    WellTyped f ↔ ∀ s s', f s = some s' → SecondLaw .transition (.thermodynamic s s')

end UMST.Kernel.Plan
```

The Rust constants `allocate_is_kleisli_compose()` and `spatial_antichain_implies_kleisli_well_typed()` stay `false` until a concrete `interp` discharges `PlanSound` in Lean. The proof of `wellTyped_iff_secondLaw` rests on the instance relating `AdmissibleSystem.admissibleStep` to `CoreAdmissible` at `ℝ` (`Real/Gate.lean:11`); the cell confirms the instance is definitional.

### Algebraic remarks

The kernels' counts, rates and weights are rationals, so K8, K9, K10 and the barrier ratios have exact statements over `ℚ`, and the Rust `f64` evaluation is a rounding of the exact value. The rational oracle in the Haskell twin supplies the reference. Transcendental functions enter only in K6 (`exp`) and in the scalar `log 2` of K10; both appear as an abstract field law or a scalar parameter, which keeps the statements within what Agda's standard library expresses.

## 4. Placement

### Lean modules (contract and support)

All paths are under `umst/umst-formal/Lean/`. Each contract module imports only `Support` modules and the existing modules named.

| Module | Invariant | Imports |
|---|---|---|
| `Kernel/Receipt.lean` | K1 | `Mathlib.Data.Finset.Basic` |
| `Kernel/CellCheck.lean` | K2 | `Kernel.Receipt` |
| `Kernel/Antichain.lean` | K3 | `Urge.AntichainIndependent` |
| `Kernel/Plan.lean` | K4 and the Kleisli composition | `Core.Constitutional`, `Real.Gate`, `Process`, `Kernel.Antichain` |
| `Kernel/LearnBounds.lean` | K5, K6 | `Mathlib.Analysis.SpecialFunctions.Exp` |
| `Kernel/Barrier.lean` | K7 | `Mathlib.Algebra.BigOperators.Basic` |
| `Kernel/Evidence.lean` | K8 | `InfoTheory` |
| `Kernel/Hodge.lean` | K9 | `DEC`, `Mathlib.Data.Matrix.Basic` |
| `Kernel/Energy.lean` | K10 and the chain | `Process`, `LandauerLaw` |
| `Kernel/PinLens.lean` | K11 | none |
| `Kernel/Admit.lean` | K12 | `Core.Constitutional` |
| `Kernel/Support/*.lean` | helper lemmas | free; outside `contract_modules` |

`lakefile.lean` gains one library, declared before `lean_lib «UMST»` like `UMST.Urge`:

```lean
@[default_target]
lean_lib UMST.Kernel where
  roots := #[`Kernel.Receipt, `Kernel.CellCheck, `Kernel.Antichain, `Kernel.Plan, `Kernel.LearnBounds,
    `Kernel.Barrier, `Kernel.Evidence, `Kernel.Hodge, `Kernel.Energy, `Kernel.PinLens, `Kernel.Admit]
  globs := #[`Kernel.+]
  srcDir := "."
```

`scripts/check_lean_ci_closure.py` then sees every file in a library. `artifacts/catalog.json` is regenerated by `scripts/regenerate_lean_catalog.sh` in each cell, and `scripts/check_catalog_fresh.py` must pass before the cell closes.

### Coq, Agda and Haskell twins

| Language | New files | Registration |
|---|---|---|
| Coq | `Coq/Kernel/Receipt.v`, `CellCheck.v`, `Antichain.v`, `Plan.v`, `LearnBounds.v`, `Barrier.v`, `Evidence.v`, `Hodge.v`, `Energy.v`, `PinLens.v`, `Admit.v` | `Coq/_CoqProject` lines `Kernel/<Name>.v`, then `make coq-check` |
| Agda | `Agda/Kernel/<Name>.agda`, same eleven names | `Agda/Makefile` check list, `--safe` kept; K6 over an `ExpField` record, K9 and K10 over `ℚ` |
| Haskell | `Haskell/UMST/Kernel/<Name>.hs` reference implementations, `Haskell/test/KernelProps.hs` | `Haskell/umst-formal.cabal` exposed modules and `test-suite`; properties named `prop_kernel_<id>` |

The Haskell modules hold executable references of the Rust kernels' functions (allocator, plan DFA, evidence rules over a record, projection, `hodge_rank` over `Rational`, lens family, gate fold). `KernelProps.hs` also writes the golden vectors `artifacts/kernel_fixtures.json` (fixed corpus plus QuickCheck-shrunk edge cases, with the generator seed). The Rust tests read that file.

### `formal_parity.json`

Row ids use the prefix `kernel.` so the pin generator selects them. Each row lists Lean, Coq, Agda and Haskell entries (no `absent`). The new rows:

| Id | Statement |
|---|---|
| `kernel.receipt.admit` | a COMPLETE receipt is admitted when it carries the rule set's witnesses and no active offence |
| `kernel.receipt.admit_mono_obs` | admission is monotone in evidence: more witnesses and fewer offences keep it |
| `kernel.receipt.admit_antitone_time` | a receipt admitted under a later rule set is admitted under every earlier one |
| `kernel.receipt.admit_requires_complete` | admission implies status COMPLETE |
| `kernel.cell.eval_sound` | the check evaluator agrees with the specification wherever it answers |
| `kernel.cell.all_false_absorbs` | a failing conjunct decides a conjunction |
| `kernel.cell.receipt_never_meets_failing_check` | a receipt never meets a cell whose check fails |
| `kernel.cell.eval_factors_through_commit` | evaluation reads the committed components and the tracker only |
| `kernel.antichain.independent` | the allocation has no conflicting pair |
| `kernel.antichain.bounded` | the allocation has at most the budget and only given cells |
| `kernel.antichain.maximal` | with budget to spare every unselected cell conflicts with a selected one |
| `kernel.antichain.perm` | the allocation depends on the set of cells |
| `kernel.antichain.independent_set_bridge` | pairwise independence equals `isIndependentSet` at `ℕ` ids |
| `kernel.plan.dfa` | the plan language equals the language of a finite automaton |
| `kernel.plan.prefix_closed` | a prefix of a well-typed plan is well-typed |
| `kernel.plan.gate` | an ill-typed plan selects nothing |
| `kernel.plan.composes` | a sound interpretation makes a well-typed plan a well-typed Kleisli composite |
| `kernel.plan.wellTyped_iff_secondLaw` | well-typed arrows at the real state are `SecondLaw` transitions |
| `kernel.learn.priority_range` | a learned priority lies in 1 to 10 |
| `kernel.learn.priority_displacement` | a learned priority moves at most two from its base |
| `kernel.learn.trust_region` | the bisection keeps every probability ratio in the trust region |
| `kernel.learn.bisect_width` | the bisection bracket has width `2⁻ⁿ` |
| `kernel.barrier.cbf_feasible` | the projection satisfies the constraint |
| `kernel.barrier.cbf_minimal` | the projection is the closest feasible point |
| `kernel.barrier.cbf_idempotent` | projecting twice equals projecting once |
| `kernel.barrier.invariant` | the discrete barrier condition from a safe start keeps every `h` nonnegative |
| `kernel.evidence.exclusive` | a claimed row is not both evidenced and hollow |
| `kernel.evidence.refute_effect` | a refuting verdict removes evidence and adds hollowness and drift |
| `kernel.evidence.rate_range` | the smoothed evidence rate lies strictly between 0 and 1 |
| `kernel.evidence.advantage_antitone` | the advantage is antitone in hollow and drift rates |
| `kernel.hodge.dd` | on a clique complex `d₁ d₀ = 0` |
| `kernel.hodge.pythagoras` | the comparison energy splits into the gradient and residual energies |
| `kernel.hodge.inconsistency_range` | the inconsistency share lies in 0 to 1 and vanishes exactly on a consistent ranking |
| `kernel.hodge.cg_certificate` | a small normal-equation residual bounds the potential's energy error |
| `kernel.energy.merge_bits` | merging meters of equal alpha adds their bits |
| `kernel.energy.merge_assoc` | merge is associative |
| `kernel.energy.merge_alpha_counterexample` | unequal alphas break additivity |
| `kernel.energy.sum_append` | the fold total of a concatenation is the sum of totals |
| `kernel.energy.chain_secondLaw` | a chain of transformations obeying the law obeys it with the summed work |
| `kernel.energy.metered_floor` | the metered surrogate total bounds the chain's work over temperature |
| `kernel.pins.bump_sound` | after bump every site pins its target |
| `kernel.pins.bump_idem` | a second bump changes nothing |
| `kernel.pins.check_after_bump` | no site is stale after bump |
| `kernel.pins.current_of_render` | a rendered commit is current |
| `kernel.admit.antitone_gates` | adding a gate narrows admission |
| `kernel.admit.perm_gates` | the verdict is independent of gate order |
| `kernel.admit.append` | admission of a union of tag lists is the conjunction of admissions |
| `kernel.admit.first_failure` | the refusal label is the first failing gate |
| `kernel.admit.pinned_grounded` | an admitted pinned claim names a declaration of a Lean file with the pinned digest |

That is 47 rows, bringing the contract from 80 to 127 statements with absent entries unchanged at 15. `max_absent` stays 15 and `scripts/check_formal_parity.py` keeps passing as each cell lands.

### `contract_modules` growth

`contract_modules` grows from `Lean/Process.lean`, `Lean/Chem/SecondLaw.lean` to include `Lean/Kernel/Energy.lean` and `Lean/Kernel/Plan.lean` in cells KG-4 and KG-5 (the two modules whose statements mention `SecondLaw`), and every remaining `Lean/Kernel/*.lean` module (excluding `Support/`) as its cell closes. A Lean-only result in a Kernel module then fails the parity check, the same protection `Process.lean` has. Each cell adds the module to `contract_modules` in the same commit that adds its rows.

## 5. Rust pins at zero cost

### The typed reference

A new generated crate, `umst/umst-formal/kernel-pins-rs` (package `umst-kernel-pins`, `#![no_std]`, `#![forbid(unsafe_code)]`), sits beside `constants-rs`. `scripts/gen_kernel_pins.py` writes it from two inputs: the `kernel.*` rows of `formal_parity.json` and the declarations of `artifacts/catalog.json`.

```rust
/// A declaration of the pinned Lean catalog: the catalog's `module` id and the declaration name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeanDecl { pub module: &'static str, pub name: &'static str }

/// A proved statement of formal_parity.json with its four language entries present.
#[derive(Clone, Copy, Debug)]
pub struct Pin { pub id: &'static str, pub statement: &'static str, pub lean: LeanDecl }

pub const KERNEL_RECEIPT_ADMIT_MONO_OBS: Pin = Pin {
    id: "kernel.receipt.admit_mono_obs",
    statement: "admission is monotone in evidence: more witnesses and fewer offences keep it",
    lean: LeanDecl { module: "Kernel.Receipt", name: "admit_mono_obs" },
};
```

The generator fails when a row names a Lean declaration absent from the catalog, when a row has an absent entry, and (`--check`) when the committed `lib.rs` differs from its output. `LeanDecl` has the layout of the umst-manifold type (`derivation.rs`, commit `13d4ff8d`); when that branch reaches `main`, `umst-math` re-exports this type and the two definitions collapse into one.

The kernels depend on the crate by path (`umst-kernel-pins = { path = "../../../umst-formal/kernel-pins-rs" }`), the same sibling-checkout form `umst-adk/Cargo.toml` uses for `umst-semantics` and `umst-arcs`. A theorem renamed or removed in Lean disappears from the generated crate, and every kernel reference to its constant stops compiling. All pins are `const` items; they add no code to a release binary beyond the string data the linker keeps when a table is printed.

### Citing sites

`umst-adk/src/grounding.rs` and `umst-gdk/src/grounding.rs` hold one table each:

```rust
pub struct Grounding {
    pub item: &'static str,        // Rust path of the checked function, e.g. "steer::evidence::refusals"
    pub pin: umst_kernel_pins::Pin,
    pub test: &'static str,        // the content-named #[test] that mirrors the Haskell property
}
pub const GROUNDING: &[Grounding] = &[ /* one row per grounded invariant */ ];
```

Tests in each crate check the table:

1. `every_pin_resolves`: each `pin.lean` appears in `umst/umst-formal/artifacts/catalog.json` (the same comparison as `theorem_derivations_resolve.rs`, with this repository's catalog), and its parity row has all four entries present, the condition under which the Rust runtime may rely on a statement (`formal_parity.json` rule).
2. `every_test_exists`: each `Grounding.test` names a `#[test]` function in the crate (source text search), and the name has no provenance (E2).
3. `every_kernel_row_is_cited`: every `kernel.<area>.*` row of the matching area has a consumer in `GROUNDING`; `umst-adk` covers receipt, cell, antichain, plan, learn, barrier, evidence, hodge, energy and pins; `umst-gdk` covers admit. This is the return path: the formal repository gains a runtime consumer for each proof, and a theorem with no consumer fails the check.

Property tests mirror the Haskell references. Rust uses `proptest` as a dev-dependency (no cost in the binary) with the generators named after the Haskell ones. Differential tests read `artifacts/kernel_fixtures.json` from the pinned checkout and require exact agreement on integer, boolean and string outputs (allocation lists, plan verdicts, refusal sets, rendered pin text) and agreement within a stated tolerance on `f64` outputs (potentials, projections), the tolerance taken from the exact rational oracle.

### Const assertions

Fixed values become compile-time checks:

- `formal_pins::SITES` has no duplicate `(file, repo)` pair (`const fn sites_unique`, byte comparison in a `const` loop), the `nodup` field of K11.
- `LoopParams::default` reads `γ`, `ρ_min`, `ε`, `τ` and `step` from `umst-constants` as policy rows with proved ranges, extending `constants/constants.json` (each row has a `reason` and `range` of two bound rows; the cell adds the exact bound rows it needs, for example 0 and 1). The ranges `0 < γ ≤ 1`, `0 ≤ ρ_min < 1`, `ε > 0`, `τ > 0` then hold by the table's proofs, which are the hypotheses of `barrier_invariant` and `bisect_within`.
- `PRIORITY_MIN = 1`, `PRIORITY_MAX = 10` and the displacement bound `2` are `const` items with `const _: () = assert!(PRIORITY_MIN <= PRIORITY_MAX)`, matched to `boundedPriority_mem` and `learnedPriority_displacement`.
- The integer plan step codes `0..=4` are `const` items with an assertion that they are pairwise distinct, matched to the constructors of `Step`.

### Automatic update

Three existing mechanisms carry a newer proof into the kernels with no hand edit.

1. `umst-adk formal-pins bump` moves every site to the newest green `origin/main` commit (`formal_pins.rs:378`). The kernel crates take their pins from the checkout at that commit, so `cargo test` after a bump evaluates `every_pin_resolves` against the new catalog.
2. `scripts/gen_kernel_pins.py --check` and `scripts/check_catalog_fresh.py` run in the formal repository's CI. A Lean change that renames or deletes a pinned declaration, or leaves the catalog stale, fails there before the commit can turn green.
3. `formal_pins::release` gains one condition in cell KG-8: a candidate commit qualifies when its GitHub checks are green and the kernels' `grounding` tests pass against that commit's catalog. The bump then stops at the newest commit whose pins all resolve; a proof rename that breaks a pin leaves the pins at the last good commit and opens a cell on the kernel owner, so a pin update never lands half done. `umst-adk formal-pins check` reports the grounding status beside the stale-site count.

A proof that gets stronger keeps its name and its constant, and the pin follows with no edit. A proof that gets weaker or renamed fails the resolution test, and the failure names the row.

## 6. Implementation cells

Each cell closes when its commands exit 0. The worklist `check` for each is `cell_complete` over its receipt plus the `rg_present` shown, so the tracker measures it on committed content (E8). Every cell commits only its own paths (`git commit --only -- <paths>`). Cells KG-3 to KG-9 start with a failing Rust test that exhibits the defect or gap named, then repair at the cause.

| Cell | Content | Done when |
|---|---|---|
| KG-1 | `Kernel/Antichain.lean` and twins (K3), parity rows `kernel.antichain.*`, `UMST.Kernel` lake library, `scripts/gen_kernel_pins.py`, `kernel-pins-rs` with the antichain pins | `lake build UMST.Kernel`; `python3 scripts/check_formal_parity.py` prints absent 15 of bound 15; `python3 scripts/check_catalog_fresh.py`; `python3 scripts/gen_kernel_pins.py --check`; `bash scripts/check_print_axioms.sh`; `make coq-check agda-check`; `cd Haskell && cabal test`; `cargo test -p umst-kernel-pins` |
| KG-2 | `umst-adk/src/grounding.rs`, antichain proptests, golden vectors, duplicate-id guard at the `from_cells` boundary (finding 11) | `cargo test -p umst-adk grounding::`; `cargo test -p umst-adk conflict::`; `rg -n "antichain" umst/umst-meta/crates/umst-adk/src/grounding.rs` |
| KG-3 | K1 and K2 modules and twins; `check_holds` Kleene `all`, `committed_exists` against `HEAD` (findings 6, 7, 10) | `lake build UMST.Kernel`; parity script; `cargo test -p umst-adk steer::compile::` including `all_false_absorbs_in_the_kernel` and `a_staged_file_is_not_committed`; `cargo test -p umst-adk steer::evidence::` |
| KG-4 | K10 energy and the chain over `SecondLaw` (Lean, Coq, Agda, Haskell); `merge` precondition (finding 8); `contract_modules` gains `Lean/Kernel/Energy.lean` | parity script; `cargo test -p umst-adk energy::`; `rg -n "Kernel/Energy.lean" umst/umst-formal/formal_parity.json` |
| KG-5 | K4 plan typing with `PlanSound` and `wellTyped_iff_secondLaw`; `contract_modules` gains `Lean/Kernel/Plan.lean`; `allocate_identity_plan_well_typed` pinned | parity script; `cargo test -p umst-adk hilbert_allocate::`; `lake build UMST.Kernel` |
| KG-6 | K5, K6, K7, K8 modules and twins; policy rows for the loop parameters in `constants/constants.json`; `LoopParams::default` reads `umst-constants`; end-to-end drift proptest (finding 9) | `python3 scripts/gen_constants.py --check`; parity script; `cargo test -p umst-adk steer::learn::`; `cargo test -p umst-constants` |
| KG-7 | K9 Hodge module over every clique complex, extending `DEC.lean`; exact-rational oracle and CG certificate test | `lake build UMST.Kernel`; parity script; `cargo test -p umst-adk steer::learn::hodge` |
| KG-8 | K11 lens family, Haskell lens with six forms, `SITES` uniqueness `const` assertion, `release` gated on kernel pins, `formal-pins check` reports grounding | `cargo test -p umst-adk formal_pins::`; `cd Haskell && cabal test`; `umst-adk formal-pins check` exit status 0 on a clean tree |
| KG-9 | K12 gate meet and `pinned_grounded`; component-wise path match in `verify_catalog_pin`; `umst-gdk/src/grounding.rs`; the consumer-coverage test for every `kernel.*` row | `cargo test -p umst-gdk`; parity script; `python3 scripts/check_catalog_fresh.py` |

Order rationale: KG-1 and KG-2 build the pin pipeline on the simplest invariant so every later cell reuses it. KG-3 repairs the steer compiler's definition of "met", which every other lane's progress is measured against. KG-4 and KG-5 are the two cells that join the one predicate. KG-6 and KG-7 ground the learning loop. KG-8 closes the automatic-update loop for the pins themselves. KG-9 grounds the document gate and checks that every Kernel statement has a runtime consumer.

## 7. Limits of the proposal

- The proofs concern models of the kernels. The Rust-to-model correspondence rests on property tests and golden vectors, which cover the sampled space; the extraction functions (`obs_of`, `Snapshot` construction) are the trusted base and carry their own tests.
- K11's lens laws hold for the six regular-expression forms by test. A Lean model of the section-based TOML form is possible and sits outside this proposal.
- K10 proves the floor for a chain of transformations. The kernel's meter has no measured work, and no statement here asserts that any lane realises the floor.
- The end-to-end learning claims (K8) and the `Within` maximality of K6 stay at the strength the code supports; the proposal records the strength each theorem has.
