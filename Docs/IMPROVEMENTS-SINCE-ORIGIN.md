# Improvements since `origin/master` (GitHub cloud)

This note summarizes **local** `umst-formal` advances versus the published
[`tytolabs/umst-formal`](https://github.com/tytolabs/umst-formal) default branch.
For an exact file list and line counts, run:

```bash
git fetch origin
git diff --stat origin/master
```

## Lean 4 (`Lean/`)

### Graded admissibility (replaces refutable `admissibleTrans`)

- **`AdmissibleN n`**, **`admissible_iff_admissibleN1`**, **`admissibleN_compose`** (`Gate.lean`):
  mass tolerance accumulates as `n * δMass` with a **proved** triangle-inequality
  argument instead of the old transitivity axiom.
- **`kleisliComposeWellTypedN`**, **`kleisliFoldWellTypedN`** (`Constitutional.lean`):
  Kleisli composition is graded; list-length rewrite uses `Nat.add_comm` for
  `WellTypedN (length + 1)` vs `1 + length`.

### Counterexamples and structure

- **`GraphProperties.lean`**: formal **non-transitivity** of mass / `Admissible`,
  transitivity of the three order legs, hydration acyclicity, graded sanity checks.
- **`EnrichedAdmissibility.lean`**: mass pseudometric + **triangle inequality**
  aligned with `AdmissibleN` composition.
- **`GaloisGate.lean`**: Galois-style view of gate conditions; **classical**
  `Decidable Prop` instance for `Finset.filter`; **`condMeet`** / **`condExtract`**
  marked **`noncomputable`**; **`condExtract_admissible`** uses `iff_true_intro`.

### Convergence (`Convergence.lean`)

- Import fix: **`Mathlib.Topology.Order.MonotoneConvergence`** (typo `Covergence` removed).
- **Hydration / free-energy limits** use **`tendsto_atTop_ciSup`** /
  **`tendsto_atTop_ciInf`** with **`le_ciSup`** / **`le_ciInf`** and careful casts
  (`mem_range`, `change`, `simpa`) instead of non-existent
  `Monotone.tendsto_nhds_iSup` / `Antitone.tendsto_nhds_iInf`.
- **`lyapunov_upper_bound`**: uses **`hydration_bounded` upper bound** (`α ≤ 1`), not the lower bound.

### Landauer layer (`LandauerLaw.lean`)

- **`two_pos`**, **`uniformBinary`**: avoid `by norm_num` inside binders (Lean parse).
- **`physicalSecondLaw`** (axiom) for general prior; **`physicalSecondLawUniformBinary`**
  (def) for the uniform binary case; **`physicalSecondLaw_uniform_binary`** theorem
  instantiates the axiom; main theorems take **`physicalSecondLawUniformBinary proc`**
  so binders parse correctly.
- **`le_div_iff₀`** for Mathlib deprecation hygiene.

### Misc

- **`Gate.lean`**: `admissible_iff_admissibleN1` uses **`simpa [one_mul]`** for
  `δMass` vs `1 * δMass`; **`admissibleN_compose`** mass step uses **`add_comm`**
  with **`add_le_add`**.

## Documentation

- **`PROOF-STATUS.md`**: axiom names and Landauer story updated for
  `physicalSecondLaw` / `physicalSecondLawUniformBinary`.
- **`lakefile.lean`**: comment updated to match axiom name.

## Coq (`Coq/`)

- **`Gate.v`**: `admissible_N` uses the same **two-sided** mass bounds as `admissible`
  (`density new - old` and `density old - new`), avoiding `Qabs` (not available / awkward
  under Rocq 9 `Stdlib` in this setup). Proofs use `Qring`, `field`, and `inject_Z`/`ring`
  for the `1 * δMass` step.
- **`Constitutional.v`**: **removes the duplicate** `admissible_N` definition; reuses
  `UMSTFormal.Gate.admissible_N`. **`admissible_N_compose`** is reproved via telescoping
  sums + **`inject_mass_triangle_rhs`**. Imports: `Qfield`, `Setoid`, `ZArith`.
- **`kleisli_fold_well_typed`**: invalid `Theorem ... :=` syntax replaced with `Proof … Qed`.

## Verification (pre-commit)

From repo root:

```bash
cd Lean && lake build UMST
cd ../Coq && make
cd ../Agda && make check   # if your Makefile provides this target
cd ../Haskell && cabal build all && cabal test all --test-show-details=streaming
```

**Green flag:** run the above in a clean tree; only then commit. Exclude build
artifacts (e.g. `Coq/.CoqMakefile.d`, `Coq/.nia.cache`, extracted `.ml` if any)
unless you intend to version them—prefer extending **`.gitignore`**.
