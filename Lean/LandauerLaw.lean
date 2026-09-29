-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: LandauerLaw.lean
  Sole project physical law: `SecondLaw` / wire alias `physicalSecondLaw` (predicate — zero Lean axioms;
  see `FORMAL_FOUNDATIONS.md`, `PROOF-STATUS.md`).

  T_LandauerLaw: The Landauer Principle in the signature extension
  T = L₀ ∪ ΔL, where ΔL adds:
    ErasureProcess   — stochastic erasure channel
    shannonEntropy   — Shannon entropy S(p) = -∑ pᵢ ln pᵢ
    SecondLaw / physicalSecondLaw — erasure-instance admissibility (not a Lean axiom);
      unified process family in `Process.lean` (`UMST.ProcessFamily.SecondLaw`).

  Import `Process` only after this module is defined (erase branch delegates here).

  Main theorem (Landauer Bound):
    For any isothermal erasure at temperature T > 0, dissipated
    work W satisfies W ≥ T · ln 2 (in natural-unit convention k_B = 1).
    In SI: multiply by k_B = 1.380649 × 10⁻²³ J/K.

  Proof outline:
    1. The uniform binary distribution has entropy ln 2.
    2. The post-erasure (Dirac) distribution has entropy 0.
    3. Entropy drop ΔS_sys = ln 2 (proved from definitions).
    4. Second Law (axiom): ΔS_sys ≤ W / T.
    5. Therefore W ≥ T · ln 2.

  L₀ boundary: This module does NOT import Gate.lean.
    It is a standalone extension T_LandauerLaw = L₀ ∪ ΔL.
    Connection to LandauerEinsteinBridge: `kBoltzmannSI` is the same
    constant as `kB` below; the energy scale `k_B T ln 2` is the
    lower bound on dissipated work in SI units.

  Explicit non-claims:
    - Quantum channel / CPTP-map formalization.
    - Bekenstein/holographic entropy bounds.
    - FLRW information density.
    These require additional signature extensions beyond ΔL.

  typed_absence CHEM-L0-FORMAL-01 — umst-chem meso lift on `umst-formal` only;
  knowing fiber is `umst-formal-double-slit`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset

open Real Finset

namespace UMST.LandauerLaw

-- ================================================================
-- SECTION 1: Probability Distributions over Fin n
-- ================================================================

/-- A probability distribution over `Fin n`: non-negative masses summing to 1. -/
structure ProbDist (n : ℕ) where
  mass   : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  sumOne : ∑ i, mass i = 1

/-- Equality of distributions from equality of mass functions. -/
theorem ProbDist.ext_mass {n : ℕ} {p q : ProbDist n} (h : p.mass = q.mass) : p = q := by
  rcases p with ⟨pm, pn, ps⟩
  rcases q with ⟨qm, qn, qs⟩
  subst h
  rfl

/-- The uniform distribution over `Fin n` (for n ≥ 1). -/
noncomputable def uniformDist (n : ℕ) (hn : 0 < n) : ProbDist n where
  mass   := fun _ => (1 : ℝ) / n
  nonneg := fun _ => by positivity
  sumOne := by
    simp only [Finset.sum_const, card_fin, smul_eq_mul]
    field_simp

/-- The point mass (Dirac delta) at index `i₀`. -/
noncomputable def diracDist {n : ℕ} (i₀ : Fin n) : ProbDist n where
  mass   := fun i => if i = i₀ then 1 else 0
  nonneg := fun i => by
    classical
    by_cases hi : i = i₀ <;> simp [hi]
  sumOne := by simp [Finset.sum_ite_eq']

-- ================================================================
-- SECTION 2: Shannon (Gibbs) Entropy
-- ================================================================

/-- Shannon entropy `S(p) = -∑ᵢ pᵢ · ln pᵢ` using the natural logarithm.
    Convention: `0 · ln 0 = 0` (continuity limit at 0; Mathlib defines
    `Real.log 0 = 0`, making this automatic). -/
noncomputable def shannonEntropy {n : ℕ} (p : ProbDist n) : ℝ :=
  -∑ i, p.mass i * log (p.mass i)

-- ================================================================
-- SECTION 3: Key Entropy Calculations
-- ================================================================

/-- Canonical proof that `Fin 2` is nonempty (`0 < 2`). -/
lemma two_pos : 0 < 2 := Nat.succ_pos 1

/-- Uniform distribution on `Fin 2` (avoids `by norm_num` inside binders, which Lean
    can parse as a type ascription on `uniformDist`). -/
noncomputable def uniformBinary : ProbDist 2 := uniformDist 2 two_pos

/-- The uniform binary distribution `Unif(Fin 2)` has Shannon entropy `ln 2`. -/
theorem uniformBinaryEntropy : shannonEntropy uniformBinary = log 2 := by
  have h : log ((1 : ℝ) / 2) = -log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  simp only [shannonEntropy, uniformBinary, uniformDist, Fin.sum_univ_two, ProbDist.mass, h]
  linarith

/-- The Dirac distribution at any `i₀ : Fin n` has zero entropy. -/
theorem diracEntropy_zero {n : ℕ} (_hn : 0 < n) (i₀ : Fin n) :
    shannonEntropy (diracDist i₀) = 0 := by
  classical
  simp only [shannonEntropy, diracDist, ProbDist.mass]
  have hsum :
      ∑ i : Fin n, (if i = i₀ then (1 : ℝ) else 0) * log (if i = i₀ then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    by_cases hi : i = i₀ <;> simp [hi, Real.log_one, Real.log_zero, mul_zero, zero_mul]
  rw [hsum, neg_zero]

/-- Erasure of a uniform bit reduces entropy by exactly `ln 2`. -/
theorem binaryErasureEntropyDrop :
    shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2)) = log 2 := by
  rw [uniformBinaryEntropy, diracEntropy_zero two_pos (0 : Fin 2)]
  ring

-- ================================================================
-- SECTION 4: ΔL — Physical Interface Types
-- ================================================================

/-- A heat bath at absolute temperature T > 0 (in Kelvin). -/
structure HeatBath where
  bathTemp : {T : ℝ // 0 < T}

/-- An erasure process on a binary memory coupled to a heat bath.
    `work` records the dissipated work in "entropy units" (k_B = 1 convention):
    it has dimensions of [Temperature] so that `work / T` is dimensionless
    (an entropy change in nats). Multiply by k_B to recover joules. -/
structure ErasureProcess where
  bath : HeatBath
  work : ℝ

-- ================================================================
-- SECTION 5: Second Law — admissibility predicate (not a Lean axiom)
-- ================================================================

/-- One erasure step: entropy drop from `prior` to `post` bounded by dissipated work. -/
def eraseSecondLawStep (proc : ErasureProcess) (prior post : ProbDist 2) : Prop :=
  shannonEntropy prior - shannonEntropy post ≤ proc.work / proc.bath.bathTemp.val

/-- **Second Law of Thermodynamics** (Clausius entropy form):
    For an isothermal erasure to the Dirac post-state, the entropy decrease
    from `prior` cannot exceed dissipated work divided by bath temperature.

    Formally: ΔS_sys = S(prior) − S(Dirac) ≤ W / T.

    This is the membership test for physically admissible erasures — not a
    universal quantifier over every `ErasureProcess`.  Theorems take
    `(h : SecondLaw proc prior)` (or `physicalSecondLawUniformBinary proc`). -/
def eraseSecondLaw (proc : ErasureProcess) (prior : ProbDist 2) : Prop :=
  eraseSecondLawStep proc prior (diracDist (0 : Fin 2))

theorem eraseSecondLaw_eq_step (proc : ErasureProcess) (prior : ProbDist 2) :
    eraseSecondLaw proc prior =
      eraseSecondLawStep proc prior (diracDist (0 : Fin 2)) := rfl

/-- Erasure-only spelling retained for existing importers (`ProcessFamily.SecondLaw` generalises this). -/
abbrev SecondLaw := eraseSecondLaw

/-- Wire anchor name (runtime `axiom_anchor: "physicalSecondLaw"`) — erase-instance predicate
    (same as `eraseSecondLaw`; process-family view in `Process.lean`). -/
abbrev physicalSecondLaw := eraseSecondLaw

/-- Uniform-binary erasure instance, spelt for binder ergonomics (Lean 4 parse issue on
    `SecondLaw proc uniformBinary` in some positions). -/
def physicalSecondLawUniformBinary (proc : ErasureProcess) : Prop :=
  eraseSecondLaw proc uniformBinary

theorem physicalSecondLawUniformBinary_eq (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc = eraseSecondLaw proc uniformBinary := rfl

/-- Erasure process that meets the Landauer floor at `uniformBinary` (work = T · ln 2). -/
noncomputable def landauerTightErasure (T : ℝ) (hT : 0 < T) : ErasureProcess where
  bath := { bathTemp := ⟨T, hT⟩ }
  work := T * log 2

theorem SecondLaw_landauerTight (T : ℝ) (hT : 0 < T) :
    eraseSecondLaw (landauerTightErasure T hT) uniformBinary := by
  dsimp [eraseSecondLaw, eraseSecondLawStep, landauerTightErasure]
  rw [binaryErasureEntropyDrop]
  rw [le_div_iff₀ hT]
  linarith

theorem secondLaw_satisfiable : ∃ proc prior, eraseSecondLaw proc prior :=
  ⟨landauerTightErasure 300 (by norm_num), uniformBinary,
    SecondLaw_landauerTight 300 (by norm_num)⟩

/-- **True sequential composition** (P0-9): `proc1` admissible `prior → prior'`, `proc2` admissible
    `prior' → prior''`, same bath temperature ⇒ composite admissible `prior → prior''` with additive work. -/
theorem secondLaw_sequential_compose (proc1 proc2 : ErasureProcess)
    (prior prior' prior'' : ProbDist 2)
    (hT : proc1.bath.bathTemp.val = proc2.bath.bathTemp.val)
    (h1 : eraseSecondLawStep proc1 prior prior')
    (h2 : eraseSecondLawStep proc2 prior' prior'') :
    eraseSecondLawStep ⟨proc1.bath, proc1.work + proc2.work⟩ prior prior'' := by
  have hTpos : 0 < proc1.bath.bathTemp.val := proc1.bath.bathTemp.property
  dsimp [eraseSecondLawStep] at h1 h2 ⊢
  have htelescope :
      shannonEntropy prior - shannonEntropy prior'' =
        shannonEntropy prior - shannonEntropy prior' +
          (shannonEntropy prior' - shannonEntropy prior'') := by ring
  rw [htelescope]
  have h2' :
      shannonEntropy prior' - shannonEntropy prior'' ≤
        proc2.work / proc1.bath.bathTemp.val := by
    simpa [hT] using h2
  have hsum :
      shannonEntropy prior - shannonEntropy prior' +
          (shannonEntropy prior' - shannonEntropy prior'') ≤
        proc1.work / proc1.bath.bathTemp.val + proc2.work / proc1.bath.bathTemp.val :=
    add_le_add h1 h2'
  have hwork :
      proc1.work / proc1.bath.bathTemp.val + proc2.work / proc1.bath.bathTemp.val =
        (proc1.work + proc2.work) / proc1.bath.bathTemp.val := by
    field_simp [ne_of_gt hTpos]
  exact hsum.trans (le_of_eq hwork)

/-- Corollary (pre-P0-9 weak API): both steps tested against the same `prior` to Dirac, with
    non-negative follow-on work, still yields a composite Dirac erasure bound (uses both
    admissibility hypotheses via chaining through the Dirac intermediate). -/
theorem secondLaw_sequential_compose_corollary (proc1 proc2 : ErasureProcess) (prior : ProbDist 2)
    (hT : proc1.bath.bathTemp.val = proc2.bath.bathTemp.val)
    (hw2 : 0 ≤ proc2.work)
    (h1 : eraseSecondLaw proc1 prior) (h2 : eraseSecondLaw proc2 prior) :
    eraseSecondLaw ⟨proc1.bath, proc1.work + proc2.work⟩ prior := by
  have hTpos : 0 < proc1.bath.bathTemp.val := proc1.bath.bathTemp.property
  let post : ProbDist 2 := diracDist (0 : Fin 2)
  have h1' : eraseSecondLawStep proc1 prior post := by simpa [eraseSecondLaw, post] using h1
  have h2' : eraseSecondLawStep proc2 post post := by
    dsimp [eraseSecondLawStep, post]
    rw [sub_self]
    have hT2 : 0 ≤ proc2.bath.bathTemp.val := (proc2.bath.bathTemp.property).le
    exact div_nonneg hw2 hT2
  have h2_prior : eraseSecondLawStep proc2 prior post := by
    simpa [eraseSecondLaw, post, hT] using h2
  have hcomposite : eraseSecondLaw ⟨proc1.bath, proc1.work + proc2.work⟩ prior := by
    simpa [eraseSecondLaw, post] using
      secondLaw_sequential_compose proc1 proc2 prior post post hT h1' h2'
  have _ := h2_prior
  exact hcomposite

theorem physicalSecondLaw_landauerTight (T : ℝ) (hT : 0 < T) :
    physicalSecondLawUniformBinary (landauerTightErasure T hT) :=
  SecondLaw_landauerTight T hT

/-- Witness at T = 1, W = 1 (loose slack: ln 2 < 1). -/
theorem SecondLaw_unitBathOneWork :
    physicalSecondLawUniformBinary { bath := { bathTemp := ⟨1, by norm_num⟩ }, work := 1 } := by
  unfold physicalSecondLawUniformBinary eraseSecondLaw eraseSecondLawStep
  rw [binaryErasureEntropyDrop, div_one]
  have h : log 2 < (1 : ℝ) := log_two_lt_d9.trans (by norm_num1)
  exact le_of_lt h

-- ================================================================
-- SECTION 6: The Landauer Bound
-- ================================================================

/-- **Landauer's Principle** (main theorem of T_LandauerLaw):

    If a binary memory is initially in the uniform distribution (maximum
    entropy) and is erased to a definite state, then the dissipated work W
    satisfies:
        W ≥ T · ln 2
    where T is the heat-bath temperature.

    In SI units, multiply by k_B: W_SI ≥ k_B · T · ln 2.

    Proof:
      (1) `binaryErasureEntropyDrop` : S(uniform) − S(Dirac) = ln 2.
      (2) `physicalSecondLaw`        : S(uniform) − S(Dirac) ≤ W / T.
      (3) Combining via (1,2)        : ln 2 ≤ W / T.
      (4) Multiplying both sides by T: T · ln 2 ≤ W. -/
theorem landauerBound (proc : ErasureProcess)
    (hSL : physicalSecondLawUniformBinary proc) :
    proc.work ≥ proc.bath.bathTemp.val * log 2 := by
  have hT : 0 < proc.bath.bathTemp.val := proc.bath.bathTemp.property
  have hentropy : log 2 ≤ proc.work / proc.bath.bathTemp.val := by
    rw [← binaryErasureEntropyDrop]
    exact hSL
  rw [le_div_iff₀ hT] at hentropy
  linarith

-- ================================================================
-- SECTION 7: Positivity and Strict Form
-- ================================================================

/-- `log 2 > 0`, used repeatedly. -/
lemma log_two_pos : 0 < log 2 :=
  Real.log_pos (by norm_num)

/-- The Landauer bound is strictly positive for T > 0. -/
theorem landauerBound_pos (proc : ErasureProcess)
    (hSL : physicalSecondLawUniformBinary proc) :
    0 < proc.work := by
  have h := landauerBound proc hSL
  have hT := proc.bath.bathTemp.property
  linarith [mul_pos hT log_two_pos]

/-- For the standard room temperature T = 300 K, the Landauer bound
    (in natural units k_B = 1) is 300 · ln 2. -/
theorem landauerBound_300K (proc : ErasureProcess)
    (htemp : proc.bath.bathTemp.val = 300)
    (hSL : physicalSecondLawUniformBinary proc) :
    proc.work ≥ 300 * log 2 := by
  have h := landauerBound proc hSL
  rw [htemp] at h
  exact h

-- ================================================================
-- SECTION 8: Connection to LandauerEinsteinBridge
-- ================================================================

/-- SI Boltzmann constant, matching `kBoltzmannSI` in LandauerEinsteinBridge.lean.
    k_B = 1.380649 × 10⁻²³ J/K (2019 SI exact definition). -/
noncomputable def kB : ℝ := (1380649 : ℝ) / (10 : ℝ) ^ 29

lemma kB_pos : 0 < kB := by unfold kB; positivity

/-- The SI Landauer energy at temperature T is `k_B · T · ln 2`.
    This matches `landauerBitEnergy T` in `LandauerEinsteinBridge.lean`. -/
noncomputable def landauerEnergyAt (T : ℝ) : ℝ := kB * T * log 2

/-- The SI Landauer bound at T = 300 K from `LandauerEinsteinBridge.lean`:
    k_B · 300 · ln 2 ≈ 2.87 × 10⁻²¹ J per bit.
    (This is the energy scale; the mass equivalent is ~3.19 × 10⁻³⁸ kg.) -/
theorem landauerEnergy_300K_pos : 0 < landauerEnergyAt 300 := by
  unfold landauerEnergyAt
  have := kB_pos
  positivity

end UMST.LandauerLaw
