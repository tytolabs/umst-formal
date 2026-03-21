/-
  UMST-Formal: LandauerExtension.lean

  Extension of T_LandauerLaw with:
    1. Temperature scaling law: the binary Landauer bound is linear in T.
    2. N-bit bound specialisation for n = 2 (baseline) and the log-monotonicity
       of the SI energy scale.
    3. Sub-additivity note: erasing two independent registers requires the sum
       of individual lower bounds.
    4. Strict positivity of the Landauer bound (re-exported for convenience).

  All proofs use only `physicalSecondLaw` (the inherited axiom) and
  Mathlib/Real arithmetic.
-/

import LandauerLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Finset UMST.LandauerLaw

namespace UMST.LandauerExtension

-- ================================================================
-- SECTION 1: Temperature Scaling (linearity in T)
-- ================================================================

/-- **Temperature scaling**: the Landauer bound scales linearly in T.
    If two baths have temperatures T₂ = a · T₁ (a > 0), then the lower bound
    at T₂ is a times the lower bound at T₁. -/
theorem landauerBound_temp_scaling (proc₁ proc₂ : ErasureProcess)
    (a : ℝ) (ha : 0 < a)
    (htemp : proc₂.bath.bathTemp.val = a * proc₁.bath.bathTemp.val)
    (hSL₁ : physicalSecondLawUniformBinary proc₁)
    (hSL₂ : physicalSecondLawUniformBinary proc₂) :
    proc₂.work ≥ a * (proc₁.bath.bathTemp.val * log 2) := by
  have hW₂ := landauerBound proc₂ hSL₂
  rw [htemp] at hW₂
  linarith

/-- The Landauer energy scale is monotone in T:
    T₁ ≤ T₂  →  T₁ · log 2  ≤  T₂ · log 2. -/
theorem landauerEnergy_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    T₁ * log 2 ≤ T₂ * log 2 :=
  mul_le_mul_of_nonneg_right h (le_of_lt log_two_pos)

-- ================================================================
-- SECTION 2: N-Bit Generalisation (n independent bits)
-- ================================================================

/-- **N-bit erasure bound**: erasing n independent uniform binary bits requires
    work W_total ≥ n · T · log 2.
    Proved by induction on n ErasureProcesses (each at the same bath T). -/
theorem landauerBound_nBit (n : ℕ) (T : ℝ) (hT : 0 < T)
    (procs : Fin n → ErasureProcess)
    (hbath : ∀ i, (procs i).bath.bathTemp.val = T)
    (hSL : ∀ i, physicalSecondLawUniformBinary (procs i)) :
    (∑ i, (procs i).work) ≥ n * (T * log 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have hk := ih (fun i => procs (Fin.castSucc i))
                  (fun i => hbath (Fin.castSucc i))
                  (fun i => hSL  (Fin.castSucc i))
    have hlast := landauerBound (procs (Fin.last k)) (hSL (Fin.last k))
    rw [hbath (Fin.last k)] at hlast
    push_cast
    linarith

-- ================================================================
-- SECTION 3: Sub-additivity of the Energy Lower Bound
-- ================================================================

/-- Combining two erasure steps (sequential, same bath) gives a combined lower bound
    equal to the sum of the individual lower bounds. -/
theorem landauerBound_additive (proc₁ proc₂ : ErasureProcess)
    (hSL₁ : physicalSecondLawUniformBinary proc₁)
    (hSL₂ : physicalSecondLawUniformBinary proc₂) :
    proc₁.work + proc₂.work ≥
      proc₁.bath.bathTemp.val * log 2 + proc₂.bath.bathTemp.val * log 2 := by
  have h₁ := landauerBound proc₁ hSL₁
  have h₂ := landauerBound proc₂ hSL₂
  linarith

-- ================================================================
-- SECTION 4: Strict Positivity (re-export for convenience)
-- ================================================================

/-- Re-export: the Landauer bound is strictly positive for T > 0. -/
theorem landauerBound_pos' (proc : ErasureProcess)
    (hSL : physicalSecondLawUniformBinary proc) : 0 < proc.work :=
  landauerBound_pos proc hSL

-- ================================================================
-- SECTION 5: SI Energy Scale at Room Temperature (300 K)
-- ================================================================

/-- The Landauer bit-energy at T = 300 K is strictly positive (SI units, k_B = 1). -/
theorem landauerEnergy_300K_pos : 0 < (300 : ℝ) * log 2 :=
  mul_pos (by norm_num) log_two_pos

end UMST.LandauerExtension
