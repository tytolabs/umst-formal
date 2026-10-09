-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: FluctuationTheorem.lean

  The Jarzynski integral fluctuation theorem on a finite state space, and the second law derived from it.

  Setting. A finite state type `α`, an inverse temperature `β > 0`, energy functions `E 0, E 1, …` on `α`, and
  relaxation kernels `M 0, M 1, …` (row-stochastic matrices on `α`). Stage `k + 1` of the protocol switches the
  energy from `E k` to `E (k + 1)` at the current state `x` (work `E (k + 1) x − E k x`), then draws the next state
  from `M k x ·`. Each kernel `M k` preserves the Boltzmann weight `g (k + 1) = exp (−β E (k + 1))` of the energy it
  relaxes under (`Σ_x g (k + 1) x · M k x y = g (k + 1) y`); detailed balance is one way to have this, and is not
  required. The initial state is drawn from the Gibbs distribution `g 0 / Z 0`. Trajectories of `K` stages live in
  the finite type `Path α K`.

  Results.
    • `tilted_sum` — the work-tilted forward functional: Σ_p P(p) e^{−βW(p)} f(x_K) = (Σ_x g K x · f x) / Z 0
      (the transfer form `tiltedForward_eq` states the same with the unnormalised forward vector).
    • `jarzynski` — ⟨e^{−βW}⟩ = Z K / Z 0 = e^{−βΔF}, with ΔF = F K − F 0 and F k = −β⁻¹ log Z k
      (C. Jarzynski, Phys. Rev. Lett. 78, 2690 (1997); finite Markov form after G. E. Crooks, J. Stat. Phys. 90,
      1481 (1998)).
    • `jensen_bridge` — on any finite ensemble, ⟨e^{−β(W − ΔF)}⟩ = 1 forces ⟨W⟩ ≥ ΔF (from e^t ≥ 1 + t).
    • `mean_work_ge_deltaF` — the protocol's mean work is at least ΔF.
    • The second law as a consequence: `jarzynski_oneInequality` (the one inequality ΔF ≤ W_in + k_B T·I at I = 0),
      `jarzynski_secondLaw_feedback` (the `measureFeedback` case of `ProcessFamily.SecondLaw` for any measurement
      whose information is non-negative; unconditional for an uncorrelated measurement), and
      `jarzynski_secondLaw_transition` (the `transition` case for the system together with its work source).
      The fluctuation theorem implies the predicate's cases; it does not replace the predicate.

  Zero `axiom`, zero `sorry`.
-/

import Process
import OneInequalitySecondLaw

open Real Finset
open UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist UMST.Core UMST.Real UMST.ProcessFamily UMST.OneInequalitySecondLaw

namespace UMST.FluctuationTheorem

universe u

-- ================================================================
-- SECTION 1: Finite trajectories
-- ================================================================

/-- Trajectories of `k` stages on `α`: the initial state and one state after each stage. -/
def Path (α : Type u) : ℕ → Type u
  | 0 => α
  | k + 1 => Path α k × α

/-- The state at the end of a trajectory. -/
def Path.last {α : Type u} : {k : ℕ} → Path α k → α
  | 0, x => x
  | _ + 1, p => p.2

/-- Trajectories of a finite state type form a finite type. -/
instance Path.fintype (α : Type u) [Fintype α] : (k : ℕ) → Fintype (Path α k)
  | 0 => (inferInstance : Fintype α)
  | k + 1 => @instFintypeProd (Path α k) α (Path.fintype α k) _

variable {α : Type u} [Fintype α]

/-- A sum over trajectories of `k + 1` stages is a sum over trajectories of `k` stages and a next state. -/
theorem sum_path_succ (k : ℕ) (F : Path α (k + 1) → ℝ) :
    ∑ q : Path α (k + 1), F q = ∑ p : Path α k, ∑ y : α, F (p, y) :=
  Fintype.sum_prod_type F

-- ================================================================
-- SECTION 2: The protocol
-- ================================================================

/-- A finite driven protocol: energies, relaxation kernels that preserve the Boltzmann weight of the energy they
    relax under, at inverse temperature `β > 0`. -/
structure Protocol (α : Type u) [Fintype α] where
  beta : ℝ
  beta_pos : 0 < beta
  energy : ℕ → α → ℝ
  kernel : ℕ → α → α → ℝ
  kernel_nonneg : ∀ k x y, 0 ≤ kernel k x y
  kernel_row : ∀ k x, ∑ y, kernel k x y = 1
  /-- Stage `k + 1` relaxes under `energy (k + 1)` and leaves its Boltzmann weight invariant. -/
  kernel_balance : ∀ k y,
    ∑ x, Real.exp (-beta * energy (k + 1) x) * kernel k x y = Real.exp (-beta * energy (k + 1) y)

namespace Protocol

variable (P : Protocol α)

/-- Boltzmann weight of stage `k`. -/
noncomputable def weight (k : ℕ) (x : α) : ℝ := Real.exp (-P.beta * P.energy k x)

/-- Partition function of stage `k`. -/
noncomputable def partition (k : ℕ) : ℝ := ∑ x, P.weight k x

/-- Free energy of stage `k`: F = −β⁻¹ log Z. -/
noncomputable def freeEnergy (k : ℕ) : ℝ := -(1 / P.beta) * Real.log (P.partition k)

/-- Free-energy change over `K` stages. -/
noncomputable def deltaF (K : ℕ) : ℝ := P.freeEnergy K - P.freeEnergy 0

theorem weight_pos (k : ℕ) (x : α) : 0 < P.weight k x := Real.exp_pos _

theorem partition_pos [Nonempty α] (k : ℕ) : 0 < P.partition k :=
  Finset.sum_pos (fun x _ => P.weight_pos k x) Finset.univ_nonempty

/-- Probability of a trajectory: Gibbs initial state, then the kernels. -/
noncomputable def pathProb : (k : ℕ) → Path α k → ℝ
  | 0, x => P.weight 0 x / P.partition 0
  | k + 1, q => pathProb k q.1 * P.kernel k (Path.last q.1) q.2

/-- Work done on the system along a trajectory: the energy switch at each stage's pre-relaxation state. -/
noncomputable def work : (k : ℕ) → Path α k → ℝ
  | 0, _ => 0
  | k + 1, q => work k q.1 + (P.energy (k + 1) (Path.last q.1) - P.energy k (Path.last q.1))

theorem pathProb_nonneg : ∀ (k : ℕ) (p : Path α k), 0 ≤ P.pathProb k p
  | 0, x => div_nonneg (P.weight_pos 0 x).le (Finset.sum_nonneg fun y _ => (P.weight_pos 0 y).le)
  | k + 1, q => mul_nonneg (pathProb_nonneg k q.1) (P.kernel_nonneg k _ _)

/-- The trajectory law is normalised: Σ_p P(p) = 1. -/
theorem sum_pathProb [Nonempty α] : ∀ (k : ℕ), ∑ p : Path α k, P.pathProb k p = 1
  | 0 => by
      show ∑ x : α, P.weight 0 x / P.partition 0 = 1
      rw [← Finset.sum_div]
      exact div_self (P.partition_pos 0).ne'
  | k + 1 => by
      rw [sum_path_succ]
      have h : ∀ p : Path α k, ∑ y : α, P.pathProb (k + 1) (p, y) = P.pathProb k p := by
        intro p
        show ∑ y, P.pathProb k p * P.kernel k (Path.last p) y = _
        rw [← Finset.mul_sum, P.kernel_row, mul_one]
      simp_rw [h]
      exact sum_pathProb k

/-- The weight of stage `k + 1` is the weight of stage `k` tilted by the work of the switch. -/
theorem weight_tilt (k : ℕ) (x : α) :
    P.weight k x * Real.exp (-P.beta * (P.energy (k + 1) x - P.energy k x)) = P.weight (k + 1) x := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

/-- **One stage**: the weight of stage `k`, tilted by the work of the switch and relaxed by the kernel, is the weight
    of stage `k + 1`. -/
theorem gibbs_tilt_stage (k : ℕ) (y : α) :
    ∑ x, P.weight k x * Real.exp (-P.beta * (P.energy (k + 1) x - P.energy k x)) * P.kernel k x y =
      P.weight (k + 1) y := by
  simp_rw [P.weight_tilt]
  exact P.kernel_balance k y

-- ================================================================
-- SECTION 3: The integral fluctuation theorem
-- ================================================================

/-- **Work-tilted forward functional.** For every observable `f` of the final state,
    Σ_p P(p) e^{−βW(p)} f(x_k) = (Σ_x g_k(x) f(x)) / Z_0. -/
theorem tilted_sum : ∀ (k : ℕ) (f : α → ℝ),
    ∑ p : Path α k, P.pathProb k p * Real.exp (-P.beta * P.work k p) * f (Path.last p) =
      (∑ x, P.weight k x * f x) / P.partition 0
  | 0, f => by
      show ∑ x : α, P.weight 0 x / P.partition 0 * Real.exp (-P.beta * 0) * f x = _
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_zero, Real.exp_zero, mul_one, div_mul_eq_mul_div]
  | k + 1, f => by
      rw [sum_path_succ]
      -- the next-state sum folds into the observable f' x = e^{−βΔE(x)} Σ_y M_k x y f y
      have hstep : ∀ p : Path α k,
          ∑ y : α, P.pathProb (k + 1) (p, y) * Real.exp (-P.beta * P.work (k + 1) (p, y)) *
              f (Path.last (α := α) (k := k + 1) (p, y)) =
            P.pathProb k p * Real.exp (-P.beta * P.work k p) *
              (Real.exp (-P.beta * (P.energy (k + 1) (Path.last p) - P.energy k (Path.last p))) *
                ∑ y, P.kernel k (Path.last p) y * f y) := by
        intro p
        show ∑ y : α, P.pathProb k p * P.kernel k (Path.last p) y *
              Real.exp (-P.beta * (P.work k p +
                (P.energy (k + 1) (Path.last p) - P.energy k (Path.last p)))) * f y = _
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [mul_add, Real.exp_add]
        ring
      simp_rw [hstep]
      have hk := tilted_sum k (fun x =>
        Real.exp (-P.beta * (P.energy (k + 1) x - P.energy k x)) * ∑ y, P.kernel k x y * f y)
      simp only at hk
      rw [hk]
      congr 1
      calc
        ∑ x, P.weight k x * (Real.exp (-P.beta * (P.energy (k + 1) x - P.energy k x)) *
              ∑ y, P.kernel k x y * f y)
            = ∑ x, ∑ y, P.weight (k + 1) x * P.kernel k x y * f y := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [← mul_assoc, P.weight_tilt, Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              ring
        _ = ∑ y, (∑ x, P.weight (k + 1) x * P.kernel k x y) * f y := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.sum_mul]
        _ = ∑ y, P.weight (k + 1) y * f y := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [show ∑ x, P.weight (k + 1) x * P.kernel k x y = P.weight (k + 1) y from
                P.kernel_balance k y]

/-- Unnormalised work-tilted forward vector (transfer form): u₀ = g₀, u_{k+1}(y) = Σ_x u_k(x) e^{−βΔE_k(x)} M_k(x, y). -/
noncomputable def tiltedForward : ℕ → α → ℝ
  | 0 => P.weight 0
  | k + 1 => fun y =>
      ∑ x, tiltedForward k x * Real.exp (-P.beta * (P.energy (k + 1) x - P.energy k x)) * P.kernel k x y

/-- **Transfer form of the Jarzynski identity**: after `k` stages the tilted forward vector is the Boltzmann weight
    of stage `k`. -/
theorem tiltedForward_eq : ∀ k : ℕ, P.tiltedForward k = P.weight k
  | 0 => rfl
  | k + 1 => by
      funext y
      show ∑ x, P.tiltedForward k x * _ * _ = _
      rw [tiltedForward_eq k]
      simp_rw [P.weight_tilt]
      exact P.kernel_balance k y

/-- **Jarzynski equality** (finite protocol): ⟨e^{−βW}⟩ = Z_K / Z_0. -/
theorem jarzynski (K : ℕ) :
    ∑ p : Path α K, P.pathProb K p * Real.exp (-P.beta * P.work K p) = P.partition K / P.partition 0 := by
  have h := P.tilted_sum K (fun _ => 1)
  simp only [mul_one] at h
  exact h

/-- Z_K / Z_0 = e^{−βΔF}. -/
theorem partition_ratio_eq_exp [Nonempty α] (K : ℕ) :
    P.partition K / P.partition 0 = Real.exp (-P.beta * P.deltaF K) := by
  have hb : P.beta ≠ 0 := P.beta_pos.ne'
  have h : -P.beta * P.deltaF K = Real.log (P.partition K / P.partition 0) := by
    unfold deltaF freeEnergy
    rw [Real.log_div (P.partition_pos K).ne' (P.partition_pos 0).ne']
    field_simp
    ring
  rw [h, Real.exp_log (div_pos (P.partition_pos K) (P.partition_pos 0))]

/-- **Integral fluctuation theorem**: ⟨e^{−β(W − ΔF)}⟩ = 1. -/
theorem integral_fluctuation [Nonempty α] (K : ℕ) :
    ∑ p : Path α K, P.pathProb K p * Real.exp (-P.beta * (P.work K p - P.deltaF K)) = 1 := by
  have h : ∀ p : Path α K, P.pathProb K p * Real.exp (-P.beta * (P.work K p - P.deltaF K)) =
      Real.exp (P.beta * P.deltaF K) * (P.pathProb K p * Real.exp (-P.beta * P.work K p)) := by
    intro p
    rw [show -P.beta * (P.work K p - P.deltaF K) = P.beta * P.deltaF K + -P.beta * P.work K p by ring,
      Real.exp_add]
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, P.jarzynski, P.partition_ratio_eq_exp, ← Real.exp_add]
  simp

end Protocol

/-- **Non-vacuity witness**: a sequence of sudden quenches with no relaxation (identity kernels) is a protocol for
    every energy schedule; the identity kernel leaves every weight invariant. -/
noncomputable def quench [DecidableEq α] (β : ℝ) (hβ : 0 < β) (E : ℕ → α → ℝ) : Protocol α where
  beta := β
  beta_pos := hβ
  energy := E
  kernel := fun _ x y => if x = y then 1 else 0
  kernel_nonneg := fun _ x y => by dsimp only; split_ifs <;> norm_num
  kernel_row := fun _ x => by simp
  kernel_balance := fun k y => by simp

-- ================================================================
-- SECTION 4: Jensen bridge on a finite ensemble
-- ================================================================

/-- **Jensen bridge.** On a finite ensemble with weights `P ≥ 0` summing to one, the integral fluctuation theorem
    ⟨e^{−β(W − ΔF)}⟩ = 1 at `β > 0` forces ⟨W⟩ ≥ ΔF. The only analytic input is e^t ≥ 1 + t. -/
theorem jensen_bridge {Ω : Type*} [Fintype Ω] (Pr W : Ω → ℝ) (β ΔF : ℝ) (hβ : 0 < β)
    (hP : ∀ ω, 0 ≤ Pr ω) (hsum : ∑ ω, Pr ω = 1)
    (hift : ∑ ω, Pr ω * Real.exp (-β * (W ω - ΔF)) = 1) :
    ΔF ≤ ∑ ω, Pr ω * W ω := by
  have hlin : ∑ ω, Pr ω * (1 + -β * (W ω - ΔF)) ≤ 1 := by
    rw [← hift]
    refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hP ω)
    have := Real.add_one_le_exp (-β * (W ω - ΔF))
    linarith
  have hexp : ∑ ω, Pr ω * (1 + -β * (W ω - ΔF)) = 1 - β * (∑ ω, Pr ω * W ω - ΔF) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hsum]
    have : ∑ ω, Pr ω * (-β * (W ω - ΔF)) = -β * (∑ ω, Pr ω * W ω) + β * ΔF * ∑ ω, Pr ω := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      ring
    rw [this, hsum]
    ring
  rw [hexp] at hlin
  have : 0 ≤ β * (∑ ω, Pr ω * W ω - ΔF) := by linarith
  have := (mul_nonneg_iff_of_pos_left hβ).1 this
  linarith

namespace Protocol

variable (P : Protocol α)

/-- Mean work over `K` stages. -/
noncomputable def meanWork (K : ℕ) : ℝ := ∑ p : Path α K, P.pathProb K p * P.work K p

/-- **Second law from the fluctuation theorem**: the mean work is at least the free-energy change. -/
theorem mean_work_ge_deltaF [Nonempty α] (K : ℕ) : P.deltaF K ≤ P.meanWork K :=
  jensen_bridge (P.pathProb K) (P.work K) P.beta (P.deltaF K) P.beta_pos (P.pathProb_nonneg K)
    (P.sum_pathProb K) (P.integral_fluctuation K)

/-- **Kelvin–Planck from the fluctuation theorem**: a cyclic protocol (final energy equal to the initial one)
    takes non-negative mean work. -/
theorem cyclic_mean_work_nonneg [Nonempty α] (K : ℕ) (hcyc : P.energy K = P.energy 0) :
    0 ≤ P.meanWork K := by
  have h := P.mean_work_ge_deltaF K
  have h0 : P.deltaF K = 0 := by
    unfold deltaF freeEnergy partition weight
    rw [hcyc]
    ring
  linarith

end Protocol

-- ================================================================
-- SECTION 5: The cases of SecondLaw derived from the fluctuation theorem
-- ================================================================

/-- A protocol at the temperature of a heat bath: β = 1 / (k_B T), energies in joules. -/
structure BathProtocol (α : Type u) [Fintype α] extends Protocol α where
  bath : HeatBath
  beta_eq : beta = 1 / (kB * bath.bathTemp.val)

namespace BathProtocol

variable (B : BathProtocol α)

/-- The protocol as one step of the one inequality: ΔF, mean work in, no information. -/
noncomputable def step (K : ℕ) : Step where
  bath := B.bath
  deltaF := B.deltaF K
  wIn := B.meanWork K
  infoI := 0

/-- **One inequality from Jarzynski**: ΔF ≤ ⟨W⟩ + k_B T · 0. -/
theorem jarzynski_oneInequality [Nonempty α] (K : ℕ) : oneInequality (B.step K) := by
  show B.deltaF K ≤ B.meanWork K + kB * B.bath.bathTemp.val * 0
  rw [mul_zero, add_zero]
  exact B.mean_work_ge_deltaF K

/-- The protocol read as a feedback process: the work it extracts is −⟨W⟩. -/
noncomputable def asFeedback (K : ℕ) : FeedbackProcess where
  bath := B.bath
  extWork := -B.meanWork K
  deltaFreeEnergy := B.deltaF K

/-- **`measureFeedback` case of SecondLaw from Jarzynski**: for any measurement whose mutual information is
    non-negative, −⟨W⟩ ≤ −ΔF + k_B T · I. -/
theorem jarzynski_secondLaw_feedback [Nonempty α] (K : ℕ) {n m : ℕ} (J : JointDist n m)
    (hI : 0 ≤ mutualInformation J) :
    SecondLaw (.measureFeedback (B.asFeedback K)) (.feedback J) := by
  show -B.meanWork K ≤ -B.deltaF K + kB * B.bath.bathTemp.val * mutualInformation J
  have h := B.mean_work_ge_deltaF K
  have hk : 0 ≤ kB * B.bath.bathTemp.val * mutualInformation J :=
    mul_nonneg (mul_nonneg kB_pos.le B.bath.bathTemp.property.le) hI
  linarith

/-- Unconditional form: a measurement uncorrelated with the protocol (a product joint) carries no information. -/
theorem jarzynski_secondLaw_uncorrelated [Nonempty α] (K : ℕ) {n m : ℕ} (p : ProbDist n) (q : ProbDist m) :
    SecondLaw (.measureFeedback (B.asFeedback K)) (.feedback (productJoint p q)) :=
  B.jarzynski_secondLaw_feedback K (productJoint p q) (by rw [mutualInformation_product_zero])

/-- **`transition` case of SecondLaw from Jarzynski**: the system together with its work source, at density `ρ`.
    Before: free energy F₀ + U (system plus work-source energy U). After: F_K + U − ⟨W⟩. The combined free energy
    does not rise and the density is unchanged, so the transition is admissible. -/
theorem jarzynski_secondLaw_transition [Nonempty α] (K : ℕ) (ρ U : ℝ) :
    SecondLaw .transition
      (.thermodynamic ⟨ρ, B.freeEnergy 0 + U⟩ ⟨ρ, B.freeEnergy K + U - B.meanWork K⟩) := by
  have h := B.mean_work_ge_deltaF K
  unfold Protocol.deltaF at h
  refine ⟨?_, ?_⟩
  · show |ρ - ρ| ≤ (δMass : ℝ)
    simp
  · show B.freeEnergy K + U - B.meanWork K ≤ B.freeEnergy 0 + U
    linarith

end BathProtocol

end UMST.FluctuationTheorem
