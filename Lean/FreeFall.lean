-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  `FreeFall` — a body dropped from rest, an instance of the passive `.transition` case of
  `UMST.ProcessFamily.SecondLaw`. No second law enters beyond that predicate.

  Geometry: gravity is the gradient of a scalar potential Φ on the configuration manifold, and free fall is
  the flow along −∇Φ. Gravity enters the free energy ψ as ψ(z) = m·Φ(z) = m·g·z, linear in the height z,
  hence convex in z, so the passive route applies (a ψ convex in the state and a dissipation potential φ convex with φ(0) = 0
  give non-negative dissipation, `ConvexPhiDissipation.gsmCartridge_passive_secondLaw`). A body at height h
  at rest has ψ = m·g·h; at the ground at speed v it has ψ = ½·m·v². The step between them is a `.transition`
  of the second law: the free energy does not rise. Reading W_in = m·g·h as the work the gravitational
  potential supplies, the dissipation D = W_in − ½·m·v² is non-negative, and so g ≥ v²/(2·h).

  * `freeFall_gravity_lower_bound`: the lemma (m > 0, h > 0): D ≥ 0, ½·m·v² = W_in − D, ½·m·v² ≤ W_in,
    v² ≤ 2·g·h and g ≥ v²/(2·h).
  * `freeFallRebound_chain_oneInequality`: fall, impact and rebound as one mixed chain of
    `OneInequalitySecondLaw.oneInequality` steps (I = 0), chained by `oneInequality_chain`; the chain's free
    energy change is m·g·(h_r − h_d) ≤ 0, so `freeFallRebound_height_le` gives h_r ≤ h_d.
  * `freeFallRebound_restitution`: with no dissipation in flight, e² = h_r / h_d (g cancels), and
    `ConvexPhiChannels.restitution_le_one` (reused, not restated) gives e ≤ 1 from the impact step.

  Typed absence. The cost of extracting each bit from the frames that record the fall, at least
  k_B·T·ln 2 per bit, is the `.measureFeedback` case (`LandauerLaw`, `ClassicalMeasurementCost`) whose joint
  distribution of frame and body state the exact-rational twins cannot state; the follow-up cell is
  FORMAL-FREEFALL-MEASURE-FEEDBACK.

  The SDF, MSDF, TESDF and FRep framing is left out: it does not reduce any proof below.

  Lean states the lemmas over ℝ, which contains the exact-rational cases of Coq, Agda and Haskell. Zero axioms.
-/

import ConvexPhiChannels
import OneInequalitySecondLaw

open UMST.ProcessFamily UMST.Core UMST.Real UMST.OneInequalitySecondLaw UMST.ConvexPhiChannels

local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.FreeFall

/-- The work the gravitational potential supplies to a body of mass `m` dropped through `h` in the field `g`. -/
noncomputable def fallWork (m g h : ℝ) : ℝ := m * g * h

/-- The dissipation of a fall: the work supplied less the kinetic energy at the ground. -/
noncomputable def fallDissipation (m g h v : ℝ) : ℝ := fallWork m g h - 1 / 2 * m * v ^ 2

/-- **Free fall as a passive transition.** A body of mass `m > 0` falls from rest through `h > 0`; its free
    energy is the potential `m·g·h` before and `½·m·v²` after, and the step is a `.transition` of the second
    law. The dissipation `D = W_in − ½·m·v²` is non-negative, the kinetic energy stays within the work
    supplied, and `g ≥ v²/(2·h)`. -/
theorem freeFall_gravity_lower_bound {ρ ρ' m g h v : ℝ} (hm : 0 < m) (hh : 0 < h)
    (hL : SecondLawₚ .transition
      (.thermodynamic ⟨ρ, fallWork m g h⟩ ⟨ρ', 1 / 2 * m * v ^ 2⟩)) :
    0 ≤ fallDissipation m g h v ∧ 1 / 2 * m * v ^ 2 = fallWork m g h - fallDissipation m g h v ∧
      1 / 2 * m * v ^ 2 ≤ fallWork m g h ∧ v ^ 2 ≤ 2 * g * h ∧ v ^ 2 / (2 * h) ≤ g := by
  have hd : 1 / 2 * m * v ^ 2 ≤ fallWork m g h := hL.2
  have hv : v ^ 2 ≤ 2 * g * h := by
    have h2 : m * v ^ 2 ≤ m * (2 * g * h) := by unfold fallWork at hd; nlinarith [hd]
    exact le_of_mul_le_mul_left h2 hm
  refine ⟨by unfold fallDissipation; linarith, by unfold fallDissipation; ring, hd, hv, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The fall step of the chain: ψ from `m·g·h_d` (at rest on top) to `½·m·v²` (at the ground). -/
noncomputable def fallStep (bath : UMST.LandauerLaw.HeatBath) (ρ ρ' m g hd v : ℝ) : Step :=
  transitionStepAt bath ⟨ρ, fallWork m g hd⟩ ⟨ρ', 1 / 2 * m * v ^ 2⟩

/-- The impact step: ψ from `½·m·v²` to `½·m·(e·v)²`. -/
noncomputable def impactStep (bath : UMST.LandauerLaw.HeatBath) (ρ ρ' m v e : ℝ) : Step :=
  transitionStepAt bath ⟨ρ, 1 / 2 * m * v ^ 2⟩ ⟨ρ', 1 / 2 * m * (e * v) ^ 2⟩

/-- The rebound step: ψ from `½·m·(e·v)²` to `m·g·h_r` (at rest at the apex). -/
noncomputable def reboundStep (bath : UMST.LandauerLaw.HeatBath) (ρ ρ' m g hr v e : ℝ) : Step :=
  transitionStepAt bath ⟨ρ, 1 / 2 * m * (e * v) ^ 2⟩ ⟨ρ', fallWork m g hr⟩

/-- **Fall, impact, rebound as one mixed chain** of the one inequality ΔF ≤ W_in + k_B·T·I (I = 0), chained
    by `oneInequality_chain` at one bath. -/
theorem freeFallRebound_chain_oneInequality (bath : UMST.LandauerLaw.HeatBath) {ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr v e : ℝ}
    (hF : SecondLawₚ .transition (.thermodynamic ⟨ρ₀, fallWork m g hd⟩ ⟨ρ₁, 1 / 2 * m * v ^ 2⟩))
    (hI : SecondLawₚ .transition
      (.thermodynamic ⟨ρ₁, 1 / 2 * m * v ^ 2⟩ ⟨ρ₂, 1 / 2 * m * (e * v) ^ 2⟩))
    (hR : SecondLawₚ .transition
      (.thermodynamic ⟨ρ₂, 1 / 2 * m * (e * v) ^ 2⟩ ⟨ρ₃, fallWork m g hr⟩)) :
    oneInequality
      (((fallStep bath ρ₀ ρ₁ m g hd v).chain (impactStep bath ρ₁ ρ₂ m v e) rfl).chain
        (reboundStep bath ρ₂ ρ₃ m g hr v e) rfl) :=
  oneInequality_chain ((fallStep bath ρ₀ ρ₁ m g hd v).chain (impactStep bath ρ₁ ρ₂ m v e) rfl)
    (reboundStep bath ρ₂ ρ₃ m g hr v e) rfl
    (oneInequality_chain (fallStep bath ρ₀ ρ₁ m g hd v) (impactStep bath ρ₁ ρ₂ m v e) rfl
      (SecondLaw_transition_oneInequality_at bath _ _ hF) (SecondLaw_transition_oneInequality_at bath _ _ hI))
    (SecondLaw_transition_oneInequality_at bath _ _ hR)

/-- The rebound never rises above the drop: the chain's free energy change `m·g·(h_r − h_d)` is at most
    zero, and `m·g > 0`. -/
theorem freeFallRebound_height_le (bath : UMST.LandauerLaw.HeatBath) {ρ₀ ρ₁ ρ₂ ρ₃ m g hd hr v e : ℝ}
    (hm : 0 < m) (hg : 0 < g)
    (hF : SecondLawₚ .transition (.thermodynamic ⟨ρ₀, fallWork m g hd⟩ ⟨ρ₁, 1 / 2 * m * v ^ 2⟩))
    (hI : SecondLawₚ .transition
      (.thermodynamic ⟨ρ₁, 1 / 2 * m * v ^ 2⟩ ⟨ρ₂, 1 / 2 * m * (e * v) ^ 2⟩))
    (hR : SecondLawₚ .transition
      (.thermodynamic ⟨ρ₂, 1 / 2 * m * (e * v) ^ 2⟩ ⟨ρ₃, fallWork m g hr⟩)) :
    hr ≤ hd := by
  have h := freeFallRebound_chain_oneInequality bath hF hI hR
  simp only [oneInequality, Step.chain, fallStep, impactStep, reboundStep, transitionStepAt, fallWork] at h
  have hmg : 0 < m * g := mul_pos hm hg
  have h2 : m * g * hr ≤ m * g * hd := by linarith
  exact le_of_mul_le_mul_left h2 hmg

/-- **Restitution from the heights** (g cancels). A fall and a rebound with no dissipation in flight
    (`½·m·v² = m·g·h_d`, `½·m·(e·v)² = m·g·h_r`) give `e² = h_r / h_d`; the impact step, the passive
    restitution of `ConvexPhiChannels`, gives `e ≤ 1`, and so `h_r / h_d ≤ 1`. -/
theorem freeFallRebound_restitution {ρ₁ ρ₂ m g hd hr v e : ℝ} (hm : 0 < m) (hg : 0 < g) (hhd : 0 < hd)
    (he : 0 ≤ e) (hv : 0 < m * v ^ 2)
    (hFall : 1 / 2 * m * v ^ 2 = fallWork m g hd)
    (hRise : 1 / 2 * m * (e * v) ^ 2 = fallWork m g hr)
    (hI : SecondLawₚ .transition
      (.thermodynamic ⟨ρ₁, 1 / 2 * m * v ^ 2⟩ ⟨ρ₂, 1 / 2 * m * (e * v) ^ 2⟩)) :
    e ^ 2 = hr / hd ∧ e ≤ 1 ∧ hr / hd ≤ 1 := by
  have hmg : 0 < m * g := mul_pos hm hg
  have hratio : e ^ 2 = hr / hd := by
    rw [eq_div_iff hhd.ne']
    unfold fallWork at hFall hRise
    have h2 : m * g * (e ^ 2 * hd) = m * g * hr := by nlinarith [hFall, hRise]
    exact mul_left_cancel₀ hmg.ne' h2
  have he1 : e ≤ 1 := restitution_le_one he hv hI
  refine ⟨hratio, he1, ?_⟩
  rw [← hratio]
  nlinarith [he, he1]

end UMST.FreeFall
