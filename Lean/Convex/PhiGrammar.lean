-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  C-CONVEX-2 (W-33): `Convex.PhiGrammar` — a grammar of dissipation potentials that are convex,
  nonnegative and zero at zero by construction.

  `PhiExpr n` is an inductive family of expressions over the rate space `Fin n → ℝ`. Its atoms are the
  positive-semidefinite quadratic form xᵀ·A·x, the absolute rate |xᵢ|, the power law |xᵢ|^p (p ≥ 1) and
  the Norton law a·|xᵢ|^(m+1) (a ≥ 0, m ≥ 0); its combinators are nonnegative scaling, sum, pointwise
  maximum and precomposition with a linear map. Every constructor preserves the three properties, so every
  expression denotes a `PassivePotential` (`toPassivePotential`) and a nonconvex potential has no expression
  (`no_expr_denotes_capped`).

  Two routes reach the passive `.transition` case of `UMST.ProcessFamily.SecondLaw`:
  * `phiExpr_passive_secondLaw` pairs the rate with any subgradient g of the potential: D = g·x ≥ φ(x) ≥ 0,
    and a passive inequality balance Δψ + D ≤ 0 closes through `ConvexPhiChannels.inequality_secondLaw`.
    No smoothness enters; |x|, max and the p = 1 power law are covered.
  * `phiExpr_gsmCartridge_secondLaw` builds a `GsmCartridge` from a one-rate expression and closes through
    `ConvexPhiDissipation.gsmCartridge_passive_secondLaw`. That route takes one extra hypothesis, the
    differentiability of the potential (the `diff` field of `GsmDissipationPotential`).

  Zero Lean axioms, no `sorry`.
-/

import ConvexPhiDissipation
import ConvexPhiChannels
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Normed
import Mathlib.Data.Matrix.Mul

open Real Set Matrix UMST.ProcessFamily UMST.Core UMST.Real UMST.ConvexPhiDissipation

local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.Convex.PhiGrammar

/-- The rate space of `n` dissipative channels. -/
abbrev Rate (n : ℕ) := Fin n → ℝ

/-- A real positive-semidefinite matrix: symmetric, with xᵀ·A·x ≥ 0 for every x (over ℝ this is Mathlib's
    `Matrix.PosSemidef`, whose Hermitian condition reads Aᵀ = A). -/
def PSD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Aᵀ = A ∧ ∀ x : Rate n, 0 ≤ x ⬝ᵥ (A *ᵥ x)

/-- Dissipation-potential expressions over `Rate n`. Every constructor carries the side condition that keeps
    its denotation convex, nonnegative and zero at zero. -/
inductive PhiExpr : ℕ → Type
  /-- Quadratic form xᵀ·A·x with A positive semidefinite (viscous dashpots, Prony arms). -/
  | quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : PSD A) : PhiExpr n
  /-- Absolute rate |xᵢ| (rate-independent plasticity, Coulomb friction). -/
  | abs {n : ℕ} (i : Fin n) : PhiExpr n
  /-- Power law |xᵢ|^p with p ≥ 1. -/
  | power {n : ℕ} (p : ℝ) (hp : 1 ≤ p) (i : Fin n) : PhiExpr n
  /-- Norton creep a·|xᵢ|^(m+1) with a ≥ 0 and m ≥ 0. -/
  | norton {n : ℕ} (a m : ℝ) (ha : 0 ≤ a) (hm : 0 ≤ m) (i : Fin n) : PhiExpr n
  /-- Nonnegative scaling c·φ with c ≥ 0. -/
  | scale {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (e : PhiExpr n) : PhiExpr n
  /-- Sum φ₁ + φ₂ (parallel channels). -/
  | add {n : ℕ} (e₁ e₂ : PhiExpr n) : PhiExpr n
  /-- Pointwise maximum max(φ₁, φ₂). -/
  | max {n : ℕ} (e₁ e₂ : PhiExpr n) : PhiExpr n
  /-- Precomposition φ ∘ L with a linear map L (change of rate variables, projection onto a channel). -/
  | precomp {m n : ℕ} (L : Rate m →ₗ[ℝ] Rate n) (e : PhiExpr n) : PhiExpr m

/-- The potential an expression denotes. -/
noncomputable def denote : {n : ℕ} → PhiExpr n → Rate n → ℝ
  | _, .quad A _, x => x ⬝ᵥ (A *ᵥ x)
  | _, .abs i, x => |x i|
  | _, .power p _ i, x => |x i| ^ p
  | _, .norton a m _ _ i, x => a * |x i| ^ (m + 1)
  | _, .scale c _ e, x => c * denote e x
  | _, .add e₁ e₂, x => denote e₁ x + denote e₂ x
  | _, .max e₁ e₂, x => Max.max (denote e₁ x) (denote e₂ x)
  | _, .precomp L e, x => denote e (L x)

/-- A positive-semidefinite quadratic form is nonnegative (over ℝ, `star x = x`). -/
theorem quad_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : PSD A) (x : Rate n) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) :=
  hA.2 x

/-- A positive-semidefinite quadratic form is convex: along a chord the gap is a·b·(x − y)ᵀA(x − y) ≥ 0. -/
theorem quad_convex {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : PSD A) :
    ConvexOn ℝ univ fun x : Rate n => x ⬝ᵥ (A *ᵥ x) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hQ := quad_nonneg hA (x - y)
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub] at hQ
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg (mul_nonneg ha hb) hQ]

/-- The scalar power law t ↦ |t|^p (p ≥ 1) is convex on ℝ: |·| is convex and t ↦ t^p is convex and
    monotone on [0, ∞). -/
theorem absRpow_convex {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ univ fun t : ℝ => |t| ^ p := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have h1 : |a • x + b • y| ≤ a * |x| + b * |y| := by
    simp only [smul_eq_mul]
    calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add _ _
      _ = a * |x| + b * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h2 : |a • x + b • y| ^ p ≤ (a * |x| + b * |y|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) h1 hp0
  have h3 := (convexOn_rpow hp).2 (mem_Ici.2 (abs_nonneg x)) (mem_Ici.2 (abs_nonneg y)) ha hb hab
  simp only [smul_eq_mul] at h3 h2 ⊢
  exact le_trans h2 h3

/-- The coordinate projection as a linear map on `Rate n`. -/
def coord {n : ℕ} (i : Fin n) : Rate n →ₗ[ℝ] ℝ := LinearMap.proj i

/-- **Zero at zero**: every expression denotes a potential with φ(0) = 0. -/
theorem denote_zero : ∀ {n : ℕ} (e : PhiExpr n), denote e 0 = 0
  | _, .quad A _ => by simp [denote]
  | _, .abs i => by simp [denote]
  | _, .power p hp i => by
      simp only [denote, Pi.zero_apply, abs_zero]
      exact Real.zero_rpow (by linarith)
  | _, .norton a m _ hm i => by
      simp only [denote, Pi.zero_apply, abs_zero]
      rw [Real.zero_rpow (by linarith), mul_zero]
  | _, .scale c _ e => by simp [denote, denote_zero e]
  | _, .add e₁ e₂ => by simp [denote, denote_zero e₁, denote_zero e₂]
  | _, .max e₁ e₂ => by simp [denote, denote_zero e₁, denote_zero e₂]
  | _, .precomp L e => by simp [denote, denote_zero e]

/-- **Nonnegative**: every expression denotes a potential with φ ≥ 0. -/
theorem denote_nonneg : ∀ {n : ℕ} (e : PhiExpr n) (x : Rate n), 0 ≤ denote e x
  | _, .quad _ hA, x => quad_nonneg hA x
  | _, .abs i, x => abs_nonneg (x i)
  | _, .power p _ i, x => Real.rpow_nonneg (abs_nonneg (x i)) p
  | _, .norton _ m ha _ i, x => mul_nonneg ha (Real.rpow_nonneg (abs_nonneg (x i)) (m + 1))
  | _, .scale _ hc e, x => mul_nonneg hc (denote_nonneg e x)
  | _, .add e₁ e₂, x => add_nonneg (denote_nonneg e₁ x) (denote_nonneg e₂ x)
  | _, .max e₁ _, x => le_trans (denote_nonneg e₁ x) (le_max_left _ _)
  | _, .precomp L e, x => denote_nonneg e (L x)

/-- **Convex**: every expression denotes a potential convex on the whole rate space. -/
theorem denote_convex : ∀ {n : ℕ} (e : PhiExpr n), ConvexOn ℝ univ (denote e)
  | _, .quad A hA => quad_convex hA
  | _, .abs i => by
      have h : ConvexOn ℝ univ fun t : ℝ => |t| := by
        simpa only [Real.norm_eq_abs] using (convexOn_univ_norm : ConvexOn ℝ univ (norm : ℝ → ℝ))
      simpa [denote, coord, Function.comp_def] using h.comp_linearMap (coord i)
  | _, .power p hp i => by
      simpa [denote, coord, Function.comp_def] using (absRpow_convex hp).comp_linearMap (coord i)
  | _, .norton a m ha hm i => by
      have h := ((absRpow_convex (p := m + 1) (by linarith)).comp_linearMap (coord i)).smul ha
      simpa [denote, coord, Function.comp_def, smul_eq_mul] using h
  | _, .scale c hc e => by
      simpa [denote, smul_eq_mul] using (denote_convex e).smul hc
  | _, .add e₁ e₂ => by
      have h := (denote_convex e₁).add (denote_convex e₂)
      refine ⟨h.1, fun x hx y hy a b ha hb hab => ?_⟩
      simpa [denote] using h.2 hx hy ha hb hab
  | _, .max e₁ e₂ => by
      have h := (denote_convex e₁).sup (denote_convex e₂)
      refine ⟨h.1, fun x hx y hy a b ha hb hab => ?_⟩
      simpa [denote] using h.2 hx hy ha hb hab
  | _, .precomp L e => by
      simpa [denote, Function.comp_def] using (denote_convex e).comp_linearMap L

/-- The semantic domain of the grammar: a potential on `Rate n` that is convex, nonnegative and zero at zero. -/
structure PassivePotential (n : ℕ) where
  φ : Rate n → ℝ
  convex : ConvexOn ℝ univ φ
  nonneg : ∀ x, 0 ≤ φ x
  zero : φ 0 = 0

/-- **Denotation**: every expression is a passive potential; the three fields are `denote_convex`,
    `denote_nonneg` and `denote_zero`. -/
noncomputable def toPassivePotential {n : ℕ} (e : PhiExpr n) : PassivePotential n :=
  ⟨denote e, denote_convex e, denote_nonneg e, denote_zero e⟩

/-- `g` is a subgradient of `φ` at `x`: φ(x) + g·(y − x) ≤ φ(y) for every rate y. -/
def IsSubgradient {n : ℕ} (φ : Rate n → ℝ) (x g : Rate n) : Prop :=
  ∀ y, φ x + g ⬝ᵥ (y - x) ≤ φ y

/-- The dissipation g·x paired with a subgradient dominates the potential: φ(x) ≤ g·x. -/
theorem phi_le_subgradient_power {n : ℕ} (P : PassivePotential n) {x g : Rate n}
    (hg : IsSubgradient P.φ x g) : P.φ x ≤ g ⬝ᵥ x := by
  have h := hg 0
  rw [P.zero, zero_sub, dotProduct_neg] at h
  linarith

/-- **Nonnegative dissipation** for every passive potential and every subgradient: 0 ≤ g·x. -/
theorem subgradient_power_nonneg {n : ℕ} (P : PassivePotential n) {x g : Rate n}
    (hg : IsSubgradient P.φ x g) : 0 ≤ g ⬝ᵥ x :=
  le_trans (P.nonneg x) (phi_le_subgradient_power P hg)

/-- **Passive second law, subgradient route**: a step whose dissipation g·x pairs the rate with a subgradient of
    any grammar potential, under the passive balance Δψ + g·x ≤ 0, is a `.transition` instance of `SecondLaw`. -/
theorem phiExpr_passive_secondLaw {n : ℕ} (e : PhiExpr n) {x g : Rate n}
    (hg : IsSubgradient (denote e) x g) {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hb : (new.freeEnergy - old.freeEnergy) + g ⬝ᵥ x ≤ 0) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  UMST.ConvexPhiChannels.inequality_secondLaw ⟨hm, subgradient_power_nonneg (toPassivePotential e) hg, hb⟩

/-- The scalar rate s seen as a one-channel rate vector. -/
noncomputable def scalarRate : ℝ →ₗ[ℝ] Rate 1 := LinearMap.pi fun _ => LinearMap.id

/-- A one-rate expression as a scalar potential s ↦ φ(s). -/
noncomputable def scalarPhi (e : PhiExpr 1) (s : ℝ) : ℝ := denote e (scalarRate s)

/-- A one-rate expression whose potential is differentiable is a `GsmDissipationPotential`. -/
noncomputable def toGsmPotential (e : PhiExpr 1) (hd : Differentiable ℝ (scalarPhi e)) :
    GsmDissipationPotential where
  φ := scalarPhi e
  convex := by
    simpa [scalarPhi, Function.comp_def] using (denote_convex e).comp_linearMap scalarRate
  nonneg s := denote_nonneg e _
  zero := by simp [scalarPhi, denote_zero e]
  diff := hd

/-- **Passive second law, cartridge route**: a differentiable one-rate grammar potential is a GSM cartridge, and its
    passive energy balance is a `.transition` instance of `SecondLaw` through
    `ConvexPhiDissipation.gsmCartridge_passive_secondLaw`. Differentiability is the one extra hypothesis. -/
theorem phiExpr_gsmCartridge_secondLaw (e : PhiExpr 1) (hd : Differentiable ℝ (scalarPhi e))
    {old new : RealThermodynamicState} {sDot : ℝ}
    (h : PassiveGsmEnergyBalance ⟨toGsmPotential e hd⟩ old new sDot) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  gsmCartridge_passive_secondLaw ⟨toGsmPotential e hd⟩ h

/-- **A nonconvex potential has no expression**: the capped potential min(|x₀|, 1) is nonnegative and zero at zero
    but not convex, so no grammar expression denotes it. -/
theorem no_expr_denotes_capped :
    ¬ ∃ e : PhiExpr 1, denote e = fun x => min |x 0| 1 := by
  rintro ⟨e, he⟩
  have hc := (denote_convex e).2 (mem_univ (fun _ => (0 : ℝ))) (mem_univ (fun _ => (2 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [he] at hc
  have hmid : ((1 / 2 : ℝ) • (fun _ => (0 : ℝ)) + (1 / 2 : ℝ) • (fun _ => (2 : ℝ)) : Rate 1) 0 = 1 := by
    norm_num
  simp only [hmid, smul_eq_mul] at hc
  norm_num at hc

/-- **A negative potential has no expression**: −x₀² is concave and negative, so no grammar expression denotes it. -/
theorem no_expr_denotes_neg_sq :
    ¬ ∃ e : PhiExpr 1, denote e = fun x => -(x 0) ^ 2 := by
  rintro ⟨e, he⟩
  have h := denote_nonneg e (fun _ => 1)
  rw [he] at h
  norm_num at h

end UMST.Convex.PhiGrammar
