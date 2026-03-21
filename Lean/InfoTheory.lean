/-
  UMST-Formal: InfoTheory.lean

  Joint Shannon entropy and mutual information on finite product alphabets.

  Extension target: general `0 ≤ mutualInformation J` (subadditivity / KL ≥ 0).
-/

import LandauerLaw
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Finset UMST LandauerLaw

namespace UMST.InfoTheory

variable {n m : ℕ}

/-- Joint distribution on `Fin n × Fin m`. -/
structure JointDist (n m : ℕ) where
  mass   : Fin n × Fin m → ℝ
  nonneg : ∀ xy, 0 ≤ mass xy
  sumOne : ∑ xy : Fin n × Fin m, mass xy = 1

namespace JointDist

variable {n m : ℕ}

/-- Left marginal (X-marginal). -/
noncomputable def marginalX (J : JointDist n m) : ProbDist n where
  mass i := ∑ j : Fin m, J.mass (i, j)
  nonneg := fun i => sum_nonneg fun j _ => J.nonneg (i, j)
  sumOne := by simpa [Fintype.sum_prod_type] using J.sumOne

/-- Right marginal (Y-marginal). -/
noncomputable def marginalY (J : JointDist n m) : ProbDist m where
  mass j := ∑ i : Fin n, J.mass (i, j)
  nonneg := fun j => sum_nonneg fun i _ => J.nonneg (i, j)
  sumOne := by
    rw [← Fintype.sum_prod_type_right']
    exact J.sumOne

noncomputable def jointEntropy (J : JointDist n m) : ℝ :=
  -∑ xy : Fin n × Fin m, J.mass xy * log (J.mass xy)

noncomputable def mutualInformation (J : JointDist n m) : ℝ :=
  shannonEntropy (marginalX J) + shannonEntropy (marginalY J) - jointEntropy J

noncomputable def productJoint (p : ProbDist n) (q : ProbDist m) : JointDist n m where
  mass xy := p.mass xy.1 * q.mass xy.2
  nonneg := fun xy => mul_nonneg (p.nonneg xy.1) (q.nonneg xy.2)
  sumOne := by
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum]
    simp [p.sumOne, q.sumOne]

theorem marginalX_product (p : ProbDist n) (q : ProbDist m) :
    marginalX (productJoint p q) = p :=
  ProbDist.ext_mass (funext fun i => by
    simp [marginalX, productJoint, Fintype.sum_prod_type, ← Finset.mul_sum, q.sumOne, mul_one])

theorem marginalY_product (p : ProbDist n) (q : ProbDist m) :
    marginalY (productJoint p q) = q :=
  ProbDist.ext_mass (funext fun j => by
    simp only [marginalY, productJoint, Fintype.sum_prod_type]
    simp_rw [mul_comm (p.mass _) (q.mass j)]
    rw [← Finset.mul_sum]
    simp [p.sumOne, mul_one])

private lemma entropy_term_product (p : ProbDist n) (q : ProbDist m) (i : Fin n) (j : Fin m) :
    p.mass i * q.mass j * log (p.mass i * q.mass j) =
      p.mass i * q.mass j * log (p.mass i) + p.mass i * q.mass j * log (q.mass j) := by
  by_cases hpi : p.mass i = 0
  · simp [hpi]
  by_cases hqj : q.mass j = 0
  · simp [hqj]
  have hi : 0 < p.mass i := lt_of_le_of_ne (p.nonneg i) (Ne.symm hpi)
  have hj : 0 < q.mass j := lt_of_le_of_ne (q.nonneg j) (Ne.symm hqj)
  rw [log_mul hi.ne' hj.ne']
  ring

theorem jointEntropy_product (p : ProbDist n) (q : ProbDist m) :
    jointEntropy (productJoint p q) = shannonEntropy p + shannonEntropy q := by
  classical
  unfold shannonEntropy jointEntropy productJoint
  conv_lhs => rw [Fintype.sum_prod_type]
  simp_rw [entropy_term_product p q]
  -- Parenthesize the summand so the binders `x,y` stay in scope across a line break
  -- (otherwise Lean may parse the inner `∑` as ending at the newline).
  have hsplit :
      (∑ x : Fin n, ∑ y : Fin m,
          (p.mass x * q.mass y * log (p.mass x) + p.mass x * q.mass y * log (q.mass y))) =
        (∑ x : Fin n, ∑ y : Fin m, p.mass x * q.mass y * log (p.mass x)) +
          ∑ x : Fin n, ∑ y : Fin m, p.mass x * q.mass y * log (q.mass y) := by
    have hi :
        (∑ x : Fin n, ∑ y : Fin m,
            (p.mass x * q.mass y * log (p.mass x) + p.mass x * q.mass y * log (q.mass y))) =
          ∑ x : Fin n,
            ((∑ y : Fin m, p.mass x * q.mass y * log (p.mass x)) +
              (∑ y : Fin m, p.mass x * q.mass y * log (q.mass y))) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_add_distrib
    rw [hi, Finset.sum_add_distrib]
  have hsumX :
      (∑ x : Fin n, ∑ y : Fin m, p.mass x * q.mass y * log (p.mass x)) =
        ∑ x : Fin n, p.mass x * log (p.mass x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    calc
      ∑ y : Fin m, p.mass x * q.mass y * log (p.mass x)
          = ∑ y : Fin m, p.mass x * log (p.mass x) * q.mass y := by
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
      _ = p.mass x * log (p.mass x) * ∑ y : Fin m, q.mass y := by rw [Finset.mul_sum]
      _ = p.mass x * log (p.mass x) := by simp [q.sumOne]
  have hsumY :
      (∑ x : Fin n, ∑ y : Fin m, p.mass x * q.mass y * log (q.mass y)) =
        ∑ y : Fin m, q.mass y * log (q.mass y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    calc
      ∑ x : Fin n, p.mass x * q.mass y * log (q.mass y)
          = ∑ x : Fin n, q.mass y * log (q.mass y) * p.mass x := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
      _ = q.mass y * log (q.mass y) * ∑ x : Fin n, p.mass x := by rw [Finset.mul_sum]
      _ = q.mass y * log (q.mass y) := by simp [p.sumOne]
  rw [hsplit, neg_add, hsumX, hsumY]

theorem mutualInformation_product_zero (p : ProbDist n) (q : ProbDist m) :
    mutualInformation (productJoint p q) = 0 := by
  unfold mutualInformation
  rw [marginalX_product, marginalY_product, jointEntropy_product]
  ring

end JointDist

end UMST.InfoTheory
