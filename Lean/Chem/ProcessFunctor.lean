-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/ProcessFunctor.lean

  Chemistry as an instance of the one predicate `UMST.ProcessFamily.SecondLaw`.

  A thermochemical update is sent to a process of the family, the erasure that pays for it, judged against the
  transformation of its state distribution. Updates at one bath form a category: the identity update leaves a
  distribution unchanged at no work, and two updates whose distributions meet compose with their works and defects
  added. The map to the process family is a functor that preserves admissibility: it sends the identity to the
  identity transformation at zero work (`SecondLaw_transformation_id`), a composite to the composite transformation
  at the summed work (`SecondLaw_transformation_comp`), and an update obeying the chemical second law to a member of
  `SecondLaw`.

  Each chemical vocabulary item is typed through a SecondLaw case by one theorem below: the erasure and the entropy
  drop (`secondLaw_iff_entropyDrop`), the Landauer work floor (`secondLaw_iff_workFloor`), the binary bridge
  (`PhysicalChemBridge.secondLaw_iff`), and the coherent P0 fixture (`coherentP0_secondLaw_iff_work_nonneg`,
  `coherentP0_reversible`).

  Zero `axiom`, zero `sorry`.
-/

import Chem.SecondLaw

open Real UMST.LandauerLaw UMST.ProcessFamily

namespace UMST.Chem.SecondLaw

-- ================================================================
-- SECTION 1: The image of an update in the process family
-- ================================================================

/-- The process an update is: the erasure that pays for it. -/
def ThermochemicalTransition.process {n : ℕ} (t : ThermochemicalTransition n) : Process :=
  .erase t.erasure

/-- The prior an update is judged against: the transformation of its state distribution. -/
def ThermochemicalTransition.transformation {n : ℕ} (t : ThermochemicalTransition n) : Prior :=
  .transformation t.prior t.post

/-- The chemical second law is coherence together with membership of the update's image in `SecondLaw`. -/
theorem chemSecondLaw_iff_process {n : ℕ} (t : ThermochemicalTransition n) :
    chemSecondLaw t ↔ structurallyCoherent t ∧ SecondLaw t.process t.transformation :=
  Iff.rfl

/-- **The erasure and the entropy drop, typed.** An update's erasure obeys the erase case of `SecondLaw` on its
    transformation exactly when the entropy drop of its assemblage is at most `W / T`. -/
theorem secondLaw_iff_entropyDrop {n : ℕ} (t : ThermochemicalTransition n) :
    SecondLaw (.erase t.erasure) (.transformation t.prior t.post) ↔
      assemblageEntropyDrop t ≤ t.dissipatedWork / t.bath.bathTemp.val :=
  Iff.rfl

/-- **The Landauer work floor, typed.** An update's erasure obeys the erase case of `SecondLaw` on its
    transformation exactly when its dissipated work meets the floor `T · ΔS` of its entropy drop. -/
theorem secondLaw_iff_workFloor {n : ℕ} (t : ThermochemicalTransition n) :
    SecondLaw (.erase t.erasure) (.transformation t.prior t.post) ↔
      refinementWorkFloor (assemblageEntropyDrop t) t.bath.bathTemp.val ≤ t.dissipatedWork :=
  (refinementWorkAccounted_iff t).symm

-- ================================================================
-- SECTION 2: The category of updates and the functor
-- ================================================================

/-- The identity update of distribution `p` at bath `b`: no change, no work, no defect. -/
def ThermochemicalTransition.idAt (b : HeatBath) {n : ℕ} (p : ProbDist n) : ThermochemicalTransition n :=
  ⟨b, p, p, 0, 0⟩

/-- The composite of `t₁` then `t₂` at the bath of `t₁`: from the prior of `t₁` to the post of `t₂`, works and
    defects added. -/
def ThermochemicalTransition.seq {n : ℕ} (t₁ t₂ : ThermochemicalTransition n) : ThermochemicalTransition n :=
  ⟨t₁.bath, t₁.prior, t₂.post, t₁.dissipatedWork + t₂.dissipatedWork, t₁.structuralDefect + t₂.structuralDefect⟩

theorem ThermochemicalTransition.seq_idAt_left {n : ℕ} (t : ThermochemicalTransition n) :
    (ThermochemicalTransition.idAt t.bath t.prior).seq t = t := by
  cases t
  simp [ThermochemicalTransition.seq, ThermochemicalTransition.idAt]

theorem ThermochemicalTransition.seq_idAt_right {n : ℕ} (t : ThermochemicalTransition n) :
    t.seq (ThermochemicalTransition.idAt t.bath t.post) = t := by
  cases t
  simp [ThermochemicalTransition.seq, ThermochemicalTransition.idAt]

theorem ThermochemicalTransition.seq_assoc {n : ℕ} (t₁ t₂ t₃ : ThermochemicalTransition n) :
    (t₁.seq t₂).seq t₃ = t₁.seq (t₂.seq t₃) := by
  simp [ThermochemicalTransition.seq, add_assoc]

/-- The functor sends an identity update to the identity transformation at zero work. -/
theorem process_idAt (b : HeatBath) {n : ℕ} (p : ProbDist n) :
    (ThermochemicalTransition.idAt b p).process = .erase ⟨b, 0⟩ ∧
      (ThermochemicalTransition.idAt b p).transformation = .transformation p p :=
  ⟨rfl, rfl⟩

/-- The functor sends a composite update to the composite transformation at the summed work. -/
theorem process_seq {n : ℕ} (t₁ t₂ : ThermochemicalTransition n) :
    (t₁.seq t₂).process = .erase ⟨t₁.bath, t₁.dissipatedWork + t₂.dissipatedWork⟩ ∧
      (t₁.seq t₂).transformation = .transformation t₁.prior t₂.post :=
  ⟨rfl, rfl⟩

/-- **Admissibility of identities.** The identity update obeys the chemical second law: its image is the identity
    transformation at zero work, a member of `SecondLaw`. -/
theorem chemSecondLaw_idAt (b : HeatBath) {n : ℕ} (p : ProbDist n) :
    chemSecondLaw (ThermochemicalTransition.idAt b p) :=
  ⟨rfl, SecondLaw_transformation_id b p⟩

/-- **Admissibility is closed under composition.** Two coherent updates at one bath, the second starting where the
    first ends, that obey the chemical second law compose into an update that obeys it. -/
theorem chemSecondLaw_seq {n : ℕ} (t₁ t₂ : ThermochemicalTransition n) (hb : t₁.bath = t₂.bath)
    (hp : t₁.post = t₂.prior) (h₁ : chemSecondLaw t₁) (h₂ : chemSecondLaw t₂) :
    chemSecondLaw (t₁.seq t₂) := by
  refine ⟨?_, chemSecondLaw_comp t₁ t₂ hb hp h₁ h₂⟩
  show t₁.structuralDefect + t₂.structuralDefect = 0
  rw [h₁.1, h₂.1, add_zero]

-- ================================================================
-- SECTION 3: The binary bridge transports the erase case
-- ================================================================

theorem PhysicalChemBridge.process_eq (b : PhysicalChemBridge) : b.transition.process = .erase b.proc := by
  show Process.erase ⟨b.transition.bath, b.transition.dissipatedWork⟩ = .erase b.proc
  rw [b.bathEq, b.workEq]

theorem PhysicalChemBridge.transformation_eq (b : PhysicalChemBridge) :
    b.transition.transformation = .transformation uniformBinary (diracDist (0 : Fin 2)) := by
  show Prior.transformation b.transition.prior b.transition.post = _
  rw [b.priorEq, b.postEq]

/-- **The bridge preserves and reflects admissibility.** A binary erasure obeys the erase case of `SecondLaw` on the
    uniform bit exactly when the update it realises obeys `SecondLaw` on its transformation. -/
theorem PhysicalChemBridge.secondLaw_iff (b : PhysicalChemBridge) :
    SecondLaw (.erase b.proc) (.erasure uniformBinary) ↔ SecondLaw b.transition.process b.transition.transformation := by
  rw [b.process_eq, b.transformation_eq]
  exact SecondLaw_erasure_iff_transformation b.proc uniformBinary

-- ================================================================
-- SECTION 4: Identity transformations and the P0 fixture
-- ================================================================

/-- An identity transformation obeys the erase case exactly at non-negative work. -/
theorem secondLaw_identity_iff_work_nonneg (b : HeatBath) {n : ℕ} (p : ProbDist n) (W : ℝ) :
    SecondLaw (.erase ⟨b, W⟩) (.transformation p p) ↔ 0 ≤ W := by
  show shannonEntropy p - shannonEntropy p ≤ W / b.bathTemp.val ↔ 0 ≤ W
  rw [sub_self, le_div_iff₀ b.bathTemp.property, zero_mul]

/-- **Reversibility at zero work.** An update and its reverse both obey the erase case at zero work exactly when the
    update removes no entropy. -/
theorem zeroWork_reversible_iff {n : ℕ} (t : ThermochemicalTransition n) :
    (SecondLaw (.erase ⟨t.bath, 0⟩) (.transformation t.prior t.post) ∧
        SecondLaw (.erase ⟨t.bath, 0⟩) (.transformation t.post t.prior)) ↔
      assemblageEntropyDrop t = 0 := by
  show (shannonEntropy t.prior - shannonEntropy t.post ≤ 0 / t.bath.bathTemp.val ∧
      shannonEntropy t.post - shannonEntropy t.prior ≤ 0 / t.bath.bathTemp.val) ↔
    shannonEntropy t.prior - shannonEntropy t.post = 0
  rw [zero_div]
  constructor
  · rintro ⟨h₁, h₂⟩; linarith
  · intro h; constructor <;> linarith

/-- The coherent P0 fixture is the identity update of the uniform bit at 300 K. -/
theorem coherentP0_eq_idAt :
    coherentP0Transition = ThermochemicalTransition.idAt coherentP0Transition.bath uniformBinary :=
  rfl

/-- **The P0 fixture, typed.** The P0 update obeys the erase case at work `W` exactly when `W` is non-negative. -/
theorem coherentP0_secondLaw_iff_work_nonneg (W : ℝ) :
    SecondLaw (.erase ⟨coherentP0Transition.bath, W⟩)
        (.transformation coherentP0Transition.prior coherentP0Transition.post) ↔ 0 ≤ W :=
  secondLaw_identity_iff_work_nonneg _ uniformBinary W

/-- The P0 update is reversible at zero work: it and its reverse both obey the erase case. -/
theorem coherentP0_reversible :
    SecondLaw (.erase ⟨coherentP0Transition.bath, 0⟩)
        (.transformation coherentP0Transition.prior coherentP0Transition.post) ∧
      SecondLaw (.erase ⟨coherentP0Transition.bath, 0⟩)
        (.transformation coherentP0Transition.post coherentP0Transition.prior) :=
  (zeroWork_reversible_iff coherentP0Transition).2 coherentP0_zero_entropy_drop

end UMST.Chem.SecondLaw
