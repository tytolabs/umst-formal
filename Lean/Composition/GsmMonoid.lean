-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  C-GLUE-ZERO (W-44): `Composition.GsmMonoid` — the composition law of GSM atoms and the glue fraction.

  The passive route of `UMST.ProcessFamily.SecondLaw` (`ConvexPhiDissipation.gsmCartridge_passive_secondLaw`)
  admits one GSM cartridge at a time. This module closes the route under composition, so a composite built
  from admissible atoms is admissible by one argument.

  * GSM dissipation potentials, GSM cartridges and GSM atoms (convex ψ with a GSM potential φ) form
    commutative monoids under pointwise sum, and modules over ℝ≥0 under non-negative scaling (convex cones).
  * At every rate ṡ the dissipation power D = ṡ·φ′(ṡ) is an ℝ≥0-linear map into ℝ≥0
    (`dissipationHom`): a monoid homomorphism from GSM potentials to the dissipation monoid of the
    non-negative reals. The dissipation of a composite is the sum of its atoms' dissipations, each ≥ 0.
  * The atoms that satisfy the passive balance Δψ + D ≤ 0 on a step form a sub-cone (`admissibleCone`);
    every finite non-negative combination of admissible atoms is admissible and satisfies
    `SecondLaw .transition` (`combination_secondLaw`).
  * Atoms on disjoint rate channels compose by `tensor` (block concatenation), with additive power.
  * Glue: a composite's dissipation is D_total = D_atoms + D_glue. A glue term that is itself a GSM potential
    is one more atom (ψ = 0) and keeps admissibility (`convexGlue_secondLaw`); an arbitrary glue term needs its
    own witness 0 ≤ D_total (`glued_secondLaw_of_witness`), and without one the law refuses the step
    (`glued_refused_of_negative_total`, `arbitrary_glue_not_closed`). The glue fraction |D_glue| / D_total lies
    in [0, 1] for a convex glue term, vanishes exactly when D_glue = 0, and exceeds 1 only for a negative glue term.

  Zero Lean axioms beyond Mathlib's foundations; no `sorry`.
-/

import ConvexPhiChannels

open Real Set UMST.ProcessFamily UMST.Core UMST.Real UMST.ConvexPhiDissipation UMST.ConvexPhiChannels
open scoped NNReal

local notation "SecondLawₚ" => UMST.ProcessFamily.SecondLaw

namespace UMST.Composition

-- ================================================================
-- SECTION 1: GSM dissipation potentials form a convex cone
-- ================================================================

@[ext]
theorem potential_ext {P Q : GsmDissipationPotential} (h : P.φ = Q.φ) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- The null potential φ = 0. -/
instance : Zero GsmDissipationPotential where
  zero :=
    { φ := fun _ => 0
      convex := convexOn_const 0 convex_univ
      nonneg := fun _ => le_rfl
      zero := rfl
      diff := differentiable_const 0 }

/-- Pointwise sum of two potentials: convex, non-negative, pinned at zero and differentiable. -/
instance : Add GsmDissipationPotential where
  add P Q :=
    { φ := fun x => P.φ x + Q.φ x
      convex := P.convex.add Q.convex
      nonneg := fun x => add_nonneg (P.nonneg x) (Q.nonneg x)
      zero := by simp [P.zero, Q.zero]
      diff := P.diff.add Q.diff }

/-- Non-negative scaling of a potential. -/
noncomputable instance : SMul ℝ≥0 GsmDissipationPotential where
  smul c P :=
    { φ := fun x => (c : ℝ) * P.φ x
      convex := by simpa [smul_eq_mul] using P.convex.smul c.2
      nonneg := fun x => mul_nonneg c.2 (P.nonneg x)
      zero := by simp [P.zero]
      diff := P.diff.const_mul _ }

@[simp] theorem zero_φ (x : ℝ) : (0 : GsmDissipationPotential).φ x = 0 := rfl

@[simp] theorem add_φ (P Q : GsmDissipationPotential) (x : ℝ) : (P + Q).φ x = P.φ x + Q.φ x := rfl

@[simp] theorem smul_φ (c : ℝ≥0) (P : GsmDissipationPotential) (x : ℝ) : (c • P).φ x = (c : ℝ) * P.φ x :=
  rfl

/-- **GSM potentials form a commutative monoid** under pointwise sum. -/
instance : AddCommMonoid GsmDissipationPotential where
  add_assoc P Q R := by ext x; simp [add_assoc]
  zero_add P := by ext x; simp
  add_zero P := by ext x; simp
  add_comm P Q := by ext x; simp [add_comm]
  nsmul := nsmulRec

/-- **GSM potentials form a convex cone**: a module over the non-negative reals. -/
noncomputable instance : Module ℝ≥0 GsmDissipationPotential where
  one_smul P := by ext x; simp
  mul_smul a b P := by ext x; simp [mul_assoc]
  smul_zero a := by ext x; simp
  smul_add a P Q := by ext x; simp [mul_add]
  add_smul a b P := by ext x; simp [add_mul]
  zero_smul P := by ext x; simp

-- ================================================================
-- SECTION 2: dissipation is additive and non-negatively homogeneous
-- ================================================================

@[simp] theorem dissipationPower_zero (sDot : ℝ) : dissipationPower 0 sDot = 0 := by
  show sDot * deriv (fun _ => (0 : ℝ)) sDot = 0
  simp

/-- The dissipation of a sum is the sum of the dissipations. -/
@[simp] theorem dissipationPower_add (P Q : GsmDissipationPotential) (sDot : ℝ) :
    dissipationPower (P + Q) sDot = dissipationPower P sDot + dissipationPower Q sDot := by
  have hd : deriv (fun x => P.φ x + Q.φ x) sDot = deriv P.φ sDot + deriv Q.φ sDot :=
    deriv_add (P.diff sDot) (Q.diff sDot)
  show sDot * deriv (fun x => P.φ x + Q.φ x) sDot = sDot * deriv P.φ sDot + sDot * deriv Q.φ sDot
  rw [hd, mul_add]

/-- The dissipation of a non-negatively scaled potential is the scaled dissipation. -/
@[simp] theorem dissipationPower_smul (c : ℝ≥0) (P : GsmDissipationPotential) (sDot : ℝ) :
    dissipationPower (c • P) sDot = (c : ℝ) * dissipationPower P sDot := by
  have hd : deriv (fun x => (c : ℝ) * P.φ x) sDot = (c : ℝ) * deriv P.φ sDot :=
    deriv_const_mul _ (P.diff sDot)
  show sDot * deriv (fun x => (c : ℝ) * P.φ x) sDot = (c : ℝ) * (sDot * deriv P.φ sDot)
  rw [hd]
  ring

/-- **Dissipation homomorphism**: at rate ṡ, D = ṡ·φ′(ṡ) is an ℝ≥0-linear map from GSM potentials into the
    dissipation monoid ℝ≥0 (non-negativity is `convex_phi_dissipation_nonneg`). -/
noncomputable def dissipationHom (sDot : ℝ) : GsmDissipationPotential →ₗ[ℝ≥0] ℝ≥0 where
  toFun P := ⟨dissipationPower P sDot, convex_phi_dissipation_nonneg P sDot⟩
  map_add' P Q := by ext; simp
  map_smul' c P := by ext; simp

@[simp] theorem dissipationHom_apply (sDot : ℝ) (P : GsmDissipationPotential) :
    (dissipationHom sDot P : ℝ) = dissipationPower P sDot := rfl

/-- The additive monoid homomorphism underlying `dissipationHom`. -/
noncomputable def dissipationAddHom (sDot : ℝ) : GsmDissipationPotential →+ ℝ≥0 :=
  (dissipationHom sDot).toAddMonoidHom

/-- **Finite combination**: the dissipation of Σᵢ cᵢ•Pᵢ is Σᵢ cᵢ·Dᵢ. -/
theorem dissipationPower_sum {ι : Type*} (t : Finset ι) (c : ι → ℝ≥0) (P : ι → GsmDissipationPotential)
    (sDot : ℝ) :
    dissipationPower (∑ i ∈ t, c i • P i) sDot = ∑ i ∈ t, (c i : ℝ) * dissipationPower (P i) sDot := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert hnot ih => simp [Finset.sum_insert hnot, ih]

/-- Each summand of a finite non-negative combination dissipates a non-negative amount. -/
theorem combination_summand_nonneg {ι : Type*} (c : ι → ℝ≥0) (P : ι → GsmDissipationPotential)
    (sDot : ℝ) (i : ι) : 0 ≤ (c i : ℝ) * dissipationPower (P i) sDot :=
  mul_nonneg (c i).2 (convex_phi_dissipation_nonneg (P i) sDot)

-- ================================================================
-- SECTION 3: GSM cartridges form a commutative monoid
-- ================================================================

@[ext]
theorem cartridge_ext {C D : GsmCartridge} (h : C.dissip = D.dissip) : C = D := by
  cases C
  cases D
  cases h
  rfl

instance : Zero GsmCartridge := ⟨⟨0⟩⟩
instance : Add GsmCartridge := ⟨fun C D => ⟨C.dissip + D.dissip⟩⟩
noncomputable instance : SMul ℝ≥0 GsmCartridge := ⟨fun c C => ⟨c • C.dissip⟩⟩

@[simp] theorem cartridge_zero_dissip : (0 : GsmCartridge).dissip = 0 := rfl
@[simp] theorem cartridge_add_dissip (C D : GsmCartridge) : (C + D).dissip = C.dissip + D.dissip := rfl
@[simp] theorem cartridge_smul_dissip (c : ℝ≥0) (C : GsmCartridge) : (c • C).dissip = c • C.dissip := rfl

/-- **GSM cartridges form a commutative monoid** under composition (sum of dissipation potentials). -/
instance : AddCommMonoid GsmCartridge where
  add_assoc C D E := by ext1; simp [add_assoc]
  zero_add C := by ext1; simp
  add_zero C := by ext1; simp
  add_comm C D := by ext1; simp [add_comm]
  nsmul := nsmulRec

/-- GSM cartridges form a convex cone. -/
noncomputable instance : Module ℝ≥0 GsmCartridge where
  one_smul C := by ext1; simp
  mul_smul a b C := by ext1; simp [mul_smul]
  smul_zero a := by ext1; simp
  smul_add a C D := by ext1; simp
  add_smul a b C := by ext1; simp [add_smul]
  zero_smul C := by ext1; simp

/-- Cartridge dissipation as a monoid homomorphism into the dissipation monoid ℝ≥0. -/
noncomputable def cartridgeDissipationHom (sDot : ℝ) : GsmCartridge →ₗ[ℝ≥0] ℝ≥0 where
  toFun C := dissipationHom sDot C.dissip
  map_add' C D := by simp
  map_smul' c C := by simp

/-- **Closure of the passive law under composition**: a composite of two GSM cartridges is a GSM cartridge,
    its dissipation is the sum of theirs (each ≥ 0), and a passive balance on it is a `.transition` step. -/
theorem composite_passive_secondLaw (C D : GsmCartridge) {old new : RealThermodynamicState} {sDot : ℝ}
    (h : PassiveGsmEnergyBalance (C + D) old new sDot) :
    SecondLawₚ .transition (.thermodynamic old new) ∧
      dissipationPower (C + D).dissip sDot =
        dissipationPower C.dissip sDot + dissipationPower D.dissip sDot ∧
      0 ≤ dissipationPower C.dissip sDot ∧ 0 ≤ dissipationPower D.dissip sDot :=
  ⟨gsmCartridge_passive_secondLaw (C + D) h, dissipationPower_add _ _ _,
    gsmCartridge_dissipation_nonneg C sDot, gsmCartridge_dissipation_nonneg D sDot⟩

-- ================================================================
-- SECTION 4: GSM atoms (convex ψ and GSM φ) and the admissible cone
-- ================================================================

/-- A GSM atom: a free energy ψ convex in the internal variable and a GSM dissipation potential φ. -/
structure GsmAtom where
  ψ : ℝ → ℝ
  ψconvex : ConvexOn ℝ univ ψ
  pot : GsmDissipationPotential

@[ext]
theorem atom_ext {A B : GsmAtom} (hψ : A.ψ = B.ψ) (hp : A.pot = B.pot) : A = B := by
  cases A
  cases B
  cases hψ
  cases hp
  rfl

instance : Zero GsmAtom := ⟨⟨fun _ => 0, convexOn_const 0 convex_univ, 0⟩⟩

instance : Add GsmAtom :=
  ⟨fun A B => ⟨fun x => A.ψ x + B.ψ x, A.ψconvex.add B.ψconvex, A.pot + B.pot⟩⟩

noncomputable instance : SMul ℝ≥0 GsmAtom :=
  ⟨fun c A => ⟨fun x => (c : ℝ) * A.ψ x, by simpa [smul_eq_mul] using A.ψconvex.smul c.2, c • A.pot⟩⟩

@[simp] theorem atom_zero_ψ (x : ℝ) : (0 : GsmAtom).ψ x = 0 := rfl
@[simp] theorem atom_zero_pot : (0 : GsmAtom).pot = 0 := rfl
@[simp] theorem atom_add_ψ (A B : GsmAtom) (x : ℝ) : (A + B).ψ x = A.ψ x + B.ψ x := rfl
@[simp] theorem atom_add_pot (A B : GsmAtom) : (A + B).pot = A.pot + B.pot := rfl
@[simp] theorem atom_smul_ψ (c : ℝ≥0) (A : GsmAtom) (x : ℝ) : (c • A).ψ x = (c : ℝ) * A.ψ x := rfl
@[simp] theorem atom_smul_pot (c : ℝ≥0) (A : GsmAtom) : (c • A).pot = c • A.pot := rfl

/-- **GSM atoms form a commutative monoid** under composition. -/
instance : AddCommMonoid GsmAtom where
  add_assoc A B C := by ext x <;> simp [add_assoc]
  zero_add A := by ext x <;> simp
  add_zero A := by ext x <;> simp
  add_comm A B := by ext x <;> simp [add_comm]
  nsmul := nsmulRec

/-- GSM atoms form a convex cone. -/
noncomputable instance : Module ℝ≥0 GsmAtom where
  one_smul A := by ext x <;> simp
  mul_smul a b A := by ext x <;> simp [mul_assoc, mul_smul]
  smul_zero a := by ext x <;> simp
  smul_add a A B := by ext x <;> simp [mul_add]
  add_smul a b A := by ext x <;> simp [add_mul, add_smul]
  zero_smul A := by ext x <;> simp

/-- The cartridge an atom carries. -/
def GsmAtom.toCartridge (A : GsmAtom) : GsmCartridge := ⟨A.pot⟩

/-- Free energy of a finite non-negative combination: Σᵢ cᵢ·ψᵢ. -/
theorem atom_sum_ψ {ι : Type*} (t : Finset ι) (c : ι → ℝ≥0) (A : ι → GsmAtom) (x : ℝ) :
    (∑ i ∈ t, c i • A i).ψ x = ∑ i ∈ t, (c i : ℝ) * (A i).ψ x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert hnot ih => simp [Finset.sum_insert hnot, ih]

/-- Dissipation potential of a finite non-negative combination: Σᵢ cᵢ•φᵢ. -/
theorem atom_sum_pot {ι : Type*} (t : Finset ι) (c : ι → ℝ≥0) (A : ι → GsmAtom) :
    (∑ i ∈ t, c i • A i).pot = ∑ i ∈ t, c i • (A i).pot := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert hnot ih => simp [Finset.sum_insert hnot, ih]

/-- Passive step of an atom: internal variable s → s′ at rate ṡ with Δψ + D ≤ 0. -/
def PassiveStep (A : GsmAtom) (s s' sDot : ℝ) : Prop :=
  (A.ψ s' - A.ψ s) + dissipationPower A.pot sDot ≤ 0

/-- **Admissible cone**: the atoms whose passive balance holds on one step form an ℝ≥0-submodule of the atoms;
    admissibility is closed under sum, non-negative scaling and the empty composite. -/
noncomputable def admissibleCone (s s' sDot : ℝ) : Submodule ℝ≥0 GsmAtom where
  carrier := {A | PassiveStep A s s' sDot}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq, PassiveStep, atom_add_ψ, atom_add_pot, dissipationPower_add] at *
    linarith
  zero_mem' := by simp [PassiveStep]
  smul_mem' c A hA := by
    simp only [Set.mem_setOf_eq, PassiveStep, atom_smul_ψ, atom_smul_pot, dissipationPower_smul] at *
    have h := mul_nonpos_of_nonneg_of_nonpos c.coe_nonneg hA
    have e : (c : ℝ) * A.ψ s' - (c : ℝ) * A.ψ s + (c : ℝ) * dissipationPower A.pot sDot =
        (c : ℝ) * (A.ψ s' - A.ψ s + dissipationPower A.pot sDot) := by ring
    linarith

theorem mem_admissibleCone {A : GsmAtom} {s s' sDot : ℝ} :
    A ∈ admissibleCone s s' sDot ↔ PassiveStep A s s' sDot := Iff.rfl

/-- A passive atom step whose free energies are the states' free energies is a `.transition` step. -/
theorem passiveStep_secondLaw (A : GsmAtom) {s s' sDot : ℝ} (h : PassiveStep A s s' sDot)
    {old new : RealThermodynamicState} (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hold : old.freeEnergy = A.ψ s) (hnew : new.freeEnergy = A.ψ s') :
    SecondLawₚ .transition (.thermodynamic old new) :=
  inequality_secondLaw ⟨hm, convex_phi_dissipation_nonneg A.pot sDot, by rw [hold, hnew]; exact h⟩

/-- **Composition law (W-44)**: a finite non-negative combination of atoms that each pass the step passes it;
    its dissipation is Σᵢ cᵢ·Dᵢ with every summand ≥ 0; and the composite step is a `.transition` instance of
    `SecondLaw`. -/
theorem combination_secondLaw {ι : Type*} (t : Finset ι) (c : ι → ℝ≥0) (A : ι → GsmAtom)
    {s s' sDot : ℝ} (h : ∀ i ∈ t, PassiveStep (A i) s s' sDot)
    {old new : RealThermodynamicState} (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hold : old.freeEnergy = ∑ i ∈ t, (c i : ℝ) * (A i).ψ s)
    (hnew : new.freeEnergy = ∑ i ∈ t, (c i : ℝ) * (A i).ψ s') :
    SecondLawₚ .transition (.thermodynamic old new) ∧
      dissipationPower (∑ i ∈ t, c i • A i).pot sDot =
        ∑ i ∈ t, (c i : ℝ) * dissipationPower (A i).pot sDot ∧
      ∀ i ∈ t, 0 ≤ (c i : ℝ) * dissipationPower (A i).pot sDot := by
  have hmem : (∑ i ∈ t, c i • A i) ∈ admissibleCone s s' sDot :=
    Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ (c i) (h i hi)
  refine ⟨passiveStep_secondLaw _ hmem hm ?_ ?_, ?_, fun i _ => combination_summand_nonneg c (fun j => (A j).pot) sDot i⟩
  · rw [hold, atom_sum_ψ]
  · rw [hnew, atom_sum_ψ]
  · rw [atom_sum_pot, dissipationPower_sum]

-- ================================================================
-- SECTION 5: independent channels compose by concatenation
-- ================================================================

/-- Atoms on disjoint rate channels: the block composite of `n` and `m` channels. -/
def tensor {n m : ℕ} (M : GsmMultiPotential n) (N : GsmMultiPotential m) : GsmMultiPotential (n + m) where
  ch := Fin.append M.ch N.ch

/-- The power of a block composite is the sum of the blocks' powers. -/
theorem tensor_power {n m : ℕ} (M : GsmMultiPotential n) (N : GsmMultiPotential m) (x : Fin n → ℝ)
    (y : Fin m → ℝ) :
    multiDissipationPower (tensor M N) (Fin.append x y) = multiDissipationPower M x + multiDissipationPower N y := by
  simp [multiDissipationPower, tensor, Fin.sum_univ_add]

/-- A block composite under the passive inequality balance satisfies the second law. -/
theorem tensor_secondLaw {n m : ℕ} (M : GsmMultiPotential n) (N : GsmMultiPotential m) (x : Fin n → ℝ)
    (y : Fin m → ℝ) {old new : RealThermodynamicState} (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hb : (new.freeEnergy - old.freeEnergy) + (multiDissipationPower M x + multiDissipationPower N y) ≤ 0) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  multi_secondLaw (tensor M N) hm (by rw [tensor_power]; exact hb)

-- ================================================================
-- SECTION 6: glue terms and the glue fraction
-- ================================================================

/-- Glue fraction |D_glue| / D_total, with D_total = D_atoms + D_glue (zero when D_total = 0). -/
noncomputable def glueFraction (dAtoms dGlue : ℝ) : ℝ :=
  |dGlue| / (dAtoms + dGlue)

/-- A convex glue term is an atom with zero free energy. -/
def glueAtom (G : GsmDissipationPotential) : GsmAtom :=
  ⟨fun _ => 0, convexOn_const 0 convex_univ, G⟩

/-- **Convex glue keeps admissibility**: the composite of atoms with a GSM glue potential is a GSM atom, its
    dissipation is D_atoms + D_glue with both terms ≥ 0, and a passive balance on it is a `.transition` step. -/
theorem convexGlue_secondLaw (A : GsmAtom) (G : GsmDissipationPotential) {s s' sDot : ℝ}
    (hb : (A.ψ s' - A.ψ s) + (dissipationPower A.pot sDot + dissipationPower G sDot) ≤ 0)
    {old new : RealThermodynamicState} (hm : CoreMassCond ℝ RealThermodynamicState old new)
    (hold : old.freeEnergy = A.ψ s) (hnew : new.freeEnergy = A.ψ s') :
    SecondLawₚ .transition (.thermodynamic old new) ∧
      dissipationPower (A + glueAtom G).pot sDot = dissipationPower A.pot sDot + dissipationPower G sDot ∧
      0 ≤ dissipationPower G sDot := by
  have hstep : PassiveStep (A + glueAtom G) s s' sDot := by
    simp only [PassiveStep, atom_add_ψ, atom_add_pot, dissipationPower_add, glueAtom]
    linarith
  refine ⟨passiveStep_secondLaw _ hstep hm ?_ ?_, by simp [glueAtom],
    convex_phi_dissipation_nonneg G sDot⟩
  · simp [glueAtom, hold]
  · simp [glueAtom, hnew]

/-- **Arbitrary glue with a witness**: a glue dissipation of any sign is admissible once the composite's
    total dissipation is witnessed non-negative. -/
theorem glued_secondLaw_of_witness {dAtoms dGlue : ℝ} {old new : RealThermodynamicState}
    (hm : CoreMassCond ℝ RealThermodynamicState old new) (hw : 0 ≤ dAtoms + dGlue)
    (hb : (new.freeEnergy - old.freeEnergy) + (dAtoms + dGlue) ≤ 0) :
    SecondLawₚ .transition (.thermodynamic old new) :=
  inequality_secondLaw ⟨hm, hw, hb⟩

/-- **Refusal without a witness**: under the passive equality balance, a negative total dissipation raises
    the free energy and the second law refuses the step. -/
theorem glued_refused_of_negative_total {dAtoms dGlue : ℝ} {old new : RealThermodynamicState}
    (hneg : dAtoms + dGlue < 0) (hb : (new.freeEnergy - old.freeEnergy) + (dAtoms + dGlue) = 0) :
    ¬ SecondLawₚ .transition (.thermodynamic old new) := by
  intro h
  have hd : new.freeEnergy ≤ old.freeEnergy := h.2
  linarith

/-- **An arbitrary glue term is not closed under the law**: non-negative atom dissipation with a negative glue
    term and a passive balance gives a step the second law refuses. -/
theorem arbitrary_glue_not_closed :
    ∃ (dAtoms dGlue : ℝ) (old new : RealThermodynamicState),
      0 ≤ dAtoms ∧ CoreMassCond ℝ RealThermodynamicState old new ∧
        (new.freeEnergy - old.freeEnergy) + (dAtoms + dGlue) = 0 ∧
        ¬ SecondLawₚ .transition (.thermodynamic old new) := by
  refine ⟨0, -1, ⟨0, 0⟩, ⟨0, 1⟩, le_rfl, ?_, by norm_num, ?_⟩
  · show |(0 : ℝ) - 0| ≤ ThermodynamicScalar.δMass (K := ℝ)
    simpa using ThermodynamicScalar.δMass_nonneg (K := ℝ)
  · exact glued_refused_of_negative_total (dAtoms := 0) (dGlue := -1) (by norm_num) (by norm_num)

/-- **Convex glue fraction lies in [0, 1]**. -/
theorem glueFraction_mem_unit {dAtoms dGlue : ℝ} (hA : 0 ≤ dAtoms) (hG : 0 ≤ dGlue) :
    0 ≤ glueFraction dAtoms dGlue ∧ glueFraction dAtoms dGlue ≤ 1 := by
  unfold glueFraction
  rw [abs_of_nonneg hG]
  refine ⟨div_nonneg hG (add_nonneg hA hG), ?_⟩
  rcases (add_nonneg hA hG).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact zero_le_one
  · rw [div_le_one hpos]; linarith

/-- The glue fraction vanishes exactly when the glue dissipation does (for a non-zero total). -/
theorem glueFraction_eq_zero_iff {dAtoms dGlue : ℝ} (hT : dAtoms + dGlue ≠ 0) :
    glueFraction dAtoms dGlue = 0 ↔ dGlue = 0 := by
  unfold glueFraction
  rw [div_eq_zero_iff, abs_eq_zero]
  exact ⟨fun h => h.resolve_right hT, Or.inl⟩

/-- **A glue fraction above one signals a negative glue term**: with non-negative atom dissipation,
    |D_glue| > D_total forces D_glue < 0, so the term is not a GSM potential and needs its own witness. -/
theorem glue_neg_of_fraction_gt_one {dAtoms dGlue : ℝ} (hA : 0 ≤ dAtoms)
    (h : 1 < glueFraction dAtoms dGlue) : dGlue < 0 := by
  by_contra hG
  have := (glueFraction_mem_unit hA (not_lt.1 hG)).2
  linarith

/-- The glue fraction of a convex glue potential at a rate, against non-negatively combined atoms. -/
theorem convexGlue_fraction_mem_unit (A : GsmAtom) (G : GsmDissipationPotential) (sDot : ℝ) :
    0 ≤ glueFraction (dissipationPower A.pot sDot) (dissipationPower G sDot) ∧
      glueFraction (dissipationPower A.pot sDot) (dissipationPower G sDot) ≤ 1 :=
  glueFraction_mem_unit (convex_phi_dissipation_nonneg A.pot sDot) (convex_phi_dissipation_nonneg G sDot)

end UMST.Composition
