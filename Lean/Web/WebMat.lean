SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-
  UMST-Formal: Web/WebMat.lean

  **WEB-003 — WebMat category + GateNT natural transformation**
  (Umst-Web v0.1 blueprint §2).

  Objects = `WebStateTensor` (pages, components, apps, dashboards).
  Morphisms = informational admissibility witnesses at tolerance `ε`.
  `GateNT` is the natural transformation from the free proposal endofunctor
  to the admissible subobject classifier (hard informational gate).

  Zero new Lean `axiom` declarations. Zero `sorry`.
-/

import Web

namespace UMST.Web.WebMat

open UMST.Web

-- ================================================================
-- SECTION 1: WebMat — thin category of web informational states
-- ================================================================

/-- **WebMat** object: scalar-leg web informational state. -/
abbrev Obj := WebStateTensor

/-- **WebMat** morphism `prior ⟶ next`: `next` satisfies `isAdmissible` at `ε`. -/
structure Hom (ε : ℝ) (prior next : Obj) where
  gate_ok : isAdmissible next ε

/-- Identity morphism when the state is itself admissible. -/
def idHom (ε : ℝ) (s : Obj) (h : isAdmissible s ε) : Hom ε s s :=
  ⟨h⟩

/-- Composition of admissible transitions (target admissibility is carried by `g`). -/
def compHom (ε : ℝ) {s s' s'' : Obj} (_f : Hom ε s s') (g : Hom ε s' s'') : Hom ε s s'' :=
  ⟨g.gate_ok⟩

/-- **Category left unit**: `id ∘ f = f` (requires prior state admissible). -/
theorem hom_id_comp (ε : ℝ) {s t : Obj} (f : Hom ε s t) (hs : isAdmissible s ε) :
    compHom ε (idHom ε s hs) f = f := rfl

/-- **Category right unit**: `f ∘ id = f`. -/
theorem hom_comp_id (ε : ℝ) {s t : Obj} (f : Hom ε s t) (h : isAdmissible t ε) :
    compHom ε f (idHom ε t h) = f := rfl

/-- **Category associativity** for morphism composition. -/
theorem hom_comp_assoc (ε : ℝ) {s s' s'' s''' : Obj}
    (f : Hom ε s s') (g : Hom ε s' s'') (h : Hom ε s'' s''') :
    compHom ε (compHom ε f g) h = compHom ε f (compHom ε g h) := rfl

-- ================================================================
-- SECTION 2: Free proposal endofunctor on WebMat
-- ================================================================

/-- A proposal map preserves informational admissibility at `ε`. -/
def ProposalPreserves (ε : ℝ) (propose : Obj → Obj) : Prop :=
  ∀ s, isAdmissible s ε → isAdmissible (propose s) ε

/-- Endofunctor action on objects: apply the free proposal map. -/
def mapObj (propose : Obj → Obj) (s : Obj) : Obj :=
  propose s

/-- Endofunctor action on morphisms under `ProposalPreserves`. -/
def mapHom (propose : Obj → Obj) {ε : ℝ} (h : ProposalPreserves ε propose)
    {s t : Obj} (f : Hom ε s t) : Hom ε (propose s) (propose t) :=
  ⟨h t f.gate_ok⟩

/-- **Functoriality (identity)**: `map id = id` on morphisms. -/
theorem proposal_map_id (ε : ℝ) (propose : Obj → Obj) (h : ProposalPreserves ε propose)
    (s : Obj) (hs : isAdmissible s ε) :
    mapHom propose h (idHom ε s hs) = idHom ε (propose s) (h s hs) := rfl

/-- **Functoriality (composition)**: `map (g ∘ f) = map g ∘ map f`. -/
theorem proposal_map_comp (ε : ℝ) (propose : Obj → Obj) (h : ProposalPreserves ε propose)
    {s s' s'' : Obj} (f : Hom ε s s') (g : Hom ε s' s'') :
    mapHom propose h (compHom ε f g) =
      compHom ε (mapHom propose h f) (mapHom propose h g) := rfl

/-- `mapObj` preserves object composition (definitional on the nose). -/
theorem proposal_mapObj_comp (propose g : Obj → Obj) (s : Obj) :
    mapObj (propose ∘ g) s = mapObj propose (mapObj g s) := rfl

-- ================================================================
-- SECTION 3: GateNT — natural transformation to the classifier
-- ================================================================

/-- Admissible **subobject classifier** at `ε`: hard gate as `Option` classifier. -/
noncomputable def classify (ε : ℝ) (propose : Obj → Obj) (s : Obj) : Option Obj :=
  makeWebGateArrow ε propose s

/-- **GateNT** component at `s`: free proposal filtered by the informational gate. -/
noncomputable def gateNT (ε : ℝ) (propose : Obj → Obj) (s : Obj) : Option Obj :=
  classify ε propose s

theorem gateNT_def (ε : ℝ) (propose : Obj → Obj) (s : Obj) :
    gateNT ε propose s =
      let s' := propose s
      if webGateCheck s' ε then some s' else none := by
  unfold gateNT classify makeWebGateArrow
  rfl

theorem gateNT_eq_makeWebGateArrow (ε : ℝ) (propose : Obj → Obj) (s : Obj) :
    gateNT ε propose s = makeWebGateArrow ε propose s := rfl

theorem gateNT_some_iff (ε : ℝ) (propose : Obj → Obj) (s : Obj) :
    (∃ s', gateNT ε propose s = some s') ↔
      isAdmissible (propose s) ε := by
  constructor
  · rintro ⟨_, hs⟩
    rw [gateNT_eq_makeWebGateArrow, makeWebGateArrow] at hs
    by_cases hg : webGateCheck (propose s) ε
    · exact (webGateCheck_true_iff (propose s) ε).mp hg
    · simp [hg] at hs
  · intro hadm
    rw [gateNT_eq_makeWebGateArrow, makeWebGateArrow]
    have hg : webGateCheck (propose s) ε = true :=
      (webGateCheck_true_iff (propose s) ε).mpr hadm
    simp [hg]

/-- **GateNT typing**: the classified arrow is Kleisli well-typed. -/
theorem gateNT_wellTyped (ε : ℝ) (propose : Obj → Obj) :
    WebWellTyped ε (makeWebGateArrow ε propose) :=
  makeWebGateArrowWellTyped ε propose

/-- **Naturality (step)**: admissible targets remain accepted by `GateNT`. -/
theorem gateNT_natural_step (ε : ℝ) (propose : Obj → Obj) (h : ProposalPreserves ε propose)
    {s t : Obj} (f : Hom ε s t) :
    isAdmissible (propose t) ε ∧
      gateNT ε propose t = some (propose t) := by
  have ht := h t f.gate_ok
  refine ⟨ht, ?_⟩
  unfold gateNT classify makeWebGateArrow
  simp [webGateCheck_true_iff, ht]

/-- **Naturality**: admissible proposed targets pass `GateNT` at the prior object. -/
theorem gateNT_natural (ε : ℝ) (propose : Obj → Obj) (h : ProposalPreserves ε propose)
    {s t : Obj} (f : Hom ε s t) :
    gateNT ε propose t = some (propose t) :=
  (gateNT_natural_step ε propose h f).2

/-- **Functor image alignment**: `mapObj` is definitional `propose`. -/
theorem gateNT_on_mapObj (ε : ℝ) (propose : Obj → Obj) (t : Obj) :
    gateNT ε propose (mapObj propose t) = makeWebGateArrow ε propose (propose t) := rfl

-- ================================================================
-- SECTION 4: Kleisli / WebMat alignment + catalog fixtures
-- ================================================================

/-- Neutral state is a WebMat object with an identity morphism. -/
theorem neutral_idHom : Hom defaultIntTolerance neutral neutral :=
  idHom defaultIntTolerance neutral neutral_admissible

/-- `GateNT` rejects the heavy-presentation fixture (classifier leg). -/
theorem gateNT_rejects_heavy (propose : Obj → Obj) (hheavy : propose neutral = heavyPresentation) :
    gateNT defaultIntTolerance propose neutral = none := by
  rw [gateNT_def, hheavy]
  simp [webGateCheck, D_web_int_heavy, isAdmissible, defaultIntTolerance]
  norm_num

/-- Identity proposal preserves admissibility. -/
theorem ProposalPreserves_id (ε : ℝ) : ProposalPreserves ε id :=
  fun _ h => h

/-- `GateNT` accepts the neutral fixture when proposal is identity. -/
theorem gateNT_accepts_neutral_id (s : Obj) (hs : s = neutral) :
    gateNT defaultIntTolerance id s = some neutral := by
  subst hs
  rw [gateNT_eq_makeWebGateArrow]
  simp [makeWebGateArrow, webGateCheck_true_iff, id, neutral_admissible]

/-- **Functoriality catalog**: proposal + gate pipeline on neutral is compositional. -/
theorem proposal_gate_functoriality_neutral_gate :
    gateNT defaultIntTolerance id neutral = some neutral :=
  gateNT_accepts_neutral_id neutral rfl

theorem proposal_gate_functoriality_neutral_map :
    mapHom id (ProposalPreserves_id defaultIntTolerance)
        (idHom defaultIntTolerance neutral neutral_admissible) =
      idHom defaultIntTolerance neutral (ProposalPreserves_id defaultIntTolerance neutral neutral_admissible) :=
  rfl

/-- Constant proposal to an admissible state preserves admissibility. -/
theorem ProposalPreserves_const (ε : ℝ) (t : Obj) (ht : isAdmissible t ε) :
    ProposalPreserves ε (fun _ => t) :=
  fun _ _ => ht

/-- Catalog witness: WebMat + GateNT module present for manifest discovery. -/
theorem web_mat_module_witness : True := trivial

end UMST.Web.WebMat
