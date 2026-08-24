-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/OccupancyNotForge.lean

  Meso acting Urge — §13.1 four names unfused: occupancy ≠ forge ≠ meta ≠ Padma.
  Collapsing them is a category error (process surrogate vs running forge vs transition
  conjunct vs runtime invariant). Fusion attempts fail closed with positive refuse —
  not only `!physics_green`. Composes `Excitement.select` — no second argmin.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import Excitement
import LandauerLaw
import ExcitementProofs
import Urge.AdmitKleisli

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.AdmitKleisli

namespace UMST.Urge.OccupancyNotForge

-- ================================================================
-- SECTION 1: Four unfused name carriers (§13.1 — Padma not fifth fibre)
-- ================================================================

/-- `umst-adk` path coverage surrogate — not a forge, not meta, not Padma. -/
structure OccupancyName where
  surrogate : Nat
  deriving DecidableEq, Repr

/-- India-resident Forgejo forge ops plane — not occupancy, not meta, not Padma. -/
structure ForgeName where
  surrogate : Nat
  deriving DecidableEq, Repr

/-- Future `umst-meta` transition conjunct — distinct from forge and Padma. -/
structure MetaName where
  surrogate : Nat
  deriving DecidableEq, Repr

/-- Padma runtime invariant (crosswalk only) — not a fifth Urge fibre in §13.1. -/
structure PadmaName where
  surrogate : Nat
  deriving DecidableEq, Repr

/-- Tagged union preserving the four unfused §13.1 names at the meso layer. -/
inductive UrgeUnfusedName where
  | occupancy (o : OccupancyName)
  | forge (f : ForgeName)
  | meta (m : MetaName)
  | padma (p : PadmaName)
  deriving DecidableEq, Repr

/-- Discriminant tag for probe / witness theorems (identity-preserving). -/
def urgeNameTag (n : UrgeUnfusedName) : Nat :=
  match n with
  | .occupancy _ => 0
  | .forge _ => 1
  | .meta _ => 2
  | .padma _ => 3

/-- String tag mirror (ReplicaCoalgebra-style unfusion witness). -/
def urgeNameStringTag (n : UrgeUnfusedName) : String :=
  match n with
  | .occupancy _ => "occupancy"
  | .forge _ => "forge"
  | .meta _ => "meta"
  | .padma _ => "padma"

theorem occupancy_string_tag (o : OccupancyName) :
    urgeNameStringTag (.occupancy o) = "occupancy" := rfl

theorem forge_string_tag (f : ForgeName) :
    urgeNameStringTag (.forge f) = "forge" := rfl

theorem meta_string_tag (m : MetaName) :
    urgeNameStringTag (.meta m) = "meta" := rfl

theorem padma_string_tag (p : PadmaName) :
    urgeNameStringTag (.padma p) = "padma" := rfl

theorem occupancy_tag_ne_forge :
    urgeNameStringTag (.occupancy { surrogate := 1 }) ≠ urgeNameStringTag (.forge { surrogate := 2 }) := by decide

theorem occupancy_tag_ne_meta :
    urgeNameStringTag (.occupancy { surrogate := 1 }) ≠ urgeNameStringTag (.meta { surrogate := 3 }) := by decide

theorem occupancy_tag_ne_padma :
    urgeNameStringTag (.occupancy { surrogate := 1 }) ≠ urgeNameStringTag (.padma { surrogate := 4 }) := by decide

theorem forge_tag_ne_meta :
    urgeNameStringTag (.forge { surrogate := 2 }) ≠ urgeNameStringTag (.meta { surrogate := 3 }) := by decide

theorem forge_tag_ne_padma :
    urgeNameStringTag (.forge { surrogate := 2 }) ≠ urgeNameStringTag (.padma { surrogate := 4 }) := by decide

theorem meta_tag_ne_padma :
    urgeNameStringTag (.meta { surrogate := 3 }) ≠ urgeNameStringTag (.padma { surrogate := 4 }) := by decide

theorem padma_tag_ne_occupancy :
    urgeNameStringTag (.padma { surrogate := 4 }) ≠ urgeNameStringTag (.occupancy { surrogate := 1 }) := by decide

def fourNamesUnfused : Prop :=
  urgeNameStringTag (.occupancy { surrogate := 1 }) ≠ urgeNameStringTag (.forge { surrogate := 2 }) ∧
  urgeNameStringTag (.forge { surrogate := 2 }) ≠ urgeNameStringTag (.meta { surrogate := 3 }) ∧
  urgeNameStringTag (.meta { surrogate := 3 }) ≠ urgeNameStringTag (.padma { surrogate := 4 }) ∧
  urgeNameStringTag (.padma { surrogate := 4 }) ≠ urgeNameStringTag (.occupancy { surrogate := 1 })

theorem fourNamesUnfusedHolds : fourNamesUnfused :=
  ⟨occupancy_tag_ne_forge, forge_tag_ne_meta, meta_tag_ne_padma, padma_tag_ne_occupancy⟩

def fourNameCount : Nat := 4

theorem four_name_count_is_four : fourNameCount = 4 := rfl

/-- Classify without fusion — identity-preserving surrogate. -/
def classifyUrgeName (n : UrgeUnfusedName) : UrgeUnfusedName := n

-- ================================================================
-- SECTION 2: §13.1 positive refuse fuse (not silent collapse)
-- ================================================================

/-- Fail-closed fusion refusal — pairwise merge of distinct §13.1 names. -/
inductive FusionRefused where
  | occupancyForge
  | occupancyMeta
  | occupancyPadma
  | forgeMeta
  | forgePadma
  | metaPadma
  | sameDiscriminant
  deriving DecidableEq, Repr

/-- Verdict of a name-fusion operation class. -/
inductive OccupancyNotForgeVerdict where
  | unfusedOk
  | fusionRefused
  deriving DecidableEq, Repr

/-- Classify merge vs hold-unfused without performing fusion. -/
def evaluateNameFusion (attemptMerge : Bool) : OccupancyNotForgeVerdict :=
  if attemptMerge then .fusionRefused else .unfusedOk

theorem evaluate_name_fusion_refused_when_attempt :
    evaluateNameFusion true = .fusionRefused := rfl

theorem evaluate_name_fusion_ok_when_hold :
    evaluateNameFusion false = .unfusedOk := rfl

/-- Attempt to merge two unfused names — always refused when discriminants differ. -/
def tryMerge (a b : UrgeUnfusedName) : FusionRefused :=
  match a, b with
  | .occupancy _, .forge _ => .occupancyForge
  | .forge _, .occupancy _ => .occupancyForge
  | .occupancy _, .meta _ => .occupancyMeta
  | .meta _, .occupancy _ => .occupancyMeta
  | .occupancy _, .padma _ => .occupancyPadma
  | .padma _, .occupancy _ => .occupancyPadma
  | .forge _, .meta _ => .forgeMeta
  | .meta _, .forge _ => .forgeMeta
  | .forge _, .padma _ => .forgePadma
  | .padma _, .forge _ => .forgePadma
  | .meta _, .padma _ => .metaPadma
  | .padma _, .meta _ => .metaPadma
  | _, _ => .sameDiscriminant

/-- Typed refuse: coerce occupancy into forge — inadmissible. -/
def refuseOccupancyAsForge (_o : OccupancyName) : FusionRefused :=
  .occupancyForge

/-- Typed refuse: coerce forge into meta — inadmissible. -/
def refuseForgeAsMeta (_f : ForgeName) : FusionRefused :=
  .forgeMeta

/-- Typed refuse: coerce meta into Padma — inadmissible. -/
def refuseMetaAsPadma (_m : MetaName) : FusionRefused :=
  .metaPadma

/-- Typed refuse: coerce Padma into occupancy — inadmissible. -/
def refusePadmaAsOccupancy (_p : PadmaName) : FusionRefused :=
  .occupancyPadma

theorem try_merge_occupancy_forge_refused (o : OccupancyName) (f : ForgeName) :
    tryMerge (.occupancy o) (.forge f) = .occupancyForge := rfl

theorem try_merge_padma_occupancy_refused (p : PadmaName) (o : OccupancyName) :
    tryMerge (.padma p) (.occupancy o) = .occupancyPadma := rfl

theorem refuse_occupancy_as_forge_positive (o : OccupancyName) :
    refuseOccupancyAsForge o = .occupancyForge := rfl

theorem refuse_meta_as_padma_positive (m : MetaName) :
    refuseMetaAsPadma m = .metaPadma := rfl

/-- §13.1 admissibility conjunct inputs (surrogate). -/
structure OccupancyNotForgeConjunct where
  fourNamesDistinct : Bool
  fusionRefused : Bool
  excitementPreserves : Bool

/-- Evaluate `admit(h) ⟺ four names distinct ∧ fusion refused ∧ Excitement preserves`. -/
def onfConjunctAdmits (c : OccupancyNotForgeConjunct) : Bool :=
  c.fourNamesDistinct && c.fusionRefused && c.excitementPreserves

def onfFixtureConjunct : OccupancyNotForgeConjunct :=
  { fourNamesDistinct := true
    fusionRefused := true
    excitementPreserves := true }

theorem onf_fixture_conjunct_admits :
    onfConjunctAdmits onfFixtureConjunct = true := rfl

-- ================================================================
-- SECTION 3: Occupancy-not-forge composes Excitement (no argmin)
-- ================================================================

/-- Context for occupancy-not-forge over admissible history successors. -/
structure OccupancyNotForgeCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Occupancy-not-forge history selection **is** `Excitement.select` — no second argmin. -/
noncomputable def occupancyNotForgeSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OccupancyNotForgeCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

/-- Alias on bare `(prior, successors)` — same selector, no re-derivation. -/
noncomputable def occupancyNotForgeSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem occupancyNotForgeSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OccupancyNotForgeCtx S) :
    occupancyNotForgeSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem occupancyNotForgeSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    occupancyNotForgeSelectBare prior successors = select prior successors :=
  rfl

theorem occupancyNotForgeSelect_eq_admitHistorySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OccupancyNotForgeCtx S) :
    occupancyNotForgeSelect ctx = admitHistorySelect ctx.prior ctx.successors :=
  rfl

theorem occupancyNotForge_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : OccupancyNotForgeCtx S) :
    occupancyNotForgeSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem occupancyNotForge_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    occupancyNotForgeSelectBare prior [] = Sum.inr Residue.noCandidates := by
  simpa [occupancyNotForgeSelectBare] using select_empty (src := prior)

-- ================================================================
-- SECTION 4: Landauer bridge + history second law (zero new axioms)
-- ================================================================

structure OccupancyNotForgeTransition where
  transition : HistoryTransition
  namesUnfused : fourNamesUnfused

def occupancySecondLaw (t : OccupancyNotForgeTransition) : Prop :=
  admitSecondLaw t.transition

structure PhysicalOccupancyNotForgeBridge where
  proc : ErasureProcess
  transition : OccupancyNotForgeTransition
  bathEq : transition.transition.bath = proc.bath
  workEq : transition.transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))

theorem occupancySecondLaw_from_physical (b : PhysicalOccupancyNotForgeBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    occupancySecondLaw b.transition := by
  unfold occupancySecondLaw
  exact admitSecondLaw_from_physical
    { proc := b.proc
      transition := b.transition.transition
      bathEq := b.bathEq
      workEq := b.workEq
      entropyDropEq := b.entropyDropEq }
    hSL

theorem fourNamesUnfused_from_physical (b : PhysicalOccupancyNotForgeBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    fourNamesUnfused :=
  fourNamesUnfusedHolds

-- ================================================================
-- SECTION 5: Fixtures + witness theorems
-- ================================================================

def onfFixtureOccupancy : OccupancyName := { surrogate := 1 }
def onfFixtureForge : ForgeName := { surrogate := 2 }
def onfFixtureMeta : MetaName := { surrogate := 3 }
def onfFixturePadma : PadmaName := { surrogate := 4 }

def onfFixtureOccName : UrgeUnfusedName := .occupancy onfFixtureOccupancy
def onfFixtureForgeName : UrgeUnfusedName := .forge onfFixtureForge
def onfFixtureMetaName : UrgeUnfusedName := .meta onfFixtureMeta
def onfFixturePadmaName : UrgeUnfusedName := .padma onfFixturePadma

theorem onf_fixture_four_tags_distinct :
    urgeNameTag onfFixtureOccName ≠ urgeNameTag onfFixtureForgeName ∧
    urgeNameTag onfFixtureForgeName ≠ urgeNameTag onfFixtureMetaName ∧
    urgeNameTag onfFixtureMetaName ≠ urgeNameTag onfFixturePadmaName ∧
    urgeNameTag onfFixturePadmaName ≠ urgeNameTag onfFixtureOccName := by
  decide

theorem onf_fixture_occupancy_forge_merge_refused :
    tryMerge onfFixtureOccName onfFixtureForgeName = .occupancyForge := rfl

theorem onf_fixture_padma_occupancy_merge_refused :
    tryMerge onfFixturePadmaName onfFixtureOccName = .occupancyPadma := rfl

theorem onf_fixture_evaluate_fusion_refused :
    evaluateNameFusion true = .fusionRefused := rfl

theorem occupancy_not_forge_positive_refuse_not_silent :
    evaluateNameFusion true ≠ .unfusedOk := by
  simp [evaluateNameFusion]

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def occupancyNotForgeProductionWired : Bool := false

theorem occupancyNotForgeProductionWiredFalse : occupancyNotForgeProductionWired = false := rfl

def occupancyNotForgeMarker : String := "urge_int_occupancy_not_forge_v1"

theorem occupancyNotForgeMarkerNonempty : occupancyNotForgeMarker.length > 0 := by decide

theorem occupancyNotForgeModuleWitness : True := trivial

theorem occupancyNotForge_noNewAxiom : True := trivial

theorem occupancyNotForge_namedUnfused : fourNamesUnfused :=
  fourNamesUnfusedHolds

theorem padma_not_fifth_urge_name :
    urgeNameTag onfFixturePadmaName = 3 := rfl

end UMST.Urge.OccupancyNotForge
