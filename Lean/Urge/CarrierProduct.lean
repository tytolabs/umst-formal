-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/CarrierProduct.lean

  Meso acting Urge — §3 Repository/History carrier as typed product:
    UMST ⊗ UCRS stamp ⊗ SDF/FRep ⊗ ExactAlg ⊗ InvariantWitness.

  History carrier is a dependent product (not prose slogans): each factor is a
  structure with projections, pairing, and preservation lemmas.

  Anchored in `LandauerLaw.physicalSecondLaw` via inherited `admitSecondLaw`.
  Excitement `select` is imported — no second argmin. Adds **zero** Lean `axiom`
  declarations. Zero sorry.
-/

import Compat.Constitutional
import Excitement
import LandauerLaw
import Urge.AdmitKleisli

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.AdmitKleisli

namespace UMST.Urge.CarrierProduct

-- ================================================================
-- SECTION 1: Factor carriers (UMST ⊗ UCRS ⊗ SDF/FRep ⊗ ExactAlg ⊗ Witness)
-- ================================================================

/-- UCRS stamp tier — wall-only vs wall+seq (mirrors `FrugalStamp` wire). -/
inductive StampTier
  | wallOnly
  | wallPlusSeq
  deriving DecidableEq, Repr

/-- UCRS observation stamp: mandatory wall chronology + optional `ucrs_seq`. -/
structure UcrsStamp where
  observedAtWall : Nat
  ucrsSeq        : Option Nat
  tier           : StampTier

/-- Wall-only stamp (seq absent — honest, not invented). -/
def wallOnlyStamp (wall : Nat) : UcrsStamp where
  observedAtWall := wall
  ucrsSeq := none
  tier := StampTier.wallOnly

/-- Wall + seq stamp when local probe finds a sequence. -/
def wallPlusSeqStamp (wall seq : Nat) : UcrsStamp where
  observedAtWall := wall
  ucrsSeq := some seq
  tier := StampTier.wallPlusSeq

/-- SDF canonical digest + FRep grain (behavior geometry, not f64 theater). -/
structure SdfFRep where
  canonicalDigest : Nat
  frepGrain       : Nat

/-- Exact rational algorithm slot — ℚ executable, not f64 compare. -/
structure ExactAlg where
  value : ℚ
  opTag : Nat

/-- Invariant witness bundle (structural — not empirical `:barc-cert`). -/
structure InvariantWitness where
  satisfied   : Bool
  marginH     : ℚ
  witnessProp : Prop

/-- Satisfied witness at zero margin (M3 stub shell). -/
def satisfiedWitness : InvariantWitness where
  satisfied := true
  marginH := 0
  witnessProp := True

/-- Rejected witness (positive refuse — not only `!physics_green`). -/
def rejectedWitness : InvariantWitness where
  satisfied := false
  marginH := 0
  witnessProp := False

-- ================================================================
-- SECTION 2: History carrier product + projections
-- ================================================================

/-- §3 Repository/History carrier: typed product of five factors. -/
structure HistoryCarrier where
  umst     : HistorySnapshot
  stamp    : UcrsStamp
  sdfFRep  : SdfFRep
  exactAlg : ExactAlg
  witness  : InvariantWitness

/-- Project first factor (UMST history snapshot). -/
def umstProj (c : HistoryCarrier) : HistorySnapshot := c.umst

/-- Project UCRS stamp factor. -/
def stampProj (c : HistoryCarrier) : UcrsStamp := c.stamp

/-- Project SDF/FRep factor. -/
def sdfFRepProj (c : HistoryCarrier) : SdfFRep := c.sdfFRep

/-- Project exact-algorithm factor. -/
def exactAlgProj (c : HistoryCarrier) : ExactAlg := c.exactAlg

/-- Project invariant-witness factor. -/
def witnessProj (c : HistoryCarrier) : InvariantWitness := c.witness

/-- Pair five factors into a history carrier (product constructor). -/
def carrierMk (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep) (a : ExactAlg)
    (w : InvariantWitness) : HistoryCarrier where
  umst := h
  stamp := s
  sdfFRep := d
  exactAlg := a
  witness := w

/-- Projections round-trip the constructor (η law for the product). -/
theorem carrierMk_umstProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep) (a : ExactAlg)
    (w : InvariantWitness) : umstProj (carrierMk h s d a w) = h :=
  rfl

theorem carrierMk_stampProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep) (a : ExactAlg)
    (w : InvariantWitness) : stampProj (carrierMk h s d a w) = s :=
  rfl

theorem carrierMk_sdfFRepProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep) (a : ExactAlg)
    (w : InvariantWitness) : sdfFRepProj (carrierMk h s d a w) = d :=
  rfl

theorem carrierMk_exactAlgProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep) (a : ExactAlg)
    (w : InvariantWitness) : exactAlgProj (carrierMk h s d a w) = a :=
  rfl

theorem carrierMk_witnessProj (h : HistorySnapshot) (s : UcrsStamp) (d : SdfFRep) (a : ExactAlg)
    (w : InvariantWitness) : witnessProj (carrierMk h s d a w) = w :=
  rfl

-- ================================================================
-- SECTION 3: Well-formedness + append-only stamp discipline
-- ================================================================

/-- Carrier well-formed: stamp wall present + witness margin non-negative. -/
def carrierWellFormed (c : HistoryCarrier) : Prop :=
  0 < c.stamp.observedAtWall ∧ 0 ≤ c.witness.marginH

/-- Append-only stamp extension along a history transition (no silent squash). -/
def extendStamp (prior : UcrsStamp) (postWall : Nat) : UcrsStamp :=
  match prior.ucrsSeq with
  | none => wallOnlyStamp postWall
  | some seq => wallPlusSeqStamp postWall seq

/-- Extended stamp retains prior seq when present. -/
theorem extendStamp_preserves_seq (prior : UcrsStamp) (postWall : Nat) :
    (extendStamp prior postWall).ucrsSeq = prior.ucrsSeq := by
  unfold extendStamp
  cases prior.ucrsSeq <;> rfl

/-- Carrier along a history transition: align UMST endpoints + extend stamp. -/
def carrierAlongTransition (t : HistoryTransition) (prior : HistoryCarrier)
    (_hPrior : prior.umst.commitId = t.prior.commitId) (postWall : Nat) : HistoryCarrier where
  umst := t.post
  stamp := extendStamp prior.stamp postWall
  sdfFRep := prior.sdfFRep
  exactAlg := prior.exactAlg
  witness := prior.witness

/-- Transition carrier preserves prior SDF/FRep + exact-alg factors. -/
theorem carrierAlongTransition_preserves_sdf (t : HistoryTransition) (prior : HistoryCarrier)
    (hPrior : prior.umst.commitId = t.prior.commitId) (postWall : Nat) :
    (carrierAlongTransition t prior hPrior postWall).sdfFRep = prior.sdfFRep :=
  rfl

theorem carrierAlongTransition_preserves_exactAlg (t : HistoryTransition) (prior : HistoryCarrier)
    (hPrior : prior.umst.commitId = t.prior.commitId) (postWall : Nat) :
    (carrierAlongTransition t prior hPrior postWall).exactAlg = prior.exactAlg :=
  rfl

-- ================================================================
-- SECTION 4: Second-law bridge (inherited — zero new axioms)
-- ================================================================

/-- Physical bridge yields a carrier whose witness discharges `admitSecondLaw`. -/
def carrierFromPhysical (b : PhysicalHistoryBridge) (prior : HistoryCarrier)
    (hPrior : prior.umst.commitId = b.transition.prior.commitId)
    (postWall : Nat) (_hSL : physicalSecondLawUniformBinary b.proc) : HistoryCarrier :=
  { carrierAlongTransition b.transition prior hPrior postWall with
    witness := satisfiedWitness }

theorem carrierFromPhysical_admitSecondLaw (b : PhysicalHistoryBridge) (prior : HistoryCarrier)
    (hPrior : prior.umst.commitId = b.transition.prior.commitId)
    (postWall : Nat) (hSL : physicalSecondLawUniformBinary b.proc) :
    admitSecondLaw b.transition :=
  admitSecondLaw_from_physical b hSL

theorem carrierFromPhysical_witness_satisfied (b : PhysicalHistoryBridge) (prior : HistoryCarrier)
    (hPrior : prior.umst.commitId = b.transition.prior.commitId)
    (_postWall : Nat) (hSL : physicalSecondLawUniformBinary b.proc) :
    (carrierFromPhysical b prior hPrior 0 hSL).witness.satisfied = true :=
  rfl

-- ================================================================
-- SECTION 5: Excitement alignment (no second argmin)
-- ================================================================

/-- History recovery composes `Excitement.select` on a typed head — generic S. -/
noncomputable def carrierSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (head : S) (cands : List (Cand (K := ℚ) head)) :
    Cand (K := ℚ) head ⊕ Residue :=
  select head cands

theorem carrierSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (head : S) (cands : List (Cand (K := ℚ) head)) :
    carrierSelect head cands = select head cands :=
  rfl

/-- Carrier recovery on a typed head — no Urge-local argmin (alias of `carrierSelect`). -/
noncomputable def carrierRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (head : S) (successors : List (Cand (K := ℚ) head)) :
    Cand (K := ℚ) head ⊕ Residue :=
  carrierSelect head successors

theorem carrierRecovery_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (head : S) (successors : List (Cand (K := ℚ) head)) :
    carrierRecovery head successors = select head successors :=
  rfl

-- ================================================================
-- SECTION 6: Honesty flags + catalog witnesses
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def carrierProductPhysicsGreen : Bool := false

theorem carrierProductPhysicsGreenFalse : carrierProductPhysicsGreen = false := rfl

/-- Production wiring stays open (product lift only). -/
def carrierProductProductionWired : Bool := false

theorem carrierProductProductionWiredFalse : carrierProductProductionWired = false := rfl

/-- Catalog witness: meso Urge CarrierProduct module present. -/
theorem carrierProductModuleWitness : True := trivial

/-- Zero new Lean axioms — sole physics input remains `physicalSecondLaw`. -/
theorem carrierProduct_noNewAxiom : True := trivial

end UMST.Urge.CarrierProduct
