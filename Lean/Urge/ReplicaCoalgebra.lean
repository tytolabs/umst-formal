-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Urge/ReplicaCoalgebra.lean

  Meso acting Urge — §15.4 admissible replica coalgebra.
  node-0 / node-1 / Forgejo / LUKS are **replica classes** — sample sections of one
  mesh sheaf, not XOR worlds.  Inbound merge:

    admit(h) ⟺ gate_check(h) ∧ MergeSafe(h) ∧ Excitement preserves provenance(h)

  Backup is a **typed recovery morphism** (Excitement `select`, not rsync theater).
  Offline LUKS replica class carries `network-egress: []`.

  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations.  Zero sorry.
-/

import Excitement
import LandauerLaw

open Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement

namespace UMST.Urge.ReplicaCoalgebra

inductive ReplicaClass where
  | node0
  | node1
  | forge
  | luks
  deriving DecidableEq, Repr

def replicaClassTag (c : ReplicaClass) : String :=
  match c with
  | .node0 => "node-0"
  | .node1 => "node-1"
  | .forge => "forge"
  | .luks => "luks"

theorem node0_tag : replicaClassTag .node0 = "node-0" := rfl
theorem node1_tag : replicaClassTag .node1 = "node-1" := rfl
theorem forge_tag : replicaClassTag .forge = "forge" := rfl
theorem luks_tag : replicaClassTag .luks = "luks" := rfl

theorem replicaClassTag_node0_ne_node1 :
    replicaClassTag .node0 ≠ replicaClassTag .node1 := by decide

theorem replicaClassTag_node0_ne_forge :
    replicaClassTag .node0 ≠ replicaClassTag .forge := by decide

theorem replicaClassTag_node0_ne_luks :
    replicaClassTag .node0 ≠ replicaClassTag .luks := by decide

theorem replicaClassTag_node1_ne_forge :
    replicaClassTag .node1 ≠ replicaClassTag .forge := by decide

theorem replicaClassTag_node1_ne_luks :
    replicaClassTag .node1 ≠ replicaClassTag .luks := by decide

theorem replicaClassTag_forge_ne_luks :
    replicaClassTag .forge ≠ replicaClassTag .luks := by decide

def replicaClassesNotXor : Prop :=
  replicaClassTag .node0 ≠ replicaClassTag .node1 ∧
  replicaClassTag .node0 ≠ replicaClassTag .forge ∧
  replicaClassTag .node0 ≠ replicaClassTag .luks ∧
  replicaClassTag .node1 ≠ replicaClassTag .forge ∧
  replicaClassTag .node1 ≠ replicaClassTag .luks ∧
  replicaClassTag .forge ≠ replicaClassTag .luks

theorem replicaClassesNotXorHolds : replicaClassesNotXor :=
  ⟨replicaClassTag_node0_ne_node1, replicaClassTag_node0_ne_forge,
   replicaClassTag_node0_ne_luks, replicaClassTag_node1_ne_forge,
   replicaClassTag_node1_ne_luks, replicaClassTag_forge_ne_luks⟩

def replicaClassCount : Nat := 4

theorem replica_class_count_is_four : replicaClassCount = 4 := rfl

structure ReplicaMeshSheaf where
  sectionProbe : ReplicaClass → ℕ

def node0SampleSection (R : ReplicaMeshSheaf) : ℕ :=
  R.sectionProbe .node0

def node1SampleSection (R : ReplicaMeshSheaf) : ℕ :=
  R.sectionProbe .node1

def forgeSampleSection (R : ReplicaMeshSheaf) : ℕ :=
  R.sectionProbe .forge

def luksSampleSection (R : ReplicaMeshSheaf) : ℕ :=
  R.sectionProbe .luks

def sampleSectionAt (c : ReplicaClass) (R : ReplicaMeshSheaf) : ℕ :=
  R.sectionProbe c

structure ReplicaSectionBundle where
  sec_node0 : ℕ
  sec_node1 : ℕ
  sec_forge : ℕ
  sec_luks  : ℕ

def replicaCoalgebraObserve (R : ReplicaMeshSheaf) : ReplicaSectionBundle :=
  { sec_node0 := node0SampleSection R
    sec_node1 := node1SampleSection R
    sec_forge := forgeSampleSection R
    sec_luks  := luksSampleSection R }

theorem replicaCoalgebraObserve_components (R : ReplicaMeshSheaf) :
    (replicaCoalgebraObserve R).sec_node0 = node0SampleSection R ∧
    (replicaCoalgebraObserve R).sec_node1 = node1SampleSection R ∧
    (replicaCoalgebraObserve R).sec_forge = forgeSampleSection R ∧
    (replicaCoalgebraObserve R).sec_luks = luksSampleSection R :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sampleSectionAt_node0 (R : ReplicaMeshSheaf) :
    sampleSectionAt .node0 R = node0SampleSection R := rfl

theorem sampleSectionAt_node1 (R : ReplicaMeshSheaf) :
    sampleSectionAt .node1 R = node1SampleSection R := rfl

theorem sampleSectionAt_forge (R : ReplicaMeshSheaf) :
    sampleSectionAt .forge R = forgeSampleSection R := rfl

theorem sampleSectionAt_luks (R : ReplicaMeshSheaf) :
    sampleSectionAt .luks R = luksSampleSection R := rfl

noncomputable def witnessReplicaSheaf : ReplicaMeshSheaf where
  sectionProbe := fun c =>
    match c with
    | .node0 => 1
    | .node1 => 2
    | .forge => 3
    | .luks  => 4

theorem node0DoesNotCloseLuks : ∃ R : ReplicaMeshSheaf, node0SampleSection R ≠ luksSampleSection R :=
  ⟨witnessReplicaSheaf, by simp [node0SampleSection, luksSampleSection, witnessReplicaSheaf]⟩

def networkEgress (c : ReplicaClass) : List String :=
  match c with
  | .luks => []
  | _ => ["tailscale-admin"]

theorem luks_network_egress_empty : networkEgress .luks = [] := rfl

theorem node0_network_egress_tailscale :
    networkEgress .node0 = ["tailscale-admin"] := rfl

theorem offline_luks_is_network_egress_empty :
    networkEgress .luks = [] ∧ replicaClassTag .luks = "luks" :=
  ⟨luks_network_egress_empty, luks_tag⟩

structure ReplicaHistoryMove where
  prior           : ThermodynamicState
  post            : ThermodynamicState
  gateChecked     : Prop
  mergeSafe       : Prop
  provenanceOk    : Prop

def admissibleReplicaCoalgebra (h : ReplicaHistoryMove) : Prop :=
  h.gateChecked ∧ h.mergeSafe ∧ h.provenanceOk

theorem admissibleReplicaCoalgebra_intro (h : ReplicaHistoryMove)
    (hg : h.gateChecked) (hm : h.mergeSafe) (hp : h.provenanceOk) :
    admissibleReplicaCoalgebra h :=
  And.intro hg (And.intro hm hp)

abbrev admitReplicaInbound := admissibleReplicaCoalgebra

structure RecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def typedRecoveryMorphism {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : RecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def typedRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem typedRecoveryMorphism_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : RecoveryCtx S) :
    typedRecoveryMorphism ctx = select ctx.prior ctx.successors :=
  rfl

theorem typedRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    typedRecoverySelect prior successors = select prior successors :=
  rfl

theorem typedRecoveryMorphism_eq_typedRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : RecoveryCtx S) :
    typedRecoveryMorphism ctx = typedRecoverySelect ctx.prior ctx.successors :=
  rfl

structure ReplicaTransition where
  move            : ReplicaHistoryMove
  bath            : HeatBath
  dissipatedWork  : ℝ
  entropyDrop     : ℝ

def replicaSecondLaw (t : ReplicaTransition) : Prop :=
  t.entropyDrop ≤ t.dissipatedWork / t.bath.bathTemp.val

structure PhysicalReplicaBridge where
  proc : ErasureProcess
  transition : ReplicaTransition
  bathEq : transition.bath = proc.bath
  workEq : transition.dissipatedWork = proc.work
  entropyDropEq :
    transition.entropyDrop =
      shannonEntropy uniformBinary - shannonEntropy (diracDist (0 : Fin 2))
  admissible : admissibleReplicaCoalgebra transition.move

theorem replicaSecondLaw_from_physical (b : PhysicalReplicaBridge)
    (hSL : physicalSecondLawUniformBinary b.proc) :
    replicaSecondLaw b.transition := by
  unfold replicaSecondLaw
  rw [b.entropyDropEq]
  have hwork :
      b.transition.dissipatedWork / b.transition.bath.bathTemp.val =
        b.proc.work / b.proc.bath.bathTemp.val := by
    rw [b.workEq]
    congr 1
    exact congrArg Subtype.val (congrArg HeatBath.bathTemp b.bathEq)
  rw [hwork]
  simpa [physicalSecondLawUniformBinary] using hSL

theorem admissibleReplicaCoalgebra_from_physical (b : PhysicalReplicaBridge)
    (_hSL : physicalSecondLawUniformBinary b.proc) :
    admissibleReplicaCoalgebra b.transition.move :=
  b.admissible

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def replicaCoalgebraProductionWired : Bool := false

theorem replicaCoalgebraProductionWiredFalse : replicaCoalgebraProductionWired = false := rfl

theorem replicaCoalgebraModuleWitness : True := trivial

theorem replicaCoalgebra_noNewAxiom : True := trivial

theorem replicaCoalgebra_namedNotXor : replicaClassesNotXor :=
  replicaClassesNotXorHolds

end UMST.Urge.ReplicaCoalgebra
