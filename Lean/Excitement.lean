/-
  UMST.Excitement — directed selection coalgebra over finite candidate lists.
-/
import Core.State
import DualLedger

namespace UMST.Excitement

open UMST.Core

def kB {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] : K := 1

def jointFreeEnergy {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [JointThermo K S] (s : S) : K :=
  JointThermo.internalEnergy s
    - JointThermo.temperature s * JointThermo.entropy s
    - kB * JointThermo.temperature s * JointThermo.mutualInfo s

def globalFreeEnergyRat {S : Type} [JointThermo ℚ S] (s : S) (dl : DualLedger) : ℚ :=
  jointFreeEnergy s + DualLedger.total dl

inductive Residue where
  | noCandidates
  | allInadmissible
  | allExcludedByCBF
  | allExcludedByDEC
  | untaggedConstant
  | noStrictImprovement
  deriving DecidableEq, Repr

structure Cand {K : Type} {S : Type} [LinearOrderedField K] [ThermodynamicScalar K]
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (src : S) where
  tgt               : S
  step              : Admissible src tgt
  cbfSafe           : Bool
  decConserving     : Bool
  evidenceTagged    : Bool

def select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) : Cand (K := ℚ) src ⊕ Residue :=
  if cands.isEmpty then Sum.inr Residue.noCandidates
  else
    let tagged := cands.filter (fun c => c.evidenceTagged)
    if tagged.isEmpty then Sum.inr Residue.untaggedConstant
    else
      let cbfOk := tagged.filter (fun c => c.cbfSafe)
      if cbfOk.isEmpty then Sum.inr Residue.allExcludedByCBF
      else
        let decOk := cbfOk.filter (fun c => c.decConserving)
        if decOk.isEmpty then Sum.inr Residue.allExcludedByDEC
        else
          let pickMin (acc : Option (Cand (K := ℚ) src)) (c : Cand (K := ℚ) src) : Option (Cand src) :=
            match acc with
            | none => some c
            | some b =>
                let fc := jointFreeEnergy c.tgt
                let fb := jointFreeEnergy b.tgt
                if fc < fb then some c else if fb < fc then some b else some b
          match decOk.foldl pickMin none with
          | none => Sum.inr Residue.allInadmissible
          | some c =>
              let srcF := jointFreeEnergy src
              let cF := jointFreeEnergy c.tgt
              if cF < srcF then Sum.inl c
              else if decOk.any (fun x => jointFreeEnergy x.tgt < srcF) then Sum.inl c
              else if decOk.any (fun x => jointFreeEnergy x.tgt = srcF) then Sum.inl c
              else Sum.inr Residue.noStrictImprovement

end UMST.Excitement
