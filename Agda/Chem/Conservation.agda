-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.Conservation — meso/acting mass conservation anchor.
--
-- CHEM-L0-FORMAL-01 / CHEM-NS-W0-AXIOM (umst-formal acting fiber only).
-- Conservation is a typed Core.Gate predicate — not a new physics postulate.
-- SSOT: δ-mass tolerance matches Agda Core / Lean Core / Coq Core / Rust.
------------------------------------------------------------------------

module Chem.Conservation where

open import Core.Gate
open import Data.Rational using (ℚ)
open import Data.Product using (_×_; _,_)

open CoreAdmissible

------------------------------------------------------------------------
-- Meso chemistry mass ball (re-export universal Core predicate)
------------------------------------------------------------------------

ChemMassCond : {S : Set} → ThermodynamicSystem S → S → S → Set
ChemMassCond sys = CoreMassCond sys

ChemDissipCond : {S : Set} → ThermodynamicSystem S → S → S → Set
ChemDissipCond sys = CoreDissipCond sys

chem-mass-tolerance : ℚ
chem-mass-tolerance = δ-mass

------------------------------------------------------------------------
-- Extraction lemmas (machine-checked, no postulates)
------------------------------------------------------------------------

mass-from-core-admissible :
  ∀ {S : Set} (sys : ThermodynamicSystem S) (old new : S) →
  CoreAdmissible sys old new → ChemMassCond sys old new
mass-from-core-admissible sys old new adm = mass-conserved adm

dissip-from-core-admissible :
  ∀ {S : Set} (sys : ThermodynamicSystem S) (old new : S) →
  CoreAdmissible sys old new → ChemDissipCond sys old new
dissip-from-core-admissible sys old new adm = dissipation-nonneg adm

chem-admissible-iff-mass-dissip :
  ∀ {S : Set} (sys : ThermodynamicSystem S) (old new : S) →
  CoreAdmissible sys old new →
  ChemMassCond sys old new × ChemDissipCond sys old new
chem-admissible-iff-mass-dissip sys old new adm =
  core-admissible-iff-mass-dissip sys old new adm

chem-admissible-from-mass-dissip :
  ∀ {S : Set} (sys : ThermodynamicSystem S) (old new : S) →
  ChemMassCond sys old new × ChemDissipCond sys old new →
  CoreAdmissible sys old new
chem-admissible-from-mass-dissip sys old new =
  core-admissible-from-mass-dissip sys old new

conservationModuleWitness : {S : Set} → ThermodynamicSystem S → S → S → Set
conservationModuleWitness sys old new = ChemMassCond sys old new
