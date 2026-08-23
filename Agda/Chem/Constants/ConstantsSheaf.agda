-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Chem.Constants.ConstantsSheaf — meso/acting constants sheaf.
--
-- CHEM-L0-FORMAL-01 / CHEM-NS-W0-AXIOM (umst-formal acting fiber only).
-- T, P, μ as **Interact-graph sheaf sections** on admissible edges, with
-- Gibbs–Duhem interdependence constraining coupled section variations.
--
-- Mirrors `Lean/Chem/Constants/ConstantsSheaf.lean`,
-- `Coq/Chem/Constants/ConstantsSheaf.v`, and
-- `Haskell/UMST/Chem/Constants/ConstantsSheaf.hs` on `umst-formal/meso_acting`.
-- Anchored in `Chem.SecondLaw` via named `physicalSecondLaw` import only;
-- ZERO new postulates beyond the project second-law axiom.
--
-- physics_green: false — thermo witnesses remain Unwired until FORMAL BAR.
------------------------------------------------------------------------

module Chem.Constants.ConstantsSheaf where

open import Chem.Conservation
open import Chem.KleisliInteract using (admissible-step; admissible-refl)
open import Chem.SecondLaw
open import Concrete.Gate
open Concrete.Gate using
  ( ThermodynamicState
  ; Admissible
  ; gate
  ; concrete-thermodynamic-system
  )
open ThermodynamicState
open Admissible
open import Core.Gate using (CoreAdmissible)
open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import InfoTheory using (sumList; sumFlat; productJoint; jointMassProduct)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Base as ℚBase
open ℚBase using (_÷_; ≢-nonZero)
open import Data.Rational.Properties as ℚ-Props using (_<?_; _≤?_; *-zeroˡ; *-zeroʳ; +-identityʳ; *-identityʳ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no; Dec)

------------------------------------------------------------------------
-- SECTION 1: Interact-graph carrier (design scaffold — four slots)
------------------------------------------------------------------------

data InteractGraphVertex : Set where
  vtx-H : InteractGraphVertex
  vtx-O : InteractGraphVertex
  vtx-Ca : InteractGraphVertex
  vtx-Si : InteractGraphVertex

TemperatureGraphField : Set
TemperatureGraphField = InteractGraphVertex → ℚ

PressureGraphField : Set
PressureGraphField = InteractGraphVertex → ℚ

ChemicalPotentialGraphField : Set
ChemicalPotentialGraphField = InteractGraphVertex → ℚ

record MesoConstantsSheaf : Set where
  field
    sheaf-temperature : TemperatureGraphField
    sheaf-pressure : PressureGraphField
    sheaf-chemical-potential : ChemicalPotentialGraphField

open MesoConstantsSheaf

temperatureFieldPositive : TemperatureGraphField → Set
temperatureFieldPositive T = ∀ v → 0ℚ ℚ.< T v

pressureFieldPositive : PressureGraphField → Set
pressureFieldPositive P = ∀ v → 0ℚ ℚ.< P v

constantsSheafSectionsInterdependent : MesoConstantsSheaf → Set
constantsSheafSectionsInterdependent S =
  ∀ v → (0ℚ ℚ.< sheaf-temperature S v) × (0ℚ ℚ.< sheaf-pressure S v)

ambientGraphVertex : InteractGraphVertex
ambientGraphVertex = vtx-O

standardPressureGraphVertex : InteractGraphVertex
standardPressureGraphVertex = vtx-Ca

referencePotentialGraphVertex : InteractGraphVertex
referencePotentialGraphVertex = vtx-Si

ambientTemperatureSection : MesoConstantsSheaf → ℚ
ambientTemperatureSection S = sheaf-temperature S ambientGraphVertex

standardPressureSection : MesoConstantsSheaf → ℚ
standardPressureSection S = sheaf-pressure S standardPressureGraphVertex

referenceChemicalPotentialSection : MesoConstantsSheaf → ℚ
referenceChemicalPotentialSection S =
  sheaf-chemical-potential S referencePotentialGraphVertex

InteractGraphEdge : Set
InteractGraphEdge = ThermodynamicState × ThermodynamicState

------------------------------------------------------------------------
-- SECTION 2: Conjugate witnesses (finite difference on meso carrier)
------------------------------------------------------------------------

divℚ? : ℚ → ℚ → Maybe ℚ
divℚ? n d with d ℚ.≟ 0ℚ
... | yes _ = nothing
... | no ¬d0 = just q
  where
  instance nz : ℚBase.NonZero d
  nz = ≢-nonZero ¬d0
  q = n ÷ d

entropyWitness : ThermodynamicState → ℚ
entropyWitness s = hydration s

internalEnergyWitness : ThermodynamicState → ℚ
internalEnergyWitness s = density s * (- free-energy s)

specificVolumeWitness : ThermodynamicState → ℚ
specificVolumeWitness s with density s ℚ.≟ 0ℚ
... | yes _ = 0ℚ
... | no ¬ρ0 = q
  where
  instance nz : ℚBase.NonZero (density s)
  nz = ≢-nonZero ¬ρ0
  q = 1ℚ ÷ density s

gibbsWitness : ThermodynamicState → ℚ
gibbsWitness s = density s * free-energy s

compositionWitness : ThermodynamicState → ℚ
compositionWitness s = hydration s

inverseTemperatureBeta : ThermodynamicState → ThermodynamicState → Maybe ℚ
inverseTemperatureBeta old new =
  let dU = internalEnergyWitness new - internalEnergyWitness old
      dS = entropyWitness new - entropyWitness old
  in go dU dS
  where
  go : ℚ → ℚ → Maybe ℚ
  go dU dS with dU ℚ.≟ 0ℚ
  ... | yes _ = nothing
  ... | no _ with 0ℚ <? dU
  ... | no _ = nothing
  ... | yes _ with 0ℚ ≤? dS
  ... | no _ = nothing
  ... | yes _ = divℚ? dS dU

positiveRecip : ℚ → Maybe ℚ
positiveRecip β with 0ℚ <? β
... | yes _ = divℚ? 1ℚ β
... | no _ = nothing

temperatureSheafSection : ThermodynamicState → ThermodynamicState → Maybe ℚ
temperatureSheafSection old new with inverseTemperatureBeta old new
... | nothing = nothing
... | just β = positiveRecip β

pressureSheafSection : ThermodynamicState → ThermodynamicState → Maybe ℚ
pressureSheafSection old new with
  (specificVolumeWitness new - specificVolumeWitness old) ℚ.≟ 0ℚ
... | yes _ = nothing
... | no dV≢0 with
  divℚ? (internalEnergyWitness new - internalEnergyWitness old)
        (specificVolumeWitness new - specificVolumeWitness old)
... | nothing = nothing
... | just q = just (- q)

chemicalPotentialSheafSection : ThermodynamicState → ThermodynamicState → Maybe ℚ
chemicalPotentialSheafSection old new with
  (compositionWitness new - compositionWitness old) ℚ.≟ 0ℚ
... | yes _ = nothing
... | no dn≢0 =
  divℚ? (gibbsWitness new - gibbsWitness old)
        (compositionWitness new - compositionWitness old)

temperatureSectionOnEdge : ThermodynamicState → ThermodynamicState → Maybe ℚ
temperatureSectionOnEdge = temperatureSheafSection

combineSheafSections :
  Maybe ℚ → Maybe ℚ → Maybe ℚ → Maybe (ℚ × ℚ × ℚ)
combineSheafSections nothing _ _ = nothing
combineSheafSections (just t) nothing _ = nothing
combineSheafSections (just t) (just p) nothing = nothing
combineSheafSections (just t) (just p) (just mu) = just (t , p , mu)

constantsSheafOnEdge : ThermodynamicState → ThermodynamicState → Maybe (ℚ × ℚ × ℚ)
constantsSheafOnEdge old new with gate old new
... | no _ = nothing
... | yes prf = combineSheafSections
    (temperatureSheafSection old new)
    (pressureSheafSection old new)
    (chemicalPotentialSheafSection old new)

wellTypedOnEdge : Maybe (ℚ × ℚ × ℚ) → Set
wellTypedOnEdge nothing = ⊤
wellTypedOnEdge (just (t , _ , _)) = 0ℚ ℚ.< t

constantsSheafWellTyped : ThermodynamicState → ThermodynamicState → Set
constantsSheafWellTyped old new with gate old new
... | no _ = ⊤
... | yes prf = wellTypedOnEdge (constantsSheafOnEdge old new)

gibbsDuhemBalance :
  ℚ → ℚ → ℚ → ℚ → ℚ → Set
gibbsDuhemBalance entropy volume deltaTemperature deltaPressure deltaMu =
  deltaMu ≡ (- entropy) * deltaTemperature + volume * deltaPressure

gibbsDuhemInterdependenceEq : ThermodynamicState → ThermodynamicState → Set
gibbsDuhemInterdependenceEq old new with constantsSheafOnEdge old new
... | nothing = ⊤
... | just (t , p , mu) =
  let dG = gibbsWitness new - gibbsWitness old
      dV = specificVolumeWitness new - specificVolumeWitness old
      dN = compositionWitness new - compositionWitness old
      dS = entropyWitness new - entropyWitness old
  in dG ≡ p * dV + mu * dN - t * dS

------------------------------------------------------------------------
-- SECTION 3: Gibbs–Duhem composition interdependence (Coq dot_list mirror)
------------------------------------------------------------------------

dotList : List ℚ → List ℚ → ℚ
dotList [] _ = 0ℚ
dotList _ [] = 0ℚ
dotList (x ∷ xs) (y ∷ ys) = x * y + dotList xs ys

gibbsDuhemInterdependence : List ℚ → List ℚ → Set
gibbsDuhemInterdependence fractions variations =
  dotList fractions variations ≡ 0ℚ

dotList-zero-map : ∀ (xs : List ℚ) →
  dotList xs (map (λ _ → 0ℚ) xs) ≡ 0ℚ
dotList-zero-map [] = refl
dotList-zero-map (x ∷ xs) =
  trans (cong (x * 0ℚ +_) (dotList-zero-map xs))
        (trans (+-identityʳ (x * 0ℚ)) (*-zeroʳ x))

gibbsDuhemInterdependence-zero :
  ∀ (fractions : List ℚ) →
  gibbsDuhemInterdependence fractions (map (λ _ → 0ℚ) fractions)
gibbsDuhemInterdependence-zero fractions = dotList-zero-map fractions

------------------------------------------------------------------------
-- SECTION 4: Vertex-field Landauer bridge (Coq mirror — zero new axioms)
------------------------------------------------------------------------

chemLandauerFloor : ℚ → ℚ
chemLandauerFloor T = T

chemMeasurementFloor : ℚ → ℚ → ℚ
chemMeasurementFloor T miBits = miBits * chemLandauerFloor T

landauerFloorAtSheaf : MesoConstantsSheaf → InteractGraphVertex → ℚ
landauerFloorAtSheaf S v = chemLandauerFloor (sheaf-temperature S v)

measurementFloorAtSheaf : MesoConstantsSheaf → InteractGraphVertex → ℚ → ℚ
measurementFloorAtSheaf S v miBits =
  chemMeasurementFloor (sheaf-temperature S v) miBits

landauerFloorAtSheaf-pos :
  ∀ (S : MesoConstantsSheaf) (v : InteractGraphVertex) →
  0ℚ ℚ.< sheaf-temperature S v →
  0ℚ ℚ.< landauerFloorAtSheaf S v
landauerFloorAtSheaf-pos S v hT = hT

measurementFloorAtSheaf-zero :
  ∀ (S : MesoConstantsSheaf) (v : InteractGraphVertex) →
  measurementFloorAtSheaf S v 0ℚ ≡ 0ℚ
measurementFloorAtSheaf-zero S v = *-zeroˡ (chemLandauerFloor (sheaf-temperature S v))

measurementFloorAtSheaf-scale :
  ∀ (S : MesoConstantsSheaf) (v : InteractGraphVertex) (k : ℚ) →
  measurementFloorAtSheaf S v k ≡ k * landauerFloorAtSheaf S v
measurementFloorAtSheaf-scale S v k = refl

erasureFromDissipStep :
  HeatBath → ThermodynamicState → ThermodynamicState → ErasureProcess
erasureFromDissipStep bath old new = record
  { bath = bath
  ; dissipatedEntropy = free-energy old - free-energy new
  }

landauerOnAdmissibleStep :
  ∀ (bath : HeatBath) (old new : ThermodynamicState) (ΔS : ℚ) →
  Admissible old new →
  PhysicalSecondLaw (erasureFromDissipStep bath old new) ΔS →
  ΔS ≤ free-energy old - free-energy new
landauerOnAdmissibleStep bath old new ΔS adm h =
  landauerBound (erasureFromDissipStep bath old new) ΔS h

------------------------------------------------------------------------
-- SECTION 5: Conservation bridge (mass ball — zero new postulates)
------------------------------------------------------------------------

concreteCoreAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new →
  CoreAdmissible concrete-thermodynamic-system old new
concreteCoreAdmissible old new adm = record
  { mass-conserved = mass-conserved adm
  ; dissipation-nonneg = dissipation-nonneg adm
  }

constantsSheafMassFromAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new →
  ChemMassCond concrete-thermodynamic-system old new
constantsSheafMassFromAdmissible old new adm =
  mass-from-core-admissible
    concrete-thermodynamic-system old new
    (concreteCoreAdmissible old new adm)

constantsSheafDissipFromAdmissible :
  ∀ (old new : ThermodynamicState) → Admissible old new →
  ChemDissipCond concrete-thermodynamic-system old new
constantsSheafDissipFromAdmissible old new adm =
  dissip-from-core-admissible
    concrete-thermodynamic-system old new
    (concreteCoreAdmissible old new adm)

speciesComposition : List ℚ → Set
speciesComposition masses = sumList masses ≡ 1ℚ

chemJointMassConserved :
  ∀ (p q : List ℚ) →
  speciesComposition p →
  speciesComposition q →
  sumFlat (productJoint p q) ≡ 1ℚ
chemJointMassConserved p q Hp Hq =
  trans (jointMassProduct p q)
        (trans (cong (sumList p *_) Hq)
               (trans (*-identityʳ (sumList p)) Hp))

chemJointMassProduct :
  ∀ (p q : List ℚ) →
  sumFlat (productJoint p q) ≡ sumList p * sumList q
chemJointMassProduct p q = jointMassProduct p q

gibbsDuhemConservationNormalized :
  ∀ (p q : List ℚ) →
  speciesComposition p →
  speciesComposition q →
  sumFlat (productJoint p q) ≡ 1ℚ ×
  gibbsDuhemInterdependence p (map (λ _ → 0ℚ) p)
gibbsDuhemConservationNormalized p q Hp Hq =
  chemJointMassConserved p q Hp Hq , gibbsDuhemInterdependence-zero p

gibbsDuhemInterdependenceEq-ungated :
  ∀ (old new : ThermodynamicState) →
  constantsSheafOnEdge old new ≡ nothing →
  gibbsDuhemInterdependenceEq old new
gibbsDuhemInterdependenceEq-ungated old new h rewrite h = tt

------------------------------------------------------------------------
-- SECTION 6: Second-law witness on admissible edges (zero new postulates)
------------------------------------------------------------------------

secondLawWitnessOnStep :
  ∀ (bath : HeatBath) (old new : ThermodynamicState) (ΔS : ℚ) →
  PhysicalSecondLaw (erasureFromDissipStep bath old new) ΔS
secondLawWitnessOnStep bath old new ΔS =
  physicalSecondLaw (erasureFromDissipStep bath old new) ΔS

constantsSheafRespectsSecondLaw :
  ∀ (S : MesoConstantsSheaf) (bath : HeatBath)
    (old new : ThermodynamicState) (ΔS : ℚ) →
  Admissible old new →
  PhysicalSecondLaw (erasureFromDissipStep bath old new) ΔS →
  ΔS ≤ free-energy old - free-energy new
constantsSheafRespectsSecondLaw S bath old new ΔS adm h =
  landauerOnAdmissibleStep bath old new ΔS adm h

------------------------------------------------------------------------
-- SECTION 7: Honesty fence (physics_green false — not measured pins)
------------------------------------------------------------------------

chem-constants-sheaf-physics-green : Bool
chem-constants-sheaf-physics-green = false

chem-constants-sheaf-physics-green-false :
  chem-constants-sheaf-physics-green ≡ false
chem-constants-sheaf-physics-green-false = refl

constants-sheaf-production-wired : Bool
constants-sheaf-production-wired = false

constants-sheaf-production-wired-false :
  constants-sheaf-production-wired ≡ false
constants-sheaf-production-wired-false = refl

constantsSheafModuleWitness : ⊤
constantsSheafModuleWitness = tt
