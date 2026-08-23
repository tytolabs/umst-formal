-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: Chem/Element.lean

  Meso acting chemistry — canonical L0 **element carrier** as an inductive type for
  IUPAC atomic numbers Z = 1 .. 118.  Anchored in `Chem.SecondLaw` +
  `Chem.Conservation` via sibling meso modules.  Adds **zero** Lean `axiom` declarations.

  Fiber: meso/acting → `umst-formal` only.  No quantum theorems.
  PatternNuance keeps a local `structure Element` scaffold — this module is canonical.
-/

import Chem.Conservation
import Chem.SecondLaw

open Real Finset UMST.LandauerLaw UMST.Chem.SecondLaw UMST.Chem.Conservation

namespace UMST.Chem.Element

-- ================================================================
-- SECTION 1: Inductive element carrier (IUPAC Z = 1 .. 118)
-- ================================================================

/-- L0 element carrier — one constructor per IUPAC element (Z = 1 .. 118). -/
inductive Element where
  | H
  | He
  | Li
  | Be
  | B
  | C
  | N
  | O
  | F
  | Ne
  | Na
  | Mg
  | Al
  | Si
  | P
  | S
  | Cl
  | Ar
  | K
  | Ca
  | Sc
  | Ti
  | V
  | Cr
  | Mn
  | Fe
  | Co
  | Ni
  | Cu
  | Zn
  | Ga
  | Ge
  | As
  | Se
  | Br
  | Kr
  | Rb
  | Sr
  | Y
  | Zr
  | Nb
  | Mo
  | Tc
  | Ru
  | Rh
  | Pd
  | Ag
  | Cd
  | In
  | Sn
  | Sb
  | Te
  | I
  | Xe
  | Cs
  | Ba
  | La
  | Ce
  | Pr
  | Nd
  | Pm
  | Sm
  | Eu
  | Gd
  | Tb
  | Dy
  | Ho
  | Er
  | Tm
  | Yb
  | Lu
  | Hf
  | Ta
  | W
  | Re
  | Os
  | Ir
  | Pt
  | Au
  | Hg
  | Tl
  | Pb
  | Bi
  | Po
  | At
  | Rn
  | Fr
  | Ra
  | Ac
  | Th
  | Pa
  | U
  | Np
  | Pu
  | Am
  | Cm
  | Bk
  | Cf
  | Es
  | Fm
  | Md
  | No
  | Lr
  | Rf
  | Db
  | Sg
  | Bh
  | Hs
  | Mt
  | Ds
  | Rg
  | Cn
  | Nh
  | Fl
  | Mc
  | Lv
  | Ts
  | Og
  deriving DecidableEq, Repr

/-- Atomic number projection (IUPAC Z). -/
def elementZ : Element → ℕ
  | .H => 1
  | .He => 2
  | .Li => 3
  | .Be => 4
  | .B => 5
  | .C => 6
  | .N => 7
  | .O => 8
  | .F => 9
  | .Ne => 10
  | .Na => 11
  | .Mg => 12
  | .Al => 13
  | .Si => 14
  | .P => 15
  | .S => 16
  | .Cl => 17
  | .Ar => 18
  | .K => 19
  | .Ca => 20
  | .Sc => 21
  | .Ti => 22
  | .V => 23
  | .Cr => 24
  | .Mn => 25
  | .Fe => 26
  | .Co => 27
  | .Ni => 28
  | .Cu => 29
  | .Zn => 30
  | .Ga => 31
  | .Ge => 32
  | .As => 33
  | .Se => 34
  | .Br => 35
  | .Kr => 36
  | .Rb => 37
  | .Sr => 38
  | .Y => 39
  | .Zr => 40
  | .Nb => 41
  | .Mo => 42
  | .Tc => 43
  | .Ru => 44
  | .Rh => 45
  | .Pd => 46
  | .Ag => 47
  | .Cd => 48
  | .In => 49
  | .Sn => 50
  | .Sb => 51
  | .Te => 52
  | .I => 53
  | .Xe => 54
  | .Cs => 55
  | .Ba => 56
  | .La => 57
  | .Ce => 58
  | .Pr => 59
  | .Nd => 60
  | .Pm => 61
  | .Sm => 62
  | .Eu => 63
  | .Gd => 64
  | .Tb => 65
  | .Dy => 66
  | .Ho => 67
  | .Er => 68
  | .Tm => 69
  | .Yb => 70
  | .Lu => 71
  | .Hf => 72
  | .Ta => 73
  | .W => 74
  | .Re => 75
  | .Os => 76
  | .Ir => 77
  | .Pt => 78
  | .Au => 79
  | .Hg => 80
  | .Tl => 81
  | .Pb => 82
  | .Bi => 83
  | .Po => 84
  | .At => 85
  | .Rn => 86
  | .Fr => 87
  | .Ra => 88
  | .Ac => 89
  | .Th => 90
  | .Pa => 91
  | .U => 92
  | .Np => 93
  | .Pu => 94
  | .Am => 95
  | .Cm => 96
  | .Bk => 97
  | .Cf => 98
  | .Es => 99
  | .Fm => 100
  | .Md => 101
  | .No => 102
  | .Lr => 103
  | .Rf => 104
  | .Db => 105
  | .Sg => 106
  | .Bh => 107
  | .Hs => 108
  | .Mt => 109
  | .Ds => 110
  | .Rg => 111
  | .Cn => 112
  | .Nh => 113
  | .Fl => 114
  | .Mc => 115
  | .Lv => 116
  | .Ts => 117
  | .Og => 118

/-- IUPAC element cardinality pin. -/
def elementCardinality : ℕ := 118

theorem elementCardinality_eq : elementCardinality = 118 := rfl

/-- Atomic numbers lie in the IUPAC closed range. -/
theorem elementZ_in_range (e : Element) : 1 ≤ elementZ e ∧ elementZ e ≤ 118 := by
  cases e <;> decide

/-- `elementZ` is injective on the inductive carrier. -/
theorem elementZ_injective : Function.Injective elementZ := by
  intro a b h
  cases a <;> cases b <;> first | rfl | simp [elementZ] at h

/-- Canonical hydrogen (Z = 1). -/
def hydrogenElement : Element := .H

/-- Canonical helium (Z = 2). -/
def heliumElement : Element := .He

/-- Canonical carbon (Z = 6). -/
def carbonElement : Element := .C

/-- Canonical oganesson (Z = 118). -/
def oganessonElement : Element := .Og

theorem hydrogen_elementZ : elementZ hydrogenElement = 1 := rfl
theorem helium_elementZ : elementZ heliumElement = 2 := rfl
theorem carbon_elementZ : elementZ carbonElement = 6 := rfl
theorem oganesson_elementZ : elementZ oganessonElement = 118 := rfl

-- ================================================================
-- SECTION 2: Fin 118 bijection (L0 indexing without Z-row files)
-- ================================================================

/-- Recover element from zero-based Fin index (0 ↔ H, 117 ↔ Og). -/
def elementOfFin (i : Fin 118) : Element :=
  match i.val with
  | 0 => .H
  | 1 => .He
  | 2 => .Li
  | 3 => .Be
  | 4 => .B
  | 5 => .C
  | 6 => .N
  | 7 => .O
  | 8 => .F
  | 9 => .Ne
  | 10 => .Na
  | 11 => .Mg
  | 12 => .Al
  | 13 => .Si
  | 14 => .P
  | 15 => .S
  | 16 => .Cl
  | 17 => .Ar
  | 18 => .K
  | 19 => .Ca
  | 20 => .Sc
  | 21 => .Ti
  | 22 => .V
  | 23 => .Cr
  | 24 => .Mn
  | 25 => .Fe
  | 26 => .Co
  | 27 => .Ni
  | 28 => .Cu
  | 29 => .Zn
  | 30 => .Ga
  | 31 => .Ge
  | 32 => .As
  | 33 => .Se
  | 34 => .Br
  | 35 => .Kr
  | 36 => .Rb
  | 37 => .Sr
  | 38 => .Y
  | 39 => .Zr
  | 40 => .Nb
  | 41 => .Mo
  | 42 => .Tc
  | 43 => .Ru
  | 44 => .Rh
  | 45 => .Pd
  | 46 => .Ag
  | 47 => .Cd
  | 48 => .In
  | 49 => .Sn
  | 50 => .Sb
  | 51 => .Te
  | 52 => .I
  | 53 => .Xe
  | 54 => .Cs
  | 55 => .Ba
  | 56 => .La
  | 57 => .Ce
  | 58 => .Pr
  | 59 => .Nd
  | 60 => .Pm
  | 61 => .Sm
  | 62 => .Eu
  | 63 => .Gd
  | 64 => .Tb
  | 65 => .Dy
  | 66 => .Ho
  | 67 => .Er
  | 68 => .Tm
  | 69 => .Yb
  | 70 => .Lu
  | 71 => .Hf
  | 72 => .Ta
  | 73 => .W
  | 74 => .Re
  | 75 => .Os
  | 76 => .Ir
  | 77 => .Pt
  | 78 => .Au
  | 79 => .Hg
  | 80 => .Tl
  | 81 => .Pb
  | 82 => .Bi
  | 83 => .Po
  | 84 => .At
  | 85 => .Rn
  | 86 => .Fr
  | 87 => .Ra
  | 88 => .Ac
  | 89 => .Th
  | 90 => .Pa
  | 91 => .U
  | 92 => .Np
  | 93 => .Pu
  | 94 => .Am
  | 95 => .Cm
  | 96 => .Bk
  | 97 => .Cf
  | 98 => .Es
  | 99 => .Fm
  | 100 => .Md
  | 101 => .No
  | 102 => .Lr
  | 103 => .Rf
  | 104 => .Db
  | 105 => .Sg
  | 106 => .Bh
  | 107 => .Hs
  | 108 => .Mt
  | 109 => .Ds
  | 110 => .Rg
  | 111 => .Cn
  | 112 => .Nh
  | 113 => .Fl
  | 114 => .Mc
  | 115 => .Lv
  | 116 => .Ts
  | 117 => .Og
  | _ => .H

/-- Zero-based Fin index from element (inverse of `elementOfFin`). -/
def finOfElement (e : Element) : Fin 118 :=
  match e with
  | .H => ⟨0, by decide⟩
  | .He => ⟨1, by decide⟩
  | .Li => ⟨2, by decide⟩
  | .Be => ⟨3, by decide⟩
  | .B => ⟨4, by decide⟩
  | .C => ⟨5, by decide⟩
  | .N => ⟨6, by decide⟩
  | .O => ⟨7, by decide⟩
  | .F => ⟨8, by decide⟩
  | .Ne => ⟨9, by decide⟩
  | .Na => ⟨10, by decide⟩
  | .Mg => ⟨11, by decide⟩
  | .Al => ⟨12, by decide⟩
  | .Si => ⟨13, by decide⟩
  | .P => ⟨14, by decide⟩
  | .S => ⟨15, by decide⟩
  | .Cl => ⟨16, by decide⟩
  | .Ar => ⟨17, by decide⟩
  | .K => ⟨18, by decide⟩
  | .Ca => ⟨19, by decide⟩
  | .Sc => ⟨20, by decide⟩
  | .Ti => ⟨21, by decide⟩
  | .V => ⟨22, by decide⟩
  | .Cr => ⟨23, by decide⟩
  | .Mn => ⟨24, by decide⟩
  | .Fe => ⟨25, by decide⟩
  | .Co => ⟨26, by decide⟩
  | .Ni => ⟨27, by decide⟩
  | .Cu => ⟨28, by decide⟩
  | .Zn => ⟨29, by decide⟩
  | .Ga => ⟨30, by decide⟩
  | .Ge => ⟨31, by decide⟩
  | .As => ⟨32, by decide⟩
  | .Se => ⟨33, by decide⟩
  | .Br => ⟨34, by decide⟩
  | .Kr => ⟨35, by decide⟩
  | .Rb => ⟨36, by decide⟩
  | .Sr => ⟨37, by decide⟩
  | .Y => ⟨38, by decide⟩
  | .Zr => ⟨39, by decide⟩
  | .Nb => ⟨40, by decide⟩
  | .Mo => ⟨41, by decide⟩
  | .Tc => ⟨42, by decide⟩
  | .Ru => ⟨43, by decide⟩
  | .Rh => ⟨44, by decide⟩
  | .Pd => ⟨45, by decide⟩
  | .Ag => ⟨46, by decide⟩
  | .Cd => ⟨47, by decide⟩
  | .In => ⟨48, by decide⟩
  | .Sn => ⟨49, by decide⟩
  | .Sb => ⟨50, by decide⟩
  | .Te => ⟨51, by decide⟩
  | .I => ⟨52, by decide⟩
  | .Xe => ⟨53, by decide⟩
  | .Cs => ⟨54, by decide⟩
  | .Ba => ⟨55, by decide⟩
  | .La => ⟨56, by decide⟩
  | .Ce => ⟨57, by decide⟩
  | .Pr => ⟨58, by decide⟩
  | .Nd => ⟨59, by decide⟩
  | .Pm => ⟨60, by decide⟩
  | .Sm => ⟨61, by decide⟩
  | .Eu => ⟨62, by decide⟩
  | .Gd => ⟨63, by decide⟩
  | .Tb => ⟨64, by decide⟩
  | .Dy => ⟨65, by decide⟩
  | .Ho => ⟨66, by decide⟩
  | .Er => ⟨67, by decide⟩
  | .Tm => ⟨68, by decide⟩
  | .Yb => ⟨69, by decide⟩
  | .Lu => ⟨70, by decide⟩
  | .Hf => ⟨71, by decide⟩
  | .Ta => ⟨72, by decide⟩
  | .W => ⟨73, by decide⟩
  | .Re => ⟨74, by decide⟩
  | .Os => ⟨75, by decide⟩
  | .Ir => ⟨76, by decide⟩
  | .Pt => ⟨77, by decide⟩
  | .Au => ⟨78, by decide⟩
  | .Hg => ⟨79, by decide⟩
  | .Tl => ⟨80, by decide⟩
  | .Pb => ⟨81, by decide⟩
  | .Bi => ⟨82, by decide⟩
  | .Po => ⟨83, by decide⟩
  | .At => ⟨84, by decide⟩
  | .Rn => ⟨85, by decide⟩
  | .Fr => ⟨86, by decide⟩
  | .Ra => ⟨87, by decide⟩
  | .Ac => ⟨88, by decide⟩
  | .Th => ⟨89, by decide⟩
  | .Pa => ⟨90, by decide⟩
  | .U => ⟨91, by decide⟩
  | .Np => ⟨92, by decide⟩
  | .Pu => ⟨93, by decide⟩
  | .Am => ⟨94, by decide⟩
  | .Cm => ⟨95, by decide⟩
  | .Bk => ⟨96, by decide⟩
  | .Cf => ⟨97, by decide⟩
  | .Es => ⟨98, by decide⟩
  | .Fm => ⟨99, by decide⟩
  | .Md => ⟨100, by decide⟩
  | .No => ⟨101, by decide⟩
  | .Lr => ⟨102, by decide⟩
  | .Rf => ⟨103, by decide⟩
  | .Db => ⟨104, by decide⟩
  | .Sg => ⟨105, by decide⟩
  | .Bh => ⟨106, by decide⟩
  | .Hs => ⟨107, by decide⟩
  | .Mt => ⟨108, by decide⟩
  | .Ds => ⟨109, by decide⟩
  | .Rg => ⟨110, by decide⟩
  | .Cn => ⟨111, by decide⟩
  | .Nh => ⟨112, by decide⟩
  | .Fl => ⟨113, by decide⟩
  | .Mc => ⟨114, by decide⟩
  | .Lv => ⟨115, by decide⟩
  | .Ts => ⟨116, by decide⟩
  | .Og => ⟨117, by decide⟩

theorem finOfElement_elementOfFin (i : Fin 118) : finOfElement (elementOfFin i) = i := by
  fin_cases i <;> native_decide

theorem elementOfFin_finOfElement (e : Element) : elementOfFin (finOfElement e) = e := by
  cases e <;> native_decide

theorem elementZ_finOfElement (e : Element) :
    elementZ e = finOfElement e |>.val + 1 := by
  cases e <;> native_decide

-- ================================================================
-- SECTION 3: Sibling spine witnesses (second law + conservation)
-- ================================================================

/-- Elements participate in meso assemblage bookkeeping (design scaffold). -/
structure ElementAssemblageSlot (n : ℕ) where
  element : Element
  stoichiometry : Fin n → ℤ

/-- Conservation-aware element slot: thermochemical transition + composition delta. -/
structure ConservedElementSlot (n : ℕ) where
  slot : ElementAssemblageSlot n
  transition : ConservedChemTransition n

/-- Second-law admissibility for a conserved element slot. -/
def elementSlotAdmissible {n : ℕ} (s : ConservedElementSlot n) : Prop :=
  admissibleConservedChemTransition s.transition

/-- Catalog witness: canonical element carrier module is present. -/
theorem element_module_witness : True := trivial

end UMST.Chem.Element
