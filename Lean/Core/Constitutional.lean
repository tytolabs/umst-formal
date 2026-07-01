/-
  UMST.Core.Constitutional — Kleisli category over any `AdmissibleSystem`.
-/

import Core.State

namespace UMST.Core

def KleisliArrow (S : Type) := S → Option S

def WellTyped {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (f : KleisliArrow S) : Prop :=
  ∀ s s', f s = some s' → @AdmissibleSystem.admissibleStep K _ _ S _ _ s s'

def WellTypedN {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (n : ℕ) (f : KleisliArrow S) : Prop :=
  ∀ s s', f s = some s' → @AdmissibleSystem.admissibleNStep K _ _ S _ _ n s s'

theorem wellTyped_iff_wellTypedN1 {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (f : KleisliArrow S) :
    WellTyped f ↔ WellTypedN 1 f := by
  constructor
  · intro h s s' hs
    exact (@AdmissibleSystem.admissible_iff_admissibleN1 K _ _ S _ _ s s').mp (h s s' hs)
  · intro h s s' hs
    exact (@AdmissibleSystem.admissible_iff_admissibleN1 K _ _ S _ _ s s').mpr (h s s' hs)

def kleisliCompose {S : Type} (f g : KleisliArrow S) : KleisliArrow S :=
  fun s =>
    match f s with
    | none => none
    | some s' => g s'

theorem kleisliComposeWellTypedN {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (m n : ℕ) (f g : KleisliArrow S)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (kleisliCompose f g) := by
  intro s s'' hcomp
  simp only [kleisliCompose] at hcomp
  match h : f s with
  | none => simp [h] at hcomp
  | some s' =>
    simp [h] at hcomp
    exact @AdmissibleSystem.admissibleN_compose K _ _ S _ _ m n s s' s'' (hf s s' h) (hg s' s'' hcomp)

theorem kleisliComposeWellTyped {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (f g : KleisliArrow S) (hf : WellTyped f)
    (hg : WellTyped g) :
    WellTypedN 2 (kleisliCompose f g) :=
  kleisliComposeWellTypedN 1 1 f g
    ((wellTyped_iff_wellTypedN1 f).mp hf)
    ((wellTyped_iff_wellTypedN1 g).mp hg)

def kleisliFold {S : Type} : List (KleisliArrow S) → KleisliArrow S
  | [] => fun s => some s
  | [f] => f
  | f :: rest => kleisliCompose f (kleisliFold rest)

def AllWellTyped {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (arrows : List (KleisliArrow S)) : Prop :=
  ∀ f, f ∈ arrows → WellTyped f

theorem kleisliFoldWellTypedN {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (arrows : List (KleisliArrow S))
    (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) := by
  induction arrows with
  | nil =>
    intro s s' h
    simp [kleisliFold] at h
    subst h
    exact @AdmissibleSystem.admissibleN_refl K _ _ S _ _ 0 s
  | cons f rest ih =>
    simp only [List.length_cons]
    match rest with
    | [] =>
      simp [kleisliFold]
      exact (wellTyped_iff_wellTypedN1 f).mp (hall f (List.mem_cons_self f []))
    | g :: rest' =>
      simp only [kleisliFold]
      rw [show List.length (g :: rest') + 1 = 1 + List.length (g :: rest') from Nat.add_comm _ _]
      apply kleisliComposeWellTypedN
      · exact (wellTyped_iff_wellTypedN1 f).mp (hall f (List.mem_cons_self f _))
      · apply ih
        intro h hmem
        exact hall h (List.mem_cons_of_mem f hmem)

theorem kleisliFoldWellTyped {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (arrows : List (KleisliArrow S))
    (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) :=
  kleisliFoldWellTypedN arrows hall

inductive ConstitutionalSeq {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] : List S → Prop where
  | nil : ConstitutionalSeq []
  | one : ∀ s, ConstitutionalSeq [s]
  | cons : ∀ s1 s2 rest,
      @AdmissibleSystem.admissibleStep K _ _ S _ _ s1 s2 →
        ConstitutionalSeq (s2 :: rest) →
          ConstitutionalSeq (s1 :: s2 :: rest)

theorem subjectReduction {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] {s1 s2 : S} {rest : List S} :
    ConstitutionalSeq (s1 :: s2 :: rest) → ConstitutionalSeq (s2 :: rest) := by
  intro h
  cases h with
  | cons _ _ _ _ htail => exact htail

theorem kleisliAdmissibility {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] :
    ∀ (seq : List S),
      ConstitutionalSeq seq →
        ∀ (i : Nat) (s1 s2 : S),
          seq.get? i = some s1 →
            seq.get? (i + 1) = some s2 →
              @AdmissibleSystem.admissibleStep K _ _ S _ _ s1 s2 := by
  intro seq hseq i s1 s2 h1 h2
  induction hseq generalizing i s1 s2 with
  | nil => simp at h1
  | one s => cases i <;> simp_all
  | cons s1' s2' rest hadm _htail ih =>
    cases i with
    | zero =>
      simp [List.get?] at h1 h2
      rcases h1 with ⟨rfl⟩
      rcases h2 with ⟨rfl⟩
      exact hadm
    | succ n =>
      rw [List.get?_cons_succ] at h1
      rw [List.get?_cons_succ] at h2
      exact ih n s1 s2 h1 h2

theorem identityWellTyped {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [ThermodynamicSystem K S] [AdmissibleSystem K S] :
    WellTyped (fun (s : S) => some s) := by
  intro s s' h
  cases h
  rw [@AdmissibleSystem.admissible_iff_admissibleN1 K _ _ S _ _]
  exact @AdmissibleSystem.admissibleN_refl K _ _ S _ _ 1 s

theorem kleisliComposeAssoc {S : Type} (f g h : KleisliArrow S) :
    kleisliCompose (kleisliCompose f g) h = kleisliCompose f (kleisliCompose g h) := by
  funext s
  simp only [kleisliCompose]
  cases f s with
  | none => rfl
  | some s' =>
    cases g s' with
    | none => rfl
    | some s'' => rfl

theorem kleisliLeftUnit {S : Type} (f : KleisliArrow S) :
    kleisliCompose (fun s => some s) f = f := by
  funext s; simp [kleisliCompose]

theorem kleisliRightUnit {S : Type} (f : KleisliArrow S) :
    kleisliCompose f (fun s => some s) = f := by
  funext s
  simp only [kleisliCompose]
  cases f s with
  | none => rfl
  | some s' => rfl

end UMST.Core
