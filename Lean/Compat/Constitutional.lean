/-
  UMST.Compat.Constitutional — Kleisli layer specialized to cement `ThermodynamicState`.
-/
import Compat.Gate

namespace UMST

def KleisliArrow := ThermodynamicState → Option ThermodynamicState

def WellTyped (f : KleisliArrow) : Prop :=
  ∀ (s s' : ThermodynamicState), f s = some s' → Admissible s s'

def WellTypedN (n : ℕ) (f : KleisliArrow) : Prop :=
  ∀ (s s' : ThermodynamicState), f s = some s' → AdmissibleN n s s'

theorem wellTyped_iff_wellTypedN1 (f : KleisliArrow) :
    WellTyped f ↔ WellTypedN 1 f :=
  ⟨fun h s s' hs => (admissible_iff_admissibleN1 s s').mp (h s s' hs),
   fun h s s' hs => (admissible_iff_admissibleN1 s s').mpr (h s s' hs)⟩

def makeGateArrow (propose : ThermodynamicState → ThermodynamicState) : KleisliArrow :=
  fun s =>
    let s' := propose s
    if gateCheck s s' then some s' else none

theorem gateArrowWellTyped (propose : ThermodynamicState → ThermodynamicState) :
    WellTyped (makeGateArrow propose) := by
  intro s s' h
  simp only [makeGateArrow] at h
  match hc : gateCheck s (propose s) with
  | true =>
    simp [makeGateArrow, hc] at h
    subst h
    exact gateCheckSound s (propose s) hc
  | false =>
    simp [makeGateArrow, hc] at h

def kleisliCompose (f g : KleisliArrow) : KleisliArrow :=
  fun s =>
    match f s with
    | none => none
    | some s' => g s'

theorem kleisliComposeWellTypedN (m n : ℕ) (f g : KleisliArrow)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (kleisliCompose f g) := by
  intro s s'' hcomp
  simp only [kleisliCompose] at hcomp
  match h : f s with
  | none => simp [h] at hcomp
  | some s' =>
    simp [h] at hcomp
    exact admissibleN_compose (hf s s' h) (hg s' s'' hcomp)

theorem kleisliComposeWellTyped (f g : KleisliArrow) (hf : WellTyped f) (hg : WellTyped g) :
    WellTypedN 2 (kleisliCompose f g) :=
  kleisliComposeWellTypedN 1 1 f g
    ((wellTyped_iff_wellTypedN1 f).mp hf)
    ((wellTyped_iff_wellTypedN1 g).mp hg)

def kleisliFold : List KleisliArrow → KleisliArrow
  | [] => fun s => some s
  | [f] => f
  | f :: rest => kleisliCompose f (kleisliFold rest)

def AllWellTyped (arrows : List KleisliArrow) : Prop :=
  ∀ f, f ∈ arrows → WellTyped f

theorem kleisliFoldWellTypedN (arrows : List KleisliArrow) (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) := by
  induction arrows with
  | nil =>
    intro s s' h
    simp [kleisliFold] at h
    subst h
    exact admissibleNRefl 0 s
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

theorem kleisliFoldWellTyped (arrows : List KleisliArrow) (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) :=
  kleisliFoldWellTypedN arrows hall

theorem sequentialCompositionSafe (s0 s1 s2 : ThermodynamicState)
    (hseq : ConstitutionalSeq [s0, s1, s2]) :
    Admissible s0 s1 ∧ Admissible s1 s2 :=
  ⟨kleisliAdmissibility [s0, s1, s2] hseq 0 s0 s1 rfl rfl,
   kleisliAdmissibility [s0, s1, s2] hseq 1 s1 s2 rfl rfl⟩

theorem identityWellTyped : WellTyped (fun s => some s) := by
  intro s s' h
  injection h with hss
  subst hss
  exact admissibleRefl s

theorem kleisliComposeAssoc (f g h : KleisliArrow) :
    kleisliCompose (kleisliCompose f g) h = kleisliCompose f (kleisliCompose g h) := by
  funext s
  simp only [kleisliCompose]
  cases f s with
  | none => rfl
  | some s' =>
    cases g s' with
    | none => rfl
    | some s'' => rfl

theorem kleisliLeftUnit (f : KleisliArrow) :
    kleisliCompose (fun s => some s) f = f := by
  funext s; simp [kleisliCompose]

theorem kleisliRightUnit (f : KleisliArrow) :
    kleisliCompose f (fun s => some s) = f := by
  funext s
  simp only [kleisliCompose]
  cases f s with
  | none => rfl
  | some s' => rfl

end UMST
