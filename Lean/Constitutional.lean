/-
  UMST-Formal: Constitutional.lean
  Lean 4 — Kleisli Admissibility and Subject Reduction.

  Ports Coq/Constitutional.v to Lean 4.  Provides the full N-step
  Kleisli machinery for constitutional mediation as machine-checked proof.

  Proof status: theorems proved modulo `admissibleTrans` (Kleisli chaining;
  matches Coq `admissible_trans`; not derivable from one-step mass bound alone).

  Correspondence:
    KleisliArrow             │ Coq: KleisliArrow (Definition)
    WellTyped                │ Coq: WellTyped (Definition)
    makeGateArrow            │ Coq: make_gate_arrow
    gateArrowWellTyped       │ Coq: gate_arrow_well_typed
    kleisliCompose           │ Coq: kleisli_compose
    kleisliComposeWellTyped  │ Coq: kleisli_compose_well_typed
    kleisliFold              │ Coq: kleisli_fold (Fixpoint)
    AllWellTyped             │ Coq: AllWellTyped
    kleisliFoldWellTyped     │ Coq: kleisli_fold_well_typed (Theorem)
-/

import Gate

namespace UMST

-- ================================================================
-- SECTION 1: Kleisli Arrow Type
-- ================================================================
-- A Kleisli arrow is a function that either produces the next
-- admissible state (Some s') or rejects the transition (none).
-- The `none` / ⊥-absorbing semantics means a rejected transition
-- halts the pipeline without accepting unphysical states.

/-- A Kleisli arrow in the Admissibility monad: produces the next
    state (some s') if the proposed transition is accepted, or none
    (⊥) if it is rejected. -/
def KleisliArrow := ThermodynamicState → Option ThermodynamicState

/-- A Kleisli arrow is well-typed if every state it produces is
    admissible from the input (single-step, `AdmissibleN 1`). -/
def WellTyped (f : KleisliArrow) : Prop :=
  ∀ (s s' : ThermodynamicState), f s = some s' → Admissible s s'

/-- N-step well-typedness: every produced state satisfies `AdmissibleN n`.
    `WellTypedN 1 f` is equivalent to `WellTyped f`. -/
def WellTypedN (n : ℕ) (f : KleisliArrow) : Prop :=
  ∀ (s s' : ThermodynamicState), f s = some s' → AdmissibleN n s s'

/-- `WellTyped` and `WellTypedN 1` are equivalent. -/
theorem wellTyped_iff_wellTypedN1 (f : KleisliArrow) :
    WellTyped f ↔ WellTypedN 1 f :=
  ⟨fun h s s' hs => (admissible_iff_admissibleN1 s s').mp (h s s' hs),
   fun h s s' hs => (admissible_iff_admissibleN1 s s').mpr (h s s' hs)⟩

-- NOTE: The former `admissibleTrans` axiom has been **removed**.
-- It is REFUTABLE: two consecutive 99 kg/m³ density jumps satisfy the
-- single-step mass bound but the composed jump (198 kg/m³) violates it.
-- Formal counterexample: see GraphProperties.lean (`mass_not_transitive`).
-- Replacement: `admissibleN_compose` in Gate.lean (proved via triangle inequality).

-- ================================================================
-- SECTION 2: Gate-Mediated Arrow
-- ================================================================

/-- A gate-mediated Kleisli arrow: apply `propose` to get the
    candidate next state, then gate-check the transition.  If the
    gate accepts, return some of the new state; otherwise none. -/
def makeGateArrow (propose : ThermodynamicState → ThermodynamicState)
    : KleisliArrow :=
  fun s =>
    let s' := propose s
    if gateCheck s s' then some s' else none

/-- Any gate-mediated arrow is well-typed: the gate enforces
    admissibility before allowing the transition. -/
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

-- ================================================================
-- SECTION 3: Kleisli Composition
-- ================================================================

/-- Kleisli composition: first apply f, then g to the result.
    If f returns none, the composition returns none (⊥-absorbing). -/
def kleisliCompose (f g : KleisliArrow) : KleisliArrow :=
  fun s =>
    match f s with
    | none    => none
    | some s' => g s'

/-- **Graded Kleisli composition** (m-step ∘ n-step = (m+n)-step).
    Proved from `admissibleN_compose` without any axiom. -/
theorem kleisliComposeWellTypedN (m n : ℕ) (f g : KleisliArrow)
    (hf : WellTypedN m f) (hg : WellTypedN n g) :
    WellTypedN (m + n) (kleisliCompose f g) := by
  intro s s'' hcomp
  simp only [kleisliCompose] at hcomp
  match h : f s with
  | none    => simp [h] at hcomp
  | some s' =>
    simp [h] at hcomp
    exact admissibleN_compose (hf s s' h) (hg s' s'' hcomp)

/-- Composing two 1-step well-typed arrows gives a 2-step well-typed arrow.
    Mass may drift up to `2 * δMass` end-to-end (triangle inequality).
    Replaces the former `admissibleTrans`-based version whose conclusion
    was `WellTyped` (= `AdmissibleN 1`) — which was provably false. -/
theorem kleisliComposeWellTyped (f g : KleisliArrow)
    (hf : WellTyped f) (hg : WellTyped g) :
    WellTypedN 2 (kleisliCompose f g) :=
  kleisliComposeWellTypedN 1 1 f g
    ((wellTyped_iff_wellTypedN1 f).mp hf)
    ((wellTyped_iff_wellTypedN1 g).mp hg)

-- ================================================================
-- SECTION 4: N-Step Kleisli Composition
-- ================================================================

/-- Fold a list of Kleisli arrows into a single arrow.
    The empty list is the identity arrow (always returns some s). -/
def kleisliFold : List KleisliArrow → KleisliArrow
  | []       => fun s => some s
  | [f]      => f
  | f :: rest => kleisliCompose f (kleisliFold rest)

/-- All arrows in a list are well-typed. -/
def AllWellTyped (arrows : List KleisliArrow) : Prop :=
  ∀ f, f ∈ arrows → WellTyped f

/-- Theorem (Kleisli Admissibility, N-step, graded):
    Folding N well-typed arrows gives a `WellTypedN N` arrow.
    Mass tolerance accumulates as `N * δMass`; the three order conditions
    (Clausius-Duhem, hydration, strength) hold end-to-end by transitivity.
    Proved entirely without axioms via `admissibleN_compose`. -/
theorem kleisliFoldWellTypedN (arrows : List KleisliArrow)
    (hall : AllWellTyped arrows) :
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
      -- Goal uses `length + 1`; `kleisliComposeWellTypedN` expects `1 + length`.
      rw [show List.length (g :: rest') + 1 = 1 + List.length (g :: rest') from Nat.add_comm _ _]
      apply kleisliComposeWellTypedN
      · exact (wellTyped_iff_wellTypedN1 f).mp (hall f (List.mem_cons_self f _))
      · apply ih
        intro h hmem
        exact hall h (List.mem_cons_of_mem f hmem)

/-- Backward-compatible alias: folding well-typed arrows gives a graded arrow.
    The `WellTypedN N` result subsumes consecutive admissibility. -/
theorem kleisliFoldWellTyped (arrows : List KleisliArrow)
    (hall : AllWellTyped arrows) :
    WellTypedN arrows.length (kleisliFold arrows) :=
  kleisliFoldWellTypedN arrows hall

-- ================================================================
-- SECTION 5: Sequential Composition Safety
-- ================================================================

/-- Corollary: A two-step constitutional sequence is safe.
    Both s0 → s1 and s1 → s2 satisfy the gate. -/
theorem sequentialCompositionSafe (s0 s1 s2 : ThermodynamicState)
    (hseq : ConstitutionalSeq [s0, s1, s2]) :
    Admissible s0 s1 ∧ Admissible s1 s2 :=
  ⟨kleisliAdmissibility [s0, s1, s2] hseq 0 s0 s1 rfl rfl,
   kleisliAdmissibility [s0, s1, s2] hseq 1 s1 s2 rfl rfl⟩

-- ================================================================
-- SECTION 6: Kleisli Identity and Associativity
-- ================================================================

/-- The identity arrow is well-typed (trivially, using admissibleRefl). -/
theorem identityWellTyped : WellTyped (fun s => some s) := by
  intro s s' h
  injection h with hss
  subst hss
  exact admissibleRefl s

/-- Kleisli composition is associative (as functions, modulo funext).
    (f >=> g) >=> h = f >=> (g >=> h). -/
theorem kleisliComposeAssoc (f g h : KleisliArrow) :
    kleisliCompose (kleisliCompose f g) h =
    kleisliCompose f (kleisliCompose g h) := by
  funext s
  simp only [kleisliCompose]
  cases f s with
  | none    => rfl
  | some s' =>
    cases g s' with
    | none     => rfl
    | some s'' => rfl

/-- Left unit: identity >=> f = f. -/
theorem kleisliLeftUnit (f : KleisliArrow) :
    kleisliCompose (fun s => some s) f = f := by
  funext s; simp [kleisliCompose]

/-- Right unit: f >=> identity = f. -/
theorem kleisliRightUnit (f : KleisliArrow) :
    kleisliCompose f (fun s => some s) = f := by
  funext s
  simp only [kleisliCompose]
  cases f s with
  | none    => rfl
  | some s' => rfl

end UMST
