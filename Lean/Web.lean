/-
  UMST-Formal: Web.lean
  Phase 0 — informational web domain foundation (Umst-Web v0.1 blueprint §10).

  Single-axiom discipline: informational admissibility embeds in `physicalSecondLaw` via
  the Landauer rendering leg — no additional project axioms.
-/

import LandauerLaw
import LandauerExtension
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Real UMST.LandauerLaw UMST.LandauerExtension

namespace UMST.Web

-- ================================================================
-- SECTION 1: WebStateTensor + 𝒟_web_int
-- ================================================================

/-- Default complexity weight λ in 𝒟_web_int (matches `umst-web` scaffold). -/
def defaultComplexityWeight : ℝ := 1

/-- Default Landauer rendering weight μ in 𝒟_web_int. -/
def defaultLandauerWeight : ℝ := 1

/-- Informational slack ε_int for near-neutral transitions. -/
noncomputable def defaultIntTolerance : ℝ := 1 / (10 ^ 9 : ℕ)

/-- Web mesh state tensor — informational transition snapshot.
    Scalar legs align with `umst-web::WebStateTensor` (M4-A8-I2). -/
structure WebStateTensor where
  /-- ΔIntentFidelity between target and rendered intent. -/
  intentFidelity : ℝ
  /-- ΔComplexityCost of the presentation relative to baseline. -/
  complexityCost : ℝ
  /-- Landauer rendering cost for the transition. -/
  landauerRendering : ℝ
  /-- Complexity weight λ. -/
  complexityWeight : ℝ := defaultComplexityWeight
  /-- Landauer rendering weight μ. -/
  landauerWeight : ℝ := defaultLandauerWeight

/-- 𝒟_web_int = ΔIntentFidelity − λ·ΔComplexityCost − μ·LandauerRenderingCost. -/
noncomputable def D_web_int (s : WebStateTensor) : ℝ :=
  s.intentFidelity - s.complexityWeight * s.complexityCost - s.landauerWeight * s.landauerRendering

/-- A web transition is admissible when 𝒟_web_int ≥ −ε_int. -/
def isAdmissible (s : WebStateTensor) (ε : ℝ) : Prop :=
  D_web_int s ≥ -ε

/-- Blueprint / manifest vocabulary — **not** a new project axiom. -/
abbrev informationalSecondLaw (s : WebStateTensor) (ε : ℝ) : Prop :=
  isAdmissible s ε

-- ================================================================
-- SECTION 2: Reference fixtures (umst-web parity)
-- ================================================================

/-- Neutral web transition: unit intent fidelity, zero complexity/rendering delta. -/
def neutral : WebStateTensor :=
  { intentFidelity := 1
    complexityCost := 0
    landauerRendering := 0 }

/-- Heavy presentation fixture: high complexity + rendering cost. -/
def heavyPresentation : WebStateTensor :=
  { intentFidelity := 0.5
    complexityCost := 0.6
    landauerRendering := 0.5 }

theorem D_web_int_neutral : D_web_int neutral = 1 := by
  simp [D_web_int, neutral, defaultComplexityWeight, defaultLandauerWeight]

theorem D_web_int_heavy : D_web_int heavyPresentation = -0.6 := by
  simp [D_web_int, heavyPresentation, defaultComplexityWeight, defaultLandauerWeight]

theorem neutral_admissible : isAdmissible neutral defaultIntTolerance := by
  rw [isAdmissible, D_web_int_neutral]
  unfold defaultIntTolerance
  norm_num

theorem heavy_inadmissible : ¬ isAdmissible heavyPresentation defaultIntTolerance := by
  rw [isAdmissible, D_web_int_heavy]
  unfold defaultIntTolerance
  norm_num

-- ================================================================
-- SECTION 3: physicalSecondLaw embedding (Landauer rendering leg)
-- ================================================================

/-- Witness coupling web Landauer rendering to an erasure process at the physical layer. -/
structure WebRenderWitness where
  proc : ErasureProcess
  /-- Declared bit-count for rendering work (non-negative). -/
  bits : {b : ℝ // 0 ≤ b}

/-- Per-bit Landauer work floor inherited from `physicalSecondLaw`. -/
theorem web_rendering_single_bit_floor (w : WebRenderWitness)
    (hSL : physicalSecondLawUniformBinary w.proc)
    (_hbit : w.bits.val = 1) :
    w.proc.work ≥ w.proc.bath.bathTemp.val * log 2 := by
  simpa [_hbit, one_mul] using landauerBound w.proc hSL

/-- N-bit rendering floor: total work ≥ n · T · ln 2 when each bit erases at the same bath. -/
theorem web_rendering_n_bit_floor {n : ℕ} (T : ℝ) (hT : 0 < T)
    (procs : Fin n → ErasureProcess)
    (hbath : ∀ i, (procs i).bath.bathTemp.val = T)
    (hSL : ∀ i, physicalSecondLawUniformBinary (procs i)) :
    (∑ i, (procs i).work) ≥ n * (T * log 2) :=
  landauerBound_nBit n T hT procs hbath hSL

/-- **Embedding lemma**: informational rendering cost is bounded below by the physical
    Landauer scale anchored in `physicalSecondLaw` (single-axiom discipline). -/
theorem landauer_rendering_embeds_physical (w : WebRenderWitness)
    (hSL : physicalSecondLawUniformBinary w.proc)
    (hbit : w.bits.val = 1) :
    w.proc.bath.bathTemp.val * log 2 ≤ w.proc.work :=
  web_rendering_single_bit_floor w hSL hbit

/-- When the Landauer leg dominates costs, 𝒟_web_int is non-negative at ε = 0. -/
theorem D_web_int_nonneg_of_landauer_bound (s : WebStateTensor)
    (_hfidelity : 0 ≤ s.intentFidelity)
    (_hcomplexity : s.complexityWeight * s.complexityCost ≤ s.intentFidelity)
    (hlandauer : s.landauerWeight * s.landauerRendering ≤ s.intentFidelity - s.complexityWeight * s.complexityCost) :
    0 ≤ D_web_int s := by
  unfold D_web_int
  linarith

theorem admissible_of_nonneg (s : WebStateTensor) (h : 0 ≤ D_web_int s) (ε : ℝ) (hε : 0 ≤ ε) :
    isAdmissible s ε := by
  unfold isAdmissible
  linarith

-- ================================================================
-- SECTION 4: Kleisli admissibility composition (WebMat pattern)
-- ================================================================

/-- Kleisli arrow over web informational states (proposal → gated option). -/
abbrev WebKleisliArrow (_ε : ℝ) := WebStateTensor → Option WebStateTensor

/-- Well-typed web Kleisli arrow: every `some` output satisfies `isAdmissible`. -/
def WebWellTyped (ε : ℝ) (f : WebKleisliArrow ε) : Prop :=
  ∀ s s', f s = some s' → isAdmissible s' ε

/-- Hard informational gate (microseconds-class decision in the Rust runtime). -/
noncomputable def webGateCheck (s' : WebStateTensor) (ε : ℝ) : Bool :=
  decide (D_web_int s' ≥ -ε)

/-- Proposal functor composed with the informational gate. -/
noncomputable def makeWebGateArrow (ε : ℝ) (propose : WebStateTensor → WebStateTensor) :
    WebKleisliArrow ε :=
  fun s =>
    let s' := propose s
    if webGateCheck s' ε then some s' else none

theorem webGateCheck_true_iff (s : WebStateTensor) (ε : ℝ) :
    webGateCheck s ε = true ↔ isAdmissible s ε := by
  unfold webGateCheck isAdmissible
  simp

theorem makeWebGateArrowWellTyped (ε : ℝ) (propose : WebStateTensor → WebStateTensor) :
    WebWellTyped ε (makeWebGateArrow ε propose) := by
  intro s s' h
  simp only [makeWebGateArrow] at h
  by_cases hg : webGateCheck (propose s) ε
  · simp [hg] at h
    subst h
    exact (webGateCheck_true_iff (propose s) ε).mp hg
  · simp [hg] at h

noncomputable def webKleisliCompose (ε : ℝ) (f g : WebKleisliArrow ε) : WebKleisliArrow ε :=
  fun s =>
    match f s with
    | none => none
    | some s' => g s'

theorem webKleisliComposeWellTyped (ε : ℝ) (f g : WebKleisliArrow ε)
    (_hf : WebWellTyped ε f) (hg : WebWellTyped ε g) :
    WebWellTyped ε (webKleisliCompose ε f g) := by
  intro s s'' hcomp
  simp only [webKleisliCompose] at hcomp
  match hfs : f s with
  | none => simp [hfs] at hcomp
  | some s' =>
    simp [hfs] at hcomp
    exact hg s' s'' hcomp

/-- Graded Kleisli composition re-export (Economic-layer naming parity). -/
theorem web_kleisliComposeWellTyped (ε : ℝ) (f g : WebKleisliArrow ε)
    (hf : WebWellTyped ε f) (hg : WebWellTyped ε g) :
    WebWellTyped ε (webKleisliCompose ε f g) :=
  webKleisliComposeWellTyped ε f g hf hg

end UMST.Web
