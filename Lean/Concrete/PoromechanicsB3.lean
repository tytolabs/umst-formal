-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: PoromechanicsB3.lean
  Lean 4 — B3 poromechanics capillary porosity scaffold (ℚ slice).

  Mirrors `umst-cartridge-poromechanics/src/porosity.rs` · `flow.rs` · `dissipation.rs`:
    • `PowersCapillaryCoeffs` injected at consumer compose boundary
    • `try_capillary_porosity` / `capillary_porosity` clamped closure
    • G0 pin `non_evap_water_coeff = 0.36` · `paste_denominator_offset = 0.32`
    • `ChlorideDiffusivityCoeffs` + tortuosity / diffusivity / `FlowWitness`
    • isotropic tensor bridge `D_ij = D_scalar · δ_ij` (scalar `flow.rs` → tensor transport path)
    • `PoromechanicsDissipationCoeffs` · `𝒟_transport` / `𝒟_reaction` slice-1 ledger

  Proof status (B3-S1–S7, B3-D1–D4): clamped porosity in `[0, 1]`; antitone in `α` on admissible box;
    G0 pin agrees with `JenningsGelSpace.φ_cap`; flow witness clamp + tensor bridge on `ℝ` cast;
    dissipation slice-1 nonnegativity, passive pin, summand identity, quadratic homogeneity on ℚ.
    Zero sorry. **Not** cert `Proved` — CC-P-B3-1 remains operator-gated (P2–P7).

  Rust SSOT: `porosity.rs` · `flow.rs` · `dissipation.rs` · `energy.rs` · `saturation.rs` · consumer `compose_b3_prep.rs`
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import JenningsGelSpace

namespace UMST

open Rat

-- ================================================================
-- SECTION 1: Injected coefficient bundle (Rust-aligned)
-- ================================================================

/-- Powers–Brownyard capillary coefficients — injected at consumer boundary. -/
structure PowersCapillaryCoeffs where
  /-- Non-evaporable water coefficient in `φ_c` numerator (G0 pin: 0.36). -/
  nonEvapWaterCoeff : ℚ
  /-- Paste denominator offset in `φ_c` closure (G0 pin: 0.32). -/
  pasteDenominatorOffset : ℚ

/-- G0 homogeneous pin — matches `PowersCapillaryCoeffs::G0_PIN`. -/
def g0PowersCoeffs : PowersCapillaryCoeffs :=
  { nonEvapWaterCoeff := 36 / 100, pasteDenominatorOffset := 32 / 100 }

/-- Injected coeffs are finite and non-negative — admissibility before atom lift. -/
def coeffsAdmissible (c : PowersCapillaryCoeffs) : Prop :=
  0 ≤ c.nonEvapWaterCoeff ∧ 0 ≤ c.pasteDenominatorOffset

lemma g0PowersCoeffs_admissible : coeffsAdmissible g0PowersCoeffs := by
  constructor <;> norm_num [g0PowersCoeffs, coeffsAdmissible]

/-- Admissible porosity domain — positive paste denominator, non-negative hydration. -/
def capillaryPorosityAdmissible (wc α : ℚ) (c : PowersCapillaryCoeffs) : Prop :=
  coeffsAdmissible c ∧ 0 < wc + c.pasteDenominatorOffset ∧ 0 ≤ α

lemma denom_pos_of_admissible {wc α : ℚ} {c : PowersCapillaryCoeffs}
    (h : capillaryPorosityAdmissible wc α c) : 0 < wc + c.pasteDenominatorOffset :=
  h.2.1

-- ================================================================
-- SECTION 2: Capillary porosity closure (ℚ)
-- ================================================================

/-- Raw Powers–Brownyard numerator/denominator ratio before clamping. -/
noncomputable def capillaryPorosityRaw (wc α : ℚ) (c : PowersCapillaryCoeffs) : ℚ :=
  (wc - c.nonEvapWaterCoeff * α) / (wc + c.pasteDenominatorOffset)

/-- Strict capillary porosity — saturating projection to `[0, 1]`.
    Matches `capillary_porosity` / `try_capillary_porosity` on admissible domain. -/
noncomputable def capillaryPorosity (wc α : ℚ) (c : PowersCapillaryCoeffs) : ℚ :=
  clamp01 (capillaryPorosityRaw wc α c)

lemma capillaryPorosity_g0_eq_jennings {wc α : ℚ} :
    capillaryPorosity wc α g0PowersCoeffs = φ_cap α wc := by
  unfold capillaryPorosity capillaryPorosityRaw g0PowersCoeffs φ_cap clamp01
  norm_num

lemma capillaryPorosity_nonneg {wc α : ℚ} (c : PowersCapillaryCoeffs) :
    0 ≤ capillaryPorosity wc α c := by
  unfold capillaryPorosity clamp01
  exact le_max_left _ _

lemma capillaryPorosity_le_one {wc α : ℚ} (c : PowersCapillaryCoeffs) :
    capillaryPorosity wc α c ≤ 1 := by
  unfold capillaryPorosity clamp01
  have hmin : min 1 (capillaryPorosityRaw wc α c) ≤ 1 := min_le_left _ _
  calc
    max 0 (min 1 _) ≤ max 0 1 := max_le_max (le_refl _) hmin
    _ = 1 := by norm_num

/-- B3-S1: clamped capillary porosity lies in `[0, 1]` on ℚ. -/
theorem capillaryPorosity_unit_interval {wc α : ℚ} (c : PowersCapillaryCoeffs) :
    0 ≤ capillaryPorosity wc α c ∧ capillaryPorosity wc α c ≤ 1 :=
  ⟨capillaryPorosity_nonneg c, capillaryPorosity_le_one c⟩

private lemma capillaryPorosityRaw_mono_in_alpha {wc : ℚ} {c : PowersCapillaryCoeffs}
    (hcoeff : 0 ≤ c.nonEvapWaterCoeff) {α₁ α₂ : ℚ} (hα : α₁ ≤ α₂)
    (hd : 0 < wc + c.pasteDenominatorOffset) :
    capillaryPorosityRaw wc α₂ c ≤ capillaryPorosityRaw wc α₁ c := by
  unfold capillaryPorosityRaw
  apply (div_le_div_iff_of_pos_right hd).mpr
  linarith [mul_le_mul_of_nonneg_left hα hcoeff]

/-- B3-S2: capillary porosity is antitone in hydration degree on admissible domain. -/
theorem capillaryPorosity_antitone_in_alpha {wc α₁ α₂ : ℚ} {c : PowersCapillaryCoeffs}
    (h : capillaryPorosityAdmissible wc α₁ c) (hα : α₁ ≤ α₂) :
    capillaryPorosity wc α₂ c ≤ capillaryPorosity wc α₁ c := by
  unfold capillaryPorosity
  rcases h with ⟨hcoeff, hd, _⟩
  have hraw := capillaryPorosityRaw_mono_in_alpha (wc := wc) (c := c)
    hcoeff.1 hα hd
  exact clamp01_mono hraw

/-- B3-S3 @ G0 pin — recovers Jennings gel-space antitone witness. -/
theorem capillaryPorosity_g0_antitone_in_alpha {wc : ℚ} (hwc : 0 < wc) {α₁ α₂ : ℚ}
    (hα₁ : 0 ≤ α₁) (hα₁₂ : α₁ ≤ α₂) :
    capillaryPorosity wc α₂ g0PowersCoeffs ≤ capillaryPorosity wc α₁ g0PowersCoeffs := by
  have hg0 : capillaryPorosityAdmissible wc α₁ g0PowersCoeffs := by
    refine ⟨g0PowersCoeffs_admissible, ?_, hα₁⟩
    unfold g0PowersCoeffs
    linarith
  rw [capillaryPorosity_g0_eq_jennings, capillaryPorosity_g0_eq_jennings]
  exact capillary_porosity_antitone_in_alpha hwc hα₁ hα₁₂

/-- G0 fixture oracle — matches Rust test `capillary_porosity_matches_injected_closure_on_g0_pin`. -/
theorem capillaryPorosity_g0_fixture_value :
    capillaryPorosity (45 / 100) (55 / 100) g0PowersCoeffs = 252 / 770 := by
  unfold capillaryPorosity capillaryPorosityRaw g0PowersCoeffs clamp01
  norm_num

-- ================================================================
-- SECTION 3: Flow scalar lift + tensor bridge (mirrors flow.rs)
-- ================================================================

/-- Injected chloride diffusivity closure coefficients — Life-365 homogeneous pin. -/
structure ChlorideDiffusivityCoeffs where
  /-- Reference chloride diffusivity [m²/s]. -/
  refDiffusivityM2S : ℚ
  /-- Porosity exponent in `D = D_ref · φ^n`. -/
  porosityExponent : ℚ

/-- Life-365 / Nernst-Planck homogeneous pin — `D_ref = 1e-12`, `n = 3.5`. -/
def life365DiffusivityCoeffs : ChlorideDiffusivityCoeffs :=
  { refDiffusivityM2S := 1 / (10 ^ (12 : ℕ) : ℚ), porosityExponent := 7 / 2 }

/-- Injected diffusivity coeffs are finite and non-negative — admissibility before atom lift. -/
def chlorideDiffusivityCoeffsAdmissible (c : ChlorideDiffusivityCoeffs) : Prop :=
  0 ≤ c.refDiffusivityM2S ∧ 0 ≤ c.porosityExponent

lemma life365DiffusivityCoeffs_admissible :
    chlorideDiffusivityCoeffsAdmissible life365DiffusivityCoeffs := by
  constructor <;> norm_num [life365DiffusivityCoeffs, chlorideDiffusivityCoeffsAdmissible]

/-- Admissible capillary porosity for the B3 flow witness path on the unit box. -/
def flowPorosityAdmissible (φ : ℚ) : Prop :=
  0 ≤ φ ∧ φ ≤ 1

lemma clamp01_flow_admissible (φ : ℚ) : flowPorosityAdmissible (clamp01 φ) := by
  constructor
  · unfold clamp01
    exact le_max_left _ _
  · unfold clamp01
    have hmin : min 1 φ ≤ 1 := min_le_left _ _
    calc
      max 0 (min 1 φ) ≤ max 0 1 := max_le_max (le_refl _) hmin
      _ = 1 := by norm_num

/-- Strict tortuosity witness — scalar reduction `τ = φ^{-1/3}` on `(0, 1]` (ℝ cast). -/
noncomputable def tortuosityWitness (φ : ℚ) : ℝ :=
  if φ ≤ 0 then 0 else (φ : ℝ) ^ (-(1 : ℝ) / 3)

/-- Strict apparent chloride diffusivity — `D = D_ref · φ^n` on `(0, 1]` (ℝ cast). -/
noncomputable def chlorideDiffusivityWitness (φ : ℚ) (c : ChlorideDiffusivityCoeffs) : ℝ :=
  if φ ≤ 0 then 0
  else (c.refDiffusivityM2S : ℝ) * (φ : ℝ) ^ (c.porosityExponent : ℝ)

lemma tortuosityWitness_nonpos (φ : ℚ) (h : φ ≤ 0) : tortuosityWitness φ = 0 := by
  unfold tortuosityWitness
  simp [h]

lemma chlorideDiffusivityWitness_nonpos (φ : ℚ) (h : φ ≤ 0) (c : ChlorideDiffusivityCoeffs) :
    chlorideDiffusivityWitness φ c = 0 := by
  unfold chlorideDiffusivityWitness
  simp [h]

/-- Flow witness ledger — scalar channels beside ψ_transport. -/
structure FlowWitness where
  /-- Clamped capillary porosity `φ` ∈ [0, 1] (field name avoids shadowing `capillaryPorosity`). -/
  witnessPhi : ℚ
  /-- Tortuosity witness `τ` ≥ 1 when `φ > 0` (ℝ cast). -/
  tortuosity : ℝ
  /-- Apparent chloride diffusivity [m²/s] (ℝ cast). -/
  chlorideDiffusivityM2S : ℝ

/-- Build flow witness from capillary porosity — saturating projection via clamped `φ`. -/
noncomputable def flowWitnessAtPorosity (φ : ℚ) (c : ChlorideDiffusivityCoeffs) : FlowWitness :=
  let φc := clamp01 φ
  { witnessPhi := φc
    tortuosity := tortuosityWitness φc
    chlorideDiffusivityM2S := chlorideDiffusivityWitness φc c }

/-- B3-S4: flow witness porosity channel lies in `[0, 1]` after clamp. -/
theorem flowWitness_capillaryPorosity_unit_interval (φ : ℚ) (c : ChlorideDiffusivityCoeffs) :
    0 ≤ (flowWitnessAtPorosity φ c).witnessPhi ∧
      (flowWitnessAtPorosity φ c).witnessPhi ≤ 1 :=
  clamp01_flow_admissible φ

/-- Transport axis for isotropic tensor reduction (consumer adapter deferred path). -/
abbrev TransportAxis := Fin 3

/-- Isotropic diffusivity tensor `D_ij = D_scalar · δ_ij` — tensor transport diagonal pin. -/
noncomputable def isotropicDiffusivityTensor (d : ℝ) : Matrix TransportAxis TransportAxis ℝ :=
  Matrix.diagonal fun _ => d

/-- Scalar-to-tensor bridge predicate — scalar `flow.rs` closure equals diagonal tensor entry. -/
def flowTransportTensorBridge (φ : ℚ) (c : ChlorideDiffusivityCoeffs) : Prop :=
  ∀ i j, isotropicDiffusivityTensor (chlorideDiffusivityWitness (clamp01 φ) c) i j =
    if i = j then chlorideDiffusivityWitness (clamp01 φ) c else 0

/-- Closes `B3OpenObligation.flow_transport_tensor_bridge` — scalar diffusivity bridges to tensor path. -/
theorem flow_transport_tensor_bridge (φ : ℚ) (c : ChlorideDiffusivityCoeffs) :
    flowTransportTensorBridge φ c := by
  intro i j
  simp [flowTransportTensorBridge, isotropicDiffusivityTensor, Matrix.diagonal]

/-- Default flow witness at Life-365 pin — matches `flow_witness_at_porosity`. -/
noncomputable def flowWitnessAtPorosityLife365 (φ : ℚ) : FlowWitness :=
  flowWitnessAtPorosity φ life365DiffusivityCoeffs

-- ================================================================
-- SECTION 4: B3 dissipation channels (ℚ slice — mirrors dissipation.rs)
-- ================================================================

/-- B3 𝒟 moduli — injected from consumer `dissipation_modulus_eta` / transport pins. -/
structure PoromechanicsDissipationCoeffs where
  /-- Transport dissipation modulus [J·s/m³]. -/
  transportEta : ℚ
  /-- Reaction dissipation modulus [J·s/m³]. -/
  reactionEta : ℚ

/-- Slice-1 homogeneous pin — mirrors `PoromechanicsDissipationCoeffs::SLICE1_PIN`. -/
def slice1DissipationCoeffs : PoromechanicsDissipationCoeffs :=
  { transportEta := 10000, reactionEta := 36000000000 }

/-- Injected dissipation moduli are non-negative — admissibility before atom lift. -/
def dissipationCoeffsAdmissible (c : PoromechanicsDissipationCoeffs) : Prop :=
  0 ≤ c.transportEta ∧ 0 ≤ c.reactionEta

lemma slice1DissipationCoeffs_admissible : dissipationCoeffsAdmissible slice1DissipationCoeffs := by
  unfold dissipationCoeffsAdmissible slice1DissipationCoeffs
  constructor <;> norm_num

/-- Exhaustive 𝒟 summand selector — mirrors `DissipationTermId`. -/
inductive DissipationTermId
  | transport
  | reaction
  deriving DecidableEq, Repr

/-- Stable term ids matching `DISSIPATION_TERM_TRANSPORT` / `DISSIPATION_TERM_REACTION`. -/
def dissipationTermIdStr : DissipationTermId → String
  | .transport => "𝒟_transport"
  | .reaction => "𝒟_reaction"

/-- Transport dissipation — quadratic in `(φ̇, Ṡ)` with injected modulus. -/
def dissipationTransport (phiDot sDot : ℚ) (c : PoromechanicsDissipationCoeffs) : ℚ :=
  c.transportEta * (phiDot * phiDot + sDot * sDot)

/-- Reaction dissipation — `η·α̇²` channel owned by B3 at extract slice. -/
def dissipationReaction (alphaDot : ℚ) (c : PoromechanicsDissipationCoeffs) : ℚ :=
  c.reactionEta * alphaDot * alphaDot

/-- Per-channel 𝒟 ledger for Layer C witness — mirrors `DissipationTerms`. -/
structure DissipationTerms where
  /-- Capillary / saturation rate channel. -/
  transport : ℚ
  /-- Reaction extent rate channel. -/
  reaction : ℚ

/-- Lookup a single summand by [`DissipationTermId`]. -/
def DissipationTerms.summand (t : DissipationTerms) (id : DissipationTermId) : ℚ :=
  match id with
  | .transport => t.transport
  | .reaction => t.reaction

/-- Total B3-owned 𝒟 summands. -/
def DissipationTerms.total (t : DissipationTerms) : ℚ :=
  t.transport + t.reaction

/-- Strict 𝒟 evaluation for both B3 channels with injected moduli. -/
def dissipationTerms (phiDot sDot alphaDot : ℚ) (c : PoromechanicsDissipationCoeffs) :
    DissipationTerms :=
  { transport := dissipationTransport phiDot sDot c
  , reaction := dissipationReaction alphaDot c }

/-- Total B3 dissipation potential φ_B3 — convex in rates. -/
def dissipationTotal (phiDot sDot alphaDot : ℚ) (c : PoromechanicsDissipationCoeffs) : ℚ :=
  (dissipationTerms phiDot sDot alphaDot c).total

lemma dissipationTransport_nonneg {phiDot sDot : ℚ} {c : PoromechanicsDissipationCoeffs}
    (h : dissipationCoeffsAdmissible c) :
    0 ≤ dissipationTransport phiDot sDot c := by
  unfold dissipationTransport dissipationCoeffsAdmissible at *
  rcases h with ⟨hη, _⟩
  have hsq : 0 ≤ phiDot * phiDot + sDot * sDot := by nlinarith [sq_nonneg phiDot, sq_nonneg sDot]
  exact mul_nonneg hη hsq

lemma dissipationReaction_nonneg {alphaDot : ℚ} {c : PoromechanicsDissipationCoeffs}
    (h : dissipationCoeffsAdmissible c) :
    0 ≤ dissipationReaction alphaDot c := by
  unfold dissipationReaction dissipationCoeffsAdmissible at *
  rcases h with ⟨_, hη⟩
  nlinarith [hη, sq_nonneg alphaDot]

/-- B3-D1: per-channel 𝒟 summands are non-negative on admissible injected moduli. -/
theorem dissipationTerms_nonneg {phiDot sDot alphaDot : ℚ} {c : PoromechanicsDissipationCoeffs}
    (h : dissipationCoeffsAdmissible c) :
    let terms := dissipationTerms phiDot sDot alphaDot c
    0 ≤ terms.transport ∧ 0 ≤ terms.reaction := by
  dsimp [dissipationTerms]
  exact ⟨dissipationTransport_nonneg (phiDot := phiDot) (sDot := sDot) h,
    dissipationReaction_nonneg (alphaDot := alphaDot) h⟩

/-- B3-D2: passive pin — both channels vanish at φ̇ = Ṡ = α̇ = 0. -/
theorem dissipationTerms_passive_pin (c : PoromechanicsDissipationCoeffs) :
    let terms := dissipationTerms 0 0 0 c
    terms.transport = 0 ∧ terms.reaction = 0 ∧ terms.total = 0 := by
  dsimp [dissipationTerms, dissipationTransport, dissipationReaction, DissipationTerms.total]
  norm_num

/-- B3-D3: ledger summands add term-by-term to total. -/
theorem dissipationTerms_total_identity (phiDot sDot alphaDot : ℚ)
    (c : PoromechanicsDissipationCoeffs) :
    (dissipationTerms phiDot sDot alphaDot c).total =
      dissipationTransport phiDot sDot c + dissipationReaction alphaDot c := by
  dsimp [dissipationTerms, DissipationTerms.total]

/-- B3-D4: quadratic homogeneity — φ(s·r) = s²·φ(r) on ℚ (P-𝒟-2 slice). -/
theorem dissipation_homogeneous_degree_two (s phiDot sDot alphaDot : ℚ)
    (c : PoromechanicsDissipationCoeffs) :
    dissipationTotal (s * phiDot) (s * sDot) (s * alphaDot) c =
      s * s * dissipationTotal phiDot sDot alphaDot c := by
  unfold dissipationTotal dissipationTerms dissipationTransport dissipationReaction
    DissipationTerms.total
  ring

/-- Slice-1 Clausius–Duhem dissipation closure witness (scalar channels only).
    Full compose-stack CD remains indexed by [`B3OpenObligation.dissipation_compose_cd_closure`]. -/
def dissipationComposeCdSlice1 (phiDot sDot alphaDot : ℚ) (c : PoromechanicsDissipationCoeffs) :
    Prop :=
  let terms := dissipationTerms phiDot sDot alphaDot c
  0 ≤ terms.transport ∧ 0 ≤ terms.reaction ∧
    terms.total = terms.transport + terms.reaction

theorem dissipationComposeCdSlice1_holds {phiDot sDot alphaDot : ℚ}
    {c : PoromechanicsDissipationCoeffs} (h : dissipationCoeffsAdmissible c) :
    dissipationComposeCdSlice1 phiDot sDot alphaDot c := by
  dsimp [dissipationComposeCdSlice1]
  rcases dissipationTerms_nonneg (phiDot := phiDot) (sDot := sDot) (alphaDot := alphaDot) h with
    ⟨hT, hR⟩
  exact ⟨hT, hR, rfl⟩

-- ================================================================
-- SECTION 5: Cert obligation index (CC-P-B3-1 — scaffold only)
-- ================================================================

/-- Proof targets on the path to CC-P-B3-1. Listed for audit; no `sorry`. -/
inductive B3OpenObligation
  | flow_transport_tensor_bridge
  | dissipation_compose_cd_closure
  | chem_hydration_adapter_parity
  | operator_epsilon_calibration
  deriving DecidableEq, Repr

/-- Stable obligation id matching `open_pending_cert_inventory.rs` `OP-B3-OBL-CC-P-B3-1`. -/
def b3OpenObligationCertId : String := "CC-P-B3-1"

/-- Human-readable obligation labels for receipts / cert tooling. -/
def b3OpenObligationDescription : B3OpenObligation → String
  | .flow_transport_tensor_bridge =>
      "bridge scalar flow.rs tortuosity/diffusivity to tensor transport path (mechanized @ §3)"
  | .dissipation_compose_cd_closure =>
      "end-to-end Clausius–Duhem closure for B3 compose stack (slice-1 scalar mechanized @ §4)"
  | .chem_hydration_adapter_parity =>
      "formalize consumer chem adapter α parity beside umst-chem lift"
  | .operator_epsilon_calibration =>
      "measured ε bounds for pore_pressure + chem_hydration — P3/P4/P5 cert gate"

-- ================================================================
-- SECTION 6: ψ transport channel (ℚ) — mirrors `energy.rs` / `saturation.rs`
-- ================================================================

/-- B3 ψ moduli — injected at consumer compose boundary. -/
structure PoromechanicsEnergyCoeffs where
  /-- Transport potential modulus — mirrors `transport_modulus`. -/
  transportModulus : ℚ
  /-- Reaction free-energy well modulus — mirrors `reaction_modulus` (indexed; reaction slice open). -/
  reactionModulus : ℚ

/-- Slice-1 homogeneous pin — mirrors `PoromechanicsEnergyCoeffs::SLICE1_PIN`. -/
def slice1EnergyCoeffs : PoromechanicsEnergyCoeffs :=
  { transportModulus := 1000000, reactionModulus := 450000000 }

/-- Injected transport modulus is non-negative — admissibility before atom lift. -/
def energyCoeffsAdmissible (c : PoromechanicsEnergyCoeffs) : Prop :=
  0 ≤ c.transportModulus

lemma slice1EnergyCoeffs_admissible : energyCoeffsAdmissible slice1EnergyCoeffs := by
  unfold slice1EnergyCoeffs energyCoeffsAdmissible
  norm_num

/-- Unit-interval scalar domain — mirrors `require_unit_interval`. -/
def unitIntervalAdmissible (x : ℚ) : Prop :=
  0 ≤ x ∧ x ≤ 1

/-- ψ transport admissibility — both `φ` and `S` in `[0, 1]`. -/
def psiTransportAdmissible (phi saturationS : ℚ) : Prop :=
  unitIntervalAdmissible phi ∧ unitIntervalAdmissible saturationS

/-- Convex transport well — mirrors `try_psi_transport` on admissible domain. -/
noncomputable def psiTransport (phi saturationS : ℚ) (c : PoromechanicsEnergyCoeffs) : ℚ :=
  (1 / 2) * c.transportModulus *
    ((1 - phi) ^ 2 + (1 - saturationS) ^ 2)

/-- φ-component — mirrors `try_psi_transport_phi_component` (`S = 1` deficit vanishes). -/
noncomputable def psiTransportPhiComponent (phi : ℚ) (c : PoromechanicsEnergyCoeffs) : ℚ :=
  (1 / 2) * c.transportModulus * (1 - phi) ^ 2

/-- S-component — mirrors `psi_transport_saturation_component`. -/
noncomputable def psiTransportSaturationComponent (saturationS : ℚ) (c : PoromechanicsEnergyCoeffs) : ℚ :=
  (1 / 2) * c.transportModulus * (1 - saturationS) ^ 2

lemma psiTransport_summand_identity (phi saturationS : ℚ) (c : PoromechanicsEnergyCoeffs) :
    psiTransport phi saturationS c =
      psiTransportPhiComponent phi c + psiTransportSaturationComponent saturationS c := by
  unfold psiTransport psiTransportPhiComponent psiTransportSaturationComponent
  ring

private lemma psiTransport_factor_nonneg (phi saturationS : ℚ) :
    0 ≤ (1 - phi) ^ 2 + (1 - saturationS) ^ 2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- B3-S4: transport ψ is non-negative when modulus is admissible. -/
theorem psiTransport_nonneg {phi saturationS : ℚ} {c : PoromechanicsEnergyCoeffs}
    (hc : energyCoeffsAdmissible c) :
    0 ≤ psiTransport phi saturationS c := by
  unfold psiTransport energyCoeffsAdmissible at *
  exact mul_nonneg (mul_nonneg (by norm_num) hc) (psiTransport_factor_nonneg phi saturationS)

/-- B3-S7: transport ψ vanishes at the `(φ, S) = (1, 1)` pin. -/
theorem psiTransport_eq_zero_at_unit_pin (c : PoromechanicsEnergyCoeffs) :
    psiTransport 1 1 c = 0 := by
  unfold psiTransport
  norm_num

/-- Slice-1 fixture oracle — matches Rust test pins `φ = 0.35`, `S = 0.9`. -/
theorem psiTransport_slice1_fixture_value :
    psiTransport (35 / 100) (90 / 100) slice1EnergyCoeffs = 216250 := by
  unfold psiTransport slice1EnergyCoeffs
  norm_num

/-- S-component is antitone in `S` on `[0, 1]` when modulus is admissible. -/
theorem psiTransportSaturationComponent_antitone_in_s {s₁ s₂ : ℚ}
    {c : PoromechanicsEnergyCoeffs} (hc : energyCoeffsAdmissible c)
    (hs₁ : unitIntervalAdmissible s₁) (hs : s₁ ≤ s₂) (hs₂ : unitIntervalAdmissible s₂) :
    psiTransportSaturationComponent s₂ c ≤ psiTransportSaturationComponent s₁ c := by
  unfold psiTransportSaturationComponent energyCoeffsAdmissible at *
  have hdef : 1 - s₂ ≤ 1 - s₁ := by linarith
  have hs₂nn : 0 ≤ 1 - s₂ := by linarith [hs₂.2]
  have hsq : (1 - s₂) ^ 2 ≤ (1 - s₁) ^ 2 :=
    pow_le_pow_left₀ hs₂nn hdef 2
  have hhalf : 0 ≤ (1 / 2 : ℚ) := by norm_num
  have hscaled : (1 / 2) * (1 - s₂) ^ 2 ≤ (1 / 2) * (1 - s₁) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hhalf
  calc
    (1 / 2) * c.transportModulus * (1 - s₂) ^ 2
        = c.transportModulus * ((1 / 2) * (1 - s₂) ^ 2) := by ring
    _ ≤ c.transportModulus * ((1 / 2) * (1 - s₁) ^ 2) := mul_le_mul_of_nonneg_left hscaled hc
    _ = (1 / 2) * c.transportModulus * (1 - s₁) ^ 2 := by ring

#print axioms capillaryPorosity_unit_interval
#print axioms capillaryPorosity_antitone_in_alpha
#print axioms capillaryPorosity_g0_fixture_value
#print axioms flow_transport_tensor_bridge
#print axioms flowWitness_capillaryPorosity_unit_interval
#print axioms dissipationTerms_nonneg
#print axioms dissipationTerms_passive_pin
#print axioms dissipation_homogeneous_degree_two
#print axioms dissipationComposeCdSlice1_holds
#print axioms psiTransport_nonneg
#print axioms psiTransport_summand_identity
#print axioms psiTransport_slice1_fixture_value

end UMST
