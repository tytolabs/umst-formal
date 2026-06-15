/-
  UMST-Formal: PrimeSpectralCategory.lean
  Lean 4 — Categorical semantics for gate-preserving prime-spectral guidance.

  Endofunctor `GuidanceF` acts on `GuidedState`; gate check factors through projection
  to `ThermodynamicState` (natural transformation to identity on gate-relevant fields).

  Zero sorry. Zero new axioms.
-/

import PrimeSpectralGuidance

namespace UMST.PrimeSpectral

open UMST

-- ================================================================
-- SECTION 1: Endofunctor GuidanceF on GuidedState
-- ================================================================

/-- Endofunctor action: filter the auxiliary channel; leave thermo unchanged. -/
def GuidanceF_map {n : Nat} (f : MultiplicativeChannel n → MultiplicativeChannel n)
    (g : GuidedState n) : GuidedState n :=
  applyChannelFilter g f

/-- Identity morphism on channels is the identity on guided states. -/
theorem GuidanceF_id_map {n : Nat} (g : GuidedState n) :
    GuidanceF_map id g = g := by
  cases g
  simp [GuidanceF_map, applyChannelFilter, MultiplicativeChannel]

/-- Composition of channel maps lifts to guided states (functoriality on channel leg). -/
theorem GuidanceF_map_comp {n : Nat} (f g : MultiplicativeChannel n → MultiplicativeChannel n)
    (s : GuidedState n) :
    GuidanceF_map (f ∘ g) s = GuidanceF_map f (GuidanceF_map g s) := by
  cases s
  simp [GuidanceF_map, applyChannelFilter, Function.comp_apply]

-- ================================================================
-- SECTION 2: Gate naturality — projection commutes with GuidanceF
-- ================================================================

/-- Gate projection is natural: filtering the channel does not alter gate inputs. -/
theorem gate_projection_naturality {n : Nat}
    (f : MultiplicativeChannel n → MultiplicativeChannel n) (g : GuidedState n) :
    gateProjection (GuidanceF_map f g) = gateProjection g := by
  cases g
  rfl

/-- `gateCheck` on guided states depends only on thermodynamic fields. -/
theorem gateCheck_guidance_naturality {n : Nat}
    (f : MultiplicativeChannel n → MultiplicativeChannel n)
    (g t : GuidedState n) :
    gateCheck (GuidanceF_map f g).thermo (GuidanceF_map f t).thermo =
      gateCheck g.thermo t.thermo := rfl

/-- Alias per design doc: naturality of gate decision under guidance. -/
theorem gate_naturality {n : Nat}
    (f : MultiplicativeChannel n → MultiplicativeChannel n)
    (g t : GuidedState n) :
    gateCheck (GuidanceF_map f g).thermo (GuidanceF_map f t).thermo =
      gateCheck g.thermo t.thermo :=
  gateCheck_guidance_naturality f g t

/-- Soundness of gate check is preserved under channel-only guidance. -/
theorem gateCheckSound_guidance {n : Nat}
    (f : MultiplicativeChannel n → MultiplicativeChannel n)
    (g t : GuidedState n)
    (h : gateCheck g.thermo t.thermo = true) :
    gateCheck (GuidanceF_map f g).thermo (GuidanceF_map f t).thermo = true := by
  rw [gate_naturality f g t, h]

/-- Admissibility extracted from gate soundness is guidance-invariant. -/
theorem admissible_of_gateCheck_guidance {n : Nat}
    (f : MultiplicativeChannel n → MultiplicativeChannel n)
    (g t : GuidedState n)
    (h : gateCheck g.thermo t.thermo = true) :
    Admissible (GuidanceF_map f g).thermo (GuidanceF_map f t).thermo :=
  gateCheckSound _ _ (gateCheckSound_guidance f g t h)

end UMST.PrimeSpectral
