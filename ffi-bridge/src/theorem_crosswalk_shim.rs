// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// L-6 crosswalk helpers for public `umst-math` git pins that predate
// `theorem_registry::crosswalk_stats` (W-62 @ ce9828e). Keep in sync with
// `umst-manifold/umst-math/src/theorem_registry.rs` until the pin advances.

use std::collections::HashSet;

use umst_math::constants::registry::{ConstantTier, REGISTRY};

/// Maps theorem hints to constant `name`s (§14bis.h L-6 partial crosswalk).
pub const THEOREM_DERIVES_CONSTANT: &[(&str, &str)] = &[
    (
        "UMST.Formal.RhoEstimator::rho_based_mi_formula",
        "closed_loop_mi_step_per_accept",
    ),
    (
        "UMST.Formal.MedianConvergence::sqrt_window_warmup_is_admissible",
        "warmup_sample_threshold",
    ),
    (
        "UMST.Formal.OrderStatisticsBand::p25_p75_admissibility",
        "frugality_band_p25_percentile",
    ),
    (
        "UMST.Formal.OrderStatisticsBand::p25_p75_admissibility",
        "frugality_band_p75_percentile",
    ),
    (
        "UMST.Formal.Gate::transitionTolerance",
        "transition_tolerance",
    ),
];

/// Honest L-6 crosswalk coverage snapshot (operator / `:lcert` probe).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CrosswalkStats {
    pub map_rows: usize,
    pub mapped_constants: usize,
    pub derived_constant_rows: usize,
    pub covered_derived_rows: usize,
}

/// Compute partial crosswalk coverage (never claims full GREEN).
#[must_use]
pub fn crosswalk_stats() -> CrosswalkStats {
    let mapped: HashSet<&str> = THEOREM_DERIVES_CONSTANT.iter().map(|(_, c)| *c).collect();
    let derived: Vec<&str> = REGISTRY
        .iter()
        .filter(|r| {
            matches!(
                r.tier,
                ConstantTier::Tier0Physical
                    | ConstantTier::Tier1Measurement
                    | ConstantTier::Tier2Derivable
            ) && r.evidence.contains("UMST.Formal")
                && r.evidence.contains("::")
        })
        .map(|r| r.name)
        .collect();
    let covered = derived.iter().filter(|n| mapped.contains(**n)).count();
    CrosswalkStats {
        map_rows: THEOREM_DERIVES_CONSTANT.len(),
        mapped_constants: mapped.len(),
        derived_constant_rows: derived.len(),
        covered_derived_rows: covered,
    }
}
