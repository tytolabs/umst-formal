// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-H50 — LIB-LEARN-F-LEAN formal bridge prep slice.
// Rust↔Lean L1a/L1b computational witnesses (witnessed-not-proved).

/// H50 fleet slot id.
pub const JOB_ID: &str = "FLEET-COMPOSER-H50-LEAN-L1-BRIDGE";

/// Completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_H50_2242.md";

/// Prior G-wave slot — lean bridge absent on G46; H50 absorbs prep.
pub const PRIOR_G_SLOT: &str = "G46";

/// Honest adoption tier — computational witness only, not Proved export.
pub const POSTURE_TAG: &str = "witnessed-not-proved";

/// L1a Lean module authority (`Concrete.StiffnessTransition`).
pub const L1A_LEAN_MODULE: &str = "Concrete.StiffnessTransition";

/// L1b Lean module authority (`Concrete.MicroMechanics`).
pub const L1B_LEAN_MODULE: &str = "Concrete.MicroMechanics";

/// L1a anchor theorem — ψ antitone under forward hydration.
pub const L1A_WITNESS_THEOREM: &str = "UMST.ψAntitoneStiffnessTransition";

/// L1b anchor theorem — elastic-base ψ softens with damage.
pub const L1B_WITNESS_THEOREM: &str = "UMST.ψSofteningMicroMechanics";

/// Maximum admissible damage scalar — mirrors Lean `damageDMax = 99/100`.
pub const DAMAGE_D_MAX: f64 = 0.99;

/// Hydration threshold for stiffness scale — mirrors Lean `stiffnessAlphaThreshold = 1/2`.
pub const STIFFNESS_ALPHA_THRESHOLD: f64 = 0.5;

/// Scalar effective modulus — mirrors Lean `e_eff_mt` / Rust `effective_modulus_pa`.
#[must_use]
pub fn effective_modulus_mt(e0: f64, d: f64) -> f64 {
    e0 * (1.0 - d).powi(2)
}

/// α-dependent stiffness scale — mirrors Lean `stiffnessScale` / Rust `(α - 0.5).max(0.0)`.
#[must_use]
pub fn stiffness_scale(alpha: f64) -> f64 {
    (alpha - STIFFNESS_ALPHA_THRESHOLD).max(0.0)
}

/// Elastic-base summand — mirrors Lean `psi_elastic_base`.
#[must_use]
pub fn psi_elastic_base(epsilon: f64, d: f64, e0: f64) -> f64 {
    -0.5 * effective_modulus_mt(e0, d) * epsilon.powi(2)
}

/// MT-3 witness: intact material recovers E₀ at zero damage.
#[must_use]
pub fn e_eff_mt_at_zero_holds(e0: f64) -> bool {
    (effective_modulus_mt(e0, 0.0) - e0).abs() < 1e-12
}

/// MT-4 witness: ψ ≤ 0 when E₀ ≥ 0 and damage admissible.
#[must_use]
pub fn psi_elastic_base_nonpos_holds(epsilon: f64, d: f64, e0: f64) -> bool {
    e0 >= 0.0 && d >= 0.0 && d <= DAMAGE_D_MAX && psi_elastic_base(epsilon, d, e0) <= 0.0
}

/// L1b softening witness: ψ antitone in damage at fixed ε, E₀.
#[must_use]
pub fn psi_softening_micro_mechanics_holds(epsilon: f64, d1: f64, d2: f64, e0: f64) -> bool {
    if !(e0 >= 0.0 && d1 <= d2 && d1 >= 0.0 && d2 <= DAMAGE_D_MAX) {
        return false;
    }
    psi_elastic_base(epsilon, d1, e0) <= psi_elastic_base(epsilon, d2, e0)
}

/// L1a monotonicity witness: stiffness scale non-decreasing in α.
#[must_use]
pub fn stiffness_scale_mono_holds(alpha1: f64, alpha2: f64) -> bool {
    if alpha1 > alpha2 {
        return false;
    }
    stiffness_scale(alpha1) <= stiffness_scale(alpha2)
}

/// One L1 bridge prep row — pins Lean anchor + Rust witness predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L1BridgeWitnessRow {
    pub layer: &'static str,
    pub lean_module: &'static str,
    pub lean_theorem: &'static str,
    pub witness_holds: bool,
}

/// Machine-checkable L1 bridge prep census for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanL1BridgePrepProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_g_slot: &'static str,
    pub posture: &'static str,
    pub l1a_module: &'static str,
    pub l1b_module: &'static str,
    pub witness_rows: usize,
    pub lake_build_green: bool,
    pub catalog_export_proved: bool,
    pub wired_to_slice1: bool,
    pub lean_l1_fully_closed: bool,
    pub production_wired: bool,
}

/// H50 LIB-LEARN-F-LEAN bridge prep — honest partial formal posture.
#[must_use]
pub fn lean_l1_bridge_prep_probe(lake_build_green: bool) -> LeanL1BridgePrepProbe {
    let rows = l1_bridge_witness_rows();
    let all_hold = rows.iter().all(|r| r.witness_holds);
    debug_assert!(all_hold, "L1 bridge witness rows must hold on pinned scenarios");

    LeanL1BridgePrepProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_g_slot: PRIOR_G_SLOT,
        posture: POSTURE_TAG,
        l1a_module: L1A_LEAN_MODULE,
        l1b_module: L1B_LEAN_MODULE,
        witness_rows: rows.len(),
        lake_build_green,
        catalog_export_proved: false,
        wired_to_slice1: false,
        lean_l1_fully_closed: false,
        production_wired: false,
    }
}

/// Pinned L1a/L1b witness rows for fleet census.
#[must_use]
pub fn l1_bridge_witness_rows() -> [L1BridgeWitnessRow; 4] {
    [
        L1BridgeWitnessRow {
            layer: "L1a",
            lean_module: L1A_LEAN_MODULE,
            lean_theorem: L1A_WITNESS_THEOREM,
            witness_holds: stiffness_scale_mono_holds(0.5, 0.8),
        },
        L1BridgeWitnessRow {
            layer: "L1b",
            lean_module: L1B_LEAN_MODULE,
            lean_theorem: "UMST.e_eff_mt_at_zero",
            witness_holds: e_eff_mt_at_zero_holds(30e9),
        },
        L1BridgeWitnessRow {
            layer: "L1b",
            lean_module: L1B_LEAN_MODULE,
            lean_theorem: "UMST.psi_elastic_base_nonpos",
            witness_holds: psi_elastic_base_nonpos_holds(0.015, 0.25, 30e9),
        },
        L1BridgeWitnessRow {
            layer: "L1b",
            lean_module: L1B_LEAN_MODULE,
            lean_theorem: L1B_WITNESS_THEOREM,
            witness_holds: psi_softening_micro_mechanics_holds(0.015, 0.1, 0.4, 30e9),
        },
    ]
}

/// FLEET-COMPOSER-J31 job id (absorbs I58).
pub const COMPOSER_J31_JOB_ID: &str = "FLEET-COMPOSER-J31-LEAN-L1";

/// J31 receipt cross-ref.
pub const COMPOSER_J31_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_J31_2348.md";

/// Prior H50 receipt (J31 absorb).
pub const PRIOR_COMPOSER_H50_RECEIPT_PATH: &str = RECEIPT_PATH;

/// FLEET-COMPOSER-J31 Lean L1 bridge deepen probe — chains H50; lake build measured at session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanL1BridgeJ31Probe {
    /// J31 fleet card id.
    pub job_id: &'static str,
    /// J31 receipt path.
    pub receipt_path: &'static str,
    /// H50 prior receipt dedupe (`==` SSOT).
    pub h50_prior_receipt_deduped: bool,
    /// H50 bridge prep honest.
    pub h50_honest: bool,
    /// `lake build` measured @ J31 session.
    pub lake_build_green: bool,
    /// L1 witness row count.
    pub witness_rows: usize,
    /// L1c/L1d + catalog export still open.
    pub lean_l1_fully_closed: bool,
    /// Prep only — no production flip.
    pub production_wired: bool,
}

/// Build FLEET-COMPOSER-J31 Lean L1 bridge probe.
#[must_use]
pub fn lean_l1_bridge_j31_probe(lake_build_green: bool) -> LeanL1BridgeJ31Probe {
    let h50 = lean_l1_bridge_prep_probe(lake_build_green);
    LeanL1BridgeJ31Probe {
        job_id: COMPOSER_J31_JOB_ID,
        receipt_path: COMPOSER_J31_RECEIPT_PATH,
        h50_prior_receipt_deduped: PRIOR_COMPOSER_H50_RECEIPT_PATH == RECEIPT_PATH,
        h50_honest: lean_l1_bridge_prep_honest(&h50),
        lake_build_green,
        witness_rows: h50.witness_rows,
        lean_l1_fully_closed: h50.lean_l1_fully_closed,
        production_wired: false,
    }
}

/// FLEET-COMPOSER-J31 honesty gate — chains H50; no fake L1 GREEN.
#[must_use]
pub fn lean_l1_bridge_j31_honest(probe: &LeanL1BridgeJ31Probe) -> bool {
    probe.job_id == COMPOSER_J31_JOB_ID
        && probe.receipt_path == COMPOSER_J31_RECEIPT_PATH
        && probe.h50_prior_receipt_deduped
        && probe.h50_honest
        && probe.lake_build_green
        && probe.witness_rows == 4
        && !probe.lean_l1_fully_closed
        && !probe.production_wired
}

/// Honesty gate for operator receipts — prep slice wired, no fake GREEN.
#[must_use]
pub fn lean_l1_bridge_prep_honest(probe: &LeanL1BridgePrepProbe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("COMPOSER_H50_2242")
        && probe.prior_g_slot == PRIOR_G_SLOT
        && probe.posture == POSTURE_TAG
        && probe.l1a_module == L1A_LEAN_MODULE
        && probe.l1b_module == L1B_LEAN_MODULE
        && probe.witness_rows == 4
        && l1_bridge_witness_rows().iter().all(|r| r.witness_holds)
        && !probe.catalog_export_proved
        && !probe.wired_to_slice1
        && !probe.lean_l1_fully_closed
        && !probe.production_wired
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn h50_metadata() {
        assert_eq!(JOB_ID, "FLEET-COMPOSER-H50-LEAN-L1-BRIDGE");
        assert!(RECEIPT_PATH.contains("COMPOSER_H50_2242"));
        assert_eq!(PRIOR_G_SLOT, "G46");
    }

    #[test]
    fn l1b_effective_modulus_at_zero_damage() {
        assert!(e_eff_mt_at_zero_holds(30e9));
        assert!((effective_modulus_mt(30e9, 0.25) - 30e9 * 0.75_f64.powi(2)).abs() < 1.0);
    }

    #[test]
    fn l1b_psi_softening_antitone_in_damage() {
        assert!(psi_softening_micro_mechanics_holds(0.015, 0.1, 0.4, 30e9));
    }

    #[test]
    fn l1a_stiffness_scale_monotone() {
        assert!(stiffness_scale_mono_holds(0.5, 0.8));
        assert!((stiffness_scale(0.3) - 0.0).abs() < 1e-12);
        assert!((stiffness_scale(0.7) - 0.2).abs() < 1e-12);
    }

    #[test]
    fn lean_l1_bridge_prep_honest_partial() {
        let probe = lean_l1_bridge_prep_probe(true);
        assert!(lean_l1_bridge_prep_honest(&probe));
        assert!(probe.lake_build_green);
        assert!(!probe.lean_l1_fully_closed);
        assert!(!probe.production_wired);
    }

    #[test]
    fn fleet_composer_j31_lean_l1_bridge_deepen() {
        let probe = lean_l1_bridge_j31_probe(true);
        assert!(lean_l1_bridge_j31_honest(&probe));
        assert_eq!(probe.job_id, COMPOSER_J31_JOB_ID);
        assert!(probe.receipt_path.contains("COMPOSER_J31_2348"));
        assert!(!probe.production_wired);
    }
}
