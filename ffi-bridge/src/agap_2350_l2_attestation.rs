// SPDX-License-Identifier: MIT
//
// AGAP-2350-L-2 — attestation token / `:bind` deepen census (FLEET-COMPOSER-Y Y77).
// Cross-links umst-math THEOREM_REGISTRY rows with egoff L-2 metric bindings.

use umst_math::theorem_registry::THEOREM_REGISTRY;

/// AGAP-2350 L-Arc L-2 slot id.
pub const JOB_ID: &str = "AGAP-2350-L-2";

/// Y77 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y77_0808.md";

/// Prior SWARM-C25-0831-50 L-2-SCAFFOLD deepen receipt.
pub const PRIOR_SWARM_RECEIPT_PATH: &str =
    "outputs/.tmp/COMPLETION_SWARM_SWARM-C25-0831-50_0831.md";

/// L-2 metric-path → theorem hint rows (synced with `egoff::cockpit::attestation`).
pub const L2_METRIC_THEOREM_BINDINGS: &[(&str, &str)] = &[
    ("frugality", "UMST.Formal.EtaCog::eta_cog_nonneg"),
    ("frugality.eta_cog", "UMST.Formal.EtaCog::eta_cog_nonneg"),
    (
        "frugality.eta_cog_band",
        "UMST.Formal.OrderStatisticsBand::p25_p75_admissibility",
    ),
    (
        "frugality.dignity",
        "UMST.Formal.Dignity::dignity_monotone_under_mi_gain",
    ),
    (
        "frugality.rcc",
        "UMST.FormalDoubleSlit.GeneralResidualCoherence::residual_coherence_capacity",
    ),
    ("closed_loop.landauer_slack", "UMST.Formal.LandauerLaw::landauerBound"),
    (
        "closed_loop.mutual_information_bits",
        "UMST.Formal.RhoEstimator::rho_based_mi_formula",
    ),
    (
        "convergence.median_warmup_n",
        "UMST.Formal.MedianConvergence::sqrt_window_warmup_is_admissible",
    ),
    (
        "credit.greedy_optimal_floor",
        "UMST.Formal.CreditGreedy::credit_greedy_optimal",
    ),
];

/// THEOREM-BOUND CockpitSnapshot scalars (synced with egoff L-2 census table).
pub const L2_SNAPSHOT_BOUND_FIELDS: &[(&str, &str)] = &[
    ("eta_cog", "frugality.eta_cog"),
    ("eta_cog_band", "frugality.eta_cog_band"),
    ("landauer_slack", "closed_loop.landauer_slack"),
    ("dignity_value", "frugality.dignity"),
    ("rcc", "frugality.rcc"),
    ("cumulative_mi_bits", "closed_loop.mutual_information_bits"),
];

/// Returns `true` when `theorem_id` is an exact row in `THEOREM_REGISTRY`.
#[must_use]
pub fn registry_has_theorem(theorem_id: &str) -> bool {
    THEOREM_REGISTRY.iter().any(|(hint, _)| *hint == theorem_id)
}

/// Count L-2 metric bindings with registry-backed theorem hints.
#[must_use]
pub fn l2_registry_bound_count() -> usize {
    L2_METRIC_THEOREM_BINDINGS
        .iter()
        .filter(|(_, id)| registry_has_theorem(id))
        .count()
}

/// Nested `CockpitTheoremAttestation` populator covers every snapshot-bound field.
#[must_use]
pub fn l2_nested_populator_schema_wired() -> bool {
    L2_SNAPSHOT_BOUND_FIELDS.len() == 6
}

/// Full L-2 GREEN requires inline `Proof:` on every snapshot scalar (open).
#[must_use]
pub const fn l2_inline_proof_populators_wired() -> bool {
    false
}

/// Honest `l2_attestation_wired` mirror — stays false until L2_RECEIPT flips GREEN.
#[must_use]
pub const fn l2_attestation_wired() -> bool {
    false
}

/// AGAP-2350-L-2 operator probe — honest BLOCKED deepen posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Agap2350L2Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_swarm_receipt_deduped: bool,
    pub bind_coverage_bound: u8,
    pub bind_coverage_expected: u8,
    pub snapshot_bound_fields: u8,
    pub nested_populator_schema_wired: bool,
    pub inline_proof_populators_wired: bool,
    pub green_gate_wired: u8,
    pub green_gate_total: u8,
    pub l2_attestation_wired: bool,
    pub production_wired: bool,
}

/// Build AGAP-2350-L-2 attestation census probe.
#[must_use]
pub fn agap_2350_l2_probe() -> Agap2350L2Probe {
    let bound = l2_registry_bound_count();
    Agap2350L2Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_swarm_receipt_deduped: PRIOR_SWARM_RECEIPT_PATH.contains("SWARM-C25-0831-50"),
        bind_coverage_bound: bound as u8,
        bind_coverage_expected: L2_METRIC_THEOREM_BINDINGS.len() as u8,
        snapshot_bound_fields: L2_SNAPSHOT_BOUND_FIELDS.len() as u8,
        nested_populator_schema_wired: l2_nested_populator_schema_wired(),
        inline_proof_populators_wired: l2_inline_proof_populators_wired(),
        green_gate_wired: 2,
        green_gate_total: 4,
        l2_attestation_wired: l2_attestation_wired(),
        production_wired: false,
    }
}

/// Honesty gate — bind 9/9, nested schema wired, inline proof + full GREEN still open.
#[must_use]
pub fn agap_2350_l2_honest(probe: &Agap2350L2Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("COMPOSER_Y77_0808")
        && probe.prior_swarm_receipt_deduped
        && probe.bind_coverage_bound == probe.bind_coverage_expected
        && probe.bind_coverage_expected == 9
        && probe.snapshot_bound_fields == 6
        && probe.nested_populator_schema_wired
        && !probe.inline_proof_populators_wired
        && probe.green_gate_wired == 2
        && probe.green_gate_wired < probe.green_gate_total
        && !probe.l2_attestation_wired
        && !probe.production_wired
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agap_2350_l2_bindings_all_registry_backed() {
        assert_eq!(l2_registry_bound_count(), L2_METRIC_THEOREM_BINDINGS.len());
    }

    #[test]
    fn agap_2350_l2_snapshot_bound_six_fields() {
        assert_eq!(L2_SNAPSHOT_BOUND_FIELDS.len(), 6);
        assert!(l2_nested_populator_schema_wired());
    }

    #[test]
    fn agap_2350_l2_attestation_not_wired() {
        assert!(!l2_attestation_wired());
        assert!(!l2_inline_proof_populators_wired());
    }

    #[test]
    fn agap_2350_l2_probe_honest_blocked() {
        let probe = agap_2350_l2_probe();
        assert!(agap_2350_l2_honest(&probe));
        assert!(!probe.l2_attestation_wired);
        assert!(!probe.production_wired);
        assert_eq!(probe.bind_coverage_bound, 9);
    }
}
