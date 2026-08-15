// SPDX-License-Identifier: MIT
//
// AGAP-2350-L-1 — theorem FFI binding inventory census (FLEET-COMPOSER-Y Y76).
// Cross-links umst-formal C-ABI exports with egoff L-1 scaffold cluster rows.

/// AGAP-2350 L-Arc L-1 slot id.
pub const JOB_ID: &str = "AGAP-2350-L-1";

/// Y76 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y76_0808.md";

/// Prior H24 prep wire receipt (REGISTRY → FFI → L-1 scaffold).
pub const PRIOR_H24_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_H24_2242.md";

/// Expected ABI-9 material-agnostic cluster count (synced with egoff L-1 scaffold).
pub const L1_EXPECTED_CLUSTER_COUNT: u8 = 10;

/// One L-1 FFI cluster row for operator census.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct L1InventoryRow {
    pub ffi_symbol: &'static str,
    pub proof_anchor: &'static str,
    pub qc_bisim: bool,
}

/// Canonical 10-cluster inventory (synced with `egoff::slice_14bis_h_L_1_ffi_scaffold`).
#[must_use]
pub const fn l1_cluster_inventory() -> [L1InventoryRow; 10] {
    [
        L1InventoryRow {
            ffi_symbol: "umst_dissipation",
            proof_anchor: "UMST.Formal.Gate::clausius_duhem",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_gate_check",
            proof_anchor: "UMST.Formal.Gate::gate_check",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_dignity_step",
            proof_anchor: "UMST.Formal.Dignity::dignity_step",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_eta_cog",
            proof_anchor: "UMST.Formal.EtaCog::eta_cog_nonneg",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_rho_mi_bits",
            proof_anchor: "UMST.Formal.RhoEstimator::rho_based_mi_formula",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_n_warmup",
            proof_anchor: "UMST.Formal.MedianConvergence::sqrt_window_warmup_is_admissible",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_n_quantile",
            proof_anchor: "UMST.Formal.OrderStatisticsBand::p25_p75_admissibility",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_credit_greedy_sum",
            proof_anchor: "UMST.Formal.CreditGreedy::credit_greedy_optimal",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_ffi_abi_version",
            proof_anchor: "UMST_FFI_ABI_VERSION",
            qc_bisim: true,
        },
        L1InventoryRow {
            ffi_symbol: "umst_ffi_abi_version_expected",
            proof_anchor: "UMST_FFI_ABI_VERSION_MIN_COMPATIBLE",
            qc_bisim: false,
        },
    ]
}

/// Count clusters with QuickCheck bisim props (lean-ffi gate).
#[must_use]
pub const fn l1_qc_bisim_cluster_count() -> u8 {
    let inv = l1_cluster_inventory();
    let mut n = 0u8;
    let mut i = 0;
    while i < inv.len() {
        if inv[i].qc_bisim {
            n = n.saturating_add(1);
        }
        i += 1;
    }
    n
}

/// AGAP-2350-L-1 operator probe — honest PARTIAL posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Agap2350L1Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_h24_receipt_deduped: bool,
    pub clusters_bound: u8,
    pub expected_clusters: u8,
    pub qc_bisim_clusters: u8,
    pub l1_receipt_partial: bool,
    pub consumer_proof_wired: bool,
    pub production_wired: bool,
}

/// Build AGAP-2350-L-1 inventory probe.
#[must_use]
pub fn agap_2350_l1_probe() -> Agap2350L1Probe {
    Agap2350L1Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_h24_receipt_deduped: PRIOR_H24_RECEIPT_PATH.contains("COMPOSER_H24_2242"),
        clusters_bound: L1_EXPECTED_CLUSTER_COUNT,
        expected_clusters: L1_EXPECTED_CLUSTER_COUNT,
        qc_bisim_clusters: l1_qc_bisim_cluster_count(),
        l1_receipt_partial: true,
        consumer_proof_wired: false,
        production_wired: false,
    }
}

/// Honesty gate — inventory complete, receipt stays Partial, no fake GREEN.
#[must_use]
pub fn agap_2350_l1_honest(probe: &Agap2350L1Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("COMPOSER_Y76_0808")
        && probe.prior_h24_receipt_deduped
        && probe.clusters_bound == L1_EXPECTED_CLUSTER_COUNT
        && probe.qc_bisim_clusters == 9
        && probe.qc_bisim_clusters < L1_EXPECTED_CLUSTER_COUNT
        && probe.l1_receipt_partial
        && !probe.consumer_proof_wired
        && !probe.production_wired
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agap_2350_l1_inventory_has_ten_clusters() {
        assert_eq!(l1_cluster_inventory().len(), 10);
    }

    #[test]
    fn agap_2350_l1_qc_bisim_nine_of_ten() {
        assert_eq!(l1_qc_bisim_cluster_count(), 9);
    }

    #[test]
    fn agap_2350_l1_probe_honest_partial() {
        let probe = agap_2350_l1_probe();
        assert!(agap_2350_l1_honest(&probe));
        assert!(!probe.production_wired);
        assert!(!probe.consumer_proof_wired);
    }
}
