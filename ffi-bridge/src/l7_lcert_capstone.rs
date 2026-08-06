// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-Z Z123 — AGAP-2350-L-7 `:lcert` capstone factor table (honest SCAFFOLD).
//
// Upstream umst-formal witness for §14bis.h L-7 POSTH-04 capstone. Aggregates L-1..L-6
// prerequisite posture from disk; does not claim exit-0 GREEN or production wiring.

use std::path::{Path, PathBuf};

use umst_math::theorem_registry::crosswalk_stats;

use super::agap_2350_l1_inventory::{l1_qc_bisim_cluster_count, L1_EXPECTED_CLUSTER_COUNT};
use super::agap_2350_l2_attestation::l2_attestation_wired;
use super::l5_extract_runtime::{l5_extraction_wired, l5_runtime_inventory, L5_EXPECTED_GATE_EXIT};

/// AGAP-2350 L-Arc L-7 slot id.
pub const JOB_ID: &str = "AGAP-2350-L-7";

/// Z123 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z123_1232.md";

/// Prior AGAP-2033 L567 deepen receipt (absorbed; no blind redo).
pub const PRIOR_RECEIPT_PATH: &str =
    "archived/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_L567_2033.md";

/// Honest capstone gate exit until L-1..L-6 all GREEN (`LCERT-NOT-WIRED`).
pub const LCERT_EXPECTED_GATE_EXIT: i32 = 2;

/// L-6 crosswalk gate honest exit (partial map; gate script exit 0).
pub const L6_EXPECTED_GATE_EXIT: i32 = 0;

/// Operator posture label surfaced to CLI / receipts.
pub const POSTURE_TAG: &str = "LCERT-NOT-WIRED";

/// Disk ledger path relative to umst-formal root.
pub const L_CERT_LEDGER_REL: &str = "../umst-manifold/umst-math/L_CERT_LEDGER.txt";

/// Resolve umst-formal workspace root from ffi-bridge manifest dir.
#[must_use]
fn formal_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// Absolute path to `umst-math/L_CERT_LEDGER.txt`.
#[must_use]
pub fn l_cert_ledger_path() -> PathBuf {
    formal_root().join(L_CERT_LEDGER_REL)
}

/// One prerequisite factor row for the L-7 capstone matrix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LcertFactorRow {
    pub slice_id: &'static str,
    pub probe_wired: bool,
    pub detail: &'static str,
}

/// L-6 crosswalk partial posture — map rows on disk; full GREEN still open.
#[must_use]
pub fn l6_crosswalk_partial() -> bool {
    let stats = crosswalk_stats();
    stats.map_rows >= 5 && stats.covered_derived_rows >= 4
}

/// L-6 crosswalk fully wired (mirrors egoff `l6_crosswalk_wired`; stays false).
#[must_use]
pub const fn l6_crosswalk_wired() -> bool {
    false
}

/// Collect L-1..L-6 prerequisite factor rows from upstream probes.
#[must_use]
pub fn lcert_prereq_factor_rows() -> [LcertFactorRow; 6] {
    let l1_wired = l1_qc_bisim_cluster_count() == L1_EXPECTED_CLUSTER_COUNT;
    let l5_wired = l5_extraction_wired();
    let l6_partial = l6_crosswalk_partial();
    [
        LcertFactorRow {
            slice_id: "L-1",
            probe_wired: l1_wired,
            detail: "ffi cluster inventory 10/10",
        },
        LcertFactorRow {
            slice_id: "L-2",
            probe_wired: l2_attestation_wired(),
            detail: "attestation token / :bind",
        },
        LcertFactorRow {
            slice_id: "L-3",
            probe_wired: false,
            detail: "explain enrichment (egoff-owned)",
        },
        LcertFactorRow {
            slice_id: "L-4",
            probe_wired: false,
            detail: "ci coverage (egoff-owned)",
        },
        LcertFactorRow {
            slice_id: "L-5",
            probe_wired: l5_wired,
            detail: "lean→haskell extraction workflow",
        },
        LcertFactorRow {
            slice_id: "L-6",
            probe_wired: l6_crosswalk_wired(),
            detail: if l6_partial {
                "theorem constant crosswalk partial"
            } else {
                "theorem constant crosswalk not mapped"
            },
        },
    ]
}

/// Operator gate exit expectations for L-5/L-6/L-7 factor rows (`:lcert` deepen).
#[must_use]
pub fn lcert_gate_factor_table() -> String {
    format!(
        "LCERT gate factors: L-5 expected_gate_exit={L5_EXPECTED_GATE_EXIT} \
         L-6 expected_gate_exit={L6_EXPECTED_GATE_EXIT} \
         L-7 capstone expected_gate_exit={LCERT_EXPECTED_GATE_EXIT}"
    )
}

/// Render factor readiness matrix for operator / POSTH-04 receipts.
#[must_use]
pub fn lcert_factor_readiness_matrix() -> String {
    let rows = lcert_prereq_factor_rows();
    let mut out = String::from(
        "LCERT factor readiness (slice | probe_wired | capstone_credit):\n",
    );
    let mut blocked = 0usize;
    for row in &rows {
        let credit = row.probe_wired;
        if !credit {
            blocked += 1;
        }
        out.push_str(&format!(
            "  {} probe_wired={} capstone_credit={} — {}\n",
            row.slice_id, row.probe_wired, credit, row.detail
        ));
    }
    out.push_str(&format!("  blocked={blocked}/{}", rows.len()));
    out
}

/// Machine-checkable L-7 capstone census for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L7LcertCapstoneProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_receipt: &'static str,
    pub posture: &'static str,
    pub slice_id: &'static str,
    pub expected_gate_exit: i32,
    pub capstone_wired: bool,
    pub ledger_file_present: bool,
    pub blocked_factor_count: usize,
    pub total_factor_count: usize,
    pub l5_extraction_wired: bool,
    pub l6_crosswalk_partial: bool,
    pub production_wired: bool,
    pub gate_factor_table: String,
    pub factor_matrix: String,
}

/// AGAP-2350-L-7 `:lcert` capstone probe — honest NOT-WIRED posture.
#[must_use]
pub fn l7_lcert_capstone_probe() -> L7LcertCapstoneProbe {
    let rows = lcert_prereq_factor_rows();
    let blocked_factor_count = rows.iter().filter(|r| !r.probe_wired).count();
    let inv = l5_runtime_inventory();
    L7LcertCapstoneProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_receipt: PRIOR_RECEIPT_PATH,
        posture: POSTURE_TAG,
        slice_id: "L-7",
        expected_gate_exit: LCERT_EXPECTED_GATE_EXIT,
        capstone_wired: false,
        ledger_file_present: l_cert_ledger_path().is_file(),
        blocked_factor_count,
        total_factor_count: rows.len(),
        l5_extraction_wired: inv.workflow_present && inv.haskell_module_count >= 1,
        l6_crosswalk_partial: l6_crosswalk_partial(),
        production_wired: false,
        gate_factor_table: lcert_gate_factor_table(),
        factor_matrix: lcert_factor_readiness_matrix(),
    }
}

/// Returns true only when all L-1..L-6 factors are wired (capstone exit 0 tier).
#[must_use]
pub fn l7_capstone_wired() -> bool {
    lcert_prereq_factor_rows()
        .iter()
        .all(|r| r.probe_wired)
}

/// Honesty gate for operator receipts — scaffold posture, no fake LCERT-OK.
#[must_use]
pub fn l7_lcert_capstone_honest(probe: &L7LcertCapstoneProbe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("COMPOSER_Z123_1232")
        && probe.prior_receipt.contains("L567_2033")
        && probe.posture == POSTURE_TAG
        && probe.slice_id == "L-7"
        && probe.expected_gate_exit == LCERT_EXPECTED_GATE_EXIT
        && !probe.capstone_wired
        && !probe.production_wired
        && probe.blocked_factor_count > 0
        && probe.gate_factor_table.contains("L-7 capstone expected_gate_exit=2")
        && probe.factor_matrix.contains("LCERT factor readiness")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn l7_agap_2350_metadata() {
        assert_eq!(JOB_ID, "AGAP-2350-L-7");
        assert!(RECEIPT_PATH.contains("COMPOSER_Z123_1232"));
        assert_eq!(LCERT_EXPECTED_GATE_EXIT, 2);
        assert_eq!(L6_EXPECTED_GATE_EXIT, 0);
    }

    #[test]
    fn l7_gate_factor_table_honest_exit_2() {
        let table = lcert_gate_factor_table();
        assert!(table.contains("L-5 expected_gate_exit="));
        assert!(table.contains("L-6 expected_gate_exit=0"));
        assert!(table.contains("L-7 capstone expected_gate_exit=2"));
    }

    #[test]
    fn l7_prereq_factor_rows_six_slices() {
        let rows = lcert_prereq_factor_rows();
        assert_eq!(rows.len(), 6);
        assert_eq!(rows[0].slice_id, "L-1");
        assert_eq!(rows[5].slice_id, "L-6");
    }

    #[test]
    fn l7_capstone_not_wired_while_blockers_remain() {
        assert!(!l7_capstone_wired());
        let probe = l7_lcert_capstone_probe();
        assert!(!probe.capstone_wired);
        assert!(probe.blocked_factor_count >= 2);
        assert_eq!(probe.expected_gate_exit, 2);
    }

    #[test]
    fn l7_lcert_capstone_probe_honest_scaffold() {
        let probe = l7_lcert_capstone_probe();
        assert!(l7_lcert_capstone_honest(&probe));
        assert!(!probe.production_wired);
        assert!(probe.factor_matrix.contains("blocked="));
        if l_cert_ledger_path().is_file() {
            assert!(probe.ledger_file_present);
        }
    }

    #[test]
    fn l7_l6_crosswalk_partial_on_disk() {
        let stats = crosswalk_stats();
        if stats.map_rows >= 5 {
            assert!(l6_crosswalk_partial());
            assert!(!l6_crosswalk_wired());
        }
    }
}
