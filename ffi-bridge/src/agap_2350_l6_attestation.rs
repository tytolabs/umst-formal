// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// AGAP-2350-L-6 — theorem ↔ constant crosswalk attestation (FLEET-COMPOSER-Z Z122).
// Upstream umst-formal witness for §14bis.h L-6 partial crosswalk posture.
// `l6_crosswalk_wired` stays false until full :: derived census lands GREEN.

use umst_math::theorem_registry::{crosswalk_stats, THEOREM_DERIVES_CONSTANT};

/// AGAP-2350 L-Arc L-6 slot id.
pub const JOB_ID: &str = "AGAP-2350-L-6";

/// Z122 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z122_1232.md";

/// Prior Y-wave L-6 crosswalk deepen receipt (absorbed; no blind redo).
pub const PRIOR_Y_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y78_0808.md";

/// Operator gate script in egoff (cross-ref only; not executed here).
pub const L6_GATE_SCRIPT_REL: &str = "egoff/scripts/check_theorem_constant_crosswalk.sh";

/// Operator dump script in egoff (cross-ref only).
pub const L6_DUMP_SCRIPT_REL: &str = "egoff/scripts/dump_theorem_constant_crosswalk.sh";

/// Honest partial gate exit when crosswalk witnesses pass.
pub const L6_EXPECTED_GATE_EXIT: i32 = 0;

/// Honest adoption tier — partial map witness, not L-7 capstone GREEN.
pub const POSTURE_TAG: &str = "partial-crosswalk-not-lcert-ok";

/// Minimum explicit `THEOREM_DERIVES_CONSTANT` rows (synced with umst-math L-6 deepen).
pub const L6_MIN_MAP_ROWS: usize = 5;

/// Returns `true` when all derived :: rows are covered (full GREEN — not claimed yet).
#[must_use]
pub fn l6_crosswalk_fully_wired() -> bool {
    let stats = crosswalk_stats();
    stats.covered_derived_rows >= stats.derived_constant_rows && stats.derived_constant_rows > 0
}

/// Honest `l6_crosswalk_wired` mirror — stays false until L6_RECEIPT flips GREEN.
#[must_use]
pub fn l6_crosswalk_wired() -> bool {
    l6_crosswalk_fully_wired()
}

/// Operator-facing probe detail (honest partial; does not claim L-7 GREEN).
#[must_use]
pub fn l6_probe_detail() -> String {
    let stats = crosswalk_stats();
    format!(
        "L-6 probe (umst-formal): map_rows={} mapped_constants={} \
         derived_rows={} covered_derived={} expected_gate_exit={} \
         gate_script={L6_GATE_SCRIPT_REL} dump_script={L6_DUMP_SCRIPT_REL} \
         crosswalk_wired={}",
        stats.map_rows,
        stats.mapped_constants,
        stats.derived_constant_rows,
        stats.covered_derived_rows,
        L6_EXPECTED_GATE_EXIT,
        l6_crosswalk_wired(),
    )
}

/// Machine-checkable L-6 deepen census for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Agap2350L6Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_y_receipt: &'static str,
    pub posture: &'static str,
    pub slice_id: &'static str,
    pub map_rows: usize,
    pub mapped_constants: usize,
    pub derived_constant_rows: usize,
    pub covered_derived_rows: usize,
    pub min_map_rows: usize,
    pub expected_gate_exit: i32,
    pub crosswalk_wired: bool,
    pub lcert_capstone_open: bool,
    pub production_wired: bool,
    pub probe_detail: String,
}

/// AGAP-2350-L-6 crosswalk attestation probe — honest partial posture.
#[must_use]
pub fn agap_2350_l6_probe() -> Agap2350L6Probe {
    let stats = crosswalk_stats();
    Agap2350L6Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_y_receipt: PRIOR_Y_RECEIPT_PATH,
        posture: POSTURE_TAG,
        slice_id: "L-6",
        map_rows: stats.map_rows,
        mapped_constants: stats.mapped_constants,
        derived_constant_rows: stats.derived_constant_rows,
        covered_derived_rows: stats.covered_derived_rows,
        min_map_rows: L6_MIN_MAP_ROWS,
        expected_gate_exit: L6_EXPECTED_GATE_EXIT,
        crosswalk_wired: l6_crosswalk_wired(),
        lcert_capstone_open: true,
        production_wired: false,
        probe_detail: l6_probe_detail(),
    }
}

/// Honesty gate for operator receipts — partial map wired, no fake LCERT-OK.
#[must_use]
pub fn agap_2350_l6_honest(probe: &Agap2350L6Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("COMPOSER_Z122_1232")
        && probe.prior_y_receipt.contains("COMPOSER_Y78_0808")
        && probe.posture == POSTURE_TAG
        && probe.slice_id == "L-6"
        && probe.map_rows == THEOREM_DERIVES_CONSTANT.len()
        && probe.map_rows >= probe.min_map_rows
        && probe.covered_derived_rows >= 4
        && probe.covered_derived_rows < probe.derived_constant_rows
        && !probe.crosswalk_wired
        && probe.lcert_capstone_open
        && !probe.production_wired
        && probe.probe_detail.contains("L-6 probe")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agap_2350_l6_metadata() {
        assert_eq!(JOB_ID, "AGAP-2350-L-6");
        assert!(RECEIPT_PATH.contains("COMPOSER_Z122_1232"));
        assert_eq!(L6_EXPECTED_GATE_EXIT, 0);
        assert_eq!(L6_MIN_MAP_ROWS, 5);
    }

    #[test]
    fn l6_crosswalk_map_rows_at_least_five() {
        let stats = crosswalk_stats();
        assert!(stats.map_rows >= L6_MIN_MAP_ROWS);
        assert_eq!(stats.map_rows, THEOREM_DERIVES_CONSTANT.len());
    }

    #[test]
    fn l6_crosswalk_honest_partial_not_wired() {
        let stats = crosswalk_stats();
        assert!(stats.covered_derived_rows >= 4);
        assert!(stats.covered_derived_rows < stats.derived_constant_rows);
        assert!(!l6_crosswalk_wired());
        assert!(!l6_crosswalk_fully_wired());
    }

    #[test]
    fn l6_probe_detail_honest() {
        let d = l6_probe_detail();
        assert!(d.contains("L-6 probe"));
        assert!(d.contains("map_rows="));
        assert!(d.contains("expected_gate_exit=0"));
        assert!(d.contains("crosswalk_wired=false"));
        assert!(!d.contains("GREEN"));
    }

    #[test]
    fn agap_2350_l6_probe_honest_partial() {
        let probe = agap_2350_l6_probe();
        assert!(agap_2350_l6_honest(&probe));
        assert!(!probe.crosswalk_wired);
        assert!(!probe.production_wired);
        assert!(probe.lcert_capstone_open);
        assert!(probe.map_rows >= L6_MIN_MAP_ROWS);
        assert!(probe.covered_derived_rows < probe.derived_constant_rows);
    }
}
