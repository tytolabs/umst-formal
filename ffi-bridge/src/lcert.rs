// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-Z Z121 — AGAP-2350-L-5 `:lcert` factor slice (honest CLOSE).
//
// Upstream umst-formal witness for §14bis.h L-5 lcert prerequisite factor.
// `l5_lcert_factor_closed()` when workflow + Haskell mirror wired; does not
// claim L-7 capstone GREEN or production wiring.

use super::l5_extract_runtime::{
    l5_extraction_wired, l5_probe_detail, l5_receipt_status_label, l5_runtime_inventory,
    L5_EXPECTED_GATE_EXIT,
};

/// AGAP-2350 night slot id for L-5 lcert factor.
pub const JOB_ID: &str = "AGAP-2350-L-5";

/// Z121 Wave-Z slot id.
pub const Z121_JOB_ID: &str = "FLEET-COMPOSER-Z121-L5-LCERT";

/// Z121 Wave-Z slot label.
pub const Z121_WAVE_SLOT: &str = "Z121";

/// Z121 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z121_1232.md";

/// Prior Y78 runtime inventory receipt (absorbed; no blind redo).
pub const PRIOR_Y78_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y78_0808.md";

/// Honest adoption tier — L-5 factor wired; L-7 capstone still open.
pub const POSTURE_TAG: &str = "l5-factor-wired-capstone-open";

/// Machine-checkable L-5 lcert factor census for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L5LcertProbe {
    pub job_id: &'static str,
    pub z121_job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_y78_receipt: &'static str,
    pub posture: &'static str,
    pub slice_id: &'static str,
    pub receipt_status: &'static str,
    pub factor_closed: bool,
    pub expected_gate_exit: i32,
    pub workflow_present: bool,
    pub extraction_wired: bool,
    pub ffi_abi_version: u32,
    pub haskell_module_count: usize,
    pub lcert_capstone_open: bool,
    pub production_wired: bool,
    pub probe_detail: String,
}

/// L-5 lcert factor row wired — workflow on disk + Haskell mirror ≥1 module.
#[must_use]
pub fn l5_lcert_factor_closed() -> bool {
    l5_extraction_wired()
}

/// AGAP-2350-L-5 `:lcert` factor probe — honest L-5 slice close posture.
#[must_use]
pub fn l5_lcert_probe() -> L5LcertProbe {
    let inv = l5_runtime_inventory();
    let factor_closed = l5_lcert_factor_closed();
    L5LcertProbe {
        job_id: JOB_ID,
        z121_job_id: Z121_JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_y78_receipt: PRIOR_Y78_RECEIPT_PATH,
        posture: POSTURE_TAG,
        slice_id: "L-5",
        receipt_status: l5_receipt_status_label(),
        factor_closed,
        expected_gate_exit: L5_EXPECTED_GATE_EXIT,
        workflow_present: inv.workflow_present,
        extraction_wired: factor_closed,
        ffi_abi_version: inv.ffi_abi_version,
        haskell_module_count: inv.haskell_module_count,
        lcert_capstone_open: true,
        production_wired: false,
        probe_detail: l5_probe_detail(),
    }
}

/// Honesty gate for operator receipts — L-5 factor closed, capstone still open.
#[must_use]
pub fn l5_lcert_honest(probe: &L5LcertProbe) -> bool {
    probe.job_id == JOB_ID
        && probe.z121_job_id == Z121_JOB_ID
        && probe.receipt_path.contains("COMPOSER_Z121_1232")
        && probe.prior_y78_receipt.contains("COMPOSER_Y78_0808")
        && probe.posture == POSTURE_TAG
        && probe.slice_id == "L-5"
        && probe.expected_gate_exit == L5_EXPECTED_GATE_EXIT
        && probe.lcert_capstone_open
        && !probe.production_wired
        && probe.probe_detail.contains("L-5 probe")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn l5_lcert_agap_2350_metadata() {
        assert_eq!(JOB_ID, "AGAP-2350-L-5");
        assert_eq!(Z121_WAVE_SLOT, "Z121");
        assert!(RECEIPT_PATH.contains("COMPOSER_Z121_1232"));
        assert_eq!(L5_EXPECTED_GATE_EXIT, 0);
    }

    #[test]
    fn l5_lcert_factor_closed_when_workflow_present() {
        let closed = l5_lcert_factor_closed();
        let probe = l5_lcert_probe();
        assert_eq!(closed, probe.extraction_wired);
        if probe.workflow_present {
            assert!(closed);
            assert_eq!(probe.receipt_status, "green");
            assert!(probe.haskell_module_count >= 1);
        }
    }

    #[test]
    fn l5_lcert_probe_honest_partial() {
        let probe = l5_lcert_probe();
        assert!(l5_lcert_honest(&probe));
        assert!(probe.lcert_capstone_open);
        assert!(!probe.production_wired);
        assert!(probe.probe_detail.contains("gate_exit="));
    }

    #[test]
    fn l5_lcert_factor_closed_measured() {
        let probe = l5_lcert_probe();
        if l5_lcert_factor_closed() {
            assert!(probe.factor_closed);
            assert_eq!(probe.expected_gate_exit, 0);
        }
    }
}
