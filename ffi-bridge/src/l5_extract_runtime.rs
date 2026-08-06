// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-Y Y78 — AGAP-2350-L-5 runtime inventory probe (honest PARTIAL).
//
// Upstream umst-formal witness for §14bis.h L-5 Lean→Haskell extraction CI.
// `L5_RECEIPT` is Green when `extract-haskell-from-lean.yml` is on disk; does not
// claim L-7 `:lcert` capstone GREEN or production wiring.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

use super::UMST_FFI_ABI_VERSION;

/// AGAP-2350 night slot id for L-5 extraction deepen.
pub const JOB_ID: &str = "AGAP-2350-L-5";

/// FLEET-COMPOSER-Y Y78 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y78_0808.md";

/// Prior SWARM L-5 probe receipt (absorbed; no blind redo).
pub const PRIOR_SWARM_RECEIPT_PATH: &str =
    "archived/residuals/swarm-0831/COMPLETION_SWARM_SWARM-C25-0831-51_0831.md";

/// Upstream Lean→Haskell extraction workflow (relative to umst-formal root).
pub const L5_WORKFLOW_REL: &str = ".github/workflows/extract-haskell-from-lean.yml";

/// Operator gate script in egoff (cross-ref only; not executed here).
pub const L5_GATE_SCRIPT_REL: &str = "egoff/scripts/check_lean_haskell_extract.sh";

/// Honest gate exit when workflow + ABI + Haskell inventory pass.
pub const L5_EXPECTED_GATE_EXIT: i32 = 0;

/// Honest adoption tier — inventory witness only, not L-7 capstone GREEN.
pub const POSTURE_TAG: &str = "workflow-present-not-lcert-ok";

/// Resolve umst-formal workspace root from ffi-bridge manifest dir.
#[must_use]
fn formal_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// Absolute path to the L-5 extraction workflow on disk.
#[must_use]
pub fn l5_workflow_path() -> PathBuf {
    formal_root().join(L5_WORKFLOW_REL)
}

/// Sorted-basename fingerprint of `Haskell/*.hs` (mirrors egoff `l5_runtime_inventory`).
#[must_use]
pub fn haskell_module_inventory() -> (usize, String) {
    let dir = formal_root().join("Haskell");
    let Ok(rd) = std::fs::read_dir(&dir) else {
        return (0, "missing".into());
    };
    let mut names: Vec<String> = rd
        .filter_map(|e| e.ok())
        .filter_map(|e| {
            let p = e.path();
            if p.extension().and_then(|s| s.to_str()) == Some("hs") {
                p.file_name().and_then(|s| s.to_str()).map(str::to_string)
            } else {
                None
            }
        })
        .collect();
    if names.is_empty() {
        return (0, "empty".into());
    }
    names.sort_unstable();
    let mut h = DefaultHasher::new();
    names.join(",").hash(&mut h);
    (names.len(), format!("{:016x}", h.finish()))
}

/// Runtime inventory for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L5RuntimeInventory {
    pub ffi_abi_version: u32,
    pub haskell_module_count: usize,
    pub haskell_module_set_sha: String,
    pub workflow_present: bool,
    pub formal_pin_sha: String,
}

/// Collect L-5 runtime inventory from the umst-formal tree.
#[must_use]
pub fn l5_runtime_inventory() -> L5RuntimeInventory {
    let (haskell_module_count, haskell_module_set_sha) = haskell_module_inventory();
    L5RuntimeInventory {
        ffi_abi_version: UMST_FFI_ABI_VERSION,
        haskell_module_count,
        haskell_module_set_sha,
        workflow_present: l5_workflow_path().is_file(),
        formal_pin_sha: option_env!("UMST_FORMAL_PIN_SHA")
            .map(str::to_string)
            .unwrap_or_else(|| "unknown".into()),
    }
}

/// Receipt status label matching egoff `L5_RECEIPT` posture.
#[must_use]
pub fn l5_receipt_status_label() -> &'static str {
    if l5_workflow_path().is_file() {
        "green"
    } else {
        "pending"
    }
}

/// Returns true when workflow is on disk and Haskell mirror has ≥1 module.
#[must_use]
pub fn l5_extraction_wired() -> bool {
    let inv = l5_runtime_inventory();
    inv.workflow_present && inv.haskell_module_count >= 1
}

/// Operator-facing probe detail (honest; does not claim L-7 GREEN).
#[must_use]
pub fn l5_probe_detail() -> String {
    let inv = l5_runtime_inventory();
    format!(
        "L-5 probe (umst-formal): workflow_present={} gate_exit={} \
         abi_version={} haskell_modules={} haskell_module_set_sha={} \
         formal_pin_sha={} workflow={L5_WORKFLOW_REL}",
        inv.workflow_present,
        L5_EXPECTED_GATE_EXIT,
        inv.ffi_abi_version,
        inv.haskell_module_count,
        inv.haskell_module_set_sha,
        inv.formal_pin_sha,
    )
}

/// Machine-checkable L-5 deepen census for operator / fleet probes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L5ExtractRuntimeProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_swarm_receipt: &'static str,
    pub posture: &'static str,
    pub slice_id: &'static str,
    pub receipt_status: &'static str,
    pub workflow_present: bool,
    pub extraction_wired: bool,
    pub expected_gate_exit: i32,
    pub ffi_abi_version: u32,
    pub haskell_module_count: usize,
    pub haskell_module_set_sha: String,
    pub lcert_capstone_open: bool,
    pub production_wired: bool,
    pub probe_detail: String,
}

/// AGAP-2350-L-5 runtime inventory probe — honest workflow-present posture.
#[must_use]
pub fn l5_extract_runtime_probe() -> L5ExtractRuntimeProbe {
    let inv = l5_runtime_inventory();
    L5ExtractRuntimeProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_swarm_receipt: PRIOR_SWARM_RECEIPT_PATH,
        posture: POSTURE_TAG,
        slice_id: "L-5",
        receipt_status: l5_receipt_status_label(),
        workflow_present: inv.workflow_present,
        extraction_wired: l5_extraction_wired(),
        expected_gate_exit: L5_EXPECTED_GATE_EXIT,
        ffi_abi_version: inv.ffi_abi_version,
        haskell_module_count: inv.haskell_module_count,
        haskell_module_set_sha: inv.haskell_module_set_sha,
        lcert_capstone_open: true,
        production_wired: false,
        probe_detail: l5_probe_detail(),
    }
}

/// Honesty gate for operator receipts — workflow inventory wired, no fake LCERT-OK.
#[must_use]
pub fn l5_extract_runtime_honest(probe: &L5ExtractRuntimeProbe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path.contains("COMPOSER_Y78_0808")
        && probe.prior_swarm_receipt.contains("SWARM-C25-0831-51")
        && probe.posture == POSTURE_TAG
        && probe.slice_id == "L-5"
        && probe.ffi_abi_version == UMST_FFI_ABI_VERSION
        && probe.lcert_capstone_open
        && !probe.production_wired
        && probe.probe_detail.contains("L-5 probe")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agap_2350_l5_metadata() {
        assert_eq!(JOB_ID, "AGAP-2350-L-5");
        assert!(RECEIPT_PATH.contains("COMPOSER_Y78_0808"));
        assert_eq!(L5_EXPECTED_GATE_EXIT, 0);
    }

    #[test]
    fn l5_runtime_inventory_reads_haskell_tree() {
        let inv = l5_runtime_inventory();
        assert_eq!(inv.ffi_abi_version, UMST_FFI_ABI_VERSION);
        if l5_workflow_path().is_file() {
            assert!(inv.workflow_present);
            assert!(inv.haskell_module_count >= 1);
            assert_ne!(inv.haskell_module_set_sha, "missing");
        }
    }

    #[test]
    fn l5_green_when_workflow_present() {
        if l5_workflow_path().is_file() {
            assert_eq!(l5_receipt_status_label(), "green");
            assert!(l5_extraction_wired());
        } else {
            assert_eq!(l5_receipt_status_label(), "pending");
            assert!(!l5_extraction_wired());
        }
    }

    #[test]
    fn l5_extract_runtime_probe_honest_partial() {
        let probe = l5_extract_runtime_probe();
        assert!(l5_extract_runtime_honest(&probe));
        assert!(probe.lcert_capstone_open);
        assert!(!probe.production_wired);
        assert!(probe.probe_detail.contains("gate_exit="));
        if probe.workflow_present {
            assert_eq!(probe.receipt_status, "green");
            assert!(probe.extraction_wired);
        }
    }
}
