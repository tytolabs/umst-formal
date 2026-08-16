// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-G AC152 — PBM-011 substrate test deepen honest witness.
// PENDING_GAPS §B8: sustain `hardware_substrate_green=false` without invent GREEN.
// File-based census (no umst-hal / umst-bench dep — AC134 scaffold owns Cargo.toml).
// Absorbs AC56 HAL owner deepen + Z94 bench consumer + Z15/Z15 chain without re-census.
//
// Doctrine by ref: AC56 · Z94 · Z15 · Y61 receipts + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-G slot id.
pub const AC152_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC152-PBM-011";

/// AC152 completion receipt cross-ref.
pub const AC152_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC152.md";

/// AC56 HAL owner deepen receipt — absorbed, not re-census.
pub const PRIOR_AC56_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC56.md";

/// Z94 bench consumer witness receipt — software census close.
pub const PRIOR_Z94_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z94_1232.md";

/// Z15 HAL full-discovery close receipt.
pub const PRIOR_Z15_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z15_0928.md";

/// Y61 X66-absorb receipt.
pub const PRIOR_Y61_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y61_0808.md";

/// PENDING_GAPS §B8 sustain slice source.
pub const PENDING_GAPS_PATH: &str = "outputs/.tmp/PENDING_GAPS_COMPOSITIONAL_2134.md";

/// HAL hardware substrate owner surface @ AC56.
pub const HAL_OWNER_SURFACE: &str = "umst-hal/crates/umst-hal/src/hardware_substrate.rs";

/// Bench consumer witness surface @ Z94.
pub const BENCH_CONSUMER_SURFACE: &str = "crates/umst-bench/src/pbm_011_hal_full_substrate.rs";

/// Frozen posture pins fixture.
pub const POSTURE_FIXTURE_PATH: &str =
    "crates/umst-bench/fixtures/pbm_011_hal_full_substrate_posture.json";

/// HAL integration witness @ AC56.
pub const HAL_INTEGRATION_TEST_PATH: &str =
    "umst-hal/crates/umst-hal/tests/hardware_substrate_ac56.rs";

/// Bench integration witness @ Z94.
pub const BENCH_INTEGRATION_TEST_PATH: &str = "crates/umst-bench/tests/pbm_011_hal_full_substrate.rs";

/// PBM-011 workstream id.
pub const WORKSTREAM_ID: &str = "WS-hal-full-substrate";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-011";

/// Honest substrate posture @ AC152 (matches AC56 / Z94 tier).
pub const POSTURE_TAG: &str = "honest-partial";

/// Frozen §5 unit total @ blueprint.
pub const TOTAL_UNIT_COUNT: u8 = 19;

/// HAL owner wire map hop count @ AC56 deepen.
pub const HAL_FENCE_HOP_COUNT: u8 = 5;

/// Bench consumer wire map hop count @ Z94.
pub const BENCH_FENCE_HOP_COUNT: u8 = 4;

/// Open hardware-tier residue count @ AC152 — EGOFF-H10 + POSTH-01.
pub const OPEN_RESIDUE_COUNT: u8 = 2;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm011SubstrateResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC152 — hardware tier only (software census CLOSE).
pub const PBM011_SUBSTRATE_RESIDUE_LEDGER: [Pbm011SubstrateResidue; OPEN_RESIDUE_COUNT as usize] =
    [
        Pbm011SubstrateResidue {
            residue_id: "egoff_h10_paired_backends",
            blocker: "umst-hal/crates/umst-hal/src/substrate/discover.rs::probe_substrate_unit \
                      Unchecked→honest delegate via EGOFF-H10",
            owner: "operator",
            closed: false,
        },
        Pbm011SubstrateResidue {
            residue_id: "posth_01_hw_cert_paired",
            blocker: "egoff-cli POSTH-01 `:hw-cert --strict --paired` exit 0 ceremony",
            owner: "operator",
            closed: false,
        },
    ];

#[must_use]
pub fn workspace_root() -> PathBuf {
    let start = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut cur = start.clone();
    loop {
        if cur.join("scripts/gen-residue-ledger.sh").exists() {
            return cur;
        }
        if !cur.pop() {
            break;
        }
    }
    start
}

#[must_use]
pub fn workspace_file_on_disk(root: &Path, rel: &str) -> bool {
    root.join(rel).is_file()
}

#[must_use]
pub fn read_workspace_file(root: &Path, rel: &str) -> Option<String> {
    fs::read_to_string(root.join(rel)).ok()
}

/// Census: HAL owner declares `hardware_substrate_green() -> false` (Op-6 fence).
#[must_use]
pub fn hardware_substrate_green_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn hardware_substrate_green() -> bool")
        && src.contains("false")
        && !src.contains("hardware_substrate_green() -> bool {\n    true")
}

/// Census: HAL owner declares production wired / e2e green false.
#[must_use]
pub fn hardware_substrate_production_flags_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn hardware_substrate_production_wired() -> bool")
        && src.contains("pub const fn hardware_substrate_e2e_green() -> bool")
        && !src.contains("hardware_substrate_production_wired() -> bool {\n    true")
        && !src.contains("hardware_substrate_e2e_green() -> bool {\n    true")
}

/// Census: HAL owner five-hop wire map @ AC56 deepen.
#[must_use]
pub fn hardware_substrate_fence_hops_five_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const HARDWARE_SUBSTRATE_FENCE_HOPS")
        && src.contains("hop_id: \"HS4\"")
        && src.contains("hardware_substrate_ac56_deepen_honest")
        && src.contains("HARDWARE_SUBSTRATE_FENCE_HOPS.len() == 5")
}

/// Census: HAL done-when pins master retick false.
#[must_use]
pub fn hardware_substrate_master_retick_blocked_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("master_retick_eligible: false")
        && src.contains("hardware_substrate_done_when_probe")
}

/// Census: bench consumer declares `pbm_011_hardware_substrate_green() -> false`.
#[must_use]
pub fn pbm_011_hardware_substrate_green_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn pbm_011_hardware_substrate_green() -> bool")
        && src.contains("false")
        && !src.contains("pbm_011_hardware_substrate_green() -> bool {\n    true")
}

/// Census: bench consumer declares fully_closed / production_wired false.
#[must_use]
pub fn pbm_011_production_flags_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn pbm_011_fully_closed() -> bool")
        && src.contains("pub const fn pbm_011_production_wired() -> bool")
        && !src.contains("pbm_011_fully_closed() -> bool {\n    true")
        && !src.contains("pbm_011_production_wired() -> bool {\n    true")
}

/// Census: bench four-hop wire map @ Z94.
#[must_use]
pub fn pbm_011_bench_fence_hops_four_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const HAL_SUBSTRATE_FENCE_HOPS")
        && src.contains("hop_id: \"HS3\"")
        && src.contains("HAL_SUBSTRATE_FENCE_HOPS.len() == 4")
}

/// Census: posture fixture pins honest GREEN=false · trusted=0.
#[must_use]
pub fn pbm_011_posture_fixture_honest(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, POSTURE_FIXTURE_PATH) else {
        return false;
    };
    raw.contains("\"pbm_owner\": \"PBM-011\"")
        && raw.contains("\"workstream_id\": \"WS-hal-full-substrate\"")
        && raw.contains("\"hardware_substrate_green\": false")
        && raw.contains("\"production_wired\": false")
        && raw.contains("\"trusted_for_actuation\": 0")
        && raw.contains("\"total_unit_count\": 19")
        && raw.contains("software census close ≠ hardware substrate GREEN")
}

#[must_use]
pub fn pbm_011_substrate_residue_ledger_honest() -> bool {
    PBM011_SUBSTRATE_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM011_SUBSTRATE_RESIDUE_LEDGER.len() == OPEN_RESIDUE_COUNT as usize
}

/// AC152 substrate census — GREEN=false sustain; software census chain on disk.
#[must_use]
pub fn pbm_011_substrate_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && hardware_substrate_green_declared_false(root)
        && hardware_substrate_production_flags_declared_false(root)
        && hardware_substrate_fence_hops_five_on_disk(root)
        && hardware_substrate_master_retick_blocked_on_disk(root)
        && pbm_011_hardware_substrate_green_declared_false(root)
        && pbm_011_production_flags_declared_false(root)
        && pbm_011_bench_fence_hops_four_on_disk(root)
        && pbm_011_posture_fixture_honest(root)
        && pbm_011_substrate_residue_ledger_honest()
        && workspace_file_on_disk(root, HAL_INTEGRATION_TEST_PATH)
        && workspace_file_on_disk(root, BENCH_INTEGRATION_TEST_PATH)
}

/// Prior receipt chain absorption — AC56 + Z94 + Z15 + Y61.
#[must_use]
pub fn pbm_011_prior_chain_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_AC56_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_Z94_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_Z15_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_Y61_RECEIPT_PATH)
}

/// PENDING_GAPS §B8 row pins GREEN=false sustain.
#[must_use]
pub fn pbm_011_pending_gaps_sustain_honest(root: &Path) -> bool {
    let Some(gaps) = read_workspace_file(root, PENDING_GAPS_PATH) else {
        return false;
    };
    gaps.contains("PBM-011 substrate")
        && gaps.contains("GREEN=false")
        && gaps.contains("AC56 RESIDUE")
}

/// AC152 honest gate — chains prior receipts + on-disk owner census.
#[must_use]
pub fn pbm_011_ac152_substrate_honest(root: &Path) -> bool {
    pbm_011_substrate_census_honest(root)
        && pbm_011_prior_chain_absorbed(root)
        && pbm_011_pending_gaps_sustain_honest(root)
}

#[test]
fn pbm011_hardware_substrate_green_declared_false_on_disk() {
    let root = workspace_root();
    assert!(
        hardware_substrate_green_declared_false(&root),
        "HAL owner must declare hardware_substrate_green() -> false"
    );
    assert!(hardware_substrate_production_flags_declared_false(&root));
}

#[test]
fn pbm011_hal_fence_hops_five_wired_on_disk() {
    let root = workspace_root();
    assert!(hardware_substrate_fence_hops_five_on_disk(&root));
    assert_eq!(HAL_FENCE_HOP_COUNT, 5);
}

#[test]
fn pbm011_bench_consumer_green_declared_false_on_disk() {
    let root = workspace_root();
    assert!(pbm_011_hardware_substrate_green_declared_false(&root));
    assert!(pbm_011_production_flags_declared_false(&root));
    assert!(pbm_011_bench_fence_hops_four_on_disk(&root));
    assert_eq!(BENCH_FENCE_HOP_COUNT, 4);
}

#[test]
fn pbm011_posture_fixture_pins_honest() {
    let root = workspace_root();
    assert!(pbm_011_posture_fixture_honest(&root));
    assert_eq!(TOTAL_UNIT_COUNT, 19);
}

#[test]
fn pbm011_substrate_residue_ledger_open() {
    assert!(pbm_011_substrate_residue_ledger_honest());
    for entry in &PBM011_SUBSTRATE_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm011_master_retick_blocked_on_disk() {
    let root = workspace_root();
    assert!(hardware_substrate_master_retick_blocked_on_disk(&root));
    let Some(ac56) = read_workspace_file(&root, PRIOR_AC56_RECEIPT_PATH) else {
        panic!("AC56 receipt must exist");
    };
    assert!(ac56.contains("MASTER_RETICK") && ac56.contains("no"));
    assert!(ac56.contains("hardware_substrate_green=false"));
}

#[test]
fn pbm011_ac56_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, PRIOR_AC56_RECEIPT_PATH));
    let ac56 = read_workspace_file(&root, PRIOR_AC56_RECEIPT_PATH).expect("AC56 receipt");
    assert!(ac56.contains("PBM-011"));
    assert!(ac56.contains("hardware_substrate"));
    assert!(ac56.contains("CLOSE"));
    assert!(workspace_file_on_disk(&root, HAL_OWNER_SURFACE));
}

#[test]
fn pbm011_z94_z15_y61_chain_absorbed() {
    let root = workspace_root();
    assert!(pbm_011_prior_chain_absorbed(&root));
    let z94 = read_workspace_file(&root, PRIOR_Z94_RECEIPT_PATH).expect("Z94 receipt");
    assert!(z94.contains("PBM-011"));
    assert!(z94.contains("hardware_substrate_green=false"));
    let z15 = read_workspace_file(&root, PRIOR_Z15_RECEIPT_PATH).expect("Z15 receipt");
    assert!(z15.contains("PBM-011"));
    let y61 = read_workspace_file(&root, PRIOR_Y61_RECEIPT_PATH).expect("Y61 receipt");
    assert!(y61.contains("PBM-011") || y61.contains("substrate"));
}

#[test]
fn pbm011_owner_surfaces_no_green_invent() {
    let root = workspace_root();
    let hal = read_workspace_file(&root, HAL_OWNER_SURFACE).expect("HAL owner");
    assert!(!hal.contains("hardware_substrate_green() -> bool {\n    true"));
    let bench = read_workspace_file(&root, BENCH_CONSUMER_SURFACE).expect("bench consumer");
    assert!(!bench.contains("pbm_011_hardware_substrate_green() -> bool {\n    true"));
    assert!(!bench.contains("pbm_011_fully_closed() -> bool {\n    true"));
}

#[test]
fn pbm011_pending_gaps_sustain_row() {
    let root = workspace_root();
    assert!(pbm_011_pending_gaps_sustain_honest(&root));
}

#[test]
fn pbm011_substrate_census_honest() {
    let root = workspace_root();
    assert!(pbm_011_substrate_census_honest(&root));
}

#[test]
fn fleet_composer_accel2_ac152_pbm011_substrate_honest() {
    assert_eq!(AC152_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC152-PBM-011");
    assert_eq!(AC152_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC152.md");
    assert_eq!(WORKSTREAM_ID, "WS-hal-full-substrate");
    assert_eq!(PBM_OWNER, "PBM-011");
    assert_eq!(POSTURE_TAG, "honest-partial");
    let root = workspace_root();
    assert!(pbm_011_ac152_substrate_honest(&root));
}
