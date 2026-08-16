// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-K AC346 — PBM-011 substrate deepen v2 honest witness.
// PENDING_GAPS §B8: sustain `hardware_substrate_green=false` without invent GREEN.
// File-based census (no umst-hal / umst-bench dep — AC134 scaffold owns Cargo.toml).
// Absorbs AC152 v1 (`pbm011_substrate.rs`) + AC56/Z94/Z15/Y61 chain without re-census.
//
// Doctrine by ref: AC152 · AC56 · Z94 · Z15 · Y61 receipts + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-K slot id.
pub const AC346_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC346-PBM-011";

/// AC346 completion receipt cross-ref.
pub const AC346_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC346.md";

/// AC346 scratch target dir.
pub const AC346_SCRATCH_TARGET: &str = "/tmp/umst-accel2-ac346-pbm011";

/// AC152 v1 substrate witness receipt — absorbed, not re-census.
pub const PRIOR_AC152_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC152.md";

/// AC152 v1 test artifact path.
pub const PRIOR_AC152_TEST_PATH: &str = "umst-pbm/tests/pbm011_substrate.rs";

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

/// HAL discover probe surface — EGOFF-H10 next hop.
pub const HAL_DISCOVER_SURFACE: &str = "umst-hal/crates/umst-hal/src/substrate/discover.rs";

/// HAL posture surface @ Z15 close.
pub const HAL_POSTURE_SURFACE: &str = "umst-hal/crates/umst-hal/src/substrate/posture.rs";

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

/// Honest substrate posture @ AC346 v2 deepen (matches AC152 / AC56 / Z94 tier).
pub const POSTURE_TAG: &str = "substrate-deepen-v2-honest-partial";

/// Frozen §5 unit total @ blueprint.
pub const TOTAL_UNIT_COUNT: u8 = 19;

/// HAL owner wire map hop count @ AC56 deepen.
pub const HAL_FENCE_HOP_COUNT: u8 = 5;

/// Bench consumer wire map hop count @ Z94.
pub const BENCH_FENCE_HOP_COUNT: u8 = 4;

/// HAL fence hop ids @ AC56 deepen (HS0..HS4).
pub const HAL_FENCE_HOP_IDS: [&str; 5] = ["HS0", "HS1", "HS2", "HS3", "HS4"];

/// Bench fence hop ids @ Z94 (HS0..HS3).
pub const BENCH_FENCE_HOP_IDS: [&str; 4] = ["HS0", "HS1", "HS2", "HS3"];

/// Open hardware-tier residue count @ AC346 — EGOFF-H10 + POSTH-01.
pub const OPEN_RESIDUE_COUNT: u8 = 2;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm011V2SubstrateResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC346 — hardware tier only (software census CLOSE).
pub const PBM011_V2_SUBSTRATE_RESIDUE_LEDGER: [Pbm011V2SubstrateResidue; OPEN_RESIDUE_COUNT as usize] =
    [
        Pbm011V2SubstrateResidue {
            residue_id: "egoff_h10_paired_backends",
            blocker: "umst-hal/crates/umst-hal/src/substrate/discover.rs::probe_substrate_unit \
                      Unchecked→honest delegate via EGOFF-H10",
            owner: "operator",
            closed: false,
        },
        Pbm011V2SubstrateResidue {
            residue_id: "posth_01_hw_cert_paired",
            blocker: "egoff-cli POSTH-01 `:hw-cert --strict --paired` exit 0 ceremony",
            owner: "operator",
            closed: false,
        },
    ];

/// AC346 v2 deepen probe rollup — file-based census only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm011V2SubstrateProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub scratch_target: &'static str,
    pub posture_tag: &'static str,
    pub ac152_absorbed: bool,
    pub ac56_absorbed: bool,
    pub z94_chain_on_disk: bool,
    pub hardware_residual_on_disk: bool,
    pub done_when_on_disk: bool,
    pub probe_invariant_on_disk: bool,
    pub discover_probe_wired: bool,
    pub posture_full_discovery_wired: bool,
    pub hal_fence_hops_complete: bool,
    pub bench_fence_hops_complete: bool,
    pub hardware_substrate_green_false: bool,
    pub production_wired_false: bool,
    pub master_retick_blocked: bool,
    pub open_residue_count: u8,
}

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

/// Census: HAL owner five-hop wire map @ AC56 deepen with complete HS0..HS4 ladder.
#[must_use]
pub fn hardware_substrate_fence_hops_five_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const HARDWARE_SUBSTRATE_FENCE_HOPS")
        && HAL_FENCE_HOP_IDS.iter().all(|id| src.contains(&format!("hop_id: \"{id}\"")))
        && src.contains("hardware_substrate_ac56_deepen_honest")
        && src.contains("HARDWARE_SUBSTRATE_FENCE_HOPS.len() == 5")
}

/// Census: HAL z94 chain witness wired on disk.
#[must_use]
pub fn hardware_substrate_z94_chain_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub fn hardware_substrate_z94_chain_honest()")
        && src.contains("pbm_011_hal_full_substrate")
        && src.contains("!probe.hardware_substrate_green")
}

/// Census: HAL hardware residual witness wired on disk.
#[must_use]
pub fn hardware_substrate_hardware_residual_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub fn hardware_substrate_hardware_residual_honest()")
        && src.contains("probe.egoff_h10_open")
        && src.contains("probe.posth_01_open")
        && src.contains("NEXT_HOP_SURFACE.contains(\"probe_substrate_unit\")")
}

/// Census: HAL done-when probe wired on disk.
#[must_use]
pub fn hardware_substrate_done_when_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub fn hardware_substrate_done_when_probe()")
        && src.contains("master_retick_eligible: false")
        && src.contains("software_census_closed")
}

/// Census: HAL probe invariant wired on disk.
#[must_use]
pub fn hardware_substrate_probe_invariant_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub fn hardware_substrate_probe_invariant_honest()")
        && src.contains("probe_substrate_unit(unit_id)")
        && src.contains("!presence.is_trusted_for_actuation()")
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

/// Census: discover.rs probe_substrate_unit wired (EGOFF-H10 next hop).
#[must_use]
pub fn discover_probe_substrate_unit_wired(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_DISCOVER_SURFACE) else {
        return false;
    };
    src.contains("pub fn probe_substrate_unit(unit_id: SubstrateUnitId) -> UnitPresence")
        && src.contains("pub fn discover_laptop_substrate() -> SubstrateDiscoverResult")
        && src.contains("UnitPresence::Unchecked")
}

/// Census: posture.rs full-discovery close wired.
#[must_use]
pub fn posture_full_discovery_wired(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, HAL_POSTURE_SURFACE) else {
        return false;
    };
    src.contains("pub fn pbm_011_full_discovery_measured()")
        && src.contains("pub fn pbm_011_y61_x66_absorb_honest()")
        && src.contains("WORKSTREAM_ID")
        && src.contains("WS-hal-full-substrate")
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

/// Census: bench four-hop wire map @ Z94 with complete HS0..HS3 ladder.
#[must_use]
pub fn pbm_011_bench_fence_hops_four_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const HAL_SUBSTRATE_FENCE_HOPS")
        && BENCH_FENCE_HOP_IDS
            .iter()
            .all(|id| src.contains(&format!("hop_id: \"{id}\"")))
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
pub fn pbm_011_v2_substrate_residue_ledger_honest() -> bool {
    PBM011_V2_SUBSTRATE_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM011_V2_SUBSTRATE_RESIDUE_LEDGER.len() == OPEN_RESIDUE_COUNT as usize
}

/// AC152 v1 receipt + test artifact absorbed.
#[must_use]
pub fn pbm_011_ac152_v1_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_AC152_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_AC152_TEST_PATH)
        && read_workspace_file(root, PRIOR_AC152_RECEIPT_PATH)
            .is_some_and(|r| r.contains("AC152") && r.contains("PBM-011"))
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

/// Build AC346 v2 deepen probe from on-disk census.
#[must_use]
pub fn pbm_011_v2_substrate_probe(root: &Path) -> Pbm011V2SubstrateProbe {
    Pbm011V2SubstrateProbe {
        job_id: AC346_JOB_ID,
        receipt_path: AC346_RECEIPT_PATH,
        scratch_target: AC346_SCRATCH_TARGET,
        posture_tag: POSTURE_TAG,
        ac152_absorbed: pbm_011_ac152_v1_absorbed(root),
        ac56_absorbed: workspace_file_on_disk(root, PRIOR_AC56_RECEIPT_PATH),
        z94_chain_on_disk: hardware_substrate_z94_chain_on_disk(root),
        hardware_residual_on_disk: hardware_substrate_hardware_residual_on_disk(root),
        done_when_on_disk: hardware_substrate_done_when_on_disk(root),
        probe_invariant_on_disk: hardware_substrate_probe_invariant_on_disk(root),
        discover_probe_wired: discover_probe_substrate_unit_wired(root),
        posture_full_discovery_wired: posture_full_discovery_wired(root),
        hal_fence_hops_complete: hardware_substrate_fence_hops_five_on_disk(root),
        bench_fence_hops_complete: pbm_011_bench_fence_hops_four_on_disk(root),
        hardware_substrate_green_false: hardware_substrate_green_declared_false(root),
        production_wired_false: hardware_substrate_production_flags_declared_false(root)
            && pbm_011_production_flags_declared_false(root),
        master_retick_blocked: hardware_substrate_master_retick_blocked_on_disk(root),
        open_residue_count: OPEN_RESIDUE_COUNT,
    }
}

/// AC346 v2 substrate census — GREEN=false sustain; deepened owner chain on disk.
#[must_use]
pub fn pbm_011_v2_substrate_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "substrate-deepen-v2-honest-partial"
        && hardware_substrate_green_declared_false(root)
        && hardware_substrate_production_flags_declared_false(root)
        && hardware_substrate_fence_hops_five_on_disk(root)
        && hardware_substrate_z94_chain_on_disk(root)
        && hardware_substrate_hardware_residual_on_disk(root)
        && hardware_substrate_done_when_on_disk(root)
        && hardware_substrate_probe_invariant_on_disk(root)
        && hardware_substrate_master_retick_blocked_on_disk(root)
        && discover_probe_substrate_unit_wired(root)
        && posture_full_discovery_wired(root)
        && pbm_011_hardware_substrate_green_declared_false(root)
        && pbm_011_production_flags_declared_false(root)
        && pbm_011_bench_fence_hops_four_on_disk(root)
        && pbm_011_posture_fixture_honest(root)
        && pbm_011_v2_substrate_residue_ledger_honest()
        && workspace_file_on_disk(root, HAL_INTEGRATION_TEST_PATH)
        && workspace_file_on_disk(root, BENCH_INTEGRATION_TEST_PATH)
}

/// AC346 honest gate — chains AC152 v1 + prior receipts + deepened on-disk census.
#[must_use]
pub fn pbm_011_ac346_v2_substrate_honest(root: &Path) -> bool {
    let probe = pbm_011_v2_substrate_probe(root);
    pbm_011_v2_substrate_census_honest(root)
        && probe.ac152_absorbed
        && probe.ac56_absorbed
        && pbm_011_prior_chain_absorbed(root)
        && pbm_011_pending_gaps_sustain_honest(root)
        && probe.z94_chain_on_disk
        && probe.hardware_residual_on_disk
        && probe.done_when_on_disk
        && probe.probe_invariant_on_disk
        && probe.discover_probe_wired
        && probe.posture_full_discovery_wired
        && probe.hal_fence_hops_complete
        && probe.bench_fence_hops_complete
        && probe.hardware_substrate_green_false
        && probe.production_wired_false
        && probe.master_retick_blocked
        && probe.open_residue_count == OPEN_RESIDUE_COUNT
}

#[test]
fn pbm011_v2_job_metadata_pins() {
    assert_eq!(AC346_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC346-PBM-011");
    assert_eq!(AC346_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC346.md");
    assert_eq!(AC346_SCRATCH_TARGET, "/tmp/umst-accel2-ac346-pbm011");
    assert_eq!(WORKSTREAM_ID, "WS-hal-full-substrate");
    assert_eq!(PBM_OWNER, "PBM-011");
    assert_eq!(POSTURE_TAG, "substrate-deepen-v2-honest-partial");
    assert_eq!(HAL_FENCE_HOP_COUNT, 5);
    assert_eq!(BENCH_FENCE_HOP_COUNT, 4);
    assert_eq!(TOTAL_UNIT_COUNT, 19);
}

#[test]
fn pbm011_v2_ac152_v1_absorbed() {
    let root = workspace_root();
    assert!(pbm_011_ac152_v1_absorbed(&root));
    let ac152 = read_workspace_file(&root, PRIOR_AC152_RECEIPT_PATH).expect("AC152 receipt");
    assert!(ac152.contains("MASTER_RETICK") && ac152.contains("no"));
    assert!(ac152.contains("hardware_substrate_green=false") || ac152.contains("GREEN=false"));
    let v1 = read_workspace_file(&root, PRIOR_AC152_TEST_PATH).expect("AC152 v1 test");
    assert!(v1.contains("AC152_JOB_ID"));
    assert!(v1.contains("pbm_011_ac152_substrate_honest"));
}

#[test]
fn pbm011_v2_hal_deepen_surfaces_on_disk() {
    let root = workspace_root();
    assert!(hardware_substrate_z94_chain_on_disk(&root));
    assert!(hardware_substrate_hardware_residual_on_disk(&root));
    assert!(hardware_substrate_done_when_on_disk(&root));
    assert!(hardware_substrate_probe_invariant_on_disk(&root));
    assert!(discover_probe_substrate_unit_wired(&root));
    assert!(posture_full_discovery_wired(&root));
}

#[test]
fn pbm011_v2_hal_fence_hops_complete_ladder() {
    let root = workspace_root();
    assert!(hardware_substrate_fence_hops_five_on_disk(&root));
    let hal = read_workspace_file(&root, HAL_OWNER_SURFACE).expect("HAL owner");
    for hop in &HAL_FENCE_HOP_IDS {
        assert!(hal.contains(&format!("hop_id: \"{hop}\"")), "missing hop {hop}");
    }
}

#[test]
fn pbm011_v2_bench_fence_hops_complete_ladder() {
    let root = workspace_root();
    assert!(pbm_011_bench_fence_hops_four_on_disk(&root));
    let bench = read_workspace_file(&root, BENCH_CONSUMER_SURFACE).expect("bench consumer");
    for hop in &BENCH_FENCE_HOP_IDS {
        assert!(
            bench.contains(&format!("hop_id: \"{hop}\"")),
            "missing hop {hop}"
        );
    }
}

#[test]
fn pbm011_v2_hardware_substrate_green_declared_false_on_disk() {
    let root = workspace_root();
    assert!(
        hardware_substrate_green_declared_false(&root),
        "HAL owner must declare hardware_substrate_green() -> false"
    );
    assert!(hardware_substrate_production_flags_declared_false(&root));
    assert!(pbm_011_hardware_substrate_green_declared_false(&root));
    assert!(pbm_011_production_flags_declared_false(&root));
}

#[test]
fn pbm011_v2_posture_fixture_pins_honest() {
    let root = workspace_root();
    assert!(pbm_011_posture_fixture_honest(&root));
}

#[test]
fn pbm011_v2_substrate_residue_ledger_open() {
    assert!(pbm_011_v2_substrate_residue_ledger_honest());
    for entry in &PBM011_V2_SUBSTRATE_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm011_v2_master_retick_blocked_on_disk() {
    let root = workspace_root();
    assert!(hardware_substrate_master_retick_blocked_on_disk(&root));
    let ac56 = read_workspace_file(&root, PRIOR_AC56_RECEIPT_PATH).expect("AC56 receipt");
    assert!(ac56.contains("MASTER_RETICK") && ac56.contains("no"));
}

#[test]
fn pbm011_v2_prior_chain_absorbed() {
    let root = workspace_root();
    assert!(pbm_011_prior_chain_absorbed(&root));
    let z94 = read_workspace_file(&root, PRIOR_Z94_RECEIPT_PATH).expect("Z94 receipt");
    assert!(z94.contains("PBM-011"));
    assert!(z94.contains("hardware_substrate_green=false"));
}

#[test]
fn pbm011_v2_owner_surfaces_no_green_invent() {
    let root = workspace_root();
    let hal = read_workspace_file(&root, HAL_OWNER_SURFACE).expect("HAL owner");
    assert!(!hal.contains("hardware_substrate_green() -> bool {\n    true"));
    let bench = read_workspace_file(&root, BENCH_CONSUMER_SURFACE).expect("bench consumer");
    assert!(!bench.contains("pbm_011_hardware_substrate_green() -> bool {\n    true"));
    assert!(!bench.contains("pbm_011_fully_closed() -> bool {\n    true"));
}

#[test]
fn pbm011_v2_pending_gaps_sustain_row() {
    let root = workspace_root();
    assert!(pbm_011_pending_gaps_sustain_honest(&root));
}

#[test]
fn pbm011_v2_substrate_census_honest() {
    let root = workspace_root();
    assert!(pbm_011_v2_substrate_census_honest(&root));
}

#[test]
fn pbm011_v2_probe_rollup_honest() {
    let root = workspace_root();
    let probe = pbm_011_v2_substrate_probe(&root);
    assert_eq!(probe.job_id, AC346_JOB_ID);
    assert!(probe.ac152_absorbed);
    assert!(probe.ac56_absorbed);
    assert!(probe.z94_chain_on_disk);
    assert!(probe.hardware_residual_on_disk);
    assert!(probe.done_when_on_disk);
    assert!(probe.probe_invariant_on_disk);
    assert!(probe.hardware_substrate_green_false);
    assert!(probe.production_wired_false);
    assert!(probe.master_retick_blocked);
}

#[test]
fn fleet_composer_accel2_ac346_pbm011_v2_substrate_honest() {
    let root = workspace_root();
    assert!(pbm_011_ac346_v2_substrate_honest(&root));
}
