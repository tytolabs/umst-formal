// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL-K AC345 — PBM-006 measure slice test.
// PENDING_GAPS §B8: honest witness that measure-only lane may be closed while
// `pbm_006_fully_closed()==false`. File-based census (no umst-meta dep — AC134
// scaffold owns Cargo.toml). Does **not** invent INV4 4/4, O4 PASS, O5 flip,
// `production_energy_wired`, or master retick.
//
// Absorbs AC133 fully_closed measure census + Z42/Z99 measure-only CLOSE without re-census.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-K slot id.
pub const AC345_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC345-PBM-006";

/// AC345 completion receipt cross-ref.
pub const AC345_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC345.md";

/// AC133 prior measure slice census receipt — absorbed, not re-census.
pub const PRIOR_AC133_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC133.md";

/// PENDING_GAPS §B8 source.
pub const PENDING_GAPS_PATH: &str = "outputs/.tmp/PENDING_GAPS_COMPOSITIONAL_2134.md";

/// Meta owner witness surface.
pub const META_OWNER_PATH: &str = "crates/umst-meta/src/meta_pbm_006_ws_inv4_energy.rs";

/// Bench consumer witness surface.
pub const BENCH_CONSUMER_PATH: &str = "crates/umst-bench/src/pbm_006_ws_inv4_energy.rs";

/// Frozen posture fixture.
pub const POSTURE_FIXTURE_PATH: &str =
    "crates/umst-bench/fixtures/pbm_006_ws_inv4_energy_posture.json";

/// Live measure artifact.
pub const MEASURE_ARTIFACT_PATH: &str = "artifacts/benchmarks/inv4_energy_measured.json";

/// Live measure ingest receipt (operator sudo ceremony).
pub const LIVE_INGEST_RECEIPT_PATH: &str = "outputs/.tmp/INV4_MEASURE_LIVE_INGEST_0808.md";

/// Z42 measure-only CLOSE receipt — absorbed.
pub const Z42_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z42_1015.md";

/// Z99 measure-only re-confirm receipt — absorbed.
pub const Z99_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z99_1232.md";

/// INV4 presence probe bin surface.
pub const INV4_PRESENCE_PROBE_BIN: &str =
    "crates/umst-bench/src/bin/inv4_energy_presence_probe.rs";

/// PBM-006 workstream id.
pub const WORKSTREAM_ID: &str = "WS-inv4-energy";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-006";

/// Honest measure-slice posture @ AC345.
pub const MEASURE_SLICE_POSTURE_TAG: &str = "honest-partial";

/// Honest INV4 aggregate @ measure slice.
pub const INV4_AGGREGATE: &str = "3/4";

/// Honest INV4 sat count — do not invent 4.
pub const INV4_HONEST_SAT_COUNT: u8 = 3;

/// INV4 energy fence hop count @ Y57 deepen.
pub const FENCE_HOP_COUNT: u8 = 5;

/// Probe-wired hops @ Y57 — IE0..IE3 only (O5 flip stays open).
pub const PROBE_HOPS_WIRED: u8 = 4;

/// Measure fence hop id (IE1).
pub const MEASURE_FENCE_HOP_ID: &str = "IE1";

/// Open ceremony hops blocking full close.
pub const OPEN_CEREMONY_HOP_COUNT: u8 = 2;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm006MeasureSliceResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC345 — O4 calibrate + O5 flip ceremony only.
pub const PBM006_MEASURE_SLICE_RESIDUE_LEDGER: [Pbm006MeasureSliceResidue;
    OPEN_CEREMONY_HOP_COUNT as usize] = [
    Pbm006MeasureSliceResidue {
        residue_id: "o4_calibrate_pass",
        blocker: "crates/umst-bench/src/residual.rs::calibrate_o4 PENDING (operator O1+O2)",
        owner: "operator",
        closed: false,
    },
    Pbm006MeasureSliceResidue {
        residue_id: "o5_flip_ceremony",
        blocker: "docs/INV4_O5_FLIP_RECEIPT.template.md OPEN (operator ceremony)",
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

/// Census: bench posture fixture pins honest measure slice fields.
#[must_use]
pub fn pbm_006_measure_posture_fixture_honest(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, POSTURE_FIXTURE_PATH) else {
        return false;
    };
    raw.contains("\"pbm_owner\": \"PBM-006\"")
        && raw.contains("\"workstream_id\": \"WS-inv4-energy\"")
        && raw.contains("\"inv4_honest_sat_count\": 3")
        && raw.contains("\"inv4_aggregate\": \"3/4\"")
        && raw.contains("\"v_inv4_flip_authorized\": false")
        && raw.contains("\"production_energy_wired\": false")
        && raw.contains("\"production_hops_earned\": 0")
        && raw.contains("\"probe_hops_wired\": 4")
        && raw.contains("\"fence_hop_count\": 5")
        && raw.contains(MEASURE_ARTIFACT_PATH)
        && raw.contains("measure landing does not authorize v_inv4_flip_authorized")
}

/// Census: measure artifact landed with honest fields (string probe — no extra deps).
#[must_use]
pub fn pbm_006_measure_artifact_honest(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, MEASURE_ARTIFACT_PATH) else {
        return false;
    };
    raw.contains("\"inv4_aggregate\": \"3/4\"")
        && raw.contains("\"inv4_honest_sat_count\": 3")
        && raw.contains("\"v_inv4_flip_authorized\": false")
        && raw.contains("\"presence\": \"Here\"")
        && raw.contains("\"kj_per_result\":")
        && raw.contains("\"sample_count\":")
        && raw.contains("\"schema_version\": \"inv4_energy_measured_v0\"")
}

/// Census: bench consumer declares measure-only close hook on disk.
#[must_use]
pub fn pbm_006_bench_measure_only_hook_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_PATH) else {
        return false;
    };
    src.contains("pub fn pbm_006_energy_measure_only_closed")
        && src.contains("pub fn pbm_006_measure_ingest_snapshot")
        && src.contains("INV4_ENERGY_FENCE_HOPS")
        && src.contains("pub const fn pbm_006_fully_closed() -> bool")
        && !src.contains("pbm_006_fully_closed() -> bool {\n    true")
        && !src.contains("pbm_006_production_energy_wired() -> bool {\n    true")
}

/// Census: meta owner declares measure-only close hook on disk.
#[must_use]
pub fn pbm_006_meta_measure_only_hook_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, META_OWNER_PATH) else {
        return false;
    };
    src.contains("pub fn pbm_006_energy_measure_only_closed")
        && src.contains("pub fn pbm_006_measure_ingest_snapshot")
        && src.contains("pub fn pbm_006_done_when_probe")
        && src.contains("MEASURE_ONLY")
        && src.contains("pub const fn pbm_006_fully_closed() -> bool")
        && !src.contains("pbm_006_fully_closed() -> bool {\n    true")
}

/// Census: measure fence hop IE1 wired to artifact surface.
#[must_use]
pub fn pbm_006_measure_fence_ie1_wired(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_PATH) else {
        return false;
    };
    src.contains("hop_id: \"IE1\"")
        && src.contains(MEASURE_ARTIFACT_PATH)
        && src.contains("probe_wired: true")
}

#[must_use]
pub fn pbm_006_measure_slice_residue_ledger_honest() -> bool {
    PBM006_MEASURE_SLICE_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM006_MEASURE_SLICE_RESIDUE_LEDGER.len() == OPEN_CEREMONY_HOP_COUNT as usize
}

/// File-based measure-only lane close — mirrors meta/bench logic without dep.
#[must_use]
pub fn pbm_006_measure_only_lane_closed_honest(root: &Path) -> bool {
    pbm_006_measure_artifact_honest(root)
        && pbm_006_measure_posture_fixture_honest(root)
        && pbm_006_bench_measure_only_hook_on_disk(root)
        && pbm_006_meta_measure_only_hook_on_disk(root)
        && pbm_006_measure_fence_ie1_wired(root)
        && workspace_file_on_disk(root, INV4_PRESENCE_PROBE_BIN)
        && workspace_file_on_disk(root, LIVE_INGEST_RECEIPT_PATH)
}

/// Prior receipt chain absorption — AC133 + Z42/Z99 measure-only CLOSE.
#[must_use]
pub fn pbm_006_measure_prior_chain_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_AC133_RECEIPT_PATH)
        && workspace_file_on_disk(root, Z42_RECEIPT_PATH)
        && workspace_file_on_disk(root, Z99_RECEIPT_PATH)
}

/// PENDING_GAPS §B8 row pins measure slice sustain.
#[must_use]
pub fn pbm_006_pending_gaps_measure_slice_honest(root: &Path) -> bool {
    let Some(gaps) = read_workspace_file(root, PENDING_GAPS_PATH) else {
        return false;
    };
    gaps.contains("PBM-006 fully closed")
        && gaps.contains("measure slice")
        && gaps.contains("pbm_006_fully_closed()==false")
}

/// AC345 measure slice census — measure-only lane may be closed; full ceremony open.
#[must_use]
pub fn pbm_006_measure_slice_census_honest(root: &Path) -> bool {
    MEASURE_SLICE_POSTURE_TAG == "honest-partial"
        && pbm_006_measure_posture_fixture_honest(root)
        && pbm_006_bench_measure_only_hook_on_disk(root)
        && pbm_006_meta_measure_only_hook_on_disk(root)
        && pbm_006_measure_fence_ie1_wired(root)
        && pbm_006_measure_slice_residue_ledger_honest()
        && workspace_file_on_disk(root, META_OWNER_PATH)
        && workspace_file_on_disk(root, BENCH_CONSUMER_PATH)
        && workspace_file_on_disk(root, INV4_PRESENCE_PROBE_BIN)
}

/// AC345 honest gate — chains prior receipts + on-disk measure census.
#[must_use]
pub fn pbm_006_ac345_measure_slice_honest(root: &Path) -> bool {
    pbm_006_measure_slice_census_honest(root)
        && pbm_006_measure_prior_chain_absorbed(root)
        && pbm_006_pending_gaps_measure_slice_honest(root)
}

#[test]
fn pbm006_measure_posture_fixture_pins_honest() {
    let root = workspace_root();
    assert!(pbm_006_measure_posture_fixture_honest(&root));
    assert_eq!(INV4_HONEST_SAT_COUNT, 3);
    assert_eq!(INV4_AGGREGATE, "3/4");
    assert_eq!(FENCE_HOP_COUNT, 5);
    assert_eq!(PROBE_HOPS_WIRED, 4);
}

#[test]
fn pbm006_measure_artifact_honest_when_present() {
    let root = workspace_root();
    if !workspace_file_on_disk(&root, MEASURE_ARTIFACT_PATH) {
        eprintln!("skip pbm006_measure_artifact_honest_when_present: artifact absent");
        return;
    }
    assert!(
        pbm_006_measure_artifact_honest(&root),
        "inv4_energy_measured.json must pin honest 3/4 measure fields"
    );
}

#[test]
fn pbm006_bench_measure_only_hook_on_disk() {
    let root = workspace_root();
    assert!(pbm_006_bench_measure_only_hook_on_disk(&root));
}

#[test]
fn pbm006_meta_measure_only_hook_on_disk() {
    let root = workspace_root();
    assert!(pbm_006_meta_measure_only_hook_on_disk(&root));
}

#[test]
fn pbm006_measure_fence_ie1_wired() {
    let root = workspace_root();
    assert!(pbm_006_measure_fence_ie1_wired(&root));
    assert_eq!(MEASURE_FENCE_HOP_ID, "IE1");
}

#[test]
fn pbm006_measure_slice_residue_ledger_open() {
    assert!(pbm_006_measure_slice_residue_ledger_honest());
    for entry in &PBM006_MEASURE_SLICE_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm006_live_ingest_receipt_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, LIVE_INGEST_RECEIPT_PATH));
    let ingest = read_workspace_file(&root, LIVE_INGEST_RECEIPT_PATH).expect("live ingest receipt");
    assert!(ingest.contains("INV4 measure LIVE ingest"));
    assert!(ingest.contains("3/4"));
    assert!(ingest.contains(MEASURE_ARTIFACT_PATH) || ingest.contains("inv4_energy_measured.json"));
}

#[test]
fn pbm006_ac133_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, PRIOR_AC133_RECEIPT_PATH));
    let ac133 = read_workspace_file(&root, PRIOR_AC133_RECEIPT_PATH).expect("AC133 receipt");
    assert!(ac133.contains("PBM-006"));
    assert!(ac133.contains("measure slice"));
    assert!(ac133.contains("3/4"));
    assert!(ac133.contains("MASTER_RETICK"));
    let z42 = read_workspace_file(&root, Z42_RECEIPT_PATH).expect("Z42 receipt");
    assert!(z42.contains("PBM-006"));
    let z99 = read_workspace_file(&root, Z99_RECEIPT_PATH).expect("Z99 receipt");
    assert!(z99.contains("fully_closed") || z99.contains("pbm_006_fully_closed"));
}

#[test]
fn pbm006_measure_only_lane_closed_when_artifact_present() {
    let root = workspace_root();
    if !workspace_file_on_disk(&root, MEASURE_ARTIFACT_PATH) {
        eprintln!("skip pbm006_measure_only_lane_closed_when_artifact_present: artifact absent");
        return;
    }
    assert!(
        pbm_006_measure_only_lane_closed_honest(&root),
        "measure-only lane must close honestly when live artifact present"
    );
}

#[test]
fn pbm006_owner_surfaces_no_flip_invent() {
    let root = workspace_root();
    let meta = read_workspace_file(&root, META_OWNER_PATH).expect("meta owner");
    assert!(!meta.contains("pbm_006_fully_closed() -> bool {\n    true"));
    assert!(!meta.contains("pbm_006_production_energy_wired() -> bool {\n    true"));
    assert!(!meta.contains("pbm_006_v_inv4_flip_authorized() -> bool {\n    true"));
    let bench = read_workspace_file(&root, BENCH_CONSUMER_PATH).expect("bench consumer");
    assert!(!bench.contains("pbm_006_fully_closed() -> bool {\n    true"));
    assert!(!bench.contains("pbm_006_production_energy_wired() -> bool {\n    true"));
}

#[test]
fn pbm006_pending_gaps_measure_slice_row() {
    let root = workspace_root();
    assert!(pbm_006_pending_gaps_measure_slice_honest(&root));
}

#[test]
fn pbm006_measure_slice_census_honest() {
    let root = workspace_root();
    assert!(pbm_006_measure_slice_census_honest(&root));
}

#[test]
fn fleet_composer_accel2_ac345_pbm006_measure_slice_honest() {
    assert_eq!(AC345_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC345-PBM-006");
    assert_eq!(AC345_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC345.md");
    assert_eq!(WORKSTREAM_ID, "WS-inv4-energy");
    assert_eq!(PBM_OWNER, "PBM-006");
    assert_eq!(MEASURE_SLICE_POSTURE_TAG, "honest-partial");
    let root = workspace_root();
    assert!(pbm_006_ac345_measure_slice_honest(&root));
}
