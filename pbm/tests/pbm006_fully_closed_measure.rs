// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-F AC133 — PBM-006 fully_closed measure slice census.
// PENDING_GAPS §B8: honest witness that `pbm_006_fully_closed()==false` while
// measure-only lane may be closed. File-based census (no umst-meta dep — AC134
// scaffold owns Cargo.toml). Does **not** invent INV4 4/4, O4 PASS, O5 flip,
// `production_energy_wired`, or master retick.
//
// Absorbs Z42/Z99 measure-only CLOSE + AC10 meta deepen without re-census.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-F slot id.
pub const AC133_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC133-PBM-006";

/// AC133 completion receipt cross-ref.
pub const AC133_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC133.md";

/// PENDING_GAPS §B8 source.
pub const PENDING_GAPS_SECTION: &str = "B8";

/// Honest measure-slice posture @ AC133.
pub const MEASURE_SLICE_POSTURE_TAG: &str = "HONEST_PARTIAL";

/// Meta owner witness surface.
pub const META_OWNER_PATH: &str = "crates/umst-meta/src/meta_pbm_006_ws_inv4_energy.rs";

/// Live measure artifact.
pub const MEASURE_ARTIFACT_PATH: &str = "artifacts/benchmarks/inv4_energy_measured.json";

/// O5 flip ceremony surface — stays open.
pub const O5_FLIP_SURFACE: &str = "docs/INV4_O5_FLIP_RECEIPT.template.md";

/// O4 calibrate surface — stays PENDING.
pub const O4_CALIBRATE_SURFACE: &str = "crates/umst-bench/src/residual.rs";

/// Prior measure-only receipts — absorbed, not re-census.
pub const Y57_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y57_0808.md";
pub const Z42_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z42_1015.md";
pub const Z99_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z99_1232.md";
pub const K6_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_P1938_K6.md";
pub const AC10_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL_2030_AC10.md";

/// Honest INV4 aggregate @ measure slice.
pub const INV4_AGGREGATE: &str = "3/4";

/// Honest INV4 sat count — do not invent 4.
pub const INV4_HONEST_SAT_COUNT: u8 = 3;

/// Open ceremony hops blocking full close.
pub const OPEN_CEREMONY_HOP_COUNT: u8 = 2;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm006FullyClosedResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC133.
pub const PBM006_FULLY_CLOSED_RESIDUE_LEDGER: [Pbm006FullyClosedResidue; OPEN_CEREMONY_HOP_COUNT as usize] =
    [
        Pbm006FullyClosedResidue {
            residue_id: "o4_calibrate_pass",
            blocker: "crates/umst-bench/src/residual.rs::calibrate_o4 PENDING (operator O1+O2)",
            owner: "operator",
            closed: false,
        },
        Pbm006FullyClosedResidue {
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

/// Census: meta owner declares `pbm_006_fully_closed() -> false` (const fn).
#[must_use]
pub fn pbm_006_fully_closed_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, META_OWNER_PATH) else {
        return false;
    };
    src.contains("pub const fn pbm_006_fully_closed() -> bool")
        && src.contains("false")
        && !src.contains("pbm_006_fully_closed() -> bool {\n    true")
}

/// Census: meta owner pins INV4 3/4 honest sat count.
#[must_use]
pub fn pbm_006_inv4_aggregate_honest_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, META_OWNER_PATH) else {
        return false;
    };
    src.contains("pub const INV4_AGGREGATE: &str = \"3/4\"")
        && src.contains("pub const INV4_HONEST_SAT_COUNT: u8 = 3")
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
}

#[must_use]
pub fn pbm_006_fully_closed_residue_ledger_honest() -> bool {
    PBM006_FULLY_CLOSED_RESIDUE_LEDGER.iter().all(|r| !r.closed)
        && PBM006_FULLY_CLOSED_RESIDUE_LEDGER.len() == OPEN_CEREMONY_HOP_COUNT as usize
}

/// AC133 measure slice census — fully_closed false; measure lane may be closed.
#[must_use]
pub fn pbm_006_measure_slice_census_honest(root: &Path) -> bool {
    MEASURE_SLICE_POSTURE_TAG == "HONEST_PARTIAL"
        && pbm_006_fully_closed_declared_false(root)
        && pbm_006_inv4_aggregate_honest_on_disk(root)
        && pbm_006_fully_closed_residue_ledger_honest()
        && workspace_file_on_disk(root, O5_FLIP_SURFACE)
        && workspace_file_on_disk(root, O4_CALIBRATE_SURFACE)
}

/// AC133 honest gate — absorbs prior measure-only receipts.
#[must_use]
pub fn pbm_006_ac133_fully_closed_measure_honest(root: &Path) -> bool {
    pbm_006_measure_slice_census_honest(root)
        && workspace_file_on_disk(root, Y57_RECEIPT_PATH)
        && workspace_file_on_disk(root, Z42_RECEIPT_PATH)
        && workspace_file_on_disk(root, Z99_RECEIPT_PATH)
}

#[test]
fn pbm006_fully_closed_declared_false_on_disk() {
    let root = workspace_root();
    assert!(
        pbm_006_fully_closed_declared_false(&root),
        "meta owner must declare pbm_006_fully_closed() -> false"
    );
}

#[test]
fn pbm006_inv4_aggregate_three_of_four_on_disk() {
    let root = workspace_root();
    assert!(pbm_006_inv4_aggregate_honest_on_disk(&root));
    assert_eq!(INV4_HONEST_SAT_COUNT, 3);
    assert_eq!(INV4_AGGREGATE, "3/4");
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
fn pbm006_fully_closed_residue_ledger_open() {
    assert!(pbm_006_fully_closed_residue_ledger_honest());
    for entry in &PBM006_FULLY_CLOSED_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm006_o5_flip_ceremony_surface_open() {
    let root = workspace_root();
    assert!(
        workspace_file_on_disk(&root, O5_FLIP_SURFACE),
        "O5 flip template must exist as open ceremony surface"
    );
    let entry = &PBM006_FULLY_CLOSED_RESIDUE_LEDGER[1];
    assert_eq!(entry.residue_id, "o5_flip_ceremony");
    assert!(!entry.closed);
}

#[test]
fn pbm006_o4_calibrate_surface_pending() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, O4_CALIBRATE_SURFACE));
    let entry = &PBM006_FULLY_CLOSED_RESIDUE_LEDGER[0];
    assert_eq!(entry.residue_id, "o4_calibrate_pass");
    assert!(!entry.closed);
}

#[test]
fn pbm006_prior_measure_receipts_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, Y57_RECEIPT_PATH));
    assert!(workspace_file_on_disk(&root, Z42_RECEIPT_PATH));
    assert!(workspace_file_on_disk(&root, Z99_RECEIPT_PATH));
    let z42 = read_workspace_file(&root, Z42_RECEIPT_PATH).expect("Z42 receipt");
    assert!(z42.contains("PBM-006"));
    assert!(z42.contains("3/4"));
    let z99 = read_workspace_file(&root, Z99_RECEIPT_PATH).expect("Z99 receipt");
    assert!(z99.contains("pbm_006_fully_closed()==false") || z99.contains("fully_closed"));
}

#[test]
fn pbm006_k6_ac10_receipts_absorbed_when_present() {
    let root = workspace_root();
    if workspace_file_on_disk(&root, K6_RECEIPT_PATH) {
        let k6 = read_workspace_file(&root, K6_RECEIPT_PATH).expect("K6 receipt");
        assert!(k6.contains("PBM-006"));
        assert!(k6.contains("3/4"));
    }
    if workspace_file_on_disk(&root, AC10_RECEIPT_PATH) {
        let ac10 = read_workspace_file(&root, AC10_RECEIPT_PATH).expect("AC10 receipt");
        assert!(ac10.contains("pbm_006_fully_closed()==false") || ac10.contains("fully_closed"));
    }
}

#[test]
fn pbm006_meta_owner_no_production_flip_invent() {
    let root = workspace_root();
    let Some(src) = read_workspace_file(&root, META_OWNER_PATH) else {
        panic!("meta owner surface must exist");
    };
    assert!(src.contains("pub const fn pbm_006_production_energy_wired() -> bool"));
    assert!(src.contains("pub const fn pbm_006_v_inv4_flip_authorized() -> bool"));
    assert!(!src.contains("production_energy_wired() -> bool {\n    true"));
    assert!(!src.contains("v_inv4_flip_authorized() -> bool {\n    true"));
}

#[test]
fn pbm006_measure_slice_census_honest() {
    let root = workspace_root();
    assert!(pbm_006_measure_slice_census_honest(&root));
    assert!(pbm_006_fully_closed_declared_false(&root));
}

#[test]
fn fleet_composer_accel2_ac133_pbm006_fully_closed_measure_honest() {
    assert_eq!(AC133_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC133-PBM-006");
    assert_eq!(AC133_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC133.md");
    assert_eq!(PENDING_GAPS_SECTION, "B8");
    let root = workspace_root();
    assert!(pbm_006_ac133_fully_closed_measure_honest(&root));
}
