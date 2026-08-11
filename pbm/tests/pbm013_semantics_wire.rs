// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL2 AC609 — PBM-013 semantics wire honest witness.
// File-based census (no umst-semantics dep — AC134 scaffold owns Cargo.toml).
// Absorbs AC65 docs SSOT + 8×3 fixture-closed gate without invent production_wired.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

pub const AC609_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC609-PBM-013";
pub const AC609_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC609.md";
pub const PRIOR_AC65_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC65.md";
pub const PBM013_DOC_PATH: &str = "docs/PBM-013_SEMANTICS_WIRE.md";
pub const L10_CONCEPTS_SURFACE: &str =
    "umst-semantics/crates/umst-semantics/src/concepts.rs";
pub const L10_GATE_TEST_PATH: &str =
    "umst-semantics/crates/umst-semantics/tests/concepts_gate.rs";
pub const WORKSTREAM_ID: &str = "WS-l10-concepts";
pub const PBM_OWNER: &str = "PBM-013";
pub const POSTURE_TAG: &str = "honest-partial";
pub const CONCEPT_CATALOG_COUNT: u8 = 8;
pub const ACTIVE_LANGUAGE_COUNT: u8 = 3;
pub const GATE_LEG_COUNT: u16 = 24;

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

#[must_use]
pub fn l10_catalog_eight_concepts(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, L10_CONCEPTS_SURFACE) else {
        return false;
    };
    src.contains("L10_CONCEPT_CATALOG")
        && src.contains("L10_CONCEPT_MIN_COUNT")
        && src.contains("L10_ACTIVE_LANGUAGE_COUNT")
        && src.contains("Chair")
        && src.contains("Shelf")
}

#[must_use]
pub fn l10_gate_fence_present(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, L10_GATE_TEST_PATH) else {
        return false;
    };
    src.contains("gate_semantic")
        && src.contains("l10_concept_cross_lang_quotient_aligned")
        && src.contains("GATE_TOLERANCE")
}

#[must_use]
pub fn pbm013_doc_wire_map(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, PBM013_DOC_PATH) else {
        return false;
    };
    doc.contains("SW0")
        && doc.contains("SW4")
        && doc.contains("24/24")
        && doc.contains("production_wired")
        && doc.contains("false")
        && doc.contains("P3_MI_GATE_BLOCKED")
}

#[must_use]
pub fn pbm013_ac609_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && workspace_file_on_disk(root, L10_CONCEPTS_SURFACE)
        && workspace_file_on_disk(root, L10_GATE_TEST_PATH)
        && workspace_file_on_disk(root, PBM013_DOC_PATH)
        && l10_catalog_eight_concepts(root)
        && l10_gate_fence_present(root)
        && pbm013_doc_wire_map(root)
}

#[test]
fn pbm013_l10_catalog_owner_on_disk() {
    let root = workspace_root();
    assert!(l10_catalog_eight_concepts(&root));
    assert_eq!(CONCEPT_CATALOG_COUNT, 8);
    assert_eq!(ACTIVE_LANGUAGE_COUNT, 3);
    assert_eq!(GATE_LEG_COUNT, 24);
}

#[test]
fn pbm013_gate_fence_integration_present() {
    let root = workspace_root();
    assert!(l10_gate_fence_present(&root));
}

#[test]
fn pbm013_ac65_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, PRIOR_AC65_RECEIPT_PATH));
    let ac65 = read_workspace_file(&root, PRIOR_AC65_RECEIPT_PATH).expect("AC65 receipt");
    assert!(ac65.contains("PBM-013"));
    assert!(ac65.contains("Master retick") && ac65.contains("no"));
}

#[test]
fn pbm013_no_production_wired_invent() {
    let root = workspace_root();
    let doc = read_workspace_file(&root, PBM013_DOC_PATH).expect("PBM-013 doc");
    assert!(doc.contains("production_wired"));
    assert!(!doc.contains("production_wired` | **true**"));
    assert!(!doc.contains("production_wired | **true**"));
}

#[test]
fn fleet_composer_accel2_ac609_pbm013_semantics_wire_honest() {
    assert_eq!(AC609_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC609-PBM-013");
    assert_eq!(WORKSTREAM_ID, "WS-l10-concepts");
    assert_eq!(PBM_OWNER, "PBM-013");
    let root = workspace_root();
    assert!(pbm013_ac609_census_honest(&root));
}
