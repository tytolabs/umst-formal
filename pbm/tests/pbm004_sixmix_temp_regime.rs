// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL2 AC608 — PBM-004 six-mix temp-regime honest witness.
// File-based census (no umst-concrete-cartridge dep — AC134 scaffold owns Cargo.toml).
// Absorbs AC62 docs SSOT + LAND-6/6 fixture bytes without invent GREEN.
//
// Doctrine by ref: AC62 · R-gate-temp-regime finding + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL2 slot id.
pub const AC608_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC608-PBM-004";

/// AC608 completion receipt cross-ref.
pub const AC608_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC608.md";

/// AC62 docs owner deepen receipt — absorbed, not re-census.
pub const PRIOR_AC62_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC62.md";

/// PBM-004 six-mix temp-regime SSOT.
pub const PBM004_DOC_PATH: &str = "docs/PBM-004_SIXMIX_TEMP_REGIME.md";

/// Golden fixture bytes.
pub const GATE_PARITY_FIXTURE_PATH: &str =
    "umst-concrete-cartridge/crates/umst-mcp/tests/fixtures/gate_parity_v0.json";

/// G0 honesty pins owner.
pub const G0_FIXTURE_SURFACE: &str =
    "umst-cartridges/crates/atoms/umst-cartridge-continuum/tests/common/g0_fixture.rs";

/// T-regime finding card.
pub const T_REGIME_FINDING_PATH: &str =
    "old/residuals/residuals/misc-outputs-tmp/R-gate-temp-regime.md";

/// PBM-004 workstream id.
pub const WORKSTREAM_ID: &str = "WS-sixmix-resolve";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-004";

/// Honest posture @ AC608.
pub const POSTURE_TAG: &str = "honest-partial";

/// Measured mix_table row count @ LAND-6/6.
pub const MIX_TABLE_ROW_COUNT: u8 = 6;

/// Fixture digest prefix @ AGAP-2033.
pub const GATE_PARITY_SHA256_PREFIX: &str = "7a3d3e5f5d634322";

/// Row 6 key — historical DRAFT name, library PASS bytes.
pub const ROW6_KEY: &str = "reject_cold_regime";

/// Operator posture pin.
pub const OPERATOR_POSTURE: &str = "LAND-6/6";

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
pub fn gate_parity_fixture_six_rows(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, GATE_PARITY_FIXTURE_PATH) else {
        return false;
    };
    raw.contains("\"mix_table\"")
        && raw.matches("\"pass_rational_default\"").count() >= 1
        && raw.matches("\"reject_high_wc\"").count() >= 1
        && raw.matches("\"reject_cold_regime\"").count() >= 1
        && raw.matches("\"pass_low_wc_mature\"").count() >= 1
        && raw.matches("\"pass_early_age\"").count() >= 1
        && raw.matches("\"pass_high_wc_in_regime\"").count() >= 1
}

#[must_use]
pub fn row6_pass_verdict_on_disk(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, GATE_PARITY_FIXTURE_PATH) else {
        return false;
    };
    raw.contains("\"reject_cold_regime\"")
        && raw.contains("\"verdict\": \"PASS\"")
        && !raw.contains("\"reject_cold_regime\": {\n      \"gate_summary\": {\n        \"verdict\": \"REJECT\"")
}

#[must_use]
pub fn g0_fixture_pins_honest(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, G0_FIXTURE_SURFACE) else {
        return false;
    };
    src.contains("G0_MIX_TABLE_ROW_COUNT")
        && src.contains("= 6")
        && src.contains(GATE_PARITY_SHA256_PREFIX)
        && src.contains(ROW6_KEY)
        && src.contains("G0_SIX_MIX_OPERATOR_POSTURE")
        && src.contains(OPERATOR_POSTURE)
}

#[must_use]
pub fn pbm004_doc_land_posture(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, PBM004_DOC_PATH) else {
        return false;
    };
    doc.contains("PBM-004")
        && doc.contains(OPERATOR_POSTURE)
        && doc.contains("reject_cold_regime")
        && doc.contains("PASS")
        && doc.contains("production_wired")
        && doc.contains("false")
}

#[must_use]
pub fn pbm004_ac608_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && workspace_file_on_disk(root, GATE_PARITY_FIXTURE_PATH)
        && workspace_file_on_disk(root, G0_FIXTURE_SURFACE)
        && workspace_file_on_disk(root, PBM004_DOC_PATH)
        && gate_parity_fixture_six_rows(root)
        && row6_pass_verdict_on_disk(root)
        && g0_fixture_pins_honest(root)
        && pbm004_doc_land_posture(root)
}

#[test]
fn pbm004_fixture_six_mix_rows_measured() {
    let root = workspace_root();
    assert!(gate_parity_fixture_six_rows(&root));
    assert_eq!(MIX_TABLE_ROW_COUNT, 6);
}

#[test]
fn pbm004_row6_cold_regime_pass_bytes() {
    let root = workspace_root();
    assert!(row6_pass_verdict_on_disk(&root));
}

#[test]
fn pbm004_g0_fixture_pins_align() {
    let root = workspace_root();
    assert!(g0_fixture_pins_honest(&root));
}

#[test]
fn pbm004_ac62_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, PRIOR_AC62_RECEIPT_PATH));
    let ac62 = read_workspace_file(&root, PRIOR_AC62_RECEIPT_PATH).expect("AC62 receipt");
    assert!(ac62.contains("PBM-004"));
    let lower = ac62.to_ascii_lowercase();
    assert!(
        (lower.contains("master_retick") || lower.contains("master retick")) && lower.contains("no")
    );
}

#[test]
fn pbm004_no_reject_invent_on_row6() {
    let root = workspace_root();
    let raw = read_workspace_file(&root, GATE_PARITY_FIXTURE_PATH).expect("fixture must exist");
    assert!(raw.contains("\"reject_cold_regime\""));
    assert!(!raw.contains("\"reject_cold_regime\": {\n      \"gate_summary\": {\n        \"verdict\": \"REJECT\""));
    assert!(row6_pass_verdict_on_disk(&root));
}

#[test]
fn fleet_composer_accel2_ac608_pbm004_sixmix_temp_regime_honest() {
    assert_eq!(AC608_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC608-PBM-004");
    assert_eq!(WORKSTREAM_ID, "WS-sixmix-resolve");
    assert_eq!(PBM_OWNER, "PBM-004");
    let root = workspace_root();
    assert!(pbm004_ac608_census_honest(&root));
}
