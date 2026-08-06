// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL-F AC134 — PBM-008 hop6 catalog_live_export honest residue.
// Absorbs AC64 (`COMPOSER_ACCEL2_AC64.md`) formal fence without re-census.
// Crosswalks AC58 export-bridge residue pattern (honest hop6 OPEN — no production flip).

use std::path::{Path, PathBuf};

use umst_formal::{
    catalog_live_export_deferred, pbm_008_ac64_deepen_probe, pbm_008_ac64_honest,
    pbm_008_done_when_probe, pbm_008_formal_fence_closed, pbm_008_fully_closed,
    pbm_008_on_disk_census_honest, pbm_008_production_wired, pbm_008_wire_hops_closed_count,
    pbm_008_wire_hops_honest, FORMAL_ANCHOR_WIRE_HOPS, JOB_ID as AC64_JOB_ID,
    POSTURE_TAG, RECEIPT_PATH as AC64_RECEIPT_PATH, WIRE_HOP_COUNT, WIRE_HOPS_CLOSED,
    WORKSTREAM_ID,
};

/// FLEET-COMPOSER-ACCEL-F slot id.
pub const AC134_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC134-PBM-008";

/// AC134 completion receipt cross-ref.
pub const AC134_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC134.md";

/// AC64 formal cert fence receipt — absorbed, not re-census.
pub const PRIOR_AC64_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC64.md";

/// AC58 PF3 coupling export residue receipt — export-bridge pattern crosswalk.
pub const PRIOR_AC58_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC58.md";

/// PENDING_GAPS §B8 sustain slice source.
pub const PENDING_GAPS_PATH: &str = "outputs/.tmp/PENDING_GAPS_COMPOSITIONAL_2134.md";

/// Honest residue tier @ AC134 (matches AC64 posture).
pub const RESIDUE_POSTURE_TAG: &str = "witnessed-not-proved";

/// Hop 6 wire id — catalog live export ceremony (operator only).
pub const HOP6_WIRE_ID: &str = "catalog_live_export";

/// Hop 6 surface — operator ceremony, not agent-writable.
pub const HOP6_SURFACE: &str = "operator `lake build` + catalog refresh";

/// Open residue count @ AC134 — hop6 export only.
pub const OPEN_RESIDUE_COUNT: u8 = 1;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm008ExportResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC134 — catalog live export hop only.
pub const PBM008_EXPORT_RESIDUE_LEDGER: [Pbm008ExportResidue; OPEN_RESIDUE_COUNT as usize] =
    [Pbm008ExportResidue {
        residue_id: HOP6_WIRE_ID,
        blocker: "operator `lake build` + catalog refresh ceremony",
        owner: "operator",
        closed: false,
    }];

#[must_use]
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .unwrap_or_else(|_| Path::new(env!("CARGO_MANIFEST_DIR")).join(".."))
}

#[must_use]
pub fn workspace_file_on_disk(rel: &str) -> bool {
    workspace_root().join(rel).is_file()
}

#[must_use]
pub fn pbm008_hop6_export_wired() -> bool {
    FORMAL_ANCHOR_WIRE_HOPS
        .iter()
        .find(|h| h.wire_id == HOP6_WIRE_ID)
        .is_some_and(|h| h.wired)
}

#[must_use]
pub fn pbm008_hop6_export_residue_open_count() -> u8 {
    PBM008_EXPORT_RESIDUE_LEDGER
        .iter()
        .filter(|r| !r.closed)
        .count() as u8
}

#[must_use]
pub fn pbm008_hop6_export_residue_ledger_honest() -> bool {
    pbm008_hop6_export_residue_open_count() == OPEN_RESIDUE_COUNT
        && PBM008_EXPORT_RESIDUE_LEDGER.iter().all(|r| !r.closed)
        && PBM008_EXPORT_RESIDUE_LEDGER[0].residue_id == HOP6_WIRE_ID
}

#[must_use]
pub fn pbm008_hop6_export_residue_ac64_absorbed() -> bool {
    workspace_file_on_disk(PRIOR_AC64_RECEIPT_PATH)
        && pbm_008_formal_fence_closed()
        && pbm_008_ac64_honest()
        && pbm_008_wire_hops_honest()
}

#[must_use]
pub fn pbm008_hop6_export_residue_ac58_pattern_honest() -> bool {
    workspace_file_on_disk(PRIOR_AC58_RECEIPT_PATH)
        && !pbm_008_production_wired()
        && !pbm_008_fully_closed()
}

#[must_use]
pub fn pbm008_hop6_export_residue_honest() -> bool {
    RESIDUE_POSTURE_TAG == POSTURE_TAG
        && !pbm_008_production_wired()
        && !pbm_008_fully_closed()
        && catalog_live_export_deferred()
        && !pbm008_hop6_export_wired()
        && pbm_008_wire_hops_honest()
        && pbm_008_formal_fence_closed()
        && pbm008_hop6_export_residue_ledger_honest()
        && pbm008_hop6_export_residue_ac64_absorbed()
        && pbm008_hop6_export_residue_ac58_pattern_honest()
}

#[test]
fn pbm008_hop6_export_production_wired_honest_false() {
    assert!(!pbm_008_production_wired());
    assert!(!pbm_008_fully_closed());
    assert!(catalog_live_export_deferred());
    assert!(!pbm008_hop6_export_wired());
}

#[test]
fn pbm008_hop6_export_wire_hops_five_of_six() {
    assert!(pbm_008_wire_hops_honest());
    assert_eq!(pbm_008_wire_hops_closed_count(), WIRE_HOPS_CLOSED);
    assert_eq!(WIRE_HOP_COUNT, 6);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].wire_id, HOP6_WIRE_ID);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].surface, HOP6_SURFACE);
    assert!(!FORMAL_ANCHOR_WIRE_HOPS[5].wired);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].status, "OPEN");
}

#[test]
fn pbm008_hop6_export_residue_open_ledger() {
    assert!(pbm008_hop6_export_residue_ledger_honest());
    assert_eq!(
        PBM008_EXPORT_RESIDUE_LEDGER.len(),
        OPEN_RESIDUE_COUNT as usize
    );
    for entry in &PBM008_EXPORT_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm008_hop6_export_ac64_absorbed_witness() {
    assert!(pbm008_hop6_export_residue_ac64_absorbed());
    assert!(workspace_file_on_disk(PRIOR_AC64_RECEIPT_PATH));
    assert_eq!(AC64_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC64-PBM-008");
    assert_eq!(AC64_RECEIPT_PATH, PRIOR_AC64_RECEIPT_PATH);
    let probe = pbm_008_ac64_deepen_probe();
    assert!(probe.formal_fence_closed);
    assert!(!probe.pbm_008_fully_closed);
    assert!(probe.pbm_008_flip_blocked);
}

#[test]
fn pbm008_hop6_export_ac58_pattern_witness() {
    assert!(pbm008_hop6_export_residue_ac58_pattern_honest());
    assert!(workspace_file_on_disk(PRIOR_AC58_RECEIPT_PATH));
    assert!(!pbm_008_production_wired());
}

#[test]
fn pbm008_hop6_export_on_disk_census() {
    assert!(pbm_008_on_disk_census_honest());
    assert!(workspace_file_on_disk(PENDING_GAPS_PATH));
    let root = workspace_root();
    assert!(root.join(PRIOR_AC64_RECEIPT_PATH).is_file());
}

#[test]
fn pbm008_hop6_export_done_when_master_retick_blocked() {
    let done = pbm_008_done_when_probe();
    assert!(done.formal_anchor_fence_honest);
    assert!(!done.catalog_live_export_complete);
    assert!(!done.master_retick_eligible);
    assert_eq!(done.closure, "formal-fence-CLOSE / master-HOLD");
}

#[test]
fn fleet_composer_accel2_ac134_pbm008_hop6_export_residue_honest() {
    assert_eq!(AC134_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC134-PBM-008");
    assert_eq!(AC134_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC134.md");
    assert_eq!(WORKSTREAM_ID, "WS-formal-anchors");
    assert_eq!(RESIDUE_POSTURE_TAG, POSTURE_TAG);
    assert!(pbm008_hop6_export_residue_honest());
}
