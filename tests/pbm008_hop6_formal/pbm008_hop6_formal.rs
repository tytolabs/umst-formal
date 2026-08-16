// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-K AC344 — PBM-008 hop6 formal test.
// Formal-tree witness for `catalog_live_export` hop 6 OPEN — absorbs AC64 + AC134 without re-census.
// `pbm_008_fully_closed()==false` honest · no production flip · no master retick.

use std::path::{Path, PathBuf};

use umst_formal::{
    catalog_live_export_deferred, pbm_008_ac64_deepen_probe, pbm_008_ac64_honest,
    pbm_008_done_when_probe, pbm_008_formal_fence_closed, pbm_008_fully_closed,
    pbm_008_on_disk_census_honest, pbm_008_production_wired, pbm_008_wire_hops_closed_count,
    pbm_008_wire_hops_honest, FORMAL_ANCHOR_WIRE_HOPS, JOB_ID as AC64_JOB_ID,
    POSTURE_TAG, RECEIPT_PATH as AC64_RECEIPT_PATH, WIRE_HOP_COUNT, WIRE_HOPS_CLOSED,
    WORKSTREAM_ID,
};

/// FLEET-COMPOSER-ACCEL-K slot id.
pub const AC344_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC344-PBM-008";

/// AC344 completion receipt cross-ref.
pub const AC344_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC344.md";

/// AC64 formal cert fence receipt — absorbed, not re-census.
pub const PRIOR_AC64_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC64.md";

/// AC134 hop6 export residue receipt — sustain slice absorbed.
pub const PRIOR_AC134_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC134.md";

/// AC58 PF3 coupling export residue receipt — export-bridge pattern crosswalk.
pub const PRIOR_AC58_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC58.md";

/// Formal-tree hop6 posture tier (matches AC64 / AC134).
pub const FORMAL_POSTURE_TAG: &str = "witnessed-not-proved";

/// Hop 6 wire id — catalog live export ceremony (operator only).
pub const HOP6_WIRE_ID: &str = "catalog_live_export";

/// Hop 6 surface — operator ceremony, not agent-writable.
pub const HOP6_SURFACE: &str = "operator `lake build` + catalog refresh";

/// Formal hop6 probe count @ AC344.
pub const FORMAL_HOP6_PROBE_COUNT: usize = 8;

/// Open formal hop count — hop6 only.
pub const OPEN_FORMAL_HOP_COUNT: u8 = 1;

/// One formal hop6 fence probe outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm008Hop6FormalProbe {
    pub probe: &'static str,
    pub green: bool,
    pub detail: &'static str,
}

/// Formal hop6 open ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm008Hop6FormalResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC344 — catalog live export hop only.
pub const PBM008_HOP6_FORMAL_RESIDUE_LEDGER: [Pbm008Hop6FormalResidue; OPEN_FORMAL_HOP_COUNT as usize] =
    [Pbm008Hop6FormalResidue {
        residue_id: HOP6_WIRE_ID,
        blocker: "operator `lake build` + catalog refresh ceremony",
        owner: "operator",
        closed: false,
    }];

#[must_use]
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()
        .unwrap_or_else(|_| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.."))
}

#[must_use]
pub fn workspace_file_on_disk(rel: &str) -> bool {
    workspace_root().join(rel).is_file()
}

#[must_use]
pub fn pbm008_hop6_formal_wired() -> bool {
    FORMAL_ANCHOR_WIRE_HOPS
        .iter()
        .find(|h| h.wire_id == HOP6_WIRE_ID)
        .is_some_and(|h| h.wired)
}

#[must_use]
pub fn pbm008_hop6_formal_open_count() -> u8 {
    PBM008_HOP6_FORMAL_RESIDUE_LEDGER
        .iter()
        .filter(|r| !r.closed)
        .count() as u8
}

#[must_use]
pub fn pbm008_hop6_formal_residue_ledger_honest() -> bool {
    pbm008_hop6_formal_open_count() == OPEN_FORMAL_HOP_COUNT
        && PBM008_HOP6_FORMAL_RESIDUE_LEDGER.iter().all(|r| !r.closed)
        && PBM008_HOP6_FORMAL_RESIDUE_LEDGER[0].residue_id == HOP6_WIRE_ID
}

#[must_use]
pub fn pbm008_hop6_formal_ac64_absorbed() -> bool {
    workspace_file_on_disk(PRIOR_AC64_RECEIPT_PATH)
        && pbm_008_formal_fence_closed()
        && pbm_008_ac64_honest()
        && pbm_008_wire_hops_honest()
}

#[must_use]
pub fn pbm008_hop6_formal_ac134_absorbed() -> bool {
    workspace_file_on_disk(PRIOR_AC134_RECEIPT_PATH)
        && !pbm_008_fully_closed()
        && !pbm008_hop6_formal_wired()
}

#[must_use]
pub fn pbm008_hop6_formal_ac58_pattern_honest() -> bool {
    workspace_file_on_disk(PRIOR_AC58_RECEIPT_PATH) && !pbm_008_production_wired()
}

#[must_use]
pub fn run_pbm008_hop6_formal_audit() -> Vec<Pbm008Hop6FormalProbe> {
    vec![
        Pbm008Hop6FormalProbe {
            probe: "hop6_open",
            green: !pbm008_hop6_formal_wired(),
            detail: "catalog_live_export hop 6 stays OPEN",
        },
        Pbm008Hop6FormalProbe {
            probe: "fully_closed_false",
            green: !pbm_008_fully_closed(),
            detail: "pbm_008_fully_closed() stays false",
        },
        Pbm008Hop6FormalProbe {
            probe: "wire_hops_five_closed",
            green: pbm_008_wire_hops_honest(),
            detail: "5/6 wire hops closed — live export deferred",
        },
        Pbm008Hop6FormalProbe {
            probe: "formal_fence_closed",
            green: pbm_008_formal_fence_closed(),
            detail: "formal anchor fence GREEN — not master lift",
        },
        Pbm008Hop6FormalProbe {
            probe: "on_disk_census",
            green: pbm_008_on_disk_census_honest(),
            detail: "manifest · Lean · catalog · script · witness",
        },
        Pbm008Hop6FormalProbe {
            probe: "ac64_absorbed",
            green: pbm008_hop6_formal_ac64_absorbed(),
            detail: "AC64 formal fence absorbed without re-census",
        },
        Pbm008Hop6FormalProbe {
            probe: "ac134_absorbed",
            green: pbm008_hop6_formal_ac134_absorbed(),
            detail: "AC134 sustain residue absorbed",
        },
        Pbm008Hop6FormalProbe {
            probe: "production_wired_false",
            green: !pbm_008_production_wired() && catalog_live_export_deferred(),
            detail: "production wiring not earned",
        },
    ]
}

#[must_use]
pub fn pbm008_hop6_formal_audit_all_green() -> bool {
    run_pbm008_hop6_formal_audit().iter().all(|p| p.green)
}

#[must_use]
pub fn pbm008_hop6_formal_honest() -> bool {
    FORMAL_POSTURE_TAG == POSTURE_TAG
        && !pbm_008_production_wired()
        && !pbm_008_fully_closed()
        && catalog_live_export_deferred()
        && !pbm008_hop6_formal_wired()
        && pbm_008_wire_hops_honest()
        && pbm_008_formal_fence_closed()
        && pbm008_hop6_formal_residue_ledger_honest()
        && pbm008_hop6_formal_ac64_absorbed()
        && pbm008_hop6_formal_ac134_absorbed()
        && pbm008_hop6_formal_ac58_pattern_honest()
        && pbm008_hop6_formal_audit_all_green()
}

#[test]
fn pbm008_hop6_formal_production_wired_honest_false() {
    assert!(!pbm_008_production_wired());
    assert!(!pbm_008_fully_closed());
    assert!(catalog_live_export_deferred());
    assert!(!pbm008_hop6_formal_wired());
}

#[test]
fn pbm008_hop6_formal_wire_hops_five_of_six() {
    assert!(pbm_008_wire_hops_honest());
    assert_eq!(pbm_008_wire_hops_closed_count(), WIRE_HOPS_CLOSED);
    assert_eq!(WIRE_HOP_COUNT, 6);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].wire_id, HOP6_WIRE_ID);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].surface, HOP6_SURFACE);
    assert!(!FORMAL_ANCHOR_WIRE_HOPS[5].wired);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].status, "OPEN");
}

#[test]
fn pbm008_hop6_formal_residue_open_ledger() {
    assert!(pbm008_hop6_formal_residue_ledger_honest());
    assert_eq!(
        PBM008_HOP6_FORMAL_RESIDUE_LEDGER.len(),
        OPEN_FORMAL_HOP_COUNT as usize
    );
    for entry in &PBM008_HOP6_FORMAL_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm008_hop6_formal_ac64_absorbed_witness() {
    assert!(pbm008_hop6_formal_ac64_absorbed());
    assert!(workspace_file_on_disk(PRIOR_AC64_RECEIPT_PATH));
    assert_eq!(AC64_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC64-PBM-008");
    assert_eq!(AC64_RECEIPT_PATH, PRIOR_AC64_RECEIPT_PATH);
    let probe = pbm_008_ac64_deepen_probe();
    assert!(probe.formal_fence_closed);
    assert!(!probe.pbm_008_fully_closed);
    assert!(probe.pbm_008_flip_blocked);
}

#[test]
fn pbm008_hop6_formal_ac134_absorbed_witness() {
    assert!(pbm008_hop6_formal_ac134_absorbed());
    assert!(workspace_file_on_disk(PRIOR_AC134_RECEIPT_PATH));
    assert!(!pbm_008_fully_closed());
    assert!(!pbm008_hop6_formal_wired());
}

#[test]
fn pbm008_hop6_formal_ac58_pattern_witness() {
    assert!(pbm008_hop6_formal_ac58_pattern_honest());
    assert!(workspace_file_on_disk(PRIOR_AC58_RECEIPT_PATH));
    assert!(!pbm_008_production_wired());
}

#[test]
fn pbm008_hop6_formal_on_disk_census() {
    assert!(pbm_008_on_disk_census_honest());
    let root = workspace_root();
    assert!(root.join(PRIOR_AC64_RECEIPT_PATH).is_file());
    assert!(root.join(PRIOR_AC134_RECEIPT_PATH).is_file());
}

#[test]
fn pbm008_hop6_formal_done_when_master_retick_blocked() {
    let done = pbm_008_done_when_probe();
    assert!(done.formal_anchor_fence_honest);
    assert!(!done.catalog_live_export_complete);
    assert!(!done.master_retick_eligible);
    assert_eq!(done.closure, "formal-fence-CLOSE / master-HOLD");
}

#[test]
fn pbm008_hop6_formal_audit_green() {
    let audit = run_pbm008_hop6_formal_audit();
    assert_eq!(audit.len(), FORMAL_HOP6_PROBE_COUNT);
    assert!(pbm008_hop6_formal_audit_all_green());
    for probe in &audit {
        assert!(probe.green, "probe {} must be green: {}", probe.probe, probe.detail);
    }
}

#[test]
fn fleet_composer_accel2_ac344_pbm008_hop6_formal_honest() {
    assert_eq!(AC344_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC344-PBM-008");
    assert_eq!(AC344_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC344.md");
    assert_eq!(WORKSTREAM_ID, "WS-formal-anchors");
    assert_eq!(FORMAL_POSTURE_TAG, POSTURE_TAG);
    assert!(pbm008_hop6_formal_honest());
}
