// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL-L AC379 — PBM-HOP7 formal export test.
// Extended formal-export wire witness for hop 7 `catalog_lock_manifold_fiber` OPEN —
// absorbs AC344 hop6 formal + AC64 fence without re-census.
// `pbm_008_fully_closed()==false` honest · no production flip · no master retick.

use std::fs;
use std::path::{Path, PathBuf};

use umst_formal::{
    catalog_live_export_deferred, pbm_008_ac64_deepen_probe, pbm_008_ac64_honest,
    pbm_008_done_when_probe, pbm_008_formal_fence_closed, pbm_008_fully_closed,
    pbm_008_on_disk_census_honest, pbm_008_production_wired, pbm_008_wire_hops_closed_count,
    pbm_008_wire_hops_honest, CATALOG_RELPATH, FORMAL_ANCHOR_WIRE_HOPS, JOB_ID as AC64_JOB_ID,
    POSTURE_TAG, RECEIPT_PATH as AC64_RECEIPT_PATH, WIRE_HOP_COUNT, WIRE_HOPS_CLOSED,
    WORKSTREAM_ID,
};

/// FLEET-COMPOSER-ACCEL-L slot id.
pub const AC379_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC379-PBM-HOP7";

/// AC379 completion receipt cross-ref.
pub const AC379_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC379.md";

/// AC344 hop6 formal witness receipt — absorbed, not re-census.
pub const PRIOR_AC344_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC344.md";

/// AC64 formal cert fence receipt — absorbed, not re-census.
pub const PRIOR_AC64_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC64.md";

/// AC134 hop6 export residue receipt — sustain slice absorbed.
pub const PRIOR_AC134_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC134.md";

/// Formal-tree hop7 posture tier (matches AC64 / AC344).
pub const FORMAL_POSTURE_TAG: &str = "witnessed-not-proved";

/// Extended formal-export wire hop count @ AC379 (PBM-008 base 6 + hop7 manifold fiber).
pub const FORMAL_EXPORT_WIRE_HOP_COUNT: usize = 7;

/// Honest closed hops @ AC379 — PBM-008 hops 1–5 landed; hop6 + hop7 OPEN.
pub const FORMAL_EXPORT_HOPS_CLOSED: u8 = 5;

/// Hop 6 wire id — catalog live export ceremony (operator only).
pub const HOP6_WIRE_ID: &str = "catalog_live_export";

/// Hop 6 surface — operator ceremony, not agent-writable.
pub const HOP6_SURFACE: &str = "operator `lake build` + catalog refresh";

/// Hop 7 wire id — manifold catalog lock fiber pin (operator only).
pub const HOP7_WIRE_ID: &str = "catalog_lock_manifold_fiber";

/// Hop 7 surface — manifold INVARIANT_MANIFEST digest attach ceremony.
pub const HOP7_SURFACE: &str = "umst-manifold catalog digest fiber pin";

/// Pinned catalog lock artifact @ `umst-formal/artifacts/catalog.lock.json`.
pub const CATALOG_LOCK_RELPATH: &str = "umst-formal/artifacts/catalog.lock.json";

/// Catalog regenerate script — hop6 ceremony surface cross-ref.
pub const CATALOG_REGEN_SCRIPT: &str = "umst-formal/scripts/regenerate_lean_catalog.sh";

/// Pinned catalog digest hex @ AC379 on-disk census (matches catalog.json + lock).
pub const PINNED_CATALOG_DIGEST_HEX: &str =
    "aea5080d2ba81de9ddfdec1e4ca8f40ca851bd9bbd1a99b0416cea6ef8e85dff";

/// Pinned module count @ catalog.lock.json.
pub const PINNED_CATALOG_MODULE_COUNT: u32 = 84;

/// Open formal-export hop count — hop6 live export + hop7 manifold fiber.
pub const OPEN_FORMAL_EXPORT_HOP_COUNT: u8 = 2;

/// Formal hop7 probe count @ AC379.
pub const FORMAL_HOP7_PROBE_COUNT: usize = 10;

/// One formal-export hop7 fence probe outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbmHop7ExportProbe {
    pub probe: &'static str,
    pub green: bool,
    pub detail: &'static str,
}

/// Formal-export hop7 open ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PbmHop7ExportResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC379 — hop6 live export + hop7 manifold fiber.
pub const PBM_HOP7_EXPORT_RESIDUE_LEDGER: [PbmHop7ExportResidue; OPEN_FORMAL_EXPORT_HOP_COUNT as usize] =
    [
        PbmHop7ExportResidue {
            residue_id: HOP6_WIRE_ID,
            blocker: "operator `lake build` + catalog refresh ceremony",
            owner: "operator",
            closed: false,
        },
        PbmHop7ExportResidue {
            residue_id: HOP7_WIRE_ID,
            blocker: "manifold INVARIANT_MANIFEST catalog digest fiber pin stale",
            owner: "operator",
            closed: false,
        },
    ];

#[must_use]
pub fn workspace_root() -> PathBuf {
    Path::new(file!())
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .map(|p| {
            p.canonicalize()
                .unwrap_or_else(|_| p.to_path_buf())
        })
        .unwrap_or_else(|| PathBuf::from("."))
}

#[must_use]
pub fn workspace_file_on_disk(rel: &str) -> bool {
    workspace_root().join(rel).is_file()
}

#[must_use]
pub fn pbm_hop6_export_wired() -> bool {
    FORMAL_ANCHOR_WIRE_HOPS
        .iter()
        .find(|h| h.wire_id == HOP6_WIRE_ID)
        .is_some_and(|h| h.wired)
}

#[must_use]
pub fn pbm_hop7_export_wired() -> bool {
    false
}

#[must_use]
pub fn pbm_hop7_export_open_count() -> u8 {
    PBM_HOP7_EXPORT_RESIDUE_LEDGER
        .iter()
        .filter(|r| !r.closed)
        .count() as u8
}

#[must_use]
pub fn catalog_lock_on_disk() -> bool {
    let path = workspace_root().join(CATALOG_LOCK_RELPATH);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("\"role\": \"lean_catalog_lock\"")
        && text.contains(PINNED_CATALOG_DIGEST_HEX)
        && text.contains(&format!("\"module_count\": {PINNED_CATALOG_MODULE_COUNT}"))
}

#[must_use]
pub fn catalog_digest_matches_lock() -> bool {
    let catalog_path = workspace_root().join(CATALOG_RELPATH);
    let lock_path = workspace_root().join(CATALOG_LOCK_RELPATH);
    let Ok(catalog_text) = fs::read_to_string(catalog_path) else {
        return false;
    };
    let Ok(lock_text) = fs::read_to_string(lock_path) else {
        return false;
    };
    lock_text.contains(&format!("\"catalog_digest_hex\": \"{PINNED_CATALOG_DIGEST_HEX}\""))
        && catalog_text.contains(PINNED_CATALOG_DIGEST_HEX)
}

#[must_use]
pub fn pbm_hop7_export_residue_ledger_honest() -> bool {
    pbm_hop7_export_open_count() == OPEN_FORMAL_EXPORT_HOP_COUNT
        && PBM_HOP7_EXPORT_RESIDUE_LEDGER.iter().all(|r| !r.closed)
        && PBM_HOP7_EXPORT_RESIDUE_LEDGER[0].residue_id == HOP6_WIRE_ID
        && PBM_HOP7_EXPORT_RESIDUE_LEDGER[1].residue_id == HOP7_WIRE_ID
}

#[must_use]
pub fn pbm_hop7_export_ac64_absorbed() -> bool {
    workspace_file_on_disk(PRIOR_AC64_RECEIPT_PATH)
        && pbm_008_formal_fence_closed()
        && pbm_008_ac64_honest()
        && pbm_008_wire_hops_honest()
}

#[must_use]
pub fn pbm_hop7_export_ac344_absorbed() -> bool {
    workspace_file_on_disk(PRIOR_AC344_RECEIPT_PATH)
        && !pbm_008_fully_closed()
        && !pbm_hop6_export_wired()
        && catalog_live_export_deferred()
}

#[must_use]
pub fn pbm_hop7_export_ac134_absorbed() -> bool {
    workspace_file_on_disk(PRIOR_AC134_RECEIPT_PATH) && !pbm_008_production_wired()
}

#[must_use]
pub fn run_pbm_hop7_export_audit() -> Vec<PbmHop7ExportProbe> {
    vec![
        PbmHop7ExportProbe {
            probe: "hop6_open",
            green: !pbm_hop6_export_wired(),
            detail: "catalog_live_export hop 6 stays OPEN",
        },
        PbmHop7ExportProbe {
            probe: "hop7_open",
            green: !pbm_hop7_export_wired(),
            detail: "catalog_lock_manifold_fiber hop 7 stays OPEN",
        },
        PbmHop7ExportProbe {
            probe: "fully_closed_false",
            green: !pbm_008_fully_closed(),
            detail: "pbm_008_fully_closed() stays false",
        },
        PbmHop7ExportProbe {
            probe: "wire_hops_five_closed",
            green: pbm_008_wire_hops_honest(),
            detail: "5/6 PBM-008 wire hops closed — live export deferred",
        },
        PbmHop7ExportProbe {
            probe: "formal_fence_closed",
            green: pbm_008_formal_fence_closed(),
            detail: "formal anchor fence GREEN — not master lift",
        },
        PbmHop7ExportProbe {
            probe: "catalog_lock_on_disk",
            green: catalog_lock_on_disk() && catalog_digest_matches_lock(),
            detail: "catalog.lock.json pinned digest matches catalog.json",
        },
        PbmHop7ExportProbe {
            probe: "on_disk_census",
            green: pbm_008_on_disk_census_honest() && workspace_file_on_disk(CATALOG_LOCK_RELPATH),
            detail: "manifest · Lean · catalog · lock · script · witness",
        },
        PbmHop7ExportProbe {
            probe: "ac344_absorbed",
            green: pbm_hop7_export_ac344_absorbed(),
            detail: "AC344 hop6 formal absorbed without re-census",
        },
        PbmHop7ExportProbe {
            probe: "ac64_absorbed",
            green: pbm_hop7_export_ac64_absorbed(),
            detail: "AC64 formal fence absorbed",
        },
        PbmHop7ExportProbe {
            probe: "production_wired_false",
            green: !pbm_008_production_wired() && catalog_live_export_deferred(),
            detail: "production wiring not earned",
        },
    ]
}

#[must_use]
pub fn pbm_hop7_export_audit_all_green() -> bool {
    run_pbm_hop7_export_audit().iter().all(|p| p.green)
}

#[must_use]
pub fn pbm_hop7_export_honest() -> bool {
    FORMAL_POSTURE_TAG == POSTURE_TAG
        && !pbm_008_production_wired()
        && !pbm_008_fully_closed()
        && catalog_live_export_deferred()
        && !pbm_hop6_export_wired()
        && !pbm_hop7_export_wired()
        && pbm_008_wire_hops_honest()
        && pbm_008_formal_fence_closed()
        && pbm_hop7_export_residue_ledger_honest()
        && catalog_lock_on_disk()
        && catalog_digest_matches_lock()
        && pbm_hop7_export_ac64_absorbed()
        && pbm_hop7_export_ac344_absorbed()
        && pbm_hop7_export_ac134_absorbed()
        && pbm_hop7_export_audit_all_green()
}

#[test]
fn pbm_hop7_export_production_wired_honest_false() {
    assert!(!pbm_008_production_wired());
    assert!(!pbm_008_fully_closed());
    assert!(catalog_live_export_deferred());
    assert!(!pbm_hop6_export_wired());
    assert!(!pbm_hop7_export_wired());
}

#[test]
fn pbm_hop7_export_wire_hops_five_of_seven() {
    assert!(pbm_008_wire_hops_honest());
    assert_eq!(pbm_008_wire_hops_closed_count(), WIRE_HOPS_CLOSED);
    assert_eq!(WIRE_HOP_COUNT, 6);
    assert_eq!(FORMAL_EXPORT_WIRE_HOP_COUNT, 7);
    assert_eq!(FORMAL_EXPORT_HOPS_CLOSED, WIRE_HOPS_CLOSED);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].wire_id, HOP6_WIRE_ID);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].surface, HOP6_SURFACE);
    assert!(!FORMAL_ANCHOR_WIRE_HOPS[5].wired);
    assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[5].status, "OPEN");
}

#[test]
fn pbm_hop7_export_catalog_lock_on_disk() {
    assert!(catalog_lock_on_disk());
    assert!(catalog_digest_matches_lock());
    assert!(workspace_file_on_disk(CATALOG_LOCK_RELPATH));
    assert!(workspace_file_on_disk(CATALOG_REGEN_SCRIPT));
}

#[test]
fn pbm_hop7_export_residue_open_ledger() {
    assert!(pbm_hop7_export_residue_ledger_honest());
    assert_eq!(
        PBM_HOP7_EXPORT_RESIDUE_LEDGER.len(),
        OPEN_FORMAL_EXPORT_HOP_COUNT as usize
    );
    for entry in &PBM_HOP7_EXPORT_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
    assert_eq!(PBM_HOP7_EXPORT_RESIDUE_LEDGER[1].residue_id, HOP7_WIRE_ID);
    assert_eq!(PBM_HOP7_EXPORT_RESIDUE_LEDGER[1].blocker, "manifold INVARIANT_MANIFEST catalog digest fiber pin stale");
}

#[test]
fn pbm_hop7_export_ac344_absorbed_witness() {
    assert!(pbm_hop7_export_ac344_absorbed());
    assert!(workspace_file_on_disk(PRIOR_AC344_RECEIPT_PATH));
    assert!(!pbm_hop6_export_wired());
}

#[test]
fn pbm_hop7_export_ac64_absorbed_witness() {
    assert!(pbm_hop7_export_ac64_absorbed());
    assert!(workspace_file_on_disk(PRIOR_AC64_RECEIPT_PATH));
    assert_eq!(AC64_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC64-PBM-008");
    assert_eq!(AC64_RECEIPT_PATH, PRIOR_AC64_RECEIPT_PATH);
    let probe = pbm_008_ac64_deepen_probe();
    assert!(probe.formal_fence_closed);
    assert!(!probe.pbm_008_fully_closed);
    assert!(probe.pbm_008_flip_blocked);
}

#[test]
fn pbm_hop7_export_ac134_absorbed_witness() {
    assert!(pbm_hop7_export_ac134_absorbed());
    assert!(workspace_file_on_disk(PRIOR_AC134_RECEIPT_PATH));
}

#[test]
fn pbm_hop7_export_on_disk_census() {
    assert!(pbm_008_on_disk_census_honest());
    let root = workspace_root();
    assert!(root.join(PRIOR_AC344_RECEIPT_PATH).is_file());
    assert!(root.join(PRIOR_AC64_RECEIPT_PATH).is_file());
    assert!(root.join(CATALOG_LOCK_RELPATH).is_file());
}

#[test]
fn pbm_hop7_export_done_when_master_retick_blocked() {
    let done = pbm_008_done_when_probe();
    assert!(done.formal_anchor_fence_honest);
    assert!(!done.catalog_live_export_complete);
    assert!(!done.master_retick_eligible);
    assert_eq!(done.closure, "formal-fence-CLOSE / master-HOLD");
    assert!(!pbm_hop7_export_wired());
}

#[test]
fn pbm_hop7_export_audit_green() {
    let audit = run_pbm_hop7_export_audit();
    assert_eq!(audit.len(), FORMAL_HOP7_PROBE_COUNT);
    assert!(pbm_hop7_export_audit_all_green());
    for probe in &audit {
        assert!(probe.green, "probe {} must be green: {}", probe.probe, probe.detail);
    }
}

#[test]
fn fleet_composer_accel2_ac379_pbm_hop7_export_honest() {
    assert_eq!(AC379_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC379-PBM-HOP7");
    assert_eq!(AC379_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC379.md");
    assert_eq!(WORKSTREAM_ID, "WS-formal-anchors");
    assert_eq!(FORMAL_POSTURE_TAG, POSTURE_TAG);
    assert_eq!(HOP7_WIRE_ID, "catalog_lock_manifold_fiber");
    assert_eq!(HOP7_SURFACE, "umst-manifold catalog digest fiber pin");
    assert!(pbm_hop7_export_honest());
}
