// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-Y42 — LIB-ADOPT-F-LEAN-RS cold-path v2 + L1a/L1b pending inventory.
// Rust-side Lean adoption lane (no live Lean FFI) — witnessed-not-proved.

use std::path::{Path, PathBuf};

use super::lean_l1_bridge_prep::{
    lean_l1_bridge_j31_probe, lean_l1_bridge_prep_probe, COMPOSER_J31_RECEIPT_PATH,
    L1A_LEAN_MODULE, L1B_LEAN_MODULE, RECEIPT_PATH as H50_RECEIPT_PATH,
};
use super::lean_l1_stiffness_adopt::{
    lean_l1_adopt_audit_closed, Z37_RECEIPT_PATH as LEAN_L1_Z37_RECEIPT_PATH,
};

/// FLEET-COMPOSER-Y42 job id.
pub const JOB_ID: &str = "FLEET-COMPOSER-Y42-LEAN-RS";

/// FLEET-COMPOSER-Z65 Wave-Z slot id.
pub const Z65_JOB_ID: &str = "FLEET-COMPOSER-Z65-LEAN-RS";

/// Z65 Wave-Z slot label.
pub const Z65_WAVE_SLOT: &str = "Z65";

/// Z65 completion receipt cross-ref.
pub const Z65_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z65_1223.md";

/// LIB adoption workstream id.
pub const WORKSTREAM_ID: &str = "LIB-ADOPT-F-LEAN-RS";

/// Y42 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y42_0808.md";

/// Cold-path schema version (v2 — inventory + on-disk sources).
pub const SCHEMA_VERSION: &str = "lean_rs_cold_path.v2";

/// Prior H50 bridge prep receipt (absorb, do not redo).
pub const PRIOR_H50_RECEIPT_PATH: &str = H50_RECEIPT_PATH;

/// Prior J31 Lean L1 deepen receipt.
pub const PRIOR_J31_RECEIPT_PATH: &str = COMPOSER_J31_RECEIPT_PATH;

/// X37 launched slot — no receipt @ 07:34; Y42 absorbs theme without blind redo.
pub const PRIOR_X37_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_X37_0734.md";

/// Honest adoption tier — computational witness + filesystem census only.
pub const POSTURE_TAG: &str = "witnessed-not-proved";

/// L1a Lean source authority on disk (relative to `umst-formal/`).
pub const L1A_LEAN_SOURCE: &str = "Lean/Concrete/StiffnessTransition.lean";

/// L1b Lean source authority on disk (relative to `umst-formal/`).
pub const L1B_LEAN_SOURCE: &str = "Lean/Concrete/MicroMechanics.lean";

/// H50 Rust witness surface (cold-path v1).
pub const H50_RUST_SURFACE: &str = "ffi-bridge/src/lean_l1_bridge_prep.rs";

/// Pending inventory row disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeanRsPendingStatus {
    /// Closed on clean tree — measured or on-disk witness.
    Closed,
    /// Open residual — not claimed GREEN.
    Pending,
}

/// One L1a/L1b adoption inventory row for cold-path census.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeanRsPendingRow {
    pub layer: &'static str,
    pub item_id: &'static str,
    pub lean_source: &'static str,
    pub rust_surface: &'static str,
    pub status: LeanRsPendingStatus,
}

/// L1a/L1b pending inventory — SSOT for LIB-ADOPT-F-LEAN-RS cold-path v2.
pub const PENDING_INVENTORY: &[LeanRsPendingRow] = &[
    LeanRsPendingRow {
        layer: "L1a",
        item_id: "stiffness_transition_on_disk",
        lean_source: L1A_LEAN_SOURCE,
        rust_surface: H50_RUST_SURFACE,
        status: LeanRsPendingStatus::Closed,
    },
    LeanRsPendingRow {
        layer: "L1a",
        item_id: "stiffness_witness_row",
        lean_source: L1A_LEAN_MODULE,
        rust_surface: "lean_l1_bridge_prep::stiffness_scale_mono_holds",
        status: LeanRsPendingStatus::Closed,
    },
    LeanRsPendingRow {
        layer: "L1a",
        item_id: "stiffness_v2_q_grid_7_7",
        lean_source: L1A_LEAN_SOURCE,
        rust_surface: "lean_l1_stiffness_adopt::lean_l1_adopt_audit_closed (Z37)",
        status: LeanRsPendingStatus::Closed,
    },
    LeanRsPendingRow {
        layer: "L1a",
        item_id: "catalog_export_proved",
        lean_source: L1A_LEAN_SOURCE,
        rust_surface: "operator make lean-catalog-export",
        status: LeanRsPendingStatus::Pending,
    },
    LeanRsPendingRow {
        layer: "L1b",
        item_id: "micro_mechanics_on_disk",
        lean_source: L1B_LEAN_SOURCE,
        rust_surface: H50_RUST_SURFACE,
        status: LeanRsPendingStatus::Closed,
    },
    LeanRsPendingRow {
        layer: "L1b",
        item_id: "micro_mechanics_witness_rows",
        lean_source: L1B_LEAN_MODULE,
        rust_surface: "lean_l1_bridge_prep::l1_bridge_witness_rows (3× L1b)",
        status: LeanRsPendingStatus::Closed,
    },
    LeanRsPendingRow {
        layer: "L1b",
        item_id: "l1c_vinet_partition",
        lean_source: "Lean/Concrete/VinetPartition.lean",
        rust_surface: "continuum cartridge (OPEN)",
        status: LeanRsPendingStatus::Pending,
    },
    LeanRsPendingRow {
        layer: "L1b",
        item_id: "l1d_psi_damage_release",
        lean_source: "Lean/Concrete/ψ_damage_release (deferred)",
        rust_surface: "continuum cartridge (OPEN)",
        status: LeanRsPendingStatus::Pending,
    },
    LeanRsPendingRow {
        layer: "L1b",
        item_id: "catalog_export_proved",
        lean_source: L1B_LEAN_SOURCE,
        rust_surface: "operator make lean-catalog-export",
        status: LeanRsPendingStatus::Pending,
    },
];

/// Resolve `umst-formal/` root from this crate manifest.
#[must_use]
pub fn formal_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// Whether a Lean source path exists on disk under `umst-formal/`.
#[must_use]
pub fn lean_source_on_disk(rel: &str) -> bool {
    if rel.contains('*') || rel.contains("(deferred)") {
        return false;
    }
    formal_root().join(rel).is_file()
}

/// On-disk witness census for pinned L1a/L1b Lean authorities.
#[must_use]
pub fn l1_on_disk_sources() -> [(bool, &'static str); 2] {
    [
        (lean_source_on_disk(L1A_LEAN_SOURCE), L1A_LEAN_SOURCE),
        (lean_source_on_disk(L1B_LEAN_SOURCE), L1B_LEAN_SOURCE),
    ]
}

/// Count inventory rows marked closed vs pending.
#[must_use]
pub fn pending_inventory_census() -> (usize, usize) {
    let closed = PENDING_INVENTORY
        .iter()
        .filter(|r| r.status == LeanRsPendingStatus::Closed)
        .count();
    let pending = PENDING_INVENTORY
        .iter()
        .filter(|r| r.status == LeanRsPendingStatus::Pending)
        .count();
    (closed, pending)
}

/// Machine-checkable cold-path v2 probe for operator / fleet receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanRsColdPathV2Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub workstream_id: &'static str,
    pub schema_version: &'static str,
    pub posture: &'static str,
    pub prior_h50_receipt: &'static str,
    pub prior_j31_receipt: &'static str,
    pub inventory_rows: usize,
    pub inventory_closed: usize,
    pub inventory_pending: usize,
    pub l1a_on_disk: bool,
    pub l1b_on_disk: bool,
    pub h50_witness_rows: usize,
    pub lake_build_green: bool,
    pub lean_l1_fully_closed: bool,
    pub production_wired: bool,
}

/// Build FLEET-COMPOSER-Y42 lean-rs cold-path v2 probe.
#[must_use]
pub fn lean_rs_cold_path_v2_probe(lake_build_green: bool) -> LeanRsColdPathV2Probe {
    let (closed, pending) = pending_inventory_census();
    let on_disk = l1_on_disk_sources();
    let h50 = lean_l1_bridge_prep_probe(lake_build_green);
    let j31 = lean_l1_bridge_j31_probe(lake_build_green);
    debug_assert!(j31.h50_honest);

    LeanRsColdPathV2Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        workstream_id: WORKSTREAM_ID,
        schema_version: SCHEMA_VERSION,
        posture: POSTURE_TAG,
        prior_h50_receipt: PRIOR_H50_RECEIPT_PATH,
        prior_j31_receipt: PRIOR_J31_RECEIPT_PATH,
        inventory_rows: PENDING_INVENTORY.len(),
        inventory_closed: closed,
        inventory_pending: pending,
        l1a_on_disk: on_disk[0].0,
        l1b_on_disk: on_disk[1].0,
        h50_witness_rows: h50.witness_rows,
        lake_build_green,
        lean_l1_fully_closed: h50.lean_l1_fully_closed,
        production_wired: false,
    }
}

/// Machine-checkable Z65 probe — chains Y42 cold-path v2 + Z37 L1a adopt close.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanRsColdPathZ65Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub wave_slot: &'static str,
    pub workstream_id: &'static str,
    pub schema_version: &'static str,
    pub prior_y42_receipt: &'static str,
    pub prior_z37_receipt: &'static str,
    pub inventory_rows: usize,
    pub inventory_closed: usize,
    pub inventory_pending: usize,
    pub z37_adopt_closed: bool,
    pub l1a_on_disk: bool,
    pub l1b_on_disk: bool,
    pub lean_l1_fully_closed: bool,
    pub production_wired: bool,
}

/// Build FLEET-COMPOSER-Z65 lean-rs cold-path probe (Z37 absorb; no census redo).
#[must_use]
pub fn lean_rs_cold_path_z65_probe(lake_build_green: bool) -> LeanRsColdPathZ65Probe {
    let (closed, pending) = pending_inventory_census();
    let on_disk = l1_on_disk_sources();
    let h50 = lean_l1_bridge_prep_probe(lake_build_green);
    let z37_closed = lean_l1_adopt_audit_closed();

    LeanRsColdPathZ65Probe {
        job_id: Z65_JOB_ID,
        receipt_path: Z65_RECEIPT_PATH,
        wave_slot: Z65_WAVE_SLOT,
        workstream_id: WORKSTREAM_ID,
        schema_version: SCHEMA_VERSION,
        prior_y42_receipt: RECEIPT_PATH,
        prior_z37_receipt: LEAN_L1_Z37_RECEIPT_PATH,
        inventory_rows: PENDING_INVENTORY.len(),
        inventory_closed: closed,
        inventory_pending: pending,
        z37_adopt_closed: z37_closed,
        l1a_on_disk: on_disk[0].0,
        l1b_on_disk: on_disk[1].0,
        lean_l1_fully_closed: h50.lean_l1_fully_closed,
        production_wired: false,
    }
}

/// Z65 honesty gate — 5/9 inventory closed; Z37 L1a row absorbed; no fake GREEN.
#[must_use]
pub fn lean_rs_cold_path_z65_honest(probe: &LeanRsColdPathZ65Probe) -> bool {
    probe.job_id == Z65_JOB_ID
        && probe.receipt_path == Z65_RECEIPT_PATH
        && probe.wave_slot == Z65_WAVE_SLOT
        && probe.workstream_id == WORKSTREAM_ID
        && probe.schema_version == SCHEMA_VERSION
        && probe.prior_y42_receipt.contains("COMPOSER_Y42_0808")
        && probe.prior_z37_receipt.contains("COMPOSER_Z37")
        && probe.inventory_rows == 9
        && probe.inventory_closed == 5
        && probe.inventory_pending == 4
        && probe.z37_adopt_closed
        && probe.l1a_on_disk
        && probe.l1b_on_disk
        && !probe.lean_l1_fully_closed
        && !probe.production_wired
}

/// Honesty gate — cold-path v2 inventory + on-disk sources; no fake GREEN.
#[must_use]
pub fn lean_rs_cold_path_v2_honest(probe: &LeanRsColdPathV2Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path == RECEIPT_PATH
        && probe.workstream_id == WORKSTREAM_ID
        && probe.schema_version == SCHEMA_VERSION
        && probe.posture == POSTURE_TAG
        && probe.prior_h50_receipt.contains("COMPOSER_H50_2242")
        && probe.prior_j31_receipt.contains("COMPOSER_J31_2348")
        && probe.inventory_rows == 9
        && probe.inventory_closed == 5
        && probe.inventory_pending == 4
        && probe.l1a_on_disk
        && probe.l1b_on_disk
        && probe.h50_witness_rows == 4
        && !probe.lean_l1_fully_closed
        && !probe.production_wired
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn y42_metadata() {
        assert_eq!(JOB_ID, "FLEET-COMPOSER-Y42-LEAN-RS");
        assert_eq!(SCHEMA_VERSION, "lean_rs_cold_path.v2");
        assert!(RECEIPT_PATH.contains("COMPOSER_Y42_0808"));
    }

    #[test]
    fn l1a_l1b_lean_sources_on_disk() {
        let sources = l1_on_disk_sources();
        assert!(sources[0].0, "missing {}", sources[0].1);
        assert!(sources[1].0, "missing {}", sources[1].1);
        assert!(lean_source_on_disk(L1A_LEAN_SOURCE));
        assert!(lean_source_on_disk(L1B_LEAN_SOURCE));
    }

    #[test]
    fn pending_inventory_census_locked() {
        let (closed, pending) = pending_inventory_census();
        assert_eq!(PENDING_INVENTORY.len(), 9);
        assert_eq!(closed, 5);
        assert_eq!(pending, 4);
    }

    #[test]
    fn stiffness_v2_row_closed_via_z37_absorb() {
        let row = PENDING_INVENTORY
            .iter()
            .find(|r| r.item_id == "stiffness_v2_q_grid_7_7")
            .expect("stiffness_v2_q_grid_7_7 row");
        assert_eq!(row.status, LeanRsPendingStatus::Closed);
        assert!(lean_l1_adopt_audit_closed());
    }

    #[test]
    fn fleet_composer_z65_lean_rs_cold_path_z37_absorb() {
        let probe = lean_rs_cold_path_z65_probe(true);
        assert!(lean_rs_cold_path_z65_honest(&probe));
        assert!(probe.z37_adopt_closed);
        assert_eq!(probe.inventory_closed, 5);
        assert_eq!(probe.inventory_pending, 4);
        assert!(!probe.production_wired);
    }

    #[test]
    fn fleet_composer_y42_lean_rs_cold_path_v2() {
        let probe = lean_rs_cold_path_v2_probe(true);
        assert!(lean_rs_cold_path_v2_honest(&probe));
        assert!(probe.l1a_on_disk);
        assert!(probe.l1b_on_disk);
        assert_eq!(probe.h50_witness_rows, 4);
        assert!(!probe.production_wired);
        assert!(!probe.lean_l1_fully_closed);
    }
}
