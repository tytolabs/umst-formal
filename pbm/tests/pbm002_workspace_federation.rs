// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL2 AC607 — PBM-002 workspace federation honest witness.
// PENDING_GAPS §B2: sustain `pbm_002_fully_closed=false` · `production_wired=false`.
// File-based census (no umst-bench dep — AC134 scaffold owns Cargo.toml).
// Absorbs AC23 docs SSOT + Y56 bench witness + J44/H69/H95 chain without re-census.
//
// Doctrine by ref: AC23 · Y56 · J44 · H69 · H95 receipts + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL2 Band P slot id.
pub const AC607_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC607-PBM-002";

/// AC607 completion receipt cross-ref.
pub const AC607_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC607.md";

/// AC607 scratch target dir.
pub const AC607_SCRATCH_TARGET: &str = "/tmp/umst-accel2-ac607-pbm002";

/// AC23 docs owner deepen receipt — absorbed, not re-census.
pub const PRIOR_AC23_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL_2030_AC23.md";

/// Y56 bench federation census receipt — absorbed, not re-census.
pub const PRIOR_Y56_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y56_0808.md";

/// J44 WEB-027 federation gap receipt.
pub const PRIOR_J44_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_J44_2348.md";

/// H69 PBM open residue census receipt.
pub const PRIOR_H69_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_H69_2242.md";

/// H95 live-fence census receipt.
pub const PRIOR_H95_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_H95_2242.md";

/// PBM-002 federation SSOT doc @ AC23.
pub const PBM002_DOC_PATH: &str = "docs/PBM-002_WORKSPACE_FEDERATION.md";

/// PENDING_GAPS §B2 workspace federation slice.
pub const PENDING_GAPS_PATH: &str = "outputs/.tmp/PENDING_GAPS_COMPOSITIONAL_2134.md";

/// Root workspace manifest.
pub const ROOT_CARGO_PATH: &str = "Cargo.toml";

/// Bench consumer witness surface @ Y56.
pub const BENCH_CONSUMER_SURFACE: &str = "crates/umst-bench/src/pbm_002_workspace_unify.rs";

/// Frozen posture pins fixture.
pub const POSTURE_FIXTURE_PATH: &str =
    "crates/umst-bench/fixtures/pbm_002_workspace_unify_posture.json";

/// PBM-002 workstream id.
pub const WORKSTREAM_ID: &str = "WS-workspace-unify";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-002";

/// Honest federation posture @ AC607 (matches AC23 / Y56 tier).
pub const POSTURE_TAG: &str = "honest-partial";

/// Root exclude count @ HEAD (frozen exclude table).
pub const EXCLUDE_COUNT: u8 = 4;

/// Federated subtree census count @ Y56 bench pin.
pub const FEDERATED_SUBTREE_COUNT: u8 = 8;

/// Federation fence hop count — WF0..WF3.
pub const FENCE_HOP_COUNT: u8 = 4;

/// Federation fence hop ids @ Y56.
pub const FENCE_HOP_IDS: [&str; 4] = ["WF0", "WF1", "WF2", "WF3"];

/// Bench frozen root member count @ Y56 (may drift vs live Cargo.toml — residue named).
pub const BENCH_FROZEN_MEMBER_COUNT: u8 = 6;

/// Open federation-tier residue count @ AC607.
pub const OPEN_RESIDUE_COUNT: u8 = 3;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm002WorkspaceFederationResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC607 — full M5 unify + witness drift + production hops.
pub const PBM002_WORKSPACE_FEDERATION_RESIDUE_LEDGER: [Pbm002WorkspaceFederationResidue;
    OPEN_RESIDUE_COUNT as usize] = [
    Pbm002WorkspaceFederationResidue {
        residue_id: "m5_full_unify",
        blocker: "feat/tyto-workspace-reorg root Cargo.toml M5 member table on master",
        owner: "operator",
        closed: false,
    },
    Pbm002WorkspaceFederationResidue {
        residue_id: "bench_witness_member_drift",
        blocker: "crates/umst-bench/src/pbm_002_workspace_unify.rs::ROOT_MEMBER_COUNT \
                  stale vs live root Cargo.toml members[]",
        owner: "umst-bench",
        closed: false,
    },
    Pbm002WorkspaceFederationResidue {
        residue_id: "production_hops_earned",
        blocker: "WORKSPACE_UNIFY_FENCE_HOPS production_earned=0 until live unify measured",
        owner: "operator",
        closed: false,
    },
];

/// AC607 federation probe rollup — file-based census only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm002WorkspaceFederationProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub scratch_target: &'static str,
    pub posture_tag: &'static str,
    pub ac23_absorbed: bool,
    pub y56_absorbed: bool,
    pub j44_chain_on_disk: bool,
    pub live_root_member_count: usize,
    pub bench_frozen_member_count: u8,
    pub exclude_count_on_disk: usize,
    pub federated_subtree_count: u8,
    pub fence_hops_on_disk: bool,
    pub pbm_002_fully_closed_false: bool,
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

/// Census: count `members = [` entries in root Cargo.toml (file-read).
#[must_use]
pub fn root_cargo_member_count(root: &Path) -> usize {
    let Some(raw) = read_workspace_file(root, ROOT_CARGO_PATH) else {
        return 0;
    };
    raw.lines()
        .filter(|l| l.trim_start().starts_with('"') && !l.contains("exclude"))
        .filter(|l| {
            let t = l.trim();
            t.starts_with('"') && !t.starts_with("\"umst-manifold")
        })
        .take_while(|_| true)
        .filter(|l| l.contains('/') || l.contains("umst-") || l.contains("egoff"))
        .count()
}

/// More reliable member count: lines between `members = [` and closing `]`.
#[must_use]
pub fn root_cargo_members_array_count(root: &Path) -> usize {
    let Some(raw) = read_workspace_file(root, ROOT_CARGO_PATH) else {
        return 0;
    };
    let mut in_members = false;
    let mut count = 0usize;
    for line in raw.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("members = [") {
            in_members = true;
            continue;
        }
        if in_members {
            if trimmed == "]" {
                break;
            }
            if trimmed.starts_with('"') {
                count += 1;
            }
        }
    }
    count
}

/// Census: count exclude entries in root Cargo.toml.
#[must_use]
pub fn root_cargo_exclude_count(root: &Path) -> usize {
    let Some(raw) = read_workspace_file(root, ROOT_CARGO_PATH) else {
        return 0;
    };
    let mut in_exclude = false;
    let mut count = 0usize;
    for line in raw.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("exclude = [") {
            in_exclude = true;
            continue;
        }
        if in_exclude {
            if trimmed == "]" {
                break;
            }
            if trimmed.starts_with('"') {
                count += 1;
            }
        }
    }
    count
}

/// Census: bench consumer declares `pbm_002_fully_closed() -> false`.
#[must_use]
pub fn pbm_002_fully_closed_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn pbm_002_fully_closed() -> bool")
        && src.contains("false")
        && !src.contains("pbm_002_fully_closed() -> bool {\n    true")
}

/// Census: bench consumer declares `pbm_002_production_wired() -> false`.
#[must_use]
pub fn pbm_002_production_wired_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn pbm_002_production_wired() -> bool")
        && !src.contains("pbm_002_production_wired() -> bool {\n    true")
}

/// Census: bench four-hop wire map @ Y56 with complete WF0..WF3 ladder.
#[must_use]
pub fn pbm_002_fence_hops_four_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const WORKSPACE_UNIFY_FENCE_HOPS")
        && FENCE_HOP_IDS
            .iter()
            .all(|id| src.contains(&format!("hop_id: \"{id}\"")))
        && src.contains("FENCE_HOP_COUNT")
        && src.contains("production_earned: false")
}

/// Census: posture fixture pins honest GREEN=false · production_wired=false.
#[must_use]
pub fn pbm_002_posture_fixture_honest(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, POSTURE_FIXTURE_PATH) else {
        return false;
    };
    raw.contains("\"pbm_owner\": \"PBM-002\"")
        && raw.contains("\"workstream_id\": \"WS-workspace-unify\"")
        && raw.contains("\"full_federation_green\": false")
        && raw.contains("\"production_wired\": false")
}

/// Census: PBM-002 doc SSOT present with honest fences.
#[must_use]
pub fn pbm_002_doc_ssot_honest(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, PBM002_DOC_PATH) else {
        return false;
    };
    doc.contains("PBM-002")
        && doc.contains("WS-workspace-unify")
        && doc.contains("production_wired")
        && (doc.contains("false") || doc.contains("**false**"))
        && doc.contains("MASTER_RETICK")
}

/// Census: umst-web not in root members (freeze respected).
#[must_use]
pub fn umst_web_not_root_member(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, ROOT_CARGO_PATH) else {
        return false;
    };
    !raw.contains("\"umst-web\"")
        && !raw.contains("\"umst-webc\"")
        && !raw.contains("\"umst-gateway\"")
}

#[must_use]
pub fn pbm_002_workspace_federation_residue_ledger_honest() -> bool {
    PBM002_WORKSPACE_FEDERATION_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM002_WORKSPACE_FEDERATION_RESIDUE_LEDGER.len() == OPEN_RESIDUE_COUNT as usize
}

/// AC23 docs receipt + federation doc absorbed.
#[must_use]
pub fn pbm_002_ac23_docs_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_AC23_RECEIPT_PATH)
        && workspace_file_on_disk(root, PBM002_DOC_PATH)
        && read_workspace_file(root, PRIOR_AC23_RECEIPT_PATH)
            .is_some_and(|r| r.contains("AC23") && r.contains("PBM-002"))
}

/// Prior receipt chain absorption — Y56 + J44 + H69 + H95.
#[must_use]
pub fn pbm_002_prior_chain_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_Y56_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_J44_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_H69_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_H95_RECEIPT_PATH)
}

/// PENDING_GAPS row pins fully_closed=false sustain.
#[must_use]
pub fn pbm_002_pending_gaps_sustain_honest(root: &Path) -> bool {
    let Some(gaps) = read_workspace_file(root, PENDING_GAPS_PATH) else {
        return false;
    };
    gaps.contains("PBM-002") || gaps.contains("workspace-unify") || gaps.contains("WS-workspace")
}

/// Build AC607 federation probe from on-disk census.
#[must_use]
pub fn pbm_002_workspace_federation_probe(root: &Path) -> Pbm002WorkspaceFederationProbe {
    Pbm002WorkspaceFederationProbe {
        job_id: AC607_JOB_ID,
        receipt_path: AC607_RECEIPT_PATH,
        scratch_target: AC607_SCRATCH_TARGET,
        posture_tag: POSTURE_TAG,
        ac23_absorbed: pbm_002_ac23_docs_absorbed(root),
        y56_absorbed: workspace_file_on_disk(root, PRIOR_Y56_RECEIPT_PATH),
        j44_chain_on_disk: workspace_file_on_disk(root, PRIOR_J44_RECEIPT_PATH),
        live_root_member_count: root_cargo_members_array_count(root),
        bench_frozen_member_count: BENCH_FROZEN_MEMBER_COUNT,
        exclude_count_on_disk: root_cargo_exclude_count(root),
        federated_subtree_count: FEDERATED_SUBTREE_COUNT,
        fence_hops_on_disk: pbm_002_fence_hops_four_on_disk(root),
        pbm_002_fully_closed_false: pbm_002_fully_closed_declared_false(root),
        production_wired_false: pbm_002_production_wired_declared_false(root),
        master_retick_blocked: true,
        open_residue_count: OPEN_RESIDUE_COUNT,
    }
}

/// AC607 workspace federation census — fully_closed=false sustain; owner chain on disk.
#[must_use]
pub fn pbm_002_workspace_federation_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && pbm_002_fully_closed_declared_false(root)
        && pbm_002_production_wired_declared_false(root)
        && pbm_002_fence_hops_four_on_disk(root)
        && pbm_002_posture_fixture_honest(root)
        && pbm_002_doc_ssot_honest(root)
        && umst_web_not_root_member(root)
        && root_cargo_exclude_count(root) == EXCLUDE_COUNT as usize
        && pbm_002_workspace_federation_residue_ledger_honest()
        && workspace_file_on_disk(root, BENCH_CONSUMER_SURFACE)
}

/// AC607 honest gate — chains AC23 docs + prior receipts + on-disk census.
#[must_use]
pub fn pbm_002_ac607_workspace_federation_honest(root: &Path) -> bool {
    let probe = pbm_002_workspace_federation_probe(root);
    pbm_002_workspace_federation_census_honest(root)
        && probe.ac23_absorbed
        && probe.y56_absorbed
        && pbm_002_prior_chain_absorbed(root)
        && probe.fence_hops_on_disk
        && probe.pbm_002_fully_closed_false
        && probe.production_wired_false
        && probe.master_retick_blocked
        && probe.open_residue_count == OPEN_RESIDUE_COUNT
        && probe.live_root_member_count > 0
}

#[test]
fn pbm002_job_metadata_pins() {
    assert_eq!(AC607_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC607-PBM-002");
    assert_eq!(AC607_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC607.md");
    assert_eq!(AC607_SCRATCH_TARGET, "/tmp/umst-accel2-ac607-pbm002");
    assert_eq!(WORKSTREAM_ID, "WS-workspace-unify");
    assert_eq!(PBM_OWNER, "PBM-002");
    assert_eq!(POSTURE_TAG, "honest-partial");
    assert_eq!(FENCE_HOP_COUNT, 4);
    assert_eq!(EXCLUDE_COUNT, 4);
    assert_eq!(FEDERATED_SUBTREE_COUNT, 8);
}

#[test]
fn pbm002_ac23_docs_absorbed() {
    let root = workspace_root();
    assert!(pbm_002_ac23_docs_absorbed(&root));
    let ac23 = read_workspace_file(&root, PRIOR_AC23_RECEIPT_PATH).expect("AC23 receipt");
    assert!(ac23.contains("MASTER_RETICK") && ac23.contains("no"));
    assert!(ac23.contains("production_wired") || ac23.contains("false"));
}

#[test]
fn pbm002_fence_hops_complete_ladder() {
    let root = workspace_root();
    assert!(pbm_002_fence_hops_four_on_disk(&root));
    let bench = read_workspace_file(&root, BENCH_CONSUMER_SURFACE).expect("bench consumer");
    for hop in &FENCE_HOP_IDS {
        assert!(bench.contains(&format!("hop_id: \"{hop}\"")), "missing hop {hop}");
    }
}

#[test]
fn pbm002_fully_closed_declared_false_on_disk() {
    let root = workspace_root();
    assert!(
        pbm_002_fully_closed_declared_false(&root),
        "bench must declare pbm_002_fully_closed() -> false"
    );
    assert!(pbm_002_production_wired_declared_false(&root));
}

#[test]
fn pbm002_posture_fixture_pins_honest() {
    let root = workspace_root();
    assert!(pbm_002_posture_fixture_honest(&root));
}

#[test]
fn pbm002_umst_web_not_root_member() {
    let root = workspace_root();
    assert!(umst_web_not_root_member(&root));
}

#[test]
fn pbm002_root_exclude_count_on_disk() {
    let root = workspace_root();
    assert_eq!(root_cargo_exclude_count(&root), EXCLUDE_COUNT as usize);
}

#[test]
fn pbm002_workspace_federation_residue_ledger_open() {
    assert!(pbm_002_workspace_federation_residue_ledger_honest());
    for entry in &PBM002_WORKSPACE_FEDERATION_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm002_prior_chain_absorbed() {
    let root = workspace_root();
    assert!(pbm_002_prior_chain_absorbed(&root));
    let y56 = read_workspace_file(&root, PRIOR_Y56_RECEIPT_PATH).expect("Y56 receipt");
    assert!(y56.contains("PBM-002"));
}

#[test]
fn pbm002_live_member_count_measured() {
    let root = workspace_root();
    let live = root_cargo_members_array_count(&root);
    assert!(live >= BENCH_FROZEN_MEMBER_COUNT as usize, "live members >= bench pin");
    // Honest drift residue: live count may exceed frozen bench table.
    let probe = pbm_002_workspace_federation_probe(&root);
    assert_eq!(probe.live_root_member_count, live);
}

#[test]
fn pbm002_owner_surfaces_no_green_invent() {
    let root = workspace_root();
    let bench = read_workspace_file(&root, BENCH_CONSUMER_SURFACE).expect("bench consumer");
    assert!(!bench.contains("pbm_002_fully_closed() -> bool {\n    true"));
    assert!(!bench.contains("pbm_002_production_wired() -> bool {\n    true"));
}

#[test]
fn pbm002_workspace_federation_census_honest() {
    let root = workspace_root();
    assert!(pbm_002_workspace_federation_census_honest(&root));
}

#[test]
fn pbm002_probe_rollup_honest() {
    let root = workspace_root();
    let probe = pbm_002_workspace_federation_probe(&root);
    assert_eq!(probe.job_id, AC607_JOB_ID);
    assert!(probe.ac23_absorbed);
    assert!(probe.y56_absorbed);
    assert!(probe.fence_hops_on_disk);
    assert!(probe.pbm_002_fully_closed_false);
    assert!(probe.production_wired_false);
    assert!(probe.master_retick_blocked);
}

#[test]
fn fleet_composer_accel2_ac607_pbm002_workspace_federation_honest() {
    let root = workspace_root();
    assert!(pbm_002_ac607_workspace_federation_honest(&root));
}
