// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL-L AC378 — PBM-014 embodiment guarded test honest witness.
// PENDING_GAPS §7.2: sustain `P3_MI_GATE_BLOCKED=true` across dignity/P3 coupling spine.
// File-based census (no egoff dep — AC134 scaffold owns Cargo.toml).
// Absorbs H69/J39 PBM-014 deepen + AGAP-2033/2350 chain without re-census.
//
// Doctrine by ref: H69 · J39 · AGAP-2033 · AGAP-2350 receipts + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-L slot id.
pub const AC378_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC378-PBM-014-EMBODIMENT";

/// AC378 completion receipt cross-ref.
pub const AC378_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC378.md";

/// AC378 scratch target dir.
pub const AC378_SCRATCH: &str = "/tmp/umst-accel2-ac378-pbm014";

/// H69 PBM-014 P3 coupling fence deepen receipt — absorbed, not re-census.
pub const PRIOR_H69_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_H69_2242.md";

/// J39 PBM open residue batch receipt — absorbs I75.
pub const PRIOR_J39_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_J39_2348.md";

/// AGAP-2033 PBM-014 deepen receipt.
pub const PRIOR_2033_RECEIPT_PATH: &str =
    "old/residuals/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_PBM-014_2033.md";

/// AGAP-2350 PBM-014 night audit receipt.
pub const PRIOR_2350_RECEIPT_PATH: &str =
    "old/residuals/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_PBM-014_2350.md";

/// Master pending gaps ledger — PBM-014 sustain row.
pub const TODO_MASTER_GAPS_PATH: &str =
    "old/residuals/residuals/misc-outputs-tmp/TODO_MASTER_PENDING_GAPS_1800.md";

/// Egoff PBM-014 dignity-freeze owner surface @ H69.
pub const EGOFF_OWNER_SURFACE: &str = "egoff/egoff/src/lib_learn_dignity_freeze.rs";

/// Bench consumer witness surface @ J39.
pub const BENCH_CONSUMER_SURFACE: &str = "crates/umst-bench/src/pbm_014_p3_coupling.rs";

/// Frozen posture pins fixture.
pub const POSTURE_FIXTURE_PATH: &str =
    "crates/umst-bench/fixtures/pbm_014_p3_coupling_posture.json";

/// Egoff wire integration witness @ H69.
pub const WIRE_TEST_PATH: &str = "egoff/egoff/tests/pbm014_p3_coupling_fence_wire.rs";

/// PBM-014 workstream id.
pub const WORKSTREAM_ID: &str = "WS-l10-p3-coupling";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-014";

/// Honest embodiment posture @ AC378 (matches H69 / J39 tier).
pub const POSTURE_TAG: &str = "honest-partial";

/// P3 coupling fence hop count @ H69 deepen.
pub const FENCE_HOP_COUNT: u8 = 5;

/// Egoff owner probe-wired hops @ H69 — PF0..PF2.
pub const EGOFF_PROBE_HOPS_WIRED: u8 = 3;

/// Bench consumer probe-wired hops @ Y63/F3 deepen — PF0..PF4.
pub const BENCH_PROBE_HOPS_WIRED: u8 = 5;

/// Honest production hops earned pin.
pub const PRODUCTION_HOPS_EARNED: u8 = 0;

/// Open production-tier residue count @ AC378.
pub const OPEN_RESIDUE_COUNT: u8 = 4;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm014EmbodimentResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC378 — production MI coupling tier only.
pub const PBM014_EMBODIMENT_RESIDUE_LEDGER: [Pbm014EmbodimentResidue;
    OPEN_RESIDUE_COUNT as usize] = [
    Pbm014EmbodimentResidue {
        residue_id: "p3_mi_gate_live_wire",
        blocker: "umst-semantics::p3_mi_gate live wire absent; PF3 bench preview only",
        owner: "umst-semantics",
        closed: false,
    },
    Pbm014EmbodimentResidue {
        residue_id: "p3_coupling_outcome_operator",
        blocker: "operator::P3CouplingOutcome @ HCOM-032 ceremony not landed",
        owner: "operator",
        closed: false,
    },
    Pbm014EmbodimentResidue {
        residue_id: "measured_mi_open_vocab",
        blocker: "open-vocab / measured MI not claimed; P3_MI_GATE_BLOCKED retained",
        owner: "PBM-014",
        closed: false,
    },
    Pbm014EmbodimentResidue {
        residue_id: "pbm_014_fully_closed",
        blocker: "no pbm_014_fully_closed() const on bench yet",
        owner: "future bench owner",
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

/// Census: egoff owner pins `P3_MI_GATE_BLOCKED = true`.
#[must_use]
pub fn p3_mi_gate_blocked_pinned_true(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, EGOFF_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const P3_MI_GATE_BLOCKED: bool = true")
        && src.contains("PARENT_PBM_JOB_ID")
        && src.contains("\"PBM-014\"")
        && src.contains("PBM014_WORKSTREAM_ID")
        && src.contains("WS-l10-p3-coupling")
}

/// Census: egoff owner declares `dignity_freeze_production_wired() -> false`.
#[must_use]
pub fn dignity_freeze_production_wired_false_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, EGOFF_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn dignity_freeze_production_wired() -> bool")
        && src.contains("false")
        && !src.contains("dignity_freeze_production_wired() -> bool {\n    true")
}

/// Census: egoff owner five-hop P3 coupling fence @ H69 deepen.
#[must_use]
pub fn pbm014_egoff_fence_hops_five_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, EGOFF_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const PBM014_P3_COUPLING_FENCE_HOPS")
        && src.contains("hop_id: \"PF0\"")
        && src.contains("hop_id: \"PF4\"")
        && src.contains("pbm014_p3_coupling_fence_honest")
        && src.contains("pbm014_j39_batch_honest")
}

/// Census: egoff owner pins production coupling false on preview.
#[must_use]
pub fn pbm014_production_coupling_not_invented(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, EGOFF_OWNER_SURFACE) else {
        return false;
    };
    src.contains("production_coupling_wired: false")
        && src.contains("pbm014_p3_coupling_fence_residual_honest")
        && !src.contains("production_coupling_wired: true")
}

/// Census: bench consumer declares `P3_MI_GATE_BLOCKED = true`.
#[must_use]
pub fn bench_p3_mi_gate_blocked_pinned(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const P3_MI_GATE_BLOCKED: bool = true")
        && src.contains("pub const PBM_OWNER: &str = \"PBM-014\"")
        && src.contains("pbm_014_p3_coupling_fence_honest")
}

/// Census: bench consumer five-hop fence + production flags false.
#[must_use]
pub fn bench_pbm014_fence_and_production_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, BENCH_CONSUMER_SURFACE) else {
        return false;
    };
    src.contains("pub const P3_COUPLING_FENCE_HOPS")
        && src.contains("hop_id: \"PF4\"")
        && src.contains("pub const fn pbm_014_fully_closed() -> bool")
        && src.contains("pbm_014_fully_closed() -> bool {\n    false")
        && src.contains("production_coupling_wired: false")
}

/// Census: posture fixture pins honest blocked gate + zero production hops.
#[must_use]
pub fn pbm014_posture_fixture_honest(root: &Path) -> bool {
    let Some(raw) = read_workspace_file(root, POSTURE_FIXTURE_PATH) else {
        return false;
    };
    raw.contains("\"pbm_owner\": \"PBM-014\"")
        && raw.contains("\"workstream_id\": \"WS-l10-p3-coupling\"")
        && raw.contains("\"p3_mi_gate_blocked\": true")
        && raw.contains("\"production_coupling_wired\": false")
        && raw.contains("\"production_hops_earned\": 0")
        && raw.contains("\"probe_hops_wired\": 5")
        && raw.contains("bench probe ≠ production MI coupling flip")
}

/// Census: wire test exists and references H69 fence hops.
#[must_use]
pub fn pbm014_wire_test_honest_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, WIRE_TEST_PATH) else {
        return false;
    };
    src.contains("PBM014_P3_COUPLING_FENCE_HOPS")
        && src.contains("pbm014_j39_batch_honest")
        && src.contains("dignity_freeze_production_wired")
}

#[must_use]
pub fn pbm014_embodiment_residue_ledger_honest() -> bool {
    PBM014_EMBODIMENT_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM014_EMBODIMENT_RESIDUE_LEDGER.len() == OPEN_RESIDUE_COUNT as usize
}

/// AC378 embodiment census — P3_MI_GATE_BLOCKED sustain; dignity freeze chain on disk.
#[must_use]
pub fn pbm014_embodiment_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && p3_mi_gate_blocked_pinned_true(root)
        && dignity_freeze_production_wired_false_on_disk(root)
        && pbm014_egoff_fence_hops_five_on_disk(root)
        && pbm014_production_coupling_not_invented(root)
        && bench_p3_mi_gate_blocked_pinned(root)
        && bench_pbm014_fence_and_production_false(root)
        && pbm014_posture_fixture_honest(root)
        && pbm014_wire_test_honest_on_disk(root)
        && pbm014_embodiment_residue_ledger_honest()
        && workspace_file_on_disk(root, EGOFF_OWNER_SURFACE)
        && workspace_file_on_disk(root, BENCH_CONSUMER_SURFACE)
}

/// Prior receipt chain absorption — H69 + J39 + AGAP-2033 + AGAP-2350.
#[must_use]
pub fn pbm014_prior_chain_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_H69_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_J39_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_2033_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_2350_RECEIPT_PATH)
}

/// H69 receipt pins P3_MI_GATE_BLOCKED and honest posture.
#[must_use]
pub fn pbm014_h69_docs_absorbed(root: &Path) -> bool {
    let Some(h69) = read_workspace_file(root, PRIOR_H69_RECEIPT_PATH) else {
        return false;
    };
    h69.contains("PBM-014")
        && h69.contains("P3_MI_GATE_BLOCKED")
        && h69.contains("dignity_freeze_production_wired() == false")
        && h69.contains("production_hops_earned")
}

/// J39 receipt chains H69 + I75 without production flip.
#[must_use]
pub fn pbm014_j39_docs_absorbed(root: &Path) -> bool {
    let Some(j39) = read_workspace_file(root, PRIOR_J39_RECEIPT_PATH) else {
        return false;
    };
    j39.contains("PBM-014")
        && j39.contains("pbm014_j39_batch_honest")
        && j39.contains("P3_MI_GATE_BLOCKED=true")
        && j39.contains("MASTER")
}

/// Master ledger sustain row pins PBM-014 `[~]` with blocked gate.
#[must_use]
pub fn pbm014_master_gaps_sustain_honest(root: &Path) -> bool {
    let Some(gaps) = read_workspace_file(root, TODO_MASTER_GAPS_PATH) else {
        return false;
    };
    gaps.contains("PBM-014")
        && gaps.contains("WS-l10-p3-coupling")
        && gaps.contains("P3_MI_GATE_BLOCKED")
}

/// AC378 honest gate — chains prior receipts + on-disk owner census.
#[must_use]
pub fn pbm014_ac378_embodiment_guarded_honest(root: &Path) -> bool {
    pbm014_embodiment_census_honest(root)
        && pbm014_prior_chain_absorbed(root)
        && pbm014_h69_docs_absorbed(root)
        && pbm014_j39_docs_absorbed(root)
        && pbm014_master_gaps_sustain_honest(root)
}

#[test]
fn ac378_metadata_wired() {
    assert_eq!(AC378_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC378-PBM-014-EMBODIMENT");
    assert_eq!(AC378_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC378.md");
    assert_eq!(AC378_SCRATCH, "/tmp/umst-accel2-ac378-pbm014");
    assert_eq!(WORKSTREAM_ID, "WS-l10-p3-coupling");
    assert_eq!(PBM_OWNER, "PBM-014");
    assert_eq!(POSTURE_TAG, "honest-partial");
}

#[test]
fn pbm014_p3_mi_gate_blocked_pinned_on_disk() {
    let root = workspace_root();
    assert!(
        p3_mi_gate_blocked_pinned_true(&root),
        "egoff owner must pin P3_MI_GATE_BLOCKED = true"
    );
    assert!(dignity_freeze_production_wired_false_on_disk(&root));
}

#[test]
fn pbm014_egoff_fence_hops_five_wired_on_disk() {
    let root = workspace_root();
    assert!(pbm014_egoff_fence_hops_five_on_disk(&root));
    assert_eq!(FENCE_HOP_COUNT, 5);
    assert_eq!(EGOFF_PROBE_HOPS_WIRED, 3);
    assert_eq!(PRODUCTION_HOPS_EARNED, 0);
}

#[test]
fn pbm014_bench_consumer_blocked_gate_on_disk() {
    let root = workspace_root();
    assert!(bench_p3_mi_gate_blocked_pinned(&root));
    assert!(bench_pbm014_fence_and_production_false(&root));
    assert_eq!(BENCH_PROBE_HOPS_WIRED, 5);
}

#[test]
fn pbm014_posture_fixture_honest_on_disk() {
    let root = workspace_root();
    assert!(pbm014_posture_fixture_honest(&root));
}

#[test]
fn pbm014_wire_test_witness_on_disk() {
    let root = workspace_root();
    assert!(pbm014_wire_test_honest_on_disk(&root));
    assert!(workspace_file_on_disk(&root, WIRE_TEST_PATH));
}

#[test]
fn pbm014_embodiment_residue_ledger_open() {
    assert!(pbm014_embodiment_residue_ledger_honest());
    for entry in &PBM014_EMBODIMENT_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm014_h69_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(pbm014_h69_docs_absorbed(&root));
    assert!(workspace_file_on_disk(&root, PRIOR_H69_RECEIPT_PATH));
}

#[test]
fn pbm014_j39_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(pbm014_j39_docs_absorbed(&root));
    assert!(workspace_file_on_disk(&root, PRIOR_J39_RECEIPT_PATH));
}

#[test]
fn pbm014_agap_prior_receipts_absorbed() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, PRIOR_2033_RECEIPT_PATH));
    assert!(workspace_file_on_disk(&root, PRIOR_2350_RECEIPT_PATH));
    let agap2350 = read_workspace_file(&root, PRIOR_2350_RECEIPT_PATH).expect("2350 receipt");
    assert!(agap2350.contains("P3_MI_GATE_BLOCKED"));
    assert!(agap2350.contains("PARTIAL"));
}

#[test]
fn pbm014_owner_surfaces_no_green_invent() {
    let root = workspace_root();
    assert!(pbm014_production_coupling_not_invented(&root));
    let bench = read_workspace_file(&root, BENCH_CONSUMER_SURFACE).expect("bench owner");
    assert!(!bench.contains("pbm_014_fully_closed() -> bool {\n    true"));
    let egoff = read_workspace_file(&root, EGOFF_OWNER_SURFACE).expect("egoff owner");
    assert!(!egoff.contains("dignity_freeze_production_wired() -> bool {\n    true"));
}

#[test]
fn pbm014_master_gaps_sustain_row() {
    let root = workspace_root();
    assert!(pbm014_master_gaps_sustain_honest(&root));
}

#[test]
fn pbm014_embodiment_census_honest_gate() {
    let root = workspace_root();
    assert!(pbm014_embodiment_census_honest(&root));
}

#[test]
fn fleet_composer_accel2_ac378_pbm014_embodiment_guarded_honest() {
    let root = workspace_root();
    assert!(pbm014_ac378_embodiment_guarded_honest(&root));
}
