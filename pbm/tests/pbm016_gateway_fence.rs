// SPDX-License-Identifier: MIT
// Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
//
// FLEET-COMPOSER-ACCEL-G AC153 — PBM-016 gateway fence test honest witness.
// PENDING_GAPS §B1: sustain `production_wired=false` across gateway/MCP/SEC spine.
// File-based census (no umst-gateway dep — AC134 scaffold owns Cargo.toml).
// Absorbs AC67 docs SSOT + Z41 federation + H67 live fence without re-census.
//
// Doctrine by ref: AC67 · Z41 · Y56 · J38 receipts + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-G slot id.
pub const AC153_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC153-PBM-016";

/// AC153 completion receipt cross-ref.
pub const AC153_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC153.md";

/// AC67 docs owner deepen receipt — absorbed, not re-census.
pub const PRIOR_AC67_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC67.md";

/// Z41 gateway federation CLOSE receipt.
pub const PRIOR_Z41_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z41_1015.md";

/// Y56 bench federation census receipt.
pub const PRIOR_Y56_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y56_0808.md";

/// H67 / J38 MCP live fence SSOT receipts.
pub const PRIOR_PBM003_LIVE_FENCE_PATH: &str = "outputs/.tmp/PBM_003_LIVE_FENCE.md";
pub const PRIOR_J38_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_J38_2348.md";

/// PBM-016 gateway fence SSOT @ AC67.
pub const GATEWAY_FENCE_DOC_PATH: &str = "docs/PBM-016_GATEWAY_FENCE.md";

/// PENDING_GAPS §B1 gateway spine slice.
pub const PENDING_GAPS_PATH: &str = "outputs/.tmp/PENDING_GAPS_COMPOSITIONAL_2134.md";

/// Gateway workspace root marker.
pub const GATEWAY_WORKSPACE_CARGO: &str = "umst-gateway/Cargo.toml";

/// Root workspace manifest — gateway must not appear in members.
pub const ROOT_CARGO_PATH: &str = "Cargo.toml";

/// PBM-002 federation fence owner @ Z41.
pub const PBM002_OWNER_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/pbm_002_workspace_unify.rs";

/// PBM-003 MCP live fence owner @ H67.
pub const PBM003_OWNER_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/pbm_003_gateway_wrap.rs";

/// SEC-GW trust wrap owner.
pub const SEC_GW_TRUST_WRAP_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/sec_gw_trust_wrap.rs";

/// SEC-MCP stdio exec trust pre-check owner.
pub const SEC_MCP_WRAP_SURFACE: &str = "umst-gateway/crates/umst-gateway/src/sec_mcp_wrap.rs";

/// F4 spine + gateway bridge prep owner.
pub const GATEWAY_BRIDGE_PREP_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/gateway_bridge_prep.rs";

/// F4 spine close path owner.
pub const F4_SPINE_CLOSE_PATH_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/spine_close_path.rs";

/// PBM-016 workstream id.
pub const WORKSTREAM_ID: &str = "WS-gateway-fence";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-016";

/// Honest gateway fence posture @ AC153 (matches AC67 / PBM-002 tier).
pub const POSTURE_TAG: &str = "honest-partial";

/// Federation fence hop count (WG0–WG3).
pub const FEDERATION_FENCE_HOP_COUNT: u8 = 4;

/// MCP live fence hop count (LF0–LF5).
pub const MCP_LIVE_FENCE_HOP_COUNT: u8 = 6;

/// MCP live fence probe-wired count @ H67.
pub const MCP_LIVE_PROBE_HOPS_WIRED: u8 = 5;

/// Honest spine counter pin.
pub const SPINE_NODES_CLOSED_PIN: &str = "0/7";

/// Gateway wire layer count on owner pkg.
pub const GATEWAY_WIRE_LAYER_COUNT: u8 = 5;

/// Open production-tier residue count @ AC153.
pub const OPEN_RESIDUE_COUNT: u8 = 6;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm016GatewayFenceResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC153 — production hops 0 earned across all fence layers.
pub const PBM016_GATEWAY_FENCE_RESIDUE_LEDGER: [Pbm016GatewayFenceResidue;
    OPEN_RESIDUE_COUNT as usize] = [
    Pbm016GatewayFenceResidue {
        residue_id: "mcp_live_wrap_closure",
        blocker: "gateway_wrap_native_mcp_closed()==false",
        owner: "pbm_003_gateway_wrap.rs",
        closed: false,
    },
    Pbm016GatewayFenceResidue {
        residue_id: "sec_mcp_stdio_pre_check",
        blocker: "mcp_stdio_exec_trust_pre_check_wired()==false",
        owner: "sec_mcp_wrap.rs",
        closed: false,
    },
    Pbm016GatewayFenceResidue {
        residue_id: "trust_wrap_production",
        blocker: "trust_wrap_wired()==false",
        owner: "sec_gw_trust_wrap.rs",
        closed: false,
    },
    Pbm016GatewayFenceResidue {
        residue_id: "f4_spine_flip",
        blocker: "SPINE_NODES_CLOSED==0/7",
        owner: "f4_spine_close_path.rs",
        closed: false,
    },
    Pbm016GatewayFenceResidue {
        residue_id: "gateway_bridge_closed",
        blocker: "gateway_bridge_closed()==false",
        owner: "gateway_bridge_prep.rs",
        closed: false,
    },
    Pbm016GatewayFenceResidue {
        residue_id: "pbm_016_bench_witness",
        blocker: "no pbm_016_fully_closed() const on bench yet",
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

/// Census: gateway separate workspace Cargo.toml present.
#[must_use]
pub fn gateway_separate_workspace_on_disk(root: &Path) -> bool {
    workspace_file_on_disk(root, GATEWAY_WORKSPACE_CARGO)
        && workspace_file_on_disk(
            root,
            "umst-gateway/crates/umst-gateway/Cargo.toml",
        )
}

/// Census: root `Cargo.toml` omits `umst-gateway` from workspace members.
#[must_use]
pub fn gateway_not_root_member_on_disk(root: &Path) -> bool {
    let Some(root_cargo) = read_workspace_file(root, ROOT_CARGO_PATH) else {
        return false;
    };
    !root_cargo.contains("umst-gateway")
}

/// Census: PBM-002 federation fence four-hop map @ Z41.
#[must_use]
pub fn pbm_002_federation_hops_four_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, PBM002_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const GATEWAY_FENCE_HOP_COUNT: usize = 4")
        && src.contains("pub const GATEWAY_PROBE_HOPS_WIRED: usize = 4")
        && src.contains("hop_id: \"WG3\"")
        && src.contains("pub const fn pbm_002_fully_closed() -> bool")
        && src.contains("pub const fn pbm_002_production_wired() -> bool")
}

/// Census: PBM-002 production flags declared false.
#[must_use]
pub fn pbm_002_production_flags_declared_false(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, PBM002_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn pbm_002_fully_closed() -> bool")
        && src.contains("pub const fn pbm_002_production_wired() -> bool")
        && !src.contains("pbm_002_fully_closed() -> bool {\n    true")
        && !src.contains("pbm_002_production_wired() -> bool {\n    true")
}

/// Census: PBM-003 declares `gateway_wrap_native_mcp_closed() -> false`.
#[must_use]
pub fn gateway_wrap_native_mcp_closed_false_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, PBM003_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const fn gateway_wrap_native_mcp_closed() -> bool")
        && src.contains("SPINE_NODES_CLOSED: &str = \"0/7\"")
        && !src.contains("gateway_wrap_native_mcp_closed() -> bool {\n    true")
}

/// Census: SEC-GW declares `trust_wrap_wired() -> false` with compile-time fence.
#[must_use]
pub fn trust_wrap_wired_false_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, SEC_GW_TRUST_WRAP_SURFACE) else {
        return false;
    };
    src.contains("pub const fn trust_wrap_wired() -> bool")
        && src.contains("assert!(!trust_wrap_wired())")
        && !src.contains("trust_wrap_wired() -> bool {\n    true")
}

/// Census: SEC-MCP stdio exec pre-check stays open.
#[must_use]
pub fn mcp_stdio_exec_trust_pre_check_false_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, SEC_MCP_WRAP_SURFACE) else {
        return false;
    };
    src.contains("pub const fn mcp_stdio_exec_trust_pre_check_wired() -> bool")
        && !src.contains("mcp_stdio_exec_trust_pre_check_wired() -> bool {\n    true")
}

/// Census: gateway bridge closure stays false.
#[must_use]
pub fn gateway_bridge_closed_false_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, GATEWAY_BRIDGE_PREP_SURFACE) else {
        return false;
    };
    src.contains("pub const fn gateway_bridge_closed() -> bool")
        && !src.contains("gateway_bridge_closed() -> bool {\n    true")
}

/// Census: F4 spine close path documents D0–D6 honest false posture.
#[must_use]
pub fn f4_spine_close_path_honest_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, F4_SPINE_CLOSE_PATH_SURFACE) else {
        return false;
    };
    src.contains("f4_spine_close_path")
        && (src.contains("D0") || src.contains("d0_residual"))
        && src.contains("CLOSE_PATH_NODE_IDS")
}

/// Census: PBM-016 SSOT doc pins five fence layers + MASTER_RETICK=no.
#[must_use]
pub fn pbm_016_gateway_fence_doc_honest(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, GATEWAY_FENCE_DOC_PATH) else {
        return false;
    };
    doc.contains("PBM-016 — Gateway Fence SSOT")
        && doc.contains("WG0–WG3")
        && doc.contains("LF0–LF5")
        && doc.contains("gateway_wrap_native_mcp_closed")
        && doc.contains("trust_wrap_wired")
        && doc.contains("SPINE_NODES_CLOSED")
        && doc.contains("gateway_bridge_closed")
        && doc.contains("MASTER_RETICK:** **no**")
        && doc.contains("production_wired")
}

/// Census: PBM-003 live fence SSOT pins 5/6 probe · 0/6 live.
#[must_use]
pub fn pbm_003_live_fence_ssot_honest(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, PRIOR_PBM003_LIVE_FENCE_PATH) else {
        return false;
    };
    doc.contains("gateway_wrap_native_mcp_closed")
        && doc.contains("trust_wrap_wired")
        && doc.contains("live_hops_earned")
        && doc.contains("0 / 6")
        && doc.contains("5/6")
}

#[must_use]
pub fn pbm016_gateway_fence_residue_ledger_honest() -> bool {
    PBM016_GATEWAY_FENCE_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM016_GATEWAY_FENCE_RESIDUE_LEDGER.len() == OPEN_RESIDUE_COUNT as usize
}

/// Prior receipt chain absorption — AC67 + Z41 + Y56 + J38 + PBM-003 SSOT.
#[must_use]
pub fn pbm016_prior_chain_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_AC67_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_Z41_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_Y56_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_PBM003_LIVE_FENCE_PATH)
        && workspace_file_on_disk(root, PRIOR_J38_RECEIPT_PATH)
        && workspace_file_on_disk(root, GATEWAY_FENCE_DOC_PATH)
}

/// PENDING_GAPS §B1 row pins gateway bridge production_wired=false sustain.
#[must_use]
pub fn pbm016_pending_gaps_sustain_honest(root: &Path) -> bool {
    let Some(gaps) = read_workspace_file(root, PENDING_GAPS_PATH) else {
        return false;
    };
    gaps.contains("gateway bridge")
        && gaps.contains("production_wired=false")
        && gaps.contains("gateway_bridge_closed")
}

/// AC153 gateway fence census — production hops 0 earned; five layers on disk.
#[must_use]
pub fn pbm016_gateway_fence_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && gateway_separate_workspace_on_disk(root)
        && gateway_not_root_member_on_disk(root)
        && pbm_002_federation_hops_four_on_disk(root)
        && pbm_002_production_flags_declared_false(root)
        && gateway_wrap_native_mcp_closed_false_on_disk(root)
        && trust_wrap_wired_false_on_disk(root)
        && mcp_stdio_exec_trust_pre_check_false_on_disk(root)
        && gateway_bridge_closed_false_on_disk(root)
        && f4_spine_close_path_honest_on_disk(root)
        && pbm_016_gateway_fence_doc_honest(root)
        && pbm_003_live_fence_ssot_honest(root)
        && pbm016_gateway_fence_residue_ledger_honest()
}

/// AC67 docs deepen absorbed — topology CLOSE ≠ production flip.
#[must_use]
pub fn pbm016_ac67_docs_absorbed(root: &Path) -> bool {
    let Some(ac67) = read_workspace_file(root, PRIOR_AC67_RECEIPT_PATH) else {
        return false;
    };
    ac67.contains("PBM-016")
        && ac67.contains("gateway fence")
        && ac67.contains("CLOSE")
        && ac67.contains("MASTER_RETICK")
        && ac67.contains("no")
        && ac67.contains("production hops")
        && ac67.contains("across all fence layers")
}

/// AC153 honest gate — chains prior receipts + on-disk owner census.
#[must_use]
pub fn pbm016_ac153_gateway_fence_honest(root: &Path) -> bool {
    pbm016_gateway_fence_census_honest(root)
        && pbm016_prior_chain_absorbed(root)
        && pbm016_ac67_docs_absorbed(root)
        && pbm016_pending_gaps_sustain_honest(root)
}

#[test]
fn pbm016_gateway_separate_workspace_on_disk() {
    let root = workspace_root();
    assert!(gateway_separate_workspace_on_disk(&root));
    assert!(gateway_not_root_member_on_disk(&root));
}

#[test]
fn pbm016_pbm002_federation_hops_four_wired_on_disk() {
    let root = workspace_root();
    assert!(pbm_002_federation_hops_four_on_disk(&root));
    assert!(pbm_002_production_flags_declared_false(&root));
    assert_eq!(FEDERATION_FENCE_HOP_COUNT, 4);
}

#[test]
fn pbm016_pbm003_mcp_live_fence_pins_honest_false() {
    let root = workspace_root();
    assert!(gateway_wrap_native_mcp_closed_false_on_disk(&root));
    assert!(trust_wrap_wired_false_on_disk(&root));
    assert!(mcp_stdio_exec_trust_pre_check_false_on_disk(&root));
    assert_eq!(SPINE_NODES_CLOSED_PIN, "0/7");
    assert_eq!(MCP_LIVE_FENCE_HOP_COUNT, 6);
    assert_eq!(MCP_LIVE_PROBE_HOPS_WIRED, 5);
}

#[test]
fn pbm016_gateway_bridge_and_spine_open_on_disk() {
    let root = workspace_root();
    assert!(gateway_bridge_closed_false_on_disk(&root));
    assert!(f4_spine_close_path_honest_on_disk(&root));
}

#[test]
fn pbm016_gateway_fence_residue_ledger_open() {
    assert!(pbm016_gateway_fence_residue_ledger_honest());
    for entry in &PBM016_GATEWAY_FENCE_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm016_gateway_fence_doc_ssot_on_disk() {
    let root = workspace_root();
    assert!(pbm_016_gateway_fence_doc_honest(&root));
    assert!(pbm_003_live_fence_ssot_honest(&root));
    assert_eq!(GATEWAY_WIRE_LAYER_COUNT, 5);
}

#[test]
fn pbm016_ac67_prior_receipt_absorbed() {
    let root = workspace_root();
    assert!(pbm016_ac67_docs_absorbed(&root));
    assert!(workspace_file_on_disk(&root, PRIOR_AC67_RECEIPT_PATH));
    assert!(workspace_file_on_disk(&root, GATEWAY_FENCE_DOC_PATH));
}

#[test]
fn pbm016_z41_y56_j38_chain_absorbed() {
    let root = workspace_root();
    assert!(pbm016_prior_chain_absorbed(&root));
    let z41 = read_workspace_file(&root, PRIOR_Z41_RECEIPT_PATH).expect("Z41 receipt");
    assert!(z41.contains("pbm_002") || z41.contains("gateway"));
    let y56 = read_workspace_file(&root, PRIOR_Y56_RECEIPT_PATH).expect("Y56 receipt");
    assert!(y56.contains("gateway") || y56.contains("federation"));
    let j38 = read_workspace_file(&root, PRIOR_J38_RECEIPT_PATH).expect("J38 receipt");
    assert!(j38.contains("PBM-003") || j38.contains("gateway"));
}

#[test]
fn pbm016_owner_surfaces_no_green_invent() {
    let root = workspace_root();
    let pbm002 = read_workspace_file(&root, PBM002_OWNER_SURFACE).expect("PBM-002 owner");
    assert!(!pbm002.contains("pbm_002_fully_closed() -> bool {\n    true"));
    let pbm003 = read_workspace_file(&root, PBM003_OWNER_SURFACE).expect("PBM-003 owner");
    assert!(!pbm003.contains("gateway_wrap_native_mcp_closed() -> bool {\n    true"));
    let trust = read_workspace_file(&root, SEC_GW_TRUST_WRAP_SURFACE).expect("SEC-GW owner");
    assert!(!trust.contains("trust_wrap_wired() -> bool {\n    true"));
    let bridge = read_workspace_file(&root, GATEWAY_BRIDGE_PREP_SURFACE).expect("bridge prep");
    assert!(!bridge.contains("gateway_bridge_closed() -> bool {\n    true"));
}

#[test]
fn pbm016_master_retick_blocked_via_ac67() {
    let root = workspace_root();
    let ac67 = read_workspace_file(&root, PRIOR_AC67_RECEIPT_PATH).expect("AC67 receipt");
    assert!(ac67.contains("MASTER_RETICK") && ac67.contains("no"));
    assert!(ac67.contains("gateway_wrap_native_mcp_closed()==false"));
    assert!(ac67.contains("SPINE_NODES_CLOSED==0/7"));
}

#[test]
fn pbm016_pending_gaps_sustain_row() {
    let root = workspace_root();
    assert!(pbm016_pending_gaps_sustain_honest(&root));
}

#[test]
fn pbm016_gateway_fence_census_honest_gate() {
    let root = workspace_root();
    assert!(pbm016_gateway_fence_census_honest(&root));
}

#[test]
fn fleet_composer_accel2_ac153_pbm016_gateway_fence_honest() {
    assert_eq!(AC153_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC153-PBM-016");
    assert_eq!(AC153_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC153.md");
    assert_eq!(WORKSTREAM_ID, "WS-gateway-fence");
    assert_eq!(PBM_OWNER, "PBM-016");
    assert_eq!(POSTURE_TAG, "honest-partial");
    let root = workspace_root();
    assert!(pbm016_ac153_gateway_fence_honest(&root));
}
