// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-L AC377 — PBM-003 MCP trust fence honest witness.
// PENDING_GAPS §B1: sustain `production_wired=false` on umst-mcp L4/L5 trust + native wrap.
// File-based census (no umst-gateway dep — AC134 scaffold owns Cargo.toml).
// Absorbs J38 cluster + H67 live fence + PBM-003 MANIFEST without re-census.
//
// Doctrine by ref: J38 · H67 · G06 receipts + owner surfaces on disk.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-L slot id.
pub const AC377_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC377-PBM-003";

/// AC377 completion receipt cross-ref.
pub const AC377_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC377.md";

/// J38 PBM-003 cluster deepen receipt — absorbed, not re-census.
pub const PRIOR_J38_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_J38_2348.md";

/// H67 live fence deepen receipt — absorbed, not re-census.
pub const PRIOR_H67_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_H67_2242.md";

/// PBM-003 live fence SSOT @ J38/H67.
pub const PBM003_LIVE_FENCE_PATH: &str = "outputs/.tmp/PBM_003_LIVE_FENCE.md";

/// PBM-003 owner path marker @ J38.
pub const PBM003_MANIFEST_PATH: &str = "umst-gateway/PBM-003/MANIFEST.md";

/// PBM-003 cluster SSOT (J38 sibling).
pub const PBM003_CLUSTER_FENCE_PATH: &str = "outputs/.tmp/PBM_018_003_LIVE_FENCE_CLUSTER.md";

/// PENDING_GAPS §B1 umst-mcp L4/L5 sustain slice.
pub const PENDING_GAPS_PATH: &str = "outputs/.tmp/PENDING_GAPS_COMPOSITIONAL_2134.md";

/// PBM-003 primary owner surface.
pub const PBM003_OWNER_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/pbm_003_gateway_wrap.rs";

/// SEC-GW trust wrap owner.
pub const SEC_GW_TRUST_WRAP_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/sec_gw_trust_wrap.rs";

/// SEC-MCP stdio exec trust pre-check owner.
pub const SEC_MCP_WRAP_SURFACE: &str = "umst-gateway/crates/umst-gateway/src/sec_mcp_wrap.rs";

/// Stdio delegate exec owner.
pub const STDIO_DELEGATE_SURFACE: &str =
    "umst-gateway/crates/umst-gateway/src/stdio_delegate.rs";

/// PBM-003 workstream id.
pub const WORKSTREAM_ID: &str = "WS-gateway-wrap";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-003";

/// Honest MCP trust posture @ AC377 (matches J38 / H67 tier).
pub const POSTURE_TAG: &str = "honest-partial";

/// Trust/gate wire map hop count (material delegate + routing + SEC-MCP).
pub const TRUST_GATE_WIRE_HOP_COUNT: u8 = 7;

/// Live fence hop count (LF0–LF5).
pub const LIVE_FENCE_HOP_COUNT: u8 = 6;

/// Live fence probe hops wired @ H67/J38.
pub const LIVE_PROBE_HOPS_WIRED: u8 = 5;

/// Live hops earned @ H67/J38 — honest zero.
pub const LIVE_HOPS_EARNED: u8 = 0;

/// Honest spine counter pin.
pub const SPINE_NODES_CLOSED_PIN: &str = "0/7";

/// Constitutional native tool manifest count.
pub const NATIVE_TOOL_MANIFEST_COUNT: u8 = 13;

/// Open MCP-trust residue count @ AC377.
pub const OPEN_RESIDUE_COUNT: u8 = 5;

/// Open residue ledger entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm003McpTrustResidue {
    pub residue_id: &'static str,
    pub blocker: &'static str,
    pub owner: &'static str,
    pub closed: bool,
}

/// Measured open residue @ AC377 — production trust tier stays open.
pub const PBM003_MCP_TRUST_RESIDUE_LEDGER: [Pbm003McpTrustResidue;
    OPEN_RESIDUE_COUNT as usize] = [
    Pbm003McpTrustResidue {
        residue_id: "stdio_exec_trust_pre_check",
        blocker: "mcp_stdio_exec_trust_pre_check_wired()==false",
        owner: "sec_mcp_wrap.rs",
        closed: false,
    },
    Pbm003McpTrustResidue {
        residue_id: "gateway_wrap_native_mcp",
        blocker: "gateway_wrap_native_mcp_closed()==false",
        owner: "pbm_003_gateway_wrap.rs",
        closed: false,
    },
    Pbm003McpTrustResidue {
        residue_id: "trust_wrap_production",
        blocker: "trust_wrap_wired()==false",
        owner: "sec_gw_trust_wrap.rs",
        closed: false,
    },
    Pbm003McpTrustResidue {
        residue_id: "live_hops_earned",
        blocker: "live_hops_earned==0/6",
        owner: "PBM_003_LIVE_FENCE.md",
        closed: false,
    },
    Pbm003McpTrustResidue {
        residue_id: "operator_ceremony_lf5",
        blocker: "LF5 operator flip OPEN",
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

/// Census: PBM-003 owner declares 7-hop trust/gate wire map.
#[must_use]
pub fn pbm_003_trust_gate_wire_hops_seven_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, PBM003_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const TRUST_GATE_WIRE_HOPS")
        && src.contains("TRUST_GATE_WIRE_HOPS.len() == 7")
        && src.contains("gate_check_material_delegate_witness")
        && src.contains("exec_native_mcp_delegate")
        && src.contains("mcp_stdio_exec_trust_pre_check_wired")
        && src.contains("pub const fn gateway_wrap_native_mcp_closed() -> bool")
        && !src.contains("gateway_wrap_native_mcp_closed() -> bool {\n    true")
}

/// Census: PBM-003 spine + ceremony gap pins honest false posture.
#[must_use]
pub fn pbm_003_ceremony_gap_honest_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, PBM003_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const SPINE_NODES_CLOSED: &str = \"0/7\"")
        && src.contains("pub fn pbm_003_ceremony_gap_honest")
        && src.contains("pub fn pbm_003_trust_gate_probe_honest")
        && src.contains("!probe.stdio_exec_trust_pre_check_wired")
        && src.contains("!probe.gateway_wrap_native_mcp_closed")
        && src.contains("Pbm003Closure::Partial")
}

/// Census: PBM-003 declares PBM id + workstream + native manifest count.
#[must_use]
pub fn pbm_003_identity_pins_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, PBM003_OWNER_SURFACE) else {
        return false;
    };
    src.contains("pub const PBM_ID: &str = \"PBM-003\"")
        && src.contains("pub const WORKSTREAM_ID: &str = \"WS-gateway-wrap\"")
        && src.contains("NATIVE_TOOL_MANIFEST_COUNT")
        && src.contains("probe.native_tool_manifest_count == 13")
}

/// Census: SEC-GW declares `trust_wrap_wired() -> false`.
#[must_use]
pub fn trust_wrap_wired_false_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, SEC_GW_TRUST_WRAP_SURFACE) else {
        return false;
    };
    src.contains("pub const fn trust_wrap_wired() -> bool")
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

/// Census: stdio delegate entry wired (no spawn claim).
#[must_use]
pub fn stdio_delegate_surface_on_disk(root: &Path) -> bool {
    let Some(src) = read_workspace_file(root, STDIO_DELEGATE_SURFACE) else {
        return false;
    };
    src.contains("pub fn exec_native_mcp_delegate")
        && src.contains("GATEWAY_MCP_BIN_NAME")
}

/// Census: PBM-003 live fence SSOT pins 5/6 probe · 0/6 live.
#[must_use]
pub fn pbm_003_live_fence_ssot_honest(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, PBM003_LIVE_FENCE_PATH) else {
        return false;
    };
    doc.contains("gateway_wrap_native_mcp_closed")
        && doc.contains("trust_wrap_wired")
        && doc.contains("live_hops_earned")
        && doc.contains("0 / 6")
        && doc.contains("5/6")
        && doc.contains("LF0")
        && doc.contains("LF5")
}

/// Census: PBM-003 MANIFEST pins honest posture @ J38.
#[must_use]
pub fn pbm_003_manifest_honest(root: &Path) -> bool {
    let Some(doc) = read_workspace_file(root, PBM003_MANIFEST_PATH) else {
        return false;
    };
    doc.contains("PBM-003")
        && doc.contains("gateway_wrap_native_mcp_closed")
        && doc.contains("trust_wrap_wired")
        && doc.contains("0 / 6")
        && doc.contains("0/7")
        && doc.contains("No fake GREEN")
}

#[must_use]
pub fn pbm003_mcp_trust_residue_ledger_honest() -> bool {
    PBM003_MCP_TRUST_RESIDUE_LEDGER
        .iter()
        .all(|r| !r.closed)
        && PBM003_MCP_TRUST_RESIDUE_LEDGER.len() == OPEN_RESIDUE_COUNT as usize
}

/// Prior receipt chain absorption — J38 + H67 + live fence SSOT + manifest.
#[must_use]
pub fn pbm003_prior_chain_absorbed(root: &Path) -> bool {
    workspace_file_on_disk(root, PRIOR_J38_RECEIPT_PATH)
        && workspace_file_on_disk(root, PRIOR_H67_RECEIPT_PATH)
        && workspace_file_on_disk(root, PBM003_LIVE_FENCE_PATH)
        && workspace_file_on_disk(root, PBM003_MANIFEST_PATH)
}

/// J38 cluster deepen absorbed — PBM-003 fence pins without re-census.
#[must_use]
pub fn pbm003_j38_cluster_absorbed(root: &Path) -> bool {
    let Some(j38) = read_workspace_file(root, PRIOR_J38_RECEIPT_PATH) else {
        return false;
    };
    j38.contains("PBM-003")
        && j38.contains("gateway_wrap_native_mcp_closed=false")
        && j38.contains("trust_wrap_wired=false")
        && j38.contains("0/6 live hops")
}

/// H67 live fence deepen absorbed.
#[must_use]
pub fn pbm003_h67_live_fence_absorbed(root: &Path) -> bool {
    let Some(h67) = read_workspace_file(root, PRIOR_H67_RECEIPT_PATH) else {
        return false;
    };
    h67.contains("PBM-003")
        && h67.contains("gateway_wrap_native_mcp_closed")
        && h67.contains("trust_wrap_wired")
        && h67.contains("0/7")
}

/// PENDING_GAPS §B1 row pins umst-mcp L4/L5 production_wired=false sustain.
#[must_use]
pub fn pbm003_pending_gaps_sustain_honest(root: &Path) -> bool {
    let Some(gaps) = read_workspace_file(root, PENDING_GAPS_PATH) else {
        return false;
    };
    gaps.contains("umst-mcp L4/L5")
        && gaps.contains("production_wired=false")
        && gaps.contains("PBM-003")
}

/// AC377 MCP trust census — production hops 0 earned; trust tier open on disk.
#[must_use]
pub fn pbm003_mcp_trust_census_honest(root: &Path) -> bool {
    POSTURE_TAG == "honest-partial"
        && pbm_003_trust_gate_wire_hops_seven_on_disk(root)
        && pbm_003_ceremony_gap_honest_on_disk(root)
        && pbm_003_identity_pins_on_disk(root)
        && trust_wrap_wired_false_on_disk(root)
        && mcp_stdio_exec_trust_pre_check_false_on_disk(root)
        && stdio_delegate_surface_on_disk(root)
        && pbm_003_live_fence_ssot_honest(root)
        && pbm_003_manifest_honest(root)
        && pbm003_mcp_trust_residue_ledger_honest()
}

/// AC377 honest gate — chains prior receipts + on-disk owner census.
#[must_use]
pub fn pbm003_ac377_mcp_trust_honest(root: &Path) -> bool {
    pbm003_mcp_trust_census_honest(root)
        && pbm003_prior_chain_absorbed(root)
        && pbm003_j38_cluster_absorbed(root)
        && pbm003_h67_live_fence_absorbed(root)
        && pbm003_pending_gaps_sustain_honest(root)
}

#[test]
fn pbm003_owner_surfaces_on_disk() {
    let root = workspace_root();
    assert!(workspace_file_on_disk(&root, PBM003_OWNER_SURFACE));
    assert!(workspace_file_on_disk(&root, SEC_GW_TRUST_WRAP_SURFACE));
    assert!(workspace_file_on_disk(&root, SEC_MCP_WRAP_SURFACE));
    assert!(workspace_file_on_disk(&root, STDIO_DELEGATE_SURFACE));
}

#[test]
fn pbm003_trust_gate_wire_hops_seven_wired_on_disk() {
    let root = workspace_root();
    assert!(pbm_003_trust_gate_wire_hops_seven_on_disk(&root));
    assert_eq!(TRUST_GATE_WIRE_HOP_COUNT, 7);
}

#[test]
fn pbm003_ceremony_gap_and_probe_honest_on_disk() {
    let root = workspace_root();
    assert!(pbm_003_ceremony_gap_honest_on_disk(&root));
    assert!(pbm_003_identity_pins_on_disk(&root));
    assert_eq!(SPINE_NODES_CLOSED_PIN, "0/7");
    assert_eq!(NATIVE_TOOL_MANIFEST_COUNT, 13);
}

#[test]
fn pbm003_trust_wrap_and_stdio_pre_check_open_on_disk() {
    let root = workspace_root();
    assert!(trust_wrap_wired_false_on_disk(&root));
    assert!(mcp_stdio_exec_trust_pre_check_false_on_disk(&root));
    assert!(stdio_delegate_surface_on_disk(&root));
}

#[test]
fn pbm003_live_fence_ssot_pins_honest_false() {
    let root = workspace_root();
    assert!(pbm_003_live_fence_ssot_honest(&root));
    assert_eq!(LIVE_FENCE_HOP_COUNT, 6);
    assert_eq!(LIVE_PROBE_HOPS_WIRED, 5);
    assert_eq!(LIVE_HOPS_EARNED, 0);
}

#[test]
fn pbm003_manifest_honest_posture_on_disk() {
    let root = workspace_root();
    assert!(pbm_003_manifest_honest(&root));
    assert!(workspace_file_on_disk(&root, PBM003_MANIFEST_PATH));
}

#[test]
fn pbm003_mcp_trust_residue_ledger_open() {
    assert!(pbm003_mcp_trust_residue_ledger_honest());
    for entry in &PBM003_MCP_TRUST_RESIDUE_LEDGER {
        assert!(!entry.closed, "residue {} must stay open", entry.residue_id);
    }
}

#[test]
fn pbm003_j38_h67_prior_chain_absorbed() {
    let root = workspace_root();
    assert!(pbm003_prior_chain_absorbed(&root));
    assert!(pbm003_j38_cluster_absorbed(&root));
    assert!(pbm003_h67_live_fence_absorbed(&root));
}

#[test]
fn pbm003_owner_surfaces_no_green_invent() {
    let root = workspace_root();
    let pbm003 = read_workspace_file(&root, PBM003_OWNER_SURFACE).expect("PBM-003 owner");
    assert!(!pbm003.contains("gateway_wrap_native_mcp_closed() -> bool {\n    true"));
    let trust = read_workspace_file(&root, SEC_GW_TRUST_WRAP_SURFACE).expect("SEC-GW owner");
    assert!(!trust.contains("trust_wrap_wired() -> bool {\n    true"));
    let mcp = read_workspace_file(&root, SEC_MCP_WRAP_SURFACE).expect("SEC-MCP owner");
    assert!(!mcp.contains("mcp_stdio_exec_trust_pre_check_wired() -> bool {\n    true"));
}

#[test]
fn pbm003_master_retick_blocked_via_j38() {
    let root = workspace_root();
    let j38 = read_workspace_file(&root, PRIOR_J38_RECEIPT_PATH).expect("J38 receipt");
    assert!(j38.contains("OP-5 PASS") && j38.contains("NOT CLAIMED"));
    assert!(j38.contains("0/6 live hops"));
    let h67 = read_workspace_file(&root, PRIOR_H67_RECEIPT_PATH).expect("H67 receipt");
    assert!(h67.contains("gateway_wrap_native_mcp_closed"));
    assert!(h67.contains("trust_wrap_wired"));
}

#[test]
fn pbm003_pending_gaps_sustain_row() {
    let root = workspace_root();
    assert!(pbm003_pending_gaps_sustain_honest(&root));
}

#[test]
fn pbm003_mcp_trust_census_honest_gate() {
    let root = workspace_root();
    assert!(pbm003_mcp_trust_census_honest(&root));
}

#[test]
fn fleet_composer_accel2_ac377_pbm003_mcp_trust_honest() {
    assert_eq!(AC377_JOB_ID, "FLEET-COMPOSER-ACCEL2-AC377-PBM-003");
    assert_eq!(AC377_RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC377.md");
    assert_eq!(WORKSTREAM_ID, "WS-gateway-wrap");
    assert_eq!(PBM_OWNER, "PBM-003");
    assert_eq!(POSTURE_TAG, "honest-partial");
    let root = workspace_root();
    assert!(pbm003_ac377_mcp_trust_honest(&root));
}
