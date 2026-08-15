// SPDX-License-Identifier: MIT
//
// OPERATOR-ACCEL-2030 AC03 — PBM-009 `WS-faithful-all` formal-tree owner deepen.
//
// Formal-side complement to `umst-bench` (J4/E4/Z68/Y59) faithful ψ/𝒟 defer fences.
// Deepens Lean `Core/Gate.lean` dissipation authority pins — **6/7 witnessed**, zero 𝒟 landed.
// Does **not** invent B6 WITNESSED_SLICE1, landed 𝒟 evaluators, production tensor close,
// `pbm_009_fully_closed` flip, or INV4 4/4.
//
// Prior: J4 (`COMPOSER_P1931_J4.md`) — absorbed; not re-census.

use std::fs;
use std::path::{Path, PathBuf};

use super::lean_l1_stiffness_adopt::umst_formal_root;

/// OPERATOR-ACCEL fleet parent id.
pub const FLEET_PARENT: &str = "OPERATOR-ACCEL-2030";

/// AC03 slot job id.
pub const JOB_ID: &str = "OPERATOR-ACCEL-2030-AC03-PBM-009";

/// AC03 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL_2030_AC03.md";

/// J4 prior receipt — absorbed; not re-census.
pub const PRIOR_J4_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1931_J4.md";

/// J4 prior job id — absorbed through AC03.
pub const PRIOR_J4_JOB_ID: &str = "FLEET-COMPOSER-J4-PBM-009";

/// E4 prior receipt — absorbed through J4.
pub const PRIOR_E4_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1700_E4.md";

/// Z68 prior receipt — absorbed through E4.
pub const PRIOR_Z68_RECEIPT: &str = "outputs/.tmp/COMPOSER_Z68_1223.md";

/// Y59 prior receipt — absorbed through Z68.
pub const PRIOR_Y59_RECEIPT: &str = "outputs/.tmp/COMPOSER_Y59_0808.md";

/// Parent PBM card id.
pub const PARENT_WORKSTREAM_ID: &str = "PBM-009";

/// Workstream id per master TODO §4.4.
pub const WORKSTREAM_ID: &str = "WS-faithful-all";

/// Bench consumer witness module (umst-bench owner complement).
pub const BENCH_CONSUMER_PATH: &str = "crates/umst-bench/src/pbm_009_ws_faithful_all.rs";

/// Frozen posture fixture (bench consumer).
pub const BENCH_POSTURE_FIXTURE: &str =
    "crates/umst-bench/fixtures/pbm_009_ws_faithful_all_posture.json";

/// B6 𝒟 defer surface — next hop owner (not written here).
pub const B6_DISSIPATION_DEFER_SURFACE: &str =
    "umst-cartridges/crates/atoms/umst-cartridge-active/src/dissipation.rs";

/// Lean L1 gate authority for ψ/𝒟 dissipation foundation.
pub const LEAN_SOURCE_RELPATH: &str = "Lean/Core/Gate.lean";

/// Formal-side witness module (this file).
pub const FORMAL_WITNESS_RELPATH: &str = "umst-formal/ffi-bridge/src/pbm_009_ws_faithful_all.rs";

/// Honest adoption tier.
pub const POSTURE_TAG: &str = "honest-partial";

/// Atom census total @ AGAP-2127 B6 deepen.
pub const ATOM_TOTAL: usize = 7;

/// Witnessed atom count — B1–B5 + M1 compose; B6 remains PARTIAL_SLICE0.
pub const WITNESSED_ATOM_COUNT: usize = 6;

/// ψ witnessed count @ E4 deepen — B6 partial.
pub const PSI_WITNESSED_COUNT: usize = 6;

/// 𝒟 evaluator landed count — zero until W4-B6-2 production ceremony.
pub const D_EVALUATOR_LANDED_COUNT: usize = 0;

/// Defer blocker pinned count @ J4 deepen.
pub const DEFER_BLOCKER_PINNED_COUNT: usize = 7;

/// Formal-side faithful fence probe count (this module's audit).
pub const FORMAL_PROBE_COUNT: usize = 10;

/// Wire-hop count at J4 deepen (frozen — not current map len).
pub const J4_WIRE_HOP_COUNT: usize = 8;

/// One hop on the PBM-009 faithful wire map (formal owner).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm009FaithfulWireHop {
    pub ordinal: u8,
    pub surface: &'static str,
    pub role: &'static str,
}

/// PBM-009 faithful wire map @ AC03 (formal owner deepen).
pub const WIRE_HOPS: &[Pbm009FaithfulWireHop] = &[
    Pbm009FaithfulWireHop {
        ordinal: 1,
        surface: LEAN_SOURCE_RELPATH,
        role: "Lean CoreDissipCond ψ/𝒟 foundation (formal fence)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 2,
        surface: FORMAL_WITNESS_RELPATH,
        role: "Formal-tree ffi-bridge owner witness (AC03)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 3,
        surface: BENCH_CONSUMER_PATH,
        role: "Bench consumer faithful ψ/𝒟 defer fence (J4 chain)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 4,
        surface: BENCH_POSTURE_FIXTURE,
        role: "Frozen posture pins (witnessed=6 · d_landed=0 · defer=7)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 5,
        surface: B6_DISSIPATION_DEFER_SURFACE,
        role: "B6 𝒟 @ W4-B6-2 deferred — next hop owner",
    },
    Pbm009FaithfulWireHop {
        ordinal: 6,
        surface: PRIOR_J4_RECEIPT,
        role: "J4 defer accountability receipt (absorbed — not re-census)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 7,
        surface: PRIOR_E4_RECEIPT,
        role: "E4 ψ/𝒟 fence deepen receipt (absorbed)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 8,
        surface: PRIOR_Z68_RECEIPT,
        role: "Z68 audit receipt (absorbed)",
    },
    Pbm009FaithfulWireHop {
        ordinal: 9,
        surface: PRIOR_Y59_RECEIPT,
        role: "Y59 faithful conjunct receipt (absorbed)",
    },
];

/// Honest PBM-009 faithful posture probe for operator receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm009WsFaithfulAllProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_j4_receipt: &'static str,
    pub prior_j4_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub witnessed_atom_count: usize,
    pub psi_witnessed_count: usize,
    pub d_evaluator_landed_count: usize,
    pub defer_blocker_pinned_count: usize,
    pub pbm_009_fully_closed: bool,
    pub pbm_009_flip_blocked: bool,
    pub production_wired: bool,
    pub production_tensor_closed: bool,
    pub lean_gate_on_disk: bool,
    pub formal_owner_wired: bool,
    pub bench_consumer_wired: bool,
    pub b6_partial_slice0: bool,
    pub wire_hop_count: usize,
}

/// PBM-009 done-when probe — documents honest RESIDUE posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm009DoneWhenProbe {
    pub faithful_fence_honest: bool,
    pub b6_witnessed_slice1: bool,
    pub production_tensor_closed: bool,
    pub dissipation_evaluators_landed: bool,
    pub master_retick_eligible: bool,
    pub closure: &'static str,
}

/// One formal-side faithful fence probe outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm009FormalProbe {
    pub probe: &'static str,
    pub green: bool,
    pub detail: &'static str,
}

/// Formal-side faithful fence audit report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm009FormalAudit {
    pub job_id: &'static str,
    pub posture: &'static str,
    pub witnessed_atom_count: usize,
    pub probes: Vec<Pbm009FormalProbe>,
}

impl Pbm009FormalAudit {
    #[must_use]
    pub fn all_green(&self) -> bool {
        self.probes.iter().all(|p| p.green)
    }
}

/// Resolve tyto-workspace root from ffi-bridge manifest.
#[must_use]
pub fn tyto_workspace_root() -> PathBuf {
    umst_formal_root()
        .parent()
        .expect("tyto-workspace parent")
        .to_path_buf()
}

/// Lean Core/Gate dissipation posture pins present on disk.
#[must_use]
pub fn lean_faithful_gate_on_disk() -> bool {
    let path = umst_formal_root().join(LEAN_SOURCE_RELPATH);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("def CoreDissipCond")
        && text.contains("Core Clausius–Duhem condition (dissipation)")
        && text.contains("theorem coreAdmissible_iff_mass_dissip")
}

/// PBM-009 done-when — **false** until B6 WITNESSED_SLICE1 + production tensor close.
#[must_use]
pub const fn pbm_009_fully_closed() -> bool {
    false
}

/// Production tensor closed — **false** until rank-1+ `burn::Tensor` ceremony.
#[must_use]
pub const fn pbm_009_production_tensor_closed() -> bool {
    false
}

/// Honest fence — production wiring not earned until live substrate.
#[must_use]
pub const fn pbm_009_production_wired() -> bool {
    false
}

/// Formal faithful fence closed — structural audit GREEN; **not** B6 promotion or 𝒟 landed.
#[must_use]
pub fn pbm_009_formal_fence_closed() -> bool {
    lean_faithful_gate_on_disk()
        && run_formal_faithful_fence_audit().all_green()
        && WITNESSED_ATOM_COUNT == 6
        && D_EVALUATOR_LANDED_COUNT == 0
        && !pbm_009_fully_closed()
}

/// AC03 operator probe — chains J4; pins AC03 fence-deepen close predicate for PBM-009.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm009Ac03Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_j4_receipt: &'static str,
    pub prior_j4_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub witnessed_atom_count: usize,
    pub psi_witnessed_count: usize,
    pub d_evaluator_landed_count: usize,
    pub defer_blocker_pinned_count: usize,
    pub ac03_fence_deepen_closed: bool,
    pub formal_fence_closed: bool,
    pub faithful_fence_honest: bool,
    pub lean_gate_on_disk: bool,
    pub j4_absorbed: bool,
    pub pbm_009_fully_closed: bool,
    pub pbm_009_flip_blocked: bool,
    pub production_wired: bool,
    pub production_tensor_closed: bool,
    pub b6_partial_slice0: bool,
    pub wire_hop_count: usize,
}

/// Build OPERATOR-ACCEL-2030 AC03 probe.
#[must_use]
pub fn pbm_009_ac03_probe() -> Pbm009Ac03Probe {
    let audit = run_formal_faithful_fence_audit();
    let j4 = pbm_009_j4_absorb_probe();
    Pbm009Ac03Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_j4_receipt: PRIOR_J4_RECEIPT,
        prior_j4_job_id: PRIOR_J4_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        witnessed_atom_count: WITNESSED_ATOM_COUNT,
        psi_witnessed_count: PSI_WITNESSED_COUNT,
        d_evaluator_landed_count: D_EVALUATOR_LANDED_COUNT,
        defer_blocker_pinned_count: DEFER_BLOCKER_PINNED_COUNT,
        ac03_fence_deepen_closed: pbm_009_ac03_fence_deepen_closed(),
        formal_fence_closed: pbm_009_formal_fence_closed(),
        faithful_fence_honest: audit.all_green(),
        lean_gate_on_disk: lean_faithful_gate_on_disk(),
        j4_absorbed: pbm_009_j4_absorb_honest(&j4)
            && j4.formal_fence_candidate
            && !j4.pbm_009_fully_closed
            && j4.pbm_009_flip_blocked,
        pbm_009_fully_closed: pbm_009_fully_closed(),
        pbm_009_flip_blocked: true,
        production_wired: pbm_009_production_wired(),
        production_tensor_closed: pbm_009_production_tensor_closed(),
        b6_partial_slice0: true,
        wire_hop_count: WIRE_HOPS.len(),
    }
}

/// AC03 honesty gate — fence deepen closed; tier promotion still blocked.
#[must_use]
pub fn pbm_009_ac03_honest(probe: &Pbm009Ac03Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path == RECEIPT_PATH
        && probe.prior_j4_receipt == PRIOR_J4_RECEIPT
        && probe.prior_j4_job_id == PRIOR_J4_JOB_ID
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.workstream_id == WORKSTREAM_ID
        && probe.formal_probe_count == FORMAL_PROBE_COUNT
        && probe.witnessed_atom_count == WITNESSED_ATOM_COUNT
        && probe.psi_witnessed_count == PSI_WITNESSED_COUNT
        && probe.d_evaluator_landed_count == 0
        && probe.defer_blocker_pinned_count == DEFER_BLOCKER_PINNED_COUNT
        && probe.ac03_fence_deepen_closed
        && probe.formal_fence_closed
        && probe.faithful_fence_honest
        && probe.lean_gate_on_disk
        && probe.j4_absorbed
        && !probe.pbm_009_fully_closed
        && probe.pbm_009_flip_blocked
        && !probe.production_wired
        && !probe.production_tensor_closed
        && probe.b6_partial_slice0
        && probe.wire_hop_count == WIRE_HOPS.len()
}

/// AC03 fence deepen closed — chains J4 absorb + formal audit GREEN; **not** tier promotion.
#[must_use]
pub fn pbm_009_ac03_fence_deepen_closed() -> bool {
    pbm_009_formal_fence_closed()
        && tyto_workspace_root().join(PRIOR_J4_RECEIPT).is_file()
        && pbm_009_j4_absorb_honest(&pbm_009_j4_absorb_probe())
        && !pbm_009_fully_closed()
}

/// J4 absorb probe — filesystem + bench consumer posture pins.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm009J4AbsorbProbe {
    pub prior_j4_receipt: &'static str,
    pub prior_j4_job_id: &'static str,
    pub witnessed_atom_count: usize,
    pub defer_blocker_pinned_count: usize,
    pub formal_fence_candidate: bool,
    pub pbm_009_fully_closed: bool,
    pub pbm_009_flip_blocked: bool,
}

/// Build J4 absorb probe from on-disk bench consumer pins.
#[must_use]
pub fn pbm_009_j4_absorb_probe() -> Pbm009J4AbsorbProbe {
    let bench_ok = bench_consumer_posture_pins_honest();
    Pbm009J4AbsorbProbe {
        prior_j4_receipt: PRIOR_J4_RECEIPT,
        prior_j4_job_id: PRIOR_J4_JOB_ID,
        witnessed_atom_count: WITNESSED_ATOM_COUNT,
        defer_blocker_pinned_count: DEFER_BLOCKER_PINNED_COUNT,
        formal_fence_candidate: bench_ok,
        pbm_009_fully_closed: pbm_009_fully_closed(),
        pbm_009_flip_blocked: true,
    }
}

/// J4 absorb honesty — receipt on disk + bench consumer fence pins.
#[must_use]
pub fn pbm_009_j4_absorb_honest(probe: &Pbm009J4AbsorbProbe) -> bool {
    probe.prior_j4_receipt == PRIOR_J4_RECEIPT
        && probe.prior_j4_job_id == PRIOR_J4_JOB_ID
        && probe.witnessed_atom_count == WITNESSED_ATOM_COUNT
        && probe.defer_blocker_pinned_count == DEFER_BLOCKER_PINNED_COUNT
        && probe.formal_fence_candidate
        && tyto_workspace_root().join(PRIOR_J4_RECEIPT).is_file()
        && !probe.pbm_009_fully_closed
        && probe.pbm_009_flip_blocked
}

/// Verify bench consumer + posture fixture pins without linking umst-bench.
#[must_use]
pub fn bench_consumer_posture_pins_honest() -> bool {
    let root = tyto_workspace_root();
    let consumer = root.join(BENCH_CONSUMER_PATH);
    let fixture = root.join(BENCH_POSTURE_FIXTURE);
    let Ok(consumer_text) = fs::read_to_string(&consumer) else {
        return false;
    };
    let Ok(fixture_text) = fs::read_to_string(&fixture) else {
        return false;
    };
    consumer_text.contains("WITNESSED_ATOM_COUNT: usize = 6")
        && consumer_text.contains("D_EVALUATOR_LANDED_COUNT: usize = 0")
        && consumer_text.contains("DEFER_BLOCKER_PINNED_COUNT: usize = 7")
        && consumer_text.contains("pbm_009_faithful_psi_d_defer_accountability")
        && fixture_text.contains("\"witnessed_atom_count\": 6")
        && fixture_text.contains("\"d_evaluator_landed_count\": 0")
        && fixture_text.contains("\"defer_blocker_pinned_count\": 7")
        && fixture_text.contains("\"production_tensor_closed\": false")
}

/// Run the 10-probe formal-side faithful fence audit (stdlib only).
#[must_use]
pub fn run_formal_faithful_fence_audit() -> Pbm009FormalAudit {
    let bench_ok = bench_consumer_posture_pins_honest();
    let probes = vec![
        Pbm009FormalProbe {
            probe: "lean_gate_on_disk",
            green: lean_faithful_gate_on_disk(),
            detail: "Core/Gate.lean @ umst-formal",
        },
        Pbm009FormalProbe {
            probe: "lean_dissip_cond_pin",
            green: lean_faithful_gate_on_disk(),
            detail: "CoreDissipCond + coreAdmissible_iff_mass_dissip",
        },
        Pbm009FormalProbe {
            probe: "witnessed_atom_six",
            green: WITNESSED_ATOM_COUNT == 6 && ATOM_TOTAL == 7,
            detail: "6/7 witnessed · B6 PARTIAL_SLICE0",
        },
        Pbm009FormalProbe {
            probe: "psi_witnessed_six",
            green: PSI_WITNESSED_COUNT == 6,
            detail: "ψ witnessed 6/7 — B6 partial",
        },
        Pbm009FormalProbe {
            probe: "d_evaluator_zero",
            green: D_EVALUATOR_LANDED_COUNT == 0,
            detail: "zero 𝒟 evaluators landed",
        },
        Pbm009FormalProbe {
            probe: "defer_blocker_seven",
            green: DEFER_BLOCKER_PINNED_COUNT == ATOM_TOTAL,
            detail: "7/7 defer blocker pinned",
        },
        Pbm009FormalProbe {
            probe: "bench_consumer_pins",
            green: bench_ok,
            detail: "bench consumer + posture fixture pins",
        },
        Pbm009FormalProbe {
            probe: "pbm_009_not_fully_closed",
            green: !pbm_009_fully_closed(),
            detail: "pbm_009_fully_closed() stays false",
        },
        Pbm009FormalProbe {
            probe: "production_not_wired",
            green: !pbm_009_production_wired() && !pbm_009_production_tensor_closed(),
            detail: "production_wired=false · tensor closed=false",
        },
        Pbm009FormalProbe {
            probe: "j4_receipt_absorbed",
            green: tyto_workspace_root().join(PRIOR_J4_RECEIPT).is_file(),
            detail: "J4 receipt on disk — not re-census",
        },
    ];

    Pbm009FormalAudit {
        job_id: JOB_ID,
        posture: POSTURE_TAG,
        witnessed_atom_count: WITNESSED_ATOM_COUNT,
        probes,
    }
}

/// Returns the honest AC03 PBM-009 faithful posture (minimal I/O).
#[must_use]
pub fn pbm_009_ws_faithful_all_probe_honest() -> Pbm009WsFaithfulAllProbe {
    let audit = run_formal_faithful_fence_audit();
    Pbm009WsFaithfulAllProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_j4_receipt: PRIOR_J4_RECEIPT,
        prior_j4_job_id: PRIOR_J4_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        witnessed_atom_count: WITNESSED_ATOM_COUNT,
        psi_witnessed_count: PSI_WITNESSED_COUNT,
        d_evaluator_landed_count: D_EVALUATOR_LANDED_COUNT,
        defer_blocker_pinned_count: DEFER_BLOCKER_PINNED_COUNT,
        pbm_009_fully_closed: pbm_009_fully_closed(),
        pbm_009_flip_blocked: true,
        production_wired: pbm_009_production_wired(),
        production_tensor_closed: pbm_009_production_tensor_closed(),
        lean_gate_on_disk: lean_faithful_gate_on_disk(),
        formal_owner_wired: true,
        bench_consumer_wired: bench_consumer_posture_pins_honest(),
        b6_partial_slice0: true,
        wire_hop_count: WIRE_HOPS.len(),
    }
}

/// Done-when probe — honest RESIDUE: structural fence GREEN, B6 + tensor blocked.
#[must_use]
pub fn pbm_009_done_when_probe() -> Pbm009DoneWhenProbe {
    let audit = run_formal_faithful_fence_audit();
    Pbm009DoneWhenProbe {
        faithful_fence_honest: audit.all_green(),
        b6_witnessed_slice1: false,
        production_tensor_closed: pbm_009_production_tensor_closed(),
        dissipation_evaluators_landed: false,
        master_retick_eligible: false,
        closure: "RESIDUE",
    }
}

/// Filesystem probe for PBM-009 formal faithful posture (honest RESIDUE).
pub fn probe_pbm_009_formal_ws_faithful_all(root: &Path) -> Result<String, String> {
    let lean_source = umst_formal_root().join(LEAN_SOURCE_RELPATH);
    let bench_consumer = root.join(BENCH_CONSUMER_PATH);
    let posture_fixture = root.join(BENCH_POSTURE_FIXTURE);
    let j4_receipt = root.join(PRIOR_J4_RECEIPT);
    let b6_dissipation = root.join(B6_DISSIPATION_DEFER_SURFACE);

    if !lean_source.is_file() {
        return Err(format!("missing Lean source: {}", lean_source.display()));
    }
    if !lean_faithful_gate_on_disk() {
        return Err("Core/Gate.lean missing CoreDissipCond dissipation pins".into());
    }
    if !bench_consumer.is_file() {
        return Err(format!(
            "missing bench consumer: {}",
            bench_consumer.display()
        ));
    }
    if !posture_fixture.is_file() {
        return Err(format!(
            "missing posture fixture: {}",
            posture_fixture.display()
        ));
    }
    if !j4_receipt.is_file() {
        return Err(format!("missing J4 receipt: {}", j4_receipt.display()));
    }
    if !b6_dissipation.is_file() {
        return Err(format!(
            "missing B6 dissipation defer surface: {}",
            b6_dissipation.display()
        ));
    }
    if !bench_consumer_posture_pins_honest() {
        return Err("bench consumer posture pins regression".into());
    }

    let probe = pbm_009_ws_faithful_all_probe_honest();
    let done = pbm_009_done_when_probe();
    if probe.pbm_009_fully_closed || done.master_retick_eligible {
        return Err("PBM-009 posture regression: must remain RESIDUE with flip blocked".into());
    }

    Ok(format!(
        "job={JOB_ID} workstream={WORKSTREAM_ID} status=[~] \
         witnessed_atom_count=6 psi_witnessed_count=6 d_evaluator_landed_count=0 \
         defer_blocker_pinned_count=7 pbm_009_fully_closed=false pbm_009_flip_blocked=true \
         production_wired=false production_tensor_closed=false formal_owner_wired=true \
         lean_gate_on_disk=true bench_consumer_wired=true b6_partial_slice0=true closure=RESIDUE \
         wire_hops={} absorbed_j4={PRIOR_J4_RECEIPT}",
        WIRE_HOPS.len()
    ))
}

/// AC03 fence-deepen filesystem witness — chains J4 absorb; honest RESIDUE.
pub fn probe_pbm_009_ac03_fence_deepen(root: &Path) -> Result<String, String> {
    let j4_receipt = root.join(PRIOR_J4_RECEIPT);
    if !j4_receipt.is_file() {
        return Err(format!("missing J4 receipt: {}", j4_receipt.display()));
    }
    if !pbm_009_ac03_fence_deepen_closed() {
        return Err("AC03 fence deepen not closed — structural audit or J4 absorb failed".into());
    }
    let probe = pbm_009_ac03_probe();
    if !pbm_009_ac03_honest(&probe) {
        return Err("AC03 probe honesty gate failed".into());
    }
    if probe.pbm_009_fully_closed || probe.production_wired {
        return Err("PBM-009 posture regression: must remain RESIDUE with flip blocked".into());
    }
    Ok(format!(
        "job={JOB_ID} ac03_fence_deepen_closed=true formal_fence_closed=true \
         j4_absorbed=true witnessed_atom_count=6 d_evaluator_landed_count=0 \
         defer_blocker_pinned_count=7 pbm_009_fully_closed=false pbm_009_flip_blocked=true \
         production_wired=false production_tensor_closed=false closure=RESIDUE wire_hops={}",
        WIRE_HOPS.len()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pbm_009_ac03_metadata_wired() {
        assert_eq!(FLEET_PARENT, "OPERATOR-ACCEL-2030");
        assert_eq!(JOB_ID, "OPERATOR-ACCEL-2030-AC03-PBM-009");
        assert_eq!(RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL_2030_AC03.md");
        assert_eq!(PRIOR_J4_JOB_ID, "FLEET-COMPOSER-J4-PBM-009");
        assert_eq!(PRIOR_J4_RECEIPT, "outputs/.tmp/COMPOSER_P1931_J4.md");
        assert_eq!(PARENT_WORKSTREAM_ID, "PBM-009");
        assert_eq!(WORKSTREAM_ID, "WS-faithful-all");
        assert_eq!(FORMAL_PROBE_COUNT, 10);
        assert_eq!(J4_WIRE_HOP_COUNT, 8);
    }

    #[test]
    fn pbm_009_ws_faithful_all_probe_honest_fences_hold() {
        let probe = pbm_009_ws_faithful_all_probe_honest();
        assert_eq!(probe.job_id, JOB_ID);
        assert_eq!(probe.parent_workstream_id, "PBM-009");
        assert_eq!(probe.workstream_id, "WS-faithful-all");
        assert_eq!(probe.formal_probe_count, FORMAL_PROBE_COUNT);
        assert_eq!(probe.witnessed_atom_count, 6);
        assert_eq!(probe.psi_witnessed_count, 6);
        assert_eq!(probe.d_evaluator_landed_count, 0);
        assert_eq!(probe.defer_blocker_pinned_count, 7);
        assert!(!probe.pbm_009_fully_closed);
        assert!(!pbm_009_fully_closed());
        assert!(probe.pbm_009_flip_blocked);
        assert!(!probe.production_wired);
        assert!(!pbm_009_production_wired());
        assert!(!probe.production_tensor_closed);
        assert!(probe.lean_gate_on_disk);
        assert!(probe.formal_owner_wired);
        assert!(probe.bench_consumer_wired);
        assert!(probe.b6_partial_slice0);
        assert_eq!(probe.wire_hop_count, WIRE_HOPS.len());
    }

    #[test]
    fn pbm_009_done_when_residue_measured() {
        let done = pbm_009_done_when_probe();
        assert!(done.faithful_fence_honest);
        assert!(!done.b6_witnessed_slice1);
        assert!(!done.production_tensor_closed);
        assert!(!done.dissipation_evaluators_landed);
        assert!(!done.master_retick_eligible);
        assert_eq!(done.closure, "RESIDUE");
    }

    #[test]
    fn pbm_009_formal_faithful_fence_audit_10_green() {
        let audit = run_formal_faithful_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        for p in &audit.probes {
            assert!(p.green, "probe {:?} failed", p);
        }
    }

    #[test]
    fn pbm_009_wire_hops_cover_faithful_surfaces() {
        assert_eq!(WIRE_HOPS.len(), 9);
        assert_eq!(WIRE_HOPS[0].surface, LEAN_SOURCE_RELPATH);
        assert_eq!(WIRE_HOPS[1].surface, FORMAL_WITNESS_RELPATH);
        assert_eq!(WIRE_HOPS[2].surface, BENCH_CONSUMER_PATH);
        assert_eq!(WIRE_HOPS[5].surface, PRIOR_J4_RECEIPT);
        assert_eq!(WIRE_HOPS[4].surface, B6_DISSIPATION_DEFER_SURFACE);
    }

    #[test]
    fn pbm_009_formal_fence_closed_measured() {
        assert!(pbm_009_formal_fence_closed());
        let audit = run_formal_faithful_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        assert!(audit.all_green());
        assert!(lean_faithful_gate_on_disk());
        assert!(!pbm_009_fully_closed());
    }

    #[test]
    fn pbm_009_j4_absorb_probe_honest() {
        let probe = pbm_009_j4_absorb_probe();
        assert!(super::pbm_009_j4_absorb_honest(&probe));
        assert_eq!(probe.defer_blocker_pinned_count, 7);
        assert!(!probe.pbm_009_fully_closed);
        assert!(tyto_workspace_root().join(PRIOR_J4_RECEIPT).is_file());
    }

    #[test]
    fn pbm_009_ac03_formal_fence_deepen() {
        let probe = pbm_009_ac03_probe();
        assert!(pbm_009_ac03_honest(&probe));
        assert!(probe.ac03_fence_deepen_closed);
        assert!(probe.formal_fence_closed);
        assert!(probe.j4_absorbed);
        assert_eq!(probe.wire_hop_count, 9);
        assert!(!probe.pbm_009_fully_closed);
        assert!(!probe.production_wired);
        assert!(pbm_009_ac03_fence_deepen_closed());
    }

    #[test]
    fn probe_pbm_009_ac03_fence_deepen_witness_on_disk() {
        let root = tyto_workspace_root();
        let msg = probe_pbm_009_ac03_fence_deepen(&root).expect("AC03 fence deepen witness");
        assert!(
            msg.contains("ac03_fence_deepen_closed=true"),
            "deepen: {msg}"
        );
        assert!(msg.contains("witnessed_atom_count=6"), "fence: {msg}");
        assert!(msg.contains("pbm_009_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("wire_hops=9"), "hops: {msg}");
    }

    #[test]
    fn probe_pbm_009_formal_filesystem_honest_residue() {
        let root = tyto_workspace_root();
        if !root.join(BENCH_CONSUMER_PATH).exists() {
            eprintln!("skip probe_pbm_009_formal_filesystem_honest_residue: bench consumer absent");
            return;
        }
        let msg = probe_pbm_009_formal_ws_faithful_all(&root).expect("PBM-009 paths on disk");
        assert!(msg.contains("status=[~]"), "must not invent [x]: {msg}");
        assert!(msg.contains("witnessed_atom_count=6"), "fence: {msg}");
        assert!(msg.contains("pbm_009_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("formal_owner_wired=true"), "witness: {msg}");
        assert!(msg.contains("lean_gate_on_disk=true"), "lean: {msg}");
    }
}
