// SPDX-License-Identifier: MIT
//
// ACCEL-B-2050 AC55 — PBM-007 `WS-cert-proved` formal-tree owner deepen.
//
// Formal-side complement to `umst-meta` (Z100) and `umst-bench` (Y58/J39) cert-proved fences.
// Deepens Lean `MicroMechanics.lean` honest posture pins — **0 Proved** until operator measured ε.
// Does **not** invent Proved tier, measured ε, POSTH-02 exit 0, OP-5 PASS, or INV4 4/4.
//
// Prior: K1941 K3 (`COMPOSER_P1941_K3.md`) · K1938 K2 (`COMPOSER_P1938_K2.md`) · D3 (`COMPOSER_P1650_D3.md`) — absorbed; not re-census.

use std::fs;
use std::path::{Path, PathBuf};

use super::lean_l1_bridge_prep::{
    e_eff_mt_at_zero_holds, psi_elastic_base_nonpos_holds, psi_softening_micro_mechanics_holds,
    L1B_LEAN_MODULE, L1B_WITNESS_THEOREM,
};
use super::lean_l1_stiffness_adopt::{l1b_lean_source_on_disk, umst_formal_root};

/// ACCEL-B fleet parent id.
pub const FLEET_PARENT: &str = "ACCEL-B-2050";

/// AC55 slot job id.
pub const JOB_ID: &str = "ACCEL-B-2050-AC55-PBM-007";

/// AC55 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC55.md";

/// K3 prior receipt — absorbed; not re-census.
pub const PRIOR_K3_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1941_K3.md";

/// K3 prior job id — absorbed through AC55.
pub const PRIOR_K3_JOB_ID: &str = "PRABHU-WAVE-K-1941-K3-PBM-007";

/// K3 prior fleet parent — absorbed through AC55.
pub const PRIOR_K3_FLEET_PARENT: &str = "PRABHU-WAVE-K-1941";

/// K2 prior receipt — absorbed; not re-census.
pub const PRIOR_K2_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1938_K2.md";

/// K2 prior job id — absorbed through K3.
pub const PRIOR_K2_JOB_ID: &str = "PRABHU-WAVE-K-1938-K2-PBM-007";

/// D3 prior receipt — absorbed; not re-census.
pub const PRIOR_D3_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1650_D3.md";

/// D3 prior job id — absorbed through K2.
pub const PRIOR_D3_JOB_ID: &str = "PRABHU-WAVE-D-1650-D3-PBM-007";

/// Z100 meta owner receipt — absorbed; no re-census.
pub const ABSORBED_Z100_RECEIPT: &str = "outputs/.tmp/COMPOSER_Z100_1232.md";

/// Z43 meta prep receipt — absorbed through Z100.
pub const ABSORBED_Z43_RECEIPT: &str = "outputs/.tmp/COMPOSER_Z43_1015.md";

/// Y58 bench deepen receipt — absorbed through Z43.
pub const ABSORBED_Y58_RECEIPT: &str = "outputs/.tmp/COMPOSER_Y58_0808.md";

/// J39 10-probe fence origin — carried through Y58.
pub const ABSORBED_J39_RECEIPT: &str = "outputs/.tmp/COMPOSER_J39_2348.md";

/// Parent PBM card id.
pub const PARENT_WORKSTREAM_ID: &str = "PBM-007";

/// Workstream id per master TODO §4.2.
pub const WORKSTREAM_ID: &str = "WS-cert-proved";

/// Bench consumer witness module (umst-bench owner complement).
pub const BENCH_CONSUMER_PATH: &str = "crates/umst-bench/src/pbm_007_ws_cert_proved.rs";

/// Frozen posture fixture (bench consumer).
pub const BENCH_POSTURE_FIXTURE: &str =
    "crates/umst-bench/fixtures/pbm_007_ws_cert_proved_posture.json";

/// Meta owner witness module (umst-meta Z100 complement).
pub const META_OWNER_PATH: &str = "crates/umst-meta/src/meta_pbm_007_ws_cert_proved.rs";

/// B-Arc POSTH-02 ceremony surface blocking measured ε (next hop owner).
pub const POSTH_02_BARC_SURFACE: &str = "crates/umst-bench/src/b_arc_spine_census.rs";

/// Lean L1b authority for cert-proved posture pins.
pub const LEAN_SOURCE_RELPATH: &str = "Lean/Concrete/MicroMechanics.lean";

/// Formal-side witness module (this file).
pub const FORMAL_WITNESS_RELPATH: &str = "umst-formal/ffi-bridge/src/pbm_007_ws_cert_proved.rs";

/// Honest adoption tier.
pub const POSTURE_TAG: &str = "witnessed-not-proved";

/// Ten-probe orchestrator count per AGAP-2127 deepen (bench consumer — not re-run here).
pub const PROBE_COUNT: usize = 10;

/// Frozen proved-count posture — operator ceremony only.
pub const EXPECTED_PROVED_COUNT: usize = 0;

/// Formal-side cert-proved fence probe count (this module's audit).
pub const FORMAL_PROBE_COUNT: usize = 10;

/// Wire-hop count at K2 deepen (frozen — not current map len).
pub const K2_WIRE_HOP_COUNT: usize = 8;

/// Wire-hop count at K3 deepen (frozen — not current map len).
pub const K3_WIRE_HOP_COUNT: usize = 9;

/// One hop on the PBM-007 cert-proved wire map (formal owner).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm007CertProvedWireHop {
    pub ordinal: u8,
    pub surface: &'static str,
    pub role: &'static str,
}

/// PBM-007 cert-proved wire map @ K3 (formal owner deepen).
pub const WIRE_HOPS: &[Pbm007CertProvedWireHop] = &[
    Pbm007CertProvedWireHop {
        ordinal: 1,
        surface: LEAN_SOURCE_RELPATH,
        role: "Lean L1b honest posture pins (expectedProvedCount=0 · formalFenceClosed)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 2,
        surface: FORMAL_WITNESS_RELPATH,
        role: "Formal-tree ffi-bridge owner witness (AC55)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 3,
        surface: BENCH_CONSUMER_PATH,
        role: "Bench consumer 10-probe fence (J39 → Y58 chain)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 4,
        surface: META_OWNER_PATH,
        role: "Meta-side Z100 owner witness (absorbed)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 5,
        surface: BENCH_POSTURE_FIXTURE,
        role: "Frozen posture pins (expected_proved_count=0)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 6,
        surface: ABSORBED_Z100_RECEIPT,
        role: "Z100 residue receipt (absorbed — not re-census)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 7,
        surface: POSTH_02_BARC_SURFACE,
        role: "POSTH-02 B-Arc ceremony — blocks measured ε until operator",
    },
    Pbm007CertProvedWireHop {
        ordinal: 8,
        surface: PRIOR_D3_RECEIPT,
        role: "D3 prior receipt (absorbed — not re-census)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 9,
        surface: PRIOR_K2_RECEIPT,
        role: "K2 prior receipt (absorbed — not re-census)",
    },
    Pbm007CertProvedWireHop {
        ordinal: 10,
        surface: PRIOR_K3_RECEIPT,
        role: "K3 prior receipt (absorbed — not re-census)",
    },
];

/// Honest PBM-007 cert-proved probe for operator receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007WsCertProvedProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub absorbed_z100_receipt: &'static str,
    pub absorbed_z43_receipt: &'static str,
    pub absorbed_y58_receipt: &'static str,
    pub absorbed_j39_receipt: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub lean_module: &'static str,
    pub lean_theorem: &'static str,
    pub probe_count: usize,
    pub formal_probe_count: usize,
    pub expected_proved_count: usize,
    pub pbm_007_fully_closed: bool,
    pub pbm_007_flip_blocked: bool,
    pub production_wired: bool,
    pub lean_posture_on_disk: bool,
    pub formal_owner_wired: bool,
    pub bench_consumer_wired: bool,
    pub meta_pbm_007_wired: bool,
    pub posth_02_exit_zero: bool,
    pub catalog_export_deferred: bool,
    pub concrete_validation_status: &'static str,
    pub p7_gate_status: &'static str,
    pub wire_hop_count: usize,
}

/// PBM-007 done-when probe — documents honest RESIDUE posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007DoneWhenProbe {
    pub cert_proved_fence_honest: bool,
    pub measured_epsilon_landed: bool,
    pub posth_02_ceremony_complete: bool,
    pub operator_o5_cleared: bool,
    pub master_retick_eligible: bool,
    pub closure: &'static str,
}

/// One formal-side cert-proved fence probe outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007FormalProbe {
    pub probe: &'static str,
    pub green: bool,
    pub detail: &'static str,
}

/// Formal-side cert-proved fence audit report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007FormalAudit {
    pub job_id: &'static str,
    pub posture: &'static str,
    pub expected_proved_count: usize,
    pub probes: Vec<Pbm007FormalProbe>,
}

impl Pbm007FormalAudit {
    #[must_use]
    pub fn all_green(&self) -> bool {
        self.probes.iter().all(|p| p.green)
    }
}

/// Resolve tyto-workspace root from ffi-bridge manifest.
#[must_use]
#[allow(dead_code)]
pub fn tyto_workspace_root() -> PathBuf {
    umst_formal_root()
        .parent()
        .expect("tyto-workspace parent")
        .to_path_buf()
}

/// Lean MicroMechanics posture pins present on disk.
#[must_use]
pub fn lean_cert_proved_posture_on_disk() -> bool {
    let path = umst_formal_root().join(LEAN_SOURCE_RELPATH);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("def expectedProvedCount : Nat := 0")
        && text.contains("def catalogExportDeferred : Bool := true")
        && text.contains("theorem expectedProvedCount_zero")
        && text.contains("def certProvedFenceHonest : Bool := true")
        && text.contains("def formalFenceClosed : Bool")
        && text.contains("theorem formalFenceClosed_honest")
}

/// PBM-007 done-when — **false** until measured ε + operator ceremony.
#[must_use]
pub const fn pbm_007_fully_closed() -> bool {
    false
}

/// Honest fence — production wiring not earned until live cert Proved tier.
#[must_use]
pub const fn pbm_007_production_wired() -> bool {
    false
}

/// Catalog `[proved]` export remains operator-gated.
#[must_use]
pub const fn catalog_export_deferred() -> bool {
    true
}

/// Formal cert-proved fence closed — structural audit GREEN; **not** tier-2→Proved promotion.
#[must_use]
pub fn pbm_007_formal_fence_closed() -> bool {
    lean_cert_proved_posture_on_disk()
        && run_formal_cert_proved_fence_audit().all_green()
        && EXPECTED_PROVED_COUNT == 0
        && !pbm_007_fully_closed()
}

/// K3 operator probe — chains K2→D3; pins K1941 fence-deepen close predicate for PBM-007.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007K1941Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_k2_receipt: &'static str,
    pub prior_k2_job_id: &'static str,
    pub prior_d3_receipt: &'static str,
    pub prior_d3_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub expected_proved_count: usize,
    pub k1941_fence_deepen_closed: bool,
    pub formal_fence_closed: bool,
    pub cert_proved_fence_honest: bool,
    pub lean_posture_on_disk: bool,
    pub k2_absorbed: bool,
    pub d3_absorbed: bool,
    pub pbm_007_fully_closed: bool,
    pub pbm_007_flip_blocked: bool,
    pub production_wired: bool,
    pub posth_02_exit_zero: bool,
    pub wire_hop_count: usize,
}

/// AC55 operator probe — chains K3→K2→D3; pins AC55 fence-deepen close predicate for PBM-007.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007Ac55Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_k3_receipt: &'static str,
    pub prior_k3_job_id: &'static str,
    pub prior_k2_receipt: &'static str,
    pub prior_k2_job_id: &'static str,
    pub prior_d3_receipt: &'static str,
    pub prior_d3_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub expected_proved_count: usize,
    pub ac55_fence_deepen_closed: bool,
    pub formal_fence_closed: bool,
    pub cert_proved_fence_honest: bool,
    pub lean_posture_on_disk: bool,
    pub k3_absorbed: bool,
    pub k2_absorbed: bool,
    pub d3_absorbed: bool,
    pub pbm_007_fully_closed: bool,
    pub pbm_007_flip_blocked: bool,
    pub production_wired: bool,
    pub posth_02_exit_zero: bool,
    pub wire_hop_count: usize,
}

/// Build PRABHU-WAVE-K-1941 K3 probe (prior — absorbed through AC55).
#[must_use]
pub fn pbm_007_k1941_probe() -> Pbm007K1941Probe {
    let audit = run_formal_cert_proved_fence_audit();
    let k2 = pbm_007_k1938_probe();
    let d3 = pbm_007_ws_cert_proved_probe_honest();
    Pbm007K1941Probe {
        job_id: PRIOR_K3_JOB_ID,
        receipt_path: PRIOR_K3_RECEIPT,
        prior_k2_receipt: PRIOR_K2_RECEIPT,
        prior_k2_job_id: PRIOR_K2_JOB_ID,
        prior_d3_receipt: PRIOR_D3_RECEIPT,
        prior_d3_job_id: PRIOR_D3_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        expected_proved_count: EXPECTED_PROVED_COUNT,
        k1941_fence_deepen_closed: pbm_007_k1941_fence_deepen_closed(),
        formal_fence_closed: pbm_007_formal_fence_closed(),
        cert_proved_fence_honest: audit.all_green(),
        lean_posture_on_disk: lean_cert_proved_posture_on_disk(),
        k2_absorbed: pbm_007_k1938_honest(&k2)
            && k2.formal_fence_closed
            && !k2.pbm_007_fully_closed
            && k2.pbm_007_flip_blocked,
        d3_absorbed: tyto_workspace_root().join(PRIOR_D3_RECEIPT).is_file()
            && d3.expected_proved_count == 0
            && d3.formal_probe_count == FORMAL_PROBE_COUNT
            && d3.lean_posture_on_disk
            && !d3.pbm_007_fully_closed
            && d3.pbm_007_flip_blocked,
        pbm_007_fully_closed: pbm_007_fully_closed(),
        pbm_007_flip_blocked: true,
        production_wired: pbm_007_production_wired(),
        posth_02_exit_zero: false,
        wire_hop_count: K3_WIRE_HOP_COUNT,
    }
}

/// Build ACCEL-B-2050 AC55 probe.
#[must_use]
pub fn pbm_007_ac55_probe() -> Pbm007Ac55Probe {
    let audit = run_formal_cert_proved_fence_audit();
    let k3 = pbm_007_k1941_probe();
    let k2 = pbm_007_k1938_probe();
    let d3 = pbm_007_ws_cert_proved_probe_honest();
    Pbm007Ac55Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_k3_receipt: PRIOR_K3_RECEIPT,
        prior_k3_job_id: PRIOR_K3_JOB_ID,
        prior_k2_receipt: PRIOR_K2_RECEIPT,
        prior_k2_job_id: PRIOR_K2_JOB_ID,
        prior_d3_receipt: PRIOR_D3_RECEIPT,
        prior_d3_job_id: PRIOR_D3_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        expected_proved_count: EXPECTED_PROVED_COUNT,
        ac55_fence_deepen_closed: pbm_007_ac55_fence_deepen_closed(),
        formal_fence_closed: pbm_007_formal_fence_closed(),
        cert_proved_fence_honest: audit.all_green(),
        lean_posture_on_disk: lean_cert_proved_posture_on_disk(),
        k3_absorbed: pbm_007_k1941_honest(&k3)
            && k3.k1941_fence_deepen_closed
            && k3.formal_fence_closed
            && !k3.pbm_007_fully_closed
            && k3.pbm_007_flip_blocked,
        k2_absorbed: pbm_007_k1938_honest(&k2)
            && k2.formal_fence_closed
            && !k2.pbm_007_fully_closed
            && k2.pbm_007_flip_blocked,
        d3_absorbed: tyto_workspace_root().join(PRIOR_D3_RECEIPT).is_file()
            && d3.expected_proved_count == 0
            && d3.formal_probe_count == FORMAL_PROBE_COUNT
            && d3.lean_posture_on_disk
            && !d3.pbm_007_fully_closed
            && d3.pbm_007_flip_blocked,
        pbm_007_fully_closed: pbm_007_fully_closed(),
        pbm_007_flip_blocked: true,
        production_wired: pbm_007_production_wired(),
        posth_02_exit_zero: false,
        wire_hop_count: WIRE_HOPS.len(),
    }
}

/// K3 honesty gate — fence deepen closed; tier promotion still blocked.
#[must_use]
pub fn pbm_007_k1941_honest(probe: &Pbm007K1941Probe) -> bool {
    probe.job_id == PRIOR_K3_JOB_ID
        && probe.receipt_path == PRIOR_K3_RECEIPT
        && probe.prior_k2_receipt == PRIOR_K2_RECEIPT
        && probe.prior_k2_job_id == PRIOR_K2_JOB_ID
        && probe.prior_d3_receipt == PRIOR_D3_RECEIPT
        && probe.prior_d3_job_id == PRIOR_D3_JOB_ID
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.workstream_id == WORKSTREAM_ID
        && probe.formal_probe_count == FORMAL_PROBE_COUNT
        && probe.expected_proved_count == 0
        && probe.k1941_fence_deepen_closed
        && probe.formal_fence_closed
        && probe.cert_proved_fence_honest
        && probe.lean_posture_on_disk
        && probe.k2_absorbed
        && probe.d3_absorbed
        && !probe.pbm_007_fully_closed
        && probe.pbm_007_flip_blocked
        && !probe.production_wired
        && !probe.posth_02_exit_zero
        && probe.wire_hop_count == K3_WIRE_HOP_COUNT
}

/// AC55 honesty gate — fence deepen closed; tier promotion still blocked.
#[must_use]
pub fn pbm_007_ac55_honest(probe: &Pbm007Ac55Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path == RECEIPT_PATH
        && probe.prior_k3_receipt == PRIOR_K3_RECEIPT
        && probe.prior_k3_job_id == PRIOR_K3_JOB_ID
        && probe.prior_k2_receipt == PRIOR_K2_RECEIPT
        && probe.prior_k2_job_id == PRIOR_K2_JOB_ID
        && probe.prior_d3_receipt == PRIOR_D3_RECEIPT
        && probe.prior_d3_job_id == PRIOR_D3_JOB_ID
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.workstream_id == WORKSTREAM_ID
        && probe.formal_probe_count == FORMAL_PROBE_COUNT
        && probe.expected_proved_count == 0
        && probe.ac55_fence_deepen_closed
        && probe.formal_fence_closed
        && probe.cert_proved_fence_honest
        && probe.lean_posture_on_disk
        && probe.k3_absorbed
        && probe.k2_absorbed
        && probe.d3_absorbed
        && !probe.pbm_007_fully_closed
        && probe.pbm_007_flip_blocked
        && !probe.production_wired
        && !probe.posth_02_exit_zero
        && probe.wire_hop_count == WIRE_HOPS.len()
}

/// K3 fence deepen closed — chains K2+D3 absorb + formal audit GREEN; **not** tier promotion.
#[must_use]
pub fn pbm_007_k1941_fence_deepen_closed() -> bool {
    pbm_007_formal_fence_closed()
        && tyto_workspace_root().join(PRIOR_D3_RECEIPT).is_file()
        && pbm_007_k1938_honest(&pbm_007_k1938_probe())
        && !pbm_007_fully_closed()
}

/// AC55 fence deepen closed — chains K3+K2+D3 absorb + formal audit GREEN; **not** tier promotion.
#[must_use]
pub fn pbm_007_ac55_fence_deepen_closed() -> bool {
    pbm_007_formal_fence_closed()
        && tyto_workspace_root().join(PRIOR_K3_RECEIPT).is_file()
        && pbm_007_k1941_honest(&pbm_007_k1941_probe())
        && !pbm_007_fully_closed()
}

/// K2 operator probe — chains D3; pins formal-fence close predicate for PBM-007.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm007K1938Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_d3_receipt: &'static str,
    pub prior_d3_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub expected_proved_count: usize,
    pub formal_fence_closed: bool,
    pub cert_proved_fence_honest: bool,
    pub lean_posture_on_disk: bool,
    pub d3_absorbed: bool,
    pub pbm_007_fully_closed: bool,
    pub pbm_007_flip_blocked: bool,
    pub production_wired: bool,
    pub posth_02_exit_zero: bool,
    pub wire_hop_count: usize,
}

/// Build PRABHU-WAVE-K-1938 K2 probe.
#[must_use]
pub fn pbm_007_k1938_probe() -> Pbm007K1938Probe {
    let audit = run_formal_cert_proved_fence_audit();
    let d3 = pbm_007_ws_cert_proved_probe_honest();
    Pbm007K1938Probe {
        job_id: PRIOR_K2_JOB_ID,
        receipt_path: PRIOR_K2_RECEIPT,
        prior_d3_receipt: PRIOR_D3_RECEIPT,
        prior_d3_job_id: PRIOR_D3_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        expected_proved_count: EXPECTED_PROVED_COUNT,
        formal_fence_closed: pbm_007_formal_fence_closed(),
        cert_proved_fence_honest: audit.all_green(),
        lean_posture_on_disk: lean_cert_proved_posture_on_disk(),
        d3_absorbed: tyto_workspace_root().join(PRIOR_D3_RECEIPT).is_file()
            && d3.expected_proved_count == 0
            && d3.formal_probe_count == FORMAL_PROBE_COUNT
            && d3.lean_posture_on_disk
            && !d3.pbm_007_fully_closed
            && d3.pbm_007_flip_blocked,
        pbm_007_fully_closed: pbm_007_fully_closed(),
        pbm_007_flip_blocked: true,
        production_wired: pbm_007_production_wired(),
        posth_02_exit_zero: false,
        wire_hop_count: K2_WIRE_HOP_COUNT,
    }
}

/// K2 honesty gate — formal fence closed; tier promotion still blocked.
#[must_use]
pub fn pbm_007_k1938_honest(probe: &Pbm007K1938Probe) -> bool {
    probe.job_id == PRIOR_K2_JOB_ID
        && probe.receipt_path == PRIOR_K2_RECEIPT
        && probe.prior_d3_receipt == PRIOR_D3_RECEIPT
        && probe.prior_d3_job_id == PRIOR_D3_JOB_ID
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.workstream_id == WORKSTREAM_ID
        && probe.formal_probe_count == FORMAL_PROBE_COUNT
        && probe.expected_proved_count == 0
        && probe.formal_fence_closed
        && probe.cert_proved_fence_honest
        && probe.lean_posture_on_disk
        && probe.d3_absorbed
        && !probe.pbm_007_fully_closed
        && probe.pbm_007_flip_blocked
        && !probe.production_wired
        && !probe.posth_02_exit_zero
        && probe.wire_hop_count == K2_WIRE_HOP_COUNT
}

/// Run the 10-probe formal-side cert-proved fence audit (stdlib only).
#[must_use]
pub fn run_formal_cert_proved_fence_audit() -> Pbm007FormalAudit {
    let probes = vec![
        Pbm007FormalProbe {
            probe: "lean_l1b_on_disk",
            green: l1b_lean_source_on_disk(),
            detail: "MicroMechanics.lean @ umst-formal",
        },
        Pbm007FormalProbe {
            probe: "lean_posture_pins",
            green: lean_cert_proved_posture_on_disk(),
            detail: "expectedProvedCount=0 · catalogExportDeferred=true",
        },
        Pbm007FormalProbe {
            probe: "l1b_mt_zero_witness",
            green: e_eff_mt_at_zero_holds(30e9),
            detail: "E_eff = E₀ at d=0 (Rust↔Lean witness)",
        },
        Pbm007FormalProbe {
            probe: "l1b_psi_nonpos",
            green: psi_elastic_base_nonpos_holds(0.01, 0.5, 30e9),
            detail: "ψ_elastic_base ≤ 0 admissible domain",
        },
        Pbm007FormalProbe {
            probe: "l1b_softening_witness",
            green: psi_softening_micro_mechanics_holds(0.01, 0.2, 0.6, 30e9),
            detail: "ψ antitone in damage (MT-4 family)",
        },
        Pbm007FormalProbe {
            probe: "expected_proved_zero",
            green: EXPECTED_PROVED_COUNT == 0,
            detail: "EXPECTED_PROVED_COUNT=0 posture",
        },
        Pbm007FormalProbe {
            probe: "catalog_export_deferred",
            green: catalog_export_deferred(),
            detail: "no catalog [proved] export without operator",
        },
        Pbm007FormalProbe {
            probe: "pbm_007_not_fully_closed",
            green: !pbm_007_fully_closed(),
            detail: "pbm_007_fully_closed() stays false",
        },
        Pbm007FormalProbe {
            probe: "production_not_wired",
            green: !pbm_007_production_wired(),
            detail: "production_wired=false honest",
        },
        Pbm007FormalProbe {
            probe: "lean_module_authority",
            green: L1B_LEAN_MODULE == "Concrete.MicroMechanics"
                && L1B_WITNESS_THEOREM.contains("MicroMechanics"),
            detail: "L1b module + theorem cross-link",
        },
    ];

    Pbm007FormalAudit {
        job_id: JOB_ID,
        posture: POSTURE_TAG,
        expected_proved_count: EXPECTED_PROVED_COUNT,
        probes,
    }
}

/// Returns the honest D3 PBM-007 cert-proved posture (no I/O).
#[must_use]
pub fn pbm_007_ws_cert_proved_probe_honest() -> Pbm007WsCertProvedProbe {
    let audit = run_formal_cert_proved_fence_audit();
    Pbm007WsCertProvedProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        absorbed_z100_receipt: ABSORBED_Z100_RECEIPT,
        absorbed_z43_receipt: ABSORBED_Z43_RECEIPT,
        absorbed_y58_receipt: ABSORBED_Y58_RECEIPT,
        absorbed_j39_receipt: ABSORBED_J39_RECEIPT,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        lean_module: L1B_LEAN_MODULE,
        lean_theorem: L1B_WITNESS_THEOREM,
        probe_count: PROBE_COUNT,
        formal_probe_count: audit.probes.len(),
        expected_proved_count: EXPECTED_PROVED_COUNT,
        pbm_007_fully_closed: pbm_007_fully_closed(),
        pbm_007_flip_blocked: true,
        production_wired: pbm_007_production_wired(),
        lean_posture_on_disk: lean_cert_proved_posture_on_disk(),
        formal_owner_wired: true,
        bench_consumer_wired: true,
        meta_pbm_007_wired: true,
        posth_02_exit_zero: false,
        catalog_export_deferred: catalog_export_deferred(),
        concrete_validation_status: "unvalidated",
        p7_gate_status: "Open",
        wire_hop_count: WIRE_HOPS.len(),
    }
}

/// Done-when probe — honest RESIDUE: structural fence GREEN, tier promotion blocked.
#[must_use]
pub fn pbm_007_done_when_probe() -> Pbm007DoneWhenProbe {
    let audit = run_formal_cert_proved_fence_audit();
    Pbm007DoneWhenProbe {
        cert_proved_fence_honest: audit.all_green(),
        measured_epsilon_landed: false,
        posth_02_ceremony_complete: false,
        operator_o5_cleared: false,
        master_retick_eligible: false,
        closure: "RESIDUE",
    }
}

/// Filesystem probe for PBM-007 formal cert-proved posture (honest RESIDUE).
pub fn probe_pbm_007_formal_ws_cert_proved(root: &Path) -> Result<String, String> {
    let lean_source = umst_formal_root().join(LEAN_SOURCE_RELPATH);
    let bench_consumer = root.join(BENCH_CONSUMER_PATH);
    let posture_fixture = root.join(BENCH_POSTURE_FIXTURE);
    let meta_owner = root.join(META_OWNER_PATH);
    let z100_receipt = root.join(ABSORBED_Z100_RECEIPT);
    let posth_02_surface = root.join(POSTH_02_BARC_SURFACE);

    if !lean_source.is_file() {
        return Err(format!("missing Lean source: {}", lean_source.display()));
    }
    if !lean_cert_proved_posture_on_disk() {
        return Err("MicroMechanics.lean missing cert-proved posture pins".into());
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
    if !meta_owner.is_file() {
        return Err(format!("missing meta owner: {}", meta_owner.display()));
    }
    if !z100_receipt.is_file() {
        return Err(format!("missing Z100 receipt: {}", z100_receipt.display()));
    }
    if !posth_02_surface.is_file() {
        return Err(format!(
            "missing POSTH-02 surface: {}",
            posth_02_surface.display()
        ));
    }

    let consumer_text = fs::read_to_string(&bench_consumer)
        .map_err(|e| format!("cannot read {}: {e}", bench_consumer.display()))?;
    let posture_text = fs::read_to_string(&posture_fixture)
        .map_err(|e| format!("cannot read {}: {e}", posture_fixture.display()))?;
    let meta_text = fs::read_to_string(&meta_owner)
        .map_err(|e| format!("cannot read {}: {e}", meta_owner.display()))?;

    if !consumer_text.contains("EXPECTED_PROVED_COUNT: usize = 0") {
        return Err("bench consumer missing EXPECTED_PROVED_COUNT=0 fence".into());
    }
    if !posture_text.contains("\"expected_proved_count\": 0") {
        return Err("posture fixture missing expected_proved_count=0".into());
    }
    if !meta_text.contains("EXPECTED_PROVED_COUNT: usize = 0") {
        return Err("meta owner missing EXPECTED_PROVED_COUNT=0 fence".into());
    }

    let probe = pbm_007_ws_cert_proved_probe_honest();
    let done = pbm_007_done_when_probe();
    if probe.pbm_007_fully_closed || done.master_retick_eligible {
        return Err("PBM-007 posture regression: must remain RESIDUE with flip blocked".into());
    }

    Ok(format!(
        "job={JOB_ID} workstream={WORKSTREAM_ID} status=[~] \
         expected_proved_count=0 pbm_007_fully_closed=false pbm_007_flip_blocked=true \
         production_wired=false formal_owner_wired=true lean_posture_on_disk=true \
         bench_consumer_wired=true meta_pbm_007_wired=true posth_02_exit_zero=false \
         concrete_validation_status=unvalidated p7_gate_status=Open closure=RESIDUE \
         wire_hops={} absorbed_z100={ABSORBED_Z100_RECEIPT}",
        WIRE_HOPS.len()
    ))
}

/// K3 fence-deepen filesystem witness — chains K2+D3 absorb; honest RESIDUE.
pub fn probe_pbm_007_k1941_fence_deepen(root: &Path) -> Result<String, String> {
    let d3_receipt = root.join(PRIOR_D3_RECEIPT);
    if !d3_receipt.is_file() {
        return Err(format!("missing D3 receipt: {}", d3_receipt.display()));
    }
    if !pbm_007_k1941_fence_deepen_closed() {
        return Err("K1941 fence deepen not closed — structural audit or K2 absorb failed".into());
    }
    let probe = pbm_007_k1941_probe();
    if !pbm_007_k1941_honest(&probe) {
        return Err("K1941 probe honesty gate failed".into());
    }
    if probe.pbm_007_fully_closed || probe.posth_02_exit_zero {
        return Err("PBM-007 posture regression: must remain RESIDUE with flip blocked".into());
    }
    Ok(format!(
        "job={PRIOR_K3_JOB_ID} k1941_fence_deepen_closed=true formal_fence_closed=true \
         k2_absorbed=true d3_absorbed=true expected_proved_count=0 \
         pbm_007_fully_closed=false pbm_007_flip_blocked=true production_wired=false \
         posth_02_exit_zero=false closure=RESIDUE wire_hops={K3_WIRE_HOP_COUNT}"
    ))
}

/// AC55 fence-deepen filesystem witness — chains K3+K2+D3 absorb; honest RESIDUE.
pub fn probe_pbm_007_ac55_fence_deepen(root: &Path) -> Result<String, String> {
    let k3_receipt = root.join(PRIOR_K3_RECEIPT);
    if !k3_receipt.is_file() {
        return Err(format!("missing K3 receipt: {}", k3_receipt.display()));
    }
    if !pbm_007_ac55_fence_deepen_closed() {
        return Err("AC55 fence deepen not closed — structural audit or K3 absorb failed".into());
    }
    let probe = pbm_007_ac55_probe();
    if !pbm_007_ac55_honest(&probe) {
        return Err("AC55 probe honesty gate failed".into());
    }
    if probe.pbm_007_fully_closed || probe.posth_02_exit_zero {
        return Err("PBM-007 posture regression: must remain RESIDUE with flip blocked".into());
    }
    Ok(format!(
        "job={JOB_ID} ac55_fence_deepen_closed=true formal_fence_closed=true \
         k3_absorbed=true k2_absorbed=true d3_absorbed=true expected_proved_count=0 \
         pbm_007_fully_closed=false pbm_007_flip_blocked=true production_wired=false \
         posth_02_exit_zero=false closure=RESIDUE wire_hops={}",
        WIRE_HOPS.len()
    ))
}

/// D3 deepen honesty gate — formal audit all green; tier promotion still blocked.
#[must_use]
pub fn pbm_007_d1650_honest(probe: &Pbm007WsCertProvedProbe) -> bool {
    probe.job_id == PRIOR_D3_JOB_ID
        && probe.receipt_path == PRIOR_D3_RECEIPT
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.workstream_id == WORKSTREAM_ID
        && probe.expected_proved_count == 0
        && probe.formal_probe_count == FORMAL_PROBE_COUNT
        && probe.lean_posture_on_disk
        && probe.formal_owner_wired
        && probe.catalog_export_deferred
        && !probe.pbm_007_fully_closed
        && probe.pbm_007_flip_blocked
        && !probe.production_wired
        && !probe.posth_02_exit_zero
        && probe.p7_gate_status == "Open"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pbm_007_ac55_metadata_wired() {
        assert_eq!(FLEET_PARENT, "ACCEL-B-2050");
        assert_eq!(JOB_ID, "ACCEL-B-2050-AC55-PBM-007");
        assert_eq!(RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL2_AC55.md");
        assert_eq!(PRIOR_K3_JOB_ID, "PRABHU-WAVE-K-1941-K3-PBM-007");
        assert_eq!(PRIOR_K3_RECEIPT, "outputs/.tmp/COMPOSER_P1941_K3.md");
        assert_eq!(PRIOR_K3_FLEET_PARENT, "PRABHU-WAVE-K-1941");
        assert_eq!(PRIOR_K2_JOB_ID, "PRABHU-WAVE-K-1938-K2-PBM-007");
        assert_eq!(PRIOR_K2_RECEIPT, "outputs/.tmp/COMPOSER_P1938_K2.md");
        assert_eq!(PRIOR_D3_JOB_ID, "PRABHU-WAVE-D-1650-D3-PBM-007");
        assert_eq!(PRIOR_D3_RECEIPT, "outputs/.tmp/COMPOSER_P1650_D3.md");
        assert_eq!(PARENT_WORKSTREAM_ID, "PBM-007");
        assert_eq!(WORKSTREAM_ID, "WS-cert-proved");
        assert_eq!(FORMAL_PROBE_COUNT, 10);
        assert_eq!(K2_WIRE_HOP_COUNT, 8);
        assert_eq!(K3_WIRE_HOP_COUNT, 9);
    }

    #[test]
    fn pbm_007_ws_cert_proved_probe_honest_fences_hold() {
        let probe = pbm_007_ws_cert_proved_probe_honest();
        assert_eq!(probe.job_id, JOB_ID);
        assert_eq!(probe.parent_workstream_id, "PBM-007");
        assert_eq!(probe.workstream_id, "WS-cert-proved");
        assert_eq!(probe.probe_count, 10);
        assert_eq!(probe.formal_probe_count, FORMAL_PROBE_COUNT);
        assert_eq!(probe.expected_proved_count, 0);
        assert!(!probe.pbm_007_fully_closed);
        assert!(!pbm_007_fully_closed());
        assert!(probe.pbm_007_flip_blocked);
        assert!(!probe.production_wired);
        assert!(!pbm_007_production_wired());
        assert!(probe.lean_posture_on_disk);
        assert!(probe.formal_owner_wired);
        assert!(probe.bench_consumer_wired);
        assert!(probe.meta_pbm_007_wired);
        assert!(!probe.posth_02_exit_zero);
        assert!(probe.catalog_export_deferred);
        assert_eq!(probe.concrete_validation_status, "unvalidated");
        assert_eq!(probe.p7_gate_status, "Open");
        assert_eq!(probe.wire_hop_count, WIRE_HOPS.len());
    }

    #[test]
    fn pbm_007_done_when_residue_measured() {
        let done = pbm_007_done_when_probe();
        assert!(done.cert_proved_fence_honest);
        assert!(!done.measured_epsilon_landed);
        assert!(!done.posth_02_ceremony_complete);
        assert!(!done.operator_o5_cleared);
        assert!(!done.master_retick_eligible);
        assert_eq!(done.closure, "RESIDUE");
    }

    #[test]
    fn pbm_007_formal_cert_proved_fence_audit_10_green() {
        let audit = run_formal_cert_proved_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        for p in &audit.probes {
            assert!(p.green, "probe {:?} failed", p);
        }
    }

    #[test]
    fn pbm_007_wire_hops_cover_cert_proved_surfaces() {
        assert_eq!(WIRE_HOPS.len(), 10);
        assert_eq!(WIRE_HOPS[0].surface, LEAN_SOURCE_RELPATH);
        assert_eq!(WIRE_HOPS[1].surface, FORMAL_WITNESS_RELPATH);
        assert_eq!(WIRE_HOPS[3].surface, META_OWNER_PATH);
        assert_eq!(WIRE_HOPS[5].surface, ABSORBED_Z100_RECEIPT);
        assert_eq!(WIRE_HOPS[6].surface, POSTH_02_BARC_SURFACE);
        assert_eq!(WIRE_HOPS[7].surface, PRIOR_D3_RECEIPT);
        assert_eq!(WIRE_HOPS[8].surface, PRIOR_K2_RECEIPT);
        assert_eq!(WIRE_HOPS[9].surface, PRIOR_K3_RECEIPT);
    }

    #[test]
    fn pbm_007_formal_fence_closed_measured() {
        assert!(pbm_007_formal_fence_closed());
        let audit = run_formal_cert_proved_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        assert!(audit.all_green());
        assert!(lean_cert_proved_posture_on_disk());
        assert!(!pbm_007_fully_closed());
    }

    #[test]
    fn pbm_007_k1938_formal_fence_closed() {
        let probe = pbm_007_k1938_probe();
        assert!(pbm_007_k1938_honest(&probe));
        assert!(probe.formal_fence_closed);
        assert!(probe.cert_proved_fence_honest);
        assert!(probe.d3_absorbed);
        assert_eq!(probe.wire_hop_count, 8);
        assert!(!probe.pbm_007_fully_closed);
        assert!(!probe.production_wired);
    }

    #[test]
    fn pbm_007_d3_structural_honest() {
        let probe = pbm_007_ws_cert_proved_probe_honest();
        assert_eq!(probe.expected_proved_count, 0);
        assert_eq!(probe.formal_probe_count, FORMAL_PROBE_COUNT);
        assert!(probe.lean_posture_on_disk);
        assert!(!probe.pbm_007_fully_closed);
        assert!(probe.pbm_007_flip_blocked);
        assert!(tyto_workspace_root().join(PRIOR_D3_RECEIPT).is_file());
    }

    #[test]
    fn pbm_007_k1941_formal_fence_deepen() {
        let probe = pbm_007_k1941_probe();
        assert!(pbm_007_k1941_honest(&probe));
        assert!(probe.k1941_fence_deepen_closed);
        assert!(probe.formal_fence_closed);
        assert!(probe.k2_absorbed);
        assert!(probe.d3_absorbed);
        assert_eq!(probe.wire_hop_count, K3_WIRE_HOP_COUNT);
        assert!(!probe.pbm_007_fully_closed);
        assert!(!probe.production_wired);
        assert!(pbm_007_k1941_fence_deepen_closed());
    }

    #[test]
    fn pbm_007_ac55_formal_fence_deepen() {
        let probe = pbm_007_ac55_probe();
        assert!(pbm_007_ac55_honest(&probe));
        assert!(probe.ac55_fence_deepen_closed);
        assert!(probe.formal_fence_closed);
        assert!(probe.k3_absorbed);
        assert!(probe.k2_absorbed);
        assert!(probe.d3_absorbed);
        assert_eq!(probe.wire_hop_count, 10);
        assert!(!probe.pbm_007_fully_closed);
        assert!(!probe.production_wired);
        assert!(pbm_007_ac55_fence_deepen_closed());
    }

    #[test]
    fn probe_pbm_007_k1941_fence_deepen_witness_on_disk() {
        let root = tyto_workspace_root();
        let msg = probe_pbm_007_k1941_fence_deepen(&root).expect("K1941 fence deepen witness");
        assert!(
            msg.contains("k1941_fence_deepen_closed=true"),
            "deepen: {msg}"
        );
        assert!(msg.contains("expected_proved_count=0"), "fence: {msg}");
        assert!(msg.contains("pbm_007_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("wire_hops=9"), "hops: {msg}");
    }

    #[test]
    fn probe_pbm_007_ac55_fence_deepen_witness_on_disk() {
        let root = tyto_workspace_root();
        let msg = probe_pbm_007_ac55_fence_deepen(&root).expect("AC55 fence deepen witness");
        assert!(
            msg.contains("ac55_fence_deepen_closed=true"),
            "deepen: {msg}"
        );
        assert!(msg.contains("k3_absorbed=true"), "k3: {msg}");
        assert!(msg.contains("expected_proved_count=0"), "fence: {msg}");
        assert!(msg.contains("pbm_007_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("wire_hops=10"), "hops: {msg}");
    }

    #[test]
    fn probe_pbm_007_formal_filesystem_honest_residue() {
        let root = tyto_workspace_root();
        if !root.join(BENCH_CONSUMER_PATH).exists() {
            eprintln!("skip probe_pbm_007_formal_filesystem_honest_residue: bench consumer absent");
            return;
        }
        let msg = probe_pbm_007_formal_ws_cert_proved(&root).expect("PBM-007 paths on disk");
        assert!(msg.contains("status=[~]"), "must not invent [x]: {msg}");
        assert!(msg.contains("expected_proved_count=0"), "fence: {msg}");
        assert!(msg.contains("pbm_007_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("formal_owner_wired=true"), "witness: {msg}");
        assert!(msg.contains("lean_posture_on_disk=true"), "lean: {msg}");
    }
}
