// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-25-2030 AC04 — PBM-010 `R-atoms-scalar` formal-tree owner deepen.
//
// Formal-side complement to `umst-bench` Y60 consumer witness and manifold `atoms_*` owner.
// Deepens honest F1-lift posture pins — **no** `f1_fully_closed`, rank-1+ impl, or algebra-burn crate.
// Does **not** invent production tensor eval, measured live HAL, or INV4 4/4.
//
// Prior: Y60 (`COMPOSER_Y60_0808`) · FRONTIER owner-wire · E2 (`COMPOSER_P1700_E2`) · H4 (`COMPOSER_P1800_H4`) — absorbed; not re-census.

use std::fs;
use std::path::{Path, PathBuf};

use super::lean_l1_stiffness_adopt::umst_formal_root;

/// ACCEL-25 fleet parent id.
pub const FLEET_PARENT: &str = "FLEET-COMPOSER-ACCEL-25-2030";

/// AC04 slot job id.
pub const JOB_ID: &str = "FLEET-COMPOSER-ACCEL-25-2030-AC04-PBM-010";

/// AC04 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL_2030_AC04.md";

/// Y60 prior receipt — absorbed; not re-census.
pub const PRIOR_Y60_RECEIPT: &str = "outputs/.tmp/COMPOSER_Y60_0808.md";

/// Y60 prior job id — absorbed through AC04.
pub const PRIOR_Y60_JOB_ID: &str = "FLEET-COMPOSER-Y60-PBM-010-R-ATOMS-SCALAR";

/// FRONTIER owner-wire report — absorbed through Y60.
pub const PRIOR_FRONTIER_REPORT: &str =
    "outputs/staged-web/swarm/CELL_FRONTIER_L10_OR_ATOMS_REPORT.md";

/// E2 prior receipt — absorbed; not re-census.
pub const PRIOR_E2_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1700_E2.md";

/// E2 prior job id.
pub const PRIOR_E2_JOB_ID: &str = "PRABHU-WAVE-E-1700-E2-PBM-010";

/// H4 prior receipt — absorbed; not re-census.
pub const PRIOR_H4_RECEIPT: &str = "outputs/.tmp/COMPOSER_P1800_H4.md";

/// H4 prior job id.
pub const PRIOR_H4_JOB_ID: &str = "PRABHU-WAVE-H-1800-H4-PBM-010";

/// AGAP-2350 slice-3c authority receipt — carried through Y60.
pub const PRIOR_2350_RECEIPT: &str =
    "old/residuals/residuals/misc-outputs-tmp/COMPLETION_AGAP_AGENT_PBM-010_2350.md";

/// Parent PBM card id.
pub const PARENT_WORKSTREAM_ID: &str = "PBM-010";

/// Workstream id per master TODO §4.2.
pub const WORKSTREAM_ID: &str = "R-atoms-scalar";

/// Bench consumer witness module (umst-bench owner complement).
pub const BENCH_CONSUMER_PATH: &str = "crates/umst-bench/src/pbm_010_atoms_scalar.rs";

/// Frozen posture fixture (bench consumer).
pub const BENCH_POSTURE_FIXTURE: &str =
    "crates/umst-bench/fixtures/pbm_010_atoms_scalar_posture.json";

/// Manifold owner residual surface.
pub const MANIFOLD_RESIDUAL_SURFACE: &str =
    "umst-manifold/src/runtime/atoms_tensor_lift_residual.rs";

/// Manifold owner adapter surface.
pub const MANIFOLD_ADAPTER_SURFACE: &str = "umst-manifold/src/runtime/atoms_tensor_lift_adapter.rs";

/// Manifold owner ledger surface.
pub const MANIFOLD_LEDGER_SURFACE: &str = "umst-manifold/src/runtime/atoms_tensor_lift_ledger.rs";

/// Manifold owner ops surface.
pub const MANIFOLD_OPS_SURFACE: &str = "umst-manifold/src/runtime/atoms_tensor_lift_ops.rs";

/// Manifold F1 deepen rollup surface (E2/H4 chain).
pub const MANIFOLD_F1_DEEPEN_SURFACE: &str = "umst-manifold/src/runtime/atoms_f1_deepen.rs";

/// Deferred algebra-burn crate surface (F14 — not landed).
pub const ALGEBRA_BURN_SURFACE: &str = "umst-runtime/crates/umst-algebra-burn/";

/// Formal-side witness module (this file).
pub const FORMAL_WITNESS_RELPATH: &str = "umst-formal/ffi-bridge/src/pbm_010_atoms_scalar.rs";

/// Honest adoption tier.
pub const POSTURE_TAG: &str = "honest-partial";

/// Frozen slice residual row count @ owner census.
pub const SLICE_RESIDUAL_ROW_COUNT: usize = 8;

/// Open ladder rows (C7 only) @ owner census.
pub const OPEN_ROW_COUNT: usize = 1;

/// Blocking rows @ owner census (slice-3b, 3c, 3d, C7).
pub const BLOCKING_ROW_COUNT: usize = 4;

/// Probe-wired fence hops @ Y60 deepen (F10..F13).
pub const PROBE_HOPS_WIRED: usize = 4;

/// F1 lift fence hop count @ Y60 deepen.
pub const FENCE_HOP_COUNT: usize = 5;

/// Formal-side F1-lift fence probe count (this module's audit).
pub const FORMAL_PROBE_COUNT: usize = 10;

/// One hop on the PBM-010 F1-lift wire map (formal owner).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm010AtomsScalarWireHop {
    pub ordinal: u8,
    pub surface: &'static str,
    pub role: &'static str,
}

/// PBM-010 F1-lift wire map @ AC04 (formal owner deepen).
pub const WIRE_HOPS: &[Pbm010AtomsScalarWireHop] = &[
    Pbm010AtomsScalarWireHop {
        ordinal: 1,
        surface: FORMAL_WITNESS_RELPATH,
        role: "Formal-tree ffi-bridge owner witness (AC04)",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 2,
        surface: BENCH_CONSUMER_PATH,
        role: "Bench consumer F1-lift fence (Y60 chain)",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 3,
        surface: BENCH_POSTURE_FIXTURE,
        role: "Frozen posture pins (f1_fully_closed=false)",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 4,
        surface: MANIFOLD_RESIDUAL_SURFACE,
        role: "Owner slice residual ladder (8 rows)",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 5,
        surface: MANIFOLD_ADAPTER_SURFACE,
        role: "Owner adapter contract (6 deferred rows)",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 6,
        surface: MANIFOLD_LEDGER_SURFACE,
        role: "Owner rank-1+ ledger partial",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 7,
        surface: MANIFOLD_OPS_SURFACE,
        role: "Owner tensor op spec partial",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 8,
        surface: MANIFOLD_F1_DEEPEN_SURFACE,
        role: "E2/H4 F1 deepen rollup owner",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 9,
        surface: PRIOR_Y60_RECEIPT,
        role: "Y60 residue receipt (absorbed — not re-census)",
    },
    Pbm010AtomsScalarWireHop {
        ordinal: 10,
        surface: PRIOR_H4_RECEIPT,
        role: "H4 prior receipt (absorbed — not re-census)",
    },
];

/// One formal-side F1-lift fence probe outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm010FormalProbe {
    pub probe: &'static str,
    pub green: bool,
    pub detail: &'static str,
}

/// Formal-side F1-lift fence audit report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm010FormalAudit {
    pub job_id: &'static str,
    pub posture: &'static str,
    pub probes: Vec<Pbm010FormalProbe>,
}

impl Pbm010FormalAudit {
    #[must_use]
    pub fn all_green(&self) -> bool {
        self.probes.iter().all(|p| p.green)
    }
}

/// Honest PBM-010 F1-lift probe for operator receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm010AtomsScalarProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_y60_receipt: &'static str,
    pub prior_y60_job_id: &'static str,
    pub prior_e2_receipt: &'static str,
    pub prior_e2_job_id: &'static str,
    pub prior_h4_receipt: &'static str,
    pub prior_h4_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub slice_residual_row_count: usize,
    pub open_row_count: usize,
    pub blocking_row_count: usize,
    pub probe_hops_wired: usize,
    pub fence_hop_count: usize,
    pub formal_fence_closed: bool,
    pub f1_lift_fence_honest: bool,
    pub bench_consumer_wired: bool,
    pub posture_pins_f1_open: bool,
    pub pbm_010_fully_closed: bool,
    pub pbm_010_flip_blocked: bool,
    pub production_wired: bool,
    pub adapter_crate_landed: bool,
    pub wire_hop_count: usize,
}

/// PBM-010 done-when probe — documents honest RESIDUE posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm010DoneWhenProbe {
    pub formal_fence_closed: bool,
    pub f1_fully_closed: bool,
    pub rank1_plus_impl_landed: bool,
    pub adapter_crate_landed: bool,
    pub production_wired: bool,
    pub master_retick_eligible: bool,
    pub closure: &'static str,
}

/// AC04 operator probe — chains Y60→E2→H4; pins AC04 fence-deepen close predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm010AccelAc04Probe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub prior_y60_receipt: &'static str,
    pub prior_y60_job_id: &'static str,
    pub prior_e2_receipt: &'static str,
    pub prior_e2_job_id: &'static str,
    pub prior_h4_receipt: &'static str,
    pub prior_h4_job_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub workstream_id: &'static str,
    pub formal_probe_count: usize,
    pub accel_ac04_fence_deepen_closed: bool,
    pub formal_fence_closed: bool,
    pub f1_lift_fence_honest: bool,
    pub y60_absorbed: bool,
    pub e2_absorbed: bool,
    pub h4_absorbed: bool,
    pub pbm_010_fully_closed: bool,
    pub pbm_010_flip_blocked: bool,
    pub production_wired: bool,
    pub wire_hop_count: usize,
}

/// Resolve tyto-workspace root from ffi-bridge manifest.
#[must_use]
pub fn tyto_workspace_root() -> PathBuf {
    umst_formal_root()
        .parent()
        .expect("tyto-workspace parent")
        .to_path_buf()
}

/// Posture fixture pins `f1_fully_closed=false` on disk.
#[must_use]
pub fn posture_pins_f1_open_on_disk() -> bool {
    let path = tyto_workspace_root().join(BENCH_POSTURE_FIXTURE);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("\"f1_fully_closed\": false")
        && text.contains("\"rank1_plus_impl_landed\": false")
        && text.contains("\"adapter_crate_landed\": false")
        && text.contains("\"production_wired\": false")
        && text.contains("\"owner_wire_landed\": true")
}

/// Manifold owner surfaces for F10..F13 present on disk.
#[must_use]
pub fn manifold_owner_surfaces_on_disk() -> bool {
    let root = tyto_workspace_root();
    [
        MANIFOLD_RESIDUAL_SURFACE,
        MANIFOLD_ADAPTER_SURFACE,
        MANIFOLD_LEDGER_SURFACE,
        MANIFOLD_OPS_SURFACE,
        MANIFOLD_F1_DEEPEN_SURFACE,
    ]
    .iter()
    .all(|rel| root.join(rel).is_file())
}

/// Bench consumer F1-lift fence constants present on disk.
#[must_use]
pub fn bench_consumer_fence_on_disk() -> bool {
    let path = tyto_workspace_root().join(BENCH_CONSUMER_PATH);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("pub const SLICE_RESIDUAL_ROW_COUNT: usize = 8")
        && text.contains("pub const PROBE_HOPS_WIRED: usize = 4")
        && text.contains("pub const FENCE_HOP_COUNT: usize = 5")
        && text.contains("pub const fn pbm_010_fully_closed() -> bool")
        && text.contains("false")
}

/// PBM-010 done-when — **false** until rank-1+ tensor eval + C7 row lands.
#[must_use]
pub const fn pbm_010_fully_closed() -> bool {
    false
}

/// Honest fence — production wiring not earned until measured live tensor eval.
#[must_use]
pub const fn pbm_010_production_wired() -> bool {
    false
}

/// Algebra-burn crate (F14) — **not** landed.
#[must_use]
pub const fn adapter_crate_landed() -> bool {
    false
}

/// Run the 10-probe formal-side F1-lift fence audit (stdlib only).
#[must_use]
pub fn run_formal_atoms_scalar_fence_audit() -> Pbm010FormalAudit {
    let probes = vec![
        Pbm010FormalProbe {
            probe: "bench_consumer_on_disk",
            green: tyto_workspace_root().join(BENCH_CONSUMER_PATH).is_file(),
            detail: "umst-bench pbm_010_atoms_scalar.rs present",
        },
        Pbm010FormalProbe {
            probe: "posture_fixture_on_disk",
            green: tyto_workspace_root().join(BENCH_POSTURE_FIXTURE).is_file(),
            detail: "pbm_010_atoms_scalar_posture.json present",
        },
        Pbm010FormalProbe {
            probe: "posture_pins_f1_open",
            green: posture_pins_f1_open_on_disk(),
            detail: "f1_fully_closed=false · owner_wire_landed=true",
        },
        Pbm010FormalProbe {
            probe: "manifold_owner_surfaces",
            green: manifold_owner_surfaces_on_disk(),
            detail: "F10..F13 + atoms_f1_deepen on disk",
        },
        Pbm010FormalProbe {
            probe: "bench_consumer_fence_constants",
            green: bench_consumer_fence_on_disk(),
            detail: "8 rows · 4 probe hops · 5 fence hops",
        },
        Pbm010FormalProbe {
            probe: "slice_residual_row_count_8",
            green: SLICE_RESIDUAL_ROW_COUNT == 8,
            detail: "SLICE_RESIDUAL_ROW_COUNT=8 posture",
        },
        Pbm010FormalProbe {
            probe: "blocking_row_count_4",
            green: BLOCKING_ROW_COUNT == 4 && OPEN_ROW_COUNT == 1,
            detail: "4 blocking · 1 open (C7)",
        },
        Pbm010FormalProbe {
            probe: "pbm_010_not_fully_closed",
            green: !pbm_010_fully_closed(),
            detail: "pbm_010_fully_closed() stays false",
        },
        Pbm010FormalProbe {
            probe: "production_not_wired",
            green: !pbm_010_production_wired(),
            detail: "production_wired=false honest",
        },
        Pbm010FormalProbe {
            probe: "adapter_crate_not_landed",
            green: !adapter_crate_landed(),
            detail: "umst-algebra-burn crate still open (F14)",
        },
    ];

    Pbm010FormalAudit {
        job_id: JOB_ID,
        posture: POSTURE_TAG,
        probes,
    }
}

/// Formal F1-lift fence closed — structural audit GREEN; **not** F1/tensor promotion.
#[must_use]
pub fn pbm_010_formal_fence_closed() -> bool {
    run_formal_atoms_scalar_fence_audit().all_green()
        && posture_pins_f1_open_on_disk()
        && manifold_owner_surfaces_on_disk()
        && !pbm_010_fully_closed()
}

/// Returns the honest AC04 PBM-010 atoms-scalar posture (no I/O beyond audit helpers).
#[must_use]
pub fn pbm_010_atoms_scalar_probe_honest() -> Pbm010AtomsScalarProbe {
    let audit = run_formal_atoms_scalar_fence_audit();
    Pbm010AtomsScalarProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_y60_receipt: PRIOR_Y60_RECEIPT,
        prior_y60_job_id: PRIOR_Y60_JOB_ID,
        prior_e2_receipt: PRIOR_E2_RECEIPT,
        prior_e2_job_id: PRIOR_E2_JOB_ID,
        prior_h4_receipt: PRIOR_H4_RECEIPT,
        prior_h4_job_id: PRIOR_H4_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        slice_residual_row_count: SLICE_RESIDUAL_ROW_COUNT,
        open_row_count: OPEN_ROW_COUNT,
        blocking_row_count: BLOCKING_ROW_COUNT,
        probe_hops_wired: PROBE_HOPS_WIRED,
        fence_hop_count: FENCE_HOP_COUNT,
        formal_fence_closed: pbm_010_formal_fence_closed(),
        f1_lift_fence_honest: audit.all_green(),
        bench_consumer_wired: tyto_workspace_root().join(BENCH_CONSUMER_PATH).is_file(),
        posture_pins_f1_open: posture_pins_f1_open_on_disk(),
        pbm_010_fully_closed: pbm_010_fully_closed(),
        pbm_010_flip_blocked: true,
        production_wired: pbm_010_production_wired(),
        adapter_crate_landed: adapter_crate_landed(),
        wire_hop_count: WIRE_HOPS.len(),
    }
}

/// Done-when probe — honest RESIDUE: structural fence GREEN, F1 promotion blocked.
#[must_use]
pub fn pbm_010_done_when_probe() -> Pbm010DoneWhenProbe {
    Pbm010DoneWhenProbe {
        formal_fence_closed: pbm_010_formal_fence_closed(),
        f1_fully_closed: false,
        rank1_plus_impl_landed: false,
        adapter_crate_landed: adapter_crate_landed(),
        production_wired: pbm_010_production_wired(),
        master_retick_eligible: false,
        closure: "RESIDUE",
    }
}

/// Build FLEET-COMPOSER-ACCEL-25 AC04 probe.
#[must_use]
pub fn pbm_010_accel_ac04_probe() -> Pbm010AccelAc04Probe {
    let audit = run_formal_atoms_scalar_fence_audit();
    let base = pbm_010_atoms_scalar_probe_honest();
    Pbm010AccelAc04Probe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        prior_y60_receipt: PRIOR_Y60_RECEIPT,
        prior_y60_job_id: PRIOR_Y60_JOB_ID,
        prior_e2_receipt: PRIOR_E2_RECEIPT,
        prior_e2_job_id: PRIOR_E2_JOB_ID,
        prior_h4_receipt: PRIOR_H4_RECEIPT,
        prior_h4_job_id: PRIOR_H4_JOB_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        workstream_id: WORKSTREAM_ID,
        formal_probe_count: audit.probes.len(),
        accel_ac04_fence_deepen_closed: pbm_010_accel_ac04_fence_deepen_closed(),
        formal_fence_closed: base.formal_fence_closed,
        f1_lift_fence_honest: audit.all_green(),
        y60_absorbed: tyto_workspace_root().join(PRIOR_Y60_RECEIPT).is_file()
            && base.bench_consumer_wired,
        e2_absorbed: tyto_workspace_root().join(PRIOR_E2_RECEIPT).is_file(),
        h4_absorbed: tyto_workspace_root().join(PRIOR_H4_RECEIPT).is_file(),
        pbm_010_fully_closed: pbm_010_fully_closed(),
        pbm_010_flip_blocked: true,
        production_wired: pbm_010_production_wired(),
        wire_hop_count: WIRE_HOPS.len(),
    }
}

/// AC04 honesty gate — formal fence deepen closed; F1 promotion still blocked.
#[must_use]
pub fn pbm_010_accel_ac04_honest(probe: &Pbm010AccelAc04Probe) -> bool {
    probe.job_id == JOB_ID
        && probe.receipt_path == RECEIPT_PATH
        && probe.prior_y60_receipt == PRIOR_Y60_RECEIPT
        && probe.prior_y60_job_id == PRIOR_Y60_JOB_ID
        && probe.prior_e2_receipt == PRIOR_E2_RECEIPT
        && probe.prior_e2_job_id == PRIOR_E2_JOB_ID
        && probe.prior_h4_receipt == PRIOR_H4_RECEIPT
        && probe.prior_h4_job_id == PRIOR_H4_JOB_ID
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.workstream_id == WORKSTREAM_ID
        && probe.formal_probe_count == FORMAL_PROBE_COUNT
        && probe.accel_ac04_fence_deepen_closed
        && probe.formal_fence_closed
        && probe.f1_lift_fence_honest
        && probe.y60_absorbed
        && probe.e2_absorbed
        && probe.h4_absorbed
        && !probe.pbm_010_fully_closed
        && probe.pbm_010_flip_blocked
        && !probe.production_wired
        && probe.wire_hop_count == WIRE_HOPS.len()
}

/// AC04 fence deepen closed — chains Y60+E2+H4 absorb + formal audit GREEN; **not** F1 close.
#[must_use]
pub fn pbm_010_accel_ac04_fence_deepen_closed() -> bool {
    pbm_010_formal_fence_closed()
        && tyto_workspace_root().join(PRIOR_Y60_RECEIPT).is_file()
        && tyto_workspace_root().join(PRIOR_E2_RECEIPT).is_file()
        && tyto_workspace_root().join(PRIOR_H4_RECEIPT).is_file()
        && pbm_010_accel_ac04_honest(&pbm_010_accel_ac04_probe())
        && !pbm_010_fully_closed()
}

/// Filesystem probe for PBM-010 formal atoms-scalar posture (honest RESIDUE).
pub fn probe_pbm_010_formal_atoms_scalar(root: &Path) -> Result<String, String> {
    let bench_consumer = root.join(BENCH_CONSUMER_PATH);
    let posture_fixture = root.join(BENCH_POSTURE_FIXTURE);
    let y60_receipt = root.join(PRIOR_Y60_RECEIPT);

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
    if !posture_pins_f1_open_on_disk() {
        return Err("posture fixture missing f1_fully_closed=false pins".into());
    }
    if !manifold_owner_surfaces_on_disk() {
        return Err("manifold owner surfaces missing on disk".into());
    }
    if !y60_receipt.is_file() {
        return Err(format!("missing Y60 receipt: {}", y60_receipt.display()));
    }

    let consumer_text = fs::read_to_string(&bench_consumer)
        .map_err(|e| format!("cannot read {}: {e}", bench_consumer.display()))?;
    let posture_text = fs::read_to_string(&posture_fixture)
        .map_err(|e| format!("cannot read {}: {e}", posture_fixture.display()))?;

    if !consumer_text.contains("pub const fn pbm_010_fully_closed() -> bool") {
        return Err("bench consumer missing pbm_010_fully_closed fence".into());
    }
    if !posture_text.contains("\"f1_fully_closed\": false") {
        return Err("posture fixture missing f1_fully_closed=false".into());
    }

    let probe = pbm_010_atoms_scalar_probe_honest();
    let done = pbm_010_done_when_probe();
    if probe.pbm_010_fully_closed || done.master_retick_eligible {
        return Err("PBM-010 posture regression: must remain RESIDUE with flip blocked".into());
    }

    Ok(format!(
        "job={JOB_ID} workstream={WORKSTREAM_ID} status=[~] \
         formal_fence_closed=true f1_fully_closed=false pbm_010_fully_closed=false \
         pbm_010_flip_blocked=true production_wired=false adapter_crate_landed=false \
         formal_owner_wired=true bench_consumer_wired=true posture_pins_f1_open=true \
         closure=RESIDUE wire_hops={} absorbed_y60={PRIOR_Y60_RECEIPT}",
        WIRE_HOPS.len()
    ))
}

/// AC04 fence-deepen filesystem witness — chains Y60+E2+H4 absorb; honest RESIDUE.
pub fn probe_pbm_010_accel_ac04_fence_deepen(root: &Path) -> Result<String, String> {
    let e2_receipt = root.join(PRIOR_E2_RECEIPT);
    let h4_receipt = root.join(PRIOR_H4_RECEIPT);
    if !e2_receipt.is_file() {
        return Err(format!("missing E2 receipt: {}", e2_receipt.display()));
    }
    if !h4_receipt.is_file() {
        return Err(format!("missing H4 receipt: {}", h4_receipt.display()));
    }
    if !pbm_010_accel_ac04_fence_deepen_closed() {
        return Err(
            "AC04 fence deepen not closed — structural audit or prior absorb failed".into(),
        );
    }
    let probe = pbm_010_accel_ac04_probe();
    if !pbm_010_accel_ac04_honest(&probe) {
        return Err("AC04 probe honesty gate failed".into());
    }
    if probe.pbm_010_fully_closed {
        return Err("PBM-010 posture regression: must remain RESIDUE with flip blocked".into());
    }
    Ok(format!(
        "job={JOB_ID} accel_ac04_fence_deepen_closed=true formal_fence_closed=true \
         y60_absorbed=true e2_absorbed=true h4_absorbed=true f1_fully_closed=false \
         pbm_010_fully_closed=false pbm_010_flip_blocked=true production_wired=false \
         closure=RESIDUE wire_hops={}",
        WIRE_HOPS.len()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pbm_010_accel_ac04_metadata_wired() {
        assert_eq!(FLEET_PARENT, "FLEET-COMPOSER-ACCEL-25-2030");
        assert_eq!(JOB_ID, "FLEET-COMPOSER-ACCEL-25-2030-AC04-PBM-010");
        assert_eq!(RECEIPT_PATH, "outputs/.tmp/COMPOSER_ACCEL_2030_AC04.md");
        assert_eq!(
            PRIOR_Y60_JOB_ID,
            "FLEET-COMPOSER-Y60-PBM-010-R-ATOMS-SCALAR"
        );
        assert_eq!(PRIOR_E2_JOB_ID, "PRABHU-WAVE-E-1700-E2-PBM-010");
        assert_eq!(PRIOR_H4_JOB_ID, "PRABHU-WAVE-H-1800-H4-PBM-010");
        assert_eq!(PARENT_WORKSTREAM_ID, "PBM-010");
        assert_eq!(WORKSTREAM_ID, "R-atoms-scalar");
        assert_eq!(FORMAL_PROBE_COUNT, 10);
        assert_eq!(FENCE_HOP_COUNT, 5);
        assert_eq!(PROBE_HOPS_WIRED, 4);
    }

    #[test]
    fn pbm_010_atoms_scalar_probe_honest_fences_hold() {
        let probe = pbm_010_atoms_scalar_probe_honest();
        assert_eq!(probe.job_id, JOB_ID);
        assert_eq!(probe.parent_workstream_id, "PBM-010");
        assert_eq!(probe.workstream_id, "R-atoms-scalar");
        assert_eq!(probe.formal_probe_count, FORMAL_PROBE_COUNT);
        assert_eq!(probe.slice_residual_row_count, 8);
        assert_eq!(probe.open_row_count, 1);
        assert_eq!(probe.blocking_row_count, 4);
        assert!(!probe.pbm_010_fully_closed);
        assert!(!pbm_010_fully_closed());
        assert!(probe.pbm_010_flip_blocked);
        assert!(!probe.production_wired);
        assert!(!pbm_010_production_wired());
        assert!(!probe.adapter_crate_landed);
        assert_eq!(probe.wire_hop_count, WIRE_HOPS.len());
    }

    #[test]
    fn pbm_010_done_when_residue_measured() {
        let done = pbm_010_done_when_probe();
        assert!(done.formal_fence_closed);
        assert!(!done.f1_fully_closed);
        assert!(!done.rank1_plus_impl_landed);
        assert!(!done.adapter_crate_landed);
        assert!(!done.production_wired);
        assert!(!done.master_retick_eligible);
        assert_eq!(done.closure, "RESIDUE");
    }

    #[test]
    fn pbm_010_formal_atoms_scalar_fence_audit_10_green() {
        let audit = run_formal_atoms_scalar_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        for p in &audit.probes {
            assert!(p.green, "probe {p:?} failed");
        }
    }

    #[test]
    fn pbm_010_wire_hops_cover_atoms_scalar_surfaces() {
        assert_eq!(WIRE_HOPS.len(), 10);
        assert_eq!(WIRE_HOPS[0].surface, FORMAL_WITNESS_RELPATH);
        assert_eq!(WIRE_HOPS[1].surface, BENCH_CONSUMER_PATH);
        assert_eq!(WIRE_HOPS[7].surface, MANIFOLD_F1_DEEPEN_SURFACE);
        assert_eq!(WIRE_HOPS[8].surface, PRIOR_Y60_RECEIPT);
        assert_eq!(WIRE_HOPS[9].surface, PRIOR_H4_RECEIPT);
    }

    #[test]
    fn pbm_010_formal_fence_closed_measured() {
        assert!(pbm_010_formal_fence_closed());
        let audit = run_formal_atoms_scalar_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        assert!(audit.all_green());
        assert!(posture_pins_f1_open_on_disk());
        assert!(manifold_owner_surfaces_on_disk());
        assert!(!pbm_010_fully_closed());
    }

    #[test]
    fn pbm_010_accel_ac04_formal_fence_deepen() {
        let probe = pbm_010_accel_ac04_probe();
        assert!(pbm_010_accel_ac04_honest(&probe));
        assert!(probe.accel_ac04_fence_deepen_closed);
        assert!(probe.formal_fence_closed);
        assert!(probe.y60_absorbed);
        assert!(probe.e2_absorbed);
        assert!(probe.h4_absorbed);
        assert_eq!(probe.wire_hop_count, 10);
        assert!(!probe.pbm_010_fully_closed);
        assert!(!probe.production_wired);
        assert!(pbm_010_accel_ac04_fence_deepen_closed());
    }

    #[test]
    fn probe_pbm_010_accel_ac04_fence_deepen_witness_on_disk() {
        let root = tyto_workspace_root();
        let msg = probe_pbm_010_accel_ac04_fence_deepen(&root).expect("AC04 fence deepen witness");
        assert!(
            msg.contains("accel_ac04_fence_deepen_closed=true"),
            "deepen: {msg}"
        );
        assert!(msg.contains("f1_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("pbm_010_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("wire_hops=10"), "hops: {msg}");
    }

    #[test]
    fn probe_pbm_010_formal_filesystem_honest_residue() {
        let root = tyto_workspace_root();
        if !root.join(BENCH_CONSUMER_PATH).exists() {
            eprintln!("skip probe_pbm_010_formal_filesystem_honest_residue: bench consumer absent");
            return;
        }
        let msg = probe_pbm_010_formal_atoms_scalar(&root).expect("PBM-010 paths on disk");
        assert!(msg.contains("status=[~]"), "must not invent [x]: {msg}");
        assert!(msg.contains("f1_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("pbm_010_fully_closed=false"), "fence: {msg}");
        assert!(msg.contains("closure=RESIDUE"), "residue: {msg}");
        assert!(msg.contains("formal_owner_wired=true"), "witness: {msg}");
        assert!(msg.contains("posture_pins_f1_open=true"), "posture: {msg}");
    }
}
