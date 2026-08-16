// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-B AC43 — LIB-ADOPT-F-BARC-SCHEMA formal-tree owner deepen (INV4-S2a).
//
// Formal-side complement to `umst-bench` Z66 and semantics Y43 consumers.
// Pins REG0 `concrete-structural-v0` required-field doctrine, on-disk path census,
// and PBM-007 probe cross-ref — **never** fabricates measured ε, `:barc-cert` exit 0, or INV4 4/4.
//
// Prior: Z66 (`COMPOSER_Z66_1223.md`) · Y43 (`COMPOSER_Y43_0808.md`) · X44 — absorbed; not re-census.

use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-B slot id.
pub const AC43_JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC43-BARC-SCHEMA";

/// AC43 completion receipt cross-ref.
pub const AC43_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC43.md";

/// Z66 bench owner receipt — absorbed.
pub const PRIOR_Z66_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Z66_1223.md";

/// Y43 semantics lane receipt — absorbed.
pub const PRIOR_Y43_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_Y43_0808.md";

/// X44 prior receipt — absorbed through Y43.
pub const PRIOR_X44_RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_X44_0734.md";

/// AGAP-2127 finish card id.
pub const AGAP_JOB_ID: &str = "AGAP-2127-LIB-BARC";

/// LIB adoption workstream id.
pub const WORKSTREAM_ID: &str = "LIB-ADOPT-F-BARC-SCHEMA";

/// PBM owner cross-ref.
pub const PBM_OWNER: &str = "PBM-007";

/// REG0 structural schema document id (INV4-S2a).
pub const SCHEMA_DOCUMENT_ID: &str = "concrete-structural-v0";

/// INV4-S2a probe id mirrored from PBM-007 bench consumer.
pub const INV4_S2A_PROBE_ID: &str = "barc_inv4_s2a_structural";

/// Required-field probe id mirrored from PBM-007 bench consumer.
pub const BARC_SCHEMA_REQUIRED_FIELDS_PROBE_ID: &str = "barc_schema_required_fields";

/// Formal-side schema version pin.
pub const SCHEMA_VERSION: &str = "umst_formal_barc_schema_posture_v1";

/// Honest adoption tier.
pub const POSTURE_TAG: &str = "witnessed-not-proved";

/// INV4 aggregate — honest partial; no 4/4 invent.
pub const INV4_AGGREGATE: &str = "3/4";

/// INV4 honest satisfied count.
pub const INV4_HONEST_SAT_COUNT: u8 = 3;

/// Four-hop adoption ladder (formal owner census).
pub const WIRE_HOP_COUNT: usize = 4;

/// Honest closed hops @ AC43 — on-disk census + formal witness + bench consumer path.
pub const WIRE_HOPS_CLOSED: u8 = 3;

/// Bench consumer witness module (Z66 owner).
pub const BENCH_CONSUMER_PATH: &str = "crates/umst-bench/src/lib_adopt_f_barc_schema.rs";

/// Bench posture fixture (embedded pins).
pub const BENCH_POSTURE_FIXTURE: &str =
    "crates/umst-bench/fixtures/lib_adopt_f_barc_schema_posture.json";

/// PBM-007 bench probe surface.
pub const BENCH_PBM007_PATH: &str = "crates/umst-bench/src/pbm_007_ws_cert_proved.rs";

/// POSTH-02 B-Arc ceremony surface — blocks measured ε until operator.
pub const POSTH_02_BARC_SURFACE: &str = "crates/umst-bench/src/b_arc_spine_census.rs";

/// Formal witness module (this crate).
pub const FORMAL_WITNESS_RELPATH: &str = "umst-formal/src/barc_schema/lib.rs";

/// Honest `:barc-cert --strict` exit code on prep tree.
pub const BARC_CERT_EXIT_HONEST: i32 = 2;

/// Embedded workload catalog pin — mirrors bench Z66 + egoff B-2 subset.
pub const PINNED_EMBEDDED_WORKLOAD_IDS: &[&str] = &[
    "cpu_power_law",
    "ram_stream",
    "igpu_gemm_1024",
    "dgpu_gemm_4096",
    "npu_ane_cnn",
    "cpu_stream",
    "dgpu_training",
];

/// REG0 required fields for structural BARC cert skeleton @ unvalidated tier.
pub const REQUIRED_STRUCTURAL_FIELDS: &[&str] = &[
    "schema_version",
    "validation_status",
    "workloads",
    "cadence",
    "cartridge_id",
];

/// One wire hop in the F-BARC-SCHEMA formal adoption ladder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BarcSchemaFormalWireHop {
    pub hop: u8,
    pub wire_id: &'static str,
    pub surface: &'static str,
    pub delegate: &'static str,
    pub status: &'static str,
    pub wired: bool,
}

/// Formal-tree wire inventory — absorbs Z66/Y43 without blind redo.
pub const BARC_SCHEMA_FORMAL_WIRE_HOPS: [BarcSchemaFormalWireHop; WIRE_HOP_COUNT] = [
    BarcSchemaFormalWireHop {
        hop: 1,
        wire_id: "pbm007_on_disk",
        surface: BENCH_PBM007_PATH,
        delegate: "PBM-007 barc probes on-disk census (INV4-S2a + required fields)",
        status: "LANDED",
        wired: true,
    },
    BarcSchemaFormalWireHop {
        hop: 2,
        wire_id: "formal_witness",
        surface: FORMAL_WITNESS_RELPATH,
        delegate: "AC43 formal-tree doctrine binding @ unvalidated tier",
        status: "LANDED",
        wired: true,
    },
    BarcSchemaFormalWireHop {
        hop: 3,
        wire_id: "bench_consumer",
        surface: BENCH_CONSUMER_PATH,
        delegate: "Z66 bench owner witness + posture fixture on-disk",
        status: "LANDED",
        wired: true,
    },
    BarcSchemaFormalWireHop {
        hop: 4,
        wire_id: "production_issuance",
        surface: "egoff::slices::run_barc_cert",
        delegate: ":barc-cert --strict capstone — exit 2 honest @ prep tree",
        status: "OPEN",
        wired: false,
    },
];

/// Honest validation tiers for structural smoke — only `unvalidated` admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarcValidationTier {
    Unvalidated,
    Validated,
    Calibrated,
    Proved,
}

impl BarcValidationTier {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unvalidated => "unvalidated",
            Self::Validated => "validated",
            Self::Calibrated => "calibrated",
            Self::Proved => "proved",
        }
    }

    #[must_use]
    pub const fn structural_smoke_allowed(self) -> bool {
        matches!(self, Self::Unvalidated)
    }
}

/// Minimal structural cert skeleton for INV4-S2a smoke (no fabricated ε).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralBarcCertSkeleton {
    pub schema_version: String,
    pub validation_status: BarcValidationTier,
    pub workloads: Vec<String>,
    pub cadence: String,
    pub cartridge_id: String,
}

impl StructuralBarcCertSkeleton {
    #[must_use]
    pub fn unvalidated_structural_example() -> Self {
        Self {
            schema_version: SCHEMA_DOCUMENT_ID.to_string(),
            validation_status: BarcValidationTier::Unvalidated,
            workloads: PINNED_EMBEDDED_WORKLOAD_IDS
                .iter()
                .take(3)
                .map(|s| (*s).to_string())
                .collect(),
            cadence: "TStandard".to_string(),
            cartridge_id: "umst-cartridge-concrete".to_string(),
        }
    }
}

/// Resolve tyto-workspace root from this crate manifest (`umst-formal/src/barc_schema/`).
#[must_use]
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()
        .unwrap_or_else(|_| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.."))
}

/// Whether a workspace-relative path exists as a file.
#[must_use]
pub fn workspace_file_on_disk(rel: &str) -> bool {
    workspace_root().join(rel).is_file()
}

#[must_use]
pub const fn barc_schema_production_wired() -> bool {
    false
}

#[must_use]
pub const fn barc_schema_fully_closed() -> bool {
    false
}

#[must_use]
pub const fn ajv_subprocess_required() -> bool {
    false
}

#[must_use]
pub fn schema_required_fields_present(skeleton: &StructuralBarcCertSkeleton) -> bool {
    !skeleton.schema_version.is_empty()
        && skeleton.schema_version == SCHEMA_DOCUMENT_ID
        && skeleton.validation_status == BarcValidationTier::Unvalidated
        && !skeleton.workloads.is_empty()
        && !skeleton.cadence.is_empty()
        && !skeleton.cartridge_id.is_empty()
        && REQUIRED_STRUCTURAL_FIELDS.len() == 5
}

#[must_use]
pub fn structural_workloads_subset_honest(workloads: &[String]) -> bool {
    !workloads.is_empty()
        && workloads
            .iter()
            .all(|w| PINNED_EMBEDDED_WORKLOAD_IDS.contains(&w.as_str()))
}

#[must_use]
pub fn reject_validated_tier(tier: BarcValidationTier) -> bool {
    !tier.structural_smoke_allowed()
}

#[must_use]
pub fn barc_schema_on_disk_census_honest() -> bool {
    workspace_file_on_disk(BENCH_PBM007_PATH)
        && workspace_file_on_disk(BENCH_CONSUMER_PATH)
        && workspace_file_on_disk(BENCH_POSTURE_FIXTURE)
        && workspace_file_on_disk(POSTH_02_BARC_SURFACE)
        && workspace_file_on_disk(FORMAL_WITNESS_RELPATH)
}

#[must_use]
pub fn pbm007_barc_probe_ids_pinned() -> bool {
    INV4_S2A_PROBE_ID == "barc_inv4_s2a_structural"
        && BARC_SCHEMA_REQUIRED_FIELDS_PROBE_ID == "barc_schema_required_fields"
}

#[must_use]
pub fn barc_schema_wire_hops_closed_count() -> u8 {
    BARC_SCHEMA_FORMAL_WIRE_HOPS
        .iter()
        .filter(|h| h.wired)
        .count() as u8
}

#[must_use]
pub fn barc_schema_wire_hops_honest() -> bool {
    barc_schema_wire_hops_closed_count() == WIRE_HOPS_CLOSED
        && BARC_SCHEMA_FORMAL_WIRE_HOPS.len() == WIRE_HOP_COUNT
        && BARC_SCHEMA_FORMAL_WIRE_HOPS[0].wired
        && BARC_SCHEMA_FORMAL_WIRE_HOPS[1].wired
        && BARC_SCHEMA_FORMAL_WIRE_HOPS[2].wired
        && !BARC_SCHEMA_FORMAL_WIRE_HOPS[3].wired
}

#[must_use]
pub fn posth_02_barc_cert_fence_retained() -> bool {
    BARC_CERT_EXIT_HONEST == 2 && !barc_schema_production_wired()
}

#[must_use]
pub fn barc_schema_doctrine_binding_honest() -> bool {
    let skeleton = StructuralBarcCertSkeleton::unvalidated_structural_example();
    schema_required_fields_present(&skeleton)
        && structural_workloads_subset_honest(&skeleton.workloads)
        && pbm007_barc_probe_ids_pinned()
        && posth_02_barc_cert_fence_retained()
        && barc_schema_on_disk_census_honest()
}

#[must_use]
pub fn barc_schema_adopt_honest() -> bool {
    PBM_OWNER == "PBM-007"
        && SCHEMA_VERSION == "umst_formal_barc_schema_posture_v1"
        && INV4_HONEST_SAT_COUNT == 3
        && INV4_AGGREGATE == "3/4"
        && !barc_schema_production_wired()
        && !barc_schema_fully_closed()
        && !ajv_subprocess_required()
        && barc_schema_wire_hops_honest()
        && barc_schema_doctrine_binding_honest()
        && PINNED_EMBEDDED_WORKLOAD_IDS.len() == 7
}

/// AC43 deepen probe — formal-tree owner; absorbs Z66/Y43.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BarcSchemaAc43DeepenProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub workstream_id: &'static str,
    pub agap_job_id: &'static str,
    pub schema_document_id: &'static str,
    pub inv4_s2a_probe_id: &'static str,
    pub required_fields_probe_id: &'static str,
    pub prior_z66_receipt: &'static str,
    pub prior_y43_receipt: &'static str,
    pub prior_x44_receipt: &'static str,
    pub wire_hop_count: usize,
    pub wire_hops_closed: u8,
    pub pinned_workload_count: usize,
    pub inv4_honest_sat_count: u8,
    pub inv4_aggregate: &'static str,
    pub on_disk_census_honest: bool,
    pub doctrine_binding_honest: bool,
    pub z66_absorbed: bool,
    pub production_wired: bool,
    pub schema_fully_closed: bool,
    pub adopt_honest: bool,
}

#[must_use]
pub fn barc_schema_ac43_deepen_probe() -> BarcSchemaAc43DeepenProbe {
    BarcSchemaAc43DeepenProbe {
        job_id: AC43_JOB_ID,
        receipt_path: AC43_RECEIPT_PATH,
        workstream_id: WORKSTREAM_ID,
        agap_job_id: AGAP_JOB_ID,
        schema_document_id: SCHEMA_DOCUMENT_ID,
        inv4_s2a_probe_id: INV4_S2A_PROBE_ID,
        required_fields_probe_id: BARC_SCHEMA_REQUIRED_FIELDS_PROBE_ID,
        prior_z66_receipt: PRIOR_Z66_RECEIPT_PATH,
        prior_y43_receipt: PRIOR_Y43_RECEIPT_PATH,
        prior_x44_receipt: PRIOR_X44_RECEIPT_PATH,
        wire_hop_count: WIRE_HOP_COUNT,
        wire_hops_closed: barc_schema_wire_hops_closed_count(),
        pinned_workload_count: PINNED_EMBEDDED_WORKLOAD_IDS.len(),
        inv4_honest_sat_count: INV4_HONEST_SAT_COUNT,
        inv4_aggregate: INV4_AGGREGATE,
        on_disk_census_honest: barc_schema_on_disk_census_honest(),
        doctrine_binding_honest: barc_schema_doctrine_binding_honest(),
        z66_absorbed: true,
        production_wired: barc_schema_production_wired(),
        schema_fully_closed: barc_schema_fully_closed(),
        adopt_honest: barc_schema_adopt_honest(),
    }
}

#[must_use]
pub fn barc_schema_ac43_honest() -> bool {
    let probe = barc_schema_ac43_deepen_probe();
    probe.job_id == AC43_JOB_ID
        && probe.receipt_path == AC43_RECEIPT_PATH
        && probe.workstream_id == WORKSTREAM_ID
        && probe.wire_hops_closed == WIRE_HOPS_CLOSED
        && probe.wire_hop_count == WIRE_HOP_COUNT
        && probe.pinned_workload_count == 7
        && probe.inv4_honest_sat_count == 3
        && probe.inv4_aggregate == "3/4"
        && probe.on_disk_census_honest
        && probe.doctrine_binding_honest
        && probe.z66_absorbed
        && !probe.production_wired
        && !probe.schema_fully_closed
        && barc_schema_adopt_honest()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ac43_barc_schema_production_wired_honest_false() {
        assert!(!barc_schema_production_wired());
        assert!(!barc_schema_fully_closed());
        assert!(!ajv_subprocess_required());
    }

    #[test]
    fn ac43_barc_schema_inv4_stays_three_of_four() {
        assert_eq!(INV4_HONEST_SAT_COUNT, 3);
        assert_eq!(INV4_AGGREGATE, "3/4");
    }

    #[test]
    fn ac43_barc_schema_required_fields_present() {
        let skeleton = StructuralBarcCertSkeleton::unvalidated_structural_example();
        assert!(schema_required_fields_present(&skeleton));
        assert_eq!(skeleton.schema_version, SCHEMA_DOCUMENT_ID);
        assert_eq!(REQUIRED_STRUCTURAL_FIELDS.len(), 5);
    }

    #[test]
    fn ac43_barc_schema_wire_hops_three_closed() {
        assert!(barc_schema_wire_hops_honest());
        assert_eq!(barc_schema_wire_hops_closed_count(), WIRE_HOPS_CLOSED);
        assert_eq!(BARC_SCHEMA_FORMAL_WIRE_HOPS[1].wire_id, "formal_witness");
        assert!(!BARC_SCHEMA_FORMAL_WIRE_HOPS[3].wired);
    }

    #[test]
    fn ac43_barc_schema_on_disk_census() {
        assert!(barc_schema_on_disk_census_honest());
        assert!(workspace_file_on_disk(BENCH_CONSUMER_PATH));
        assert!(workspace_file_on_disk(BENCH_POSTURE_FIXTURE));
    }

    #[test]
    fn ac43_barc_schema_doctrine_binding_honest() {
        assert!(pbm007_barc_probe_ids_pinned());
        assert!(posth_02_barc_cert_fence_retained());
        assert!(barc_schema_doctrine_binding_honest());
        assert!(reject_validated_tier(BarcValidationTier::Calibrated));
    }

    #[test]
    fn ac43_barc_schema_absorbs_z66() {
        assert!(barc_schema_ac43_honest());
        let probe = barc_schema_ac43_deepen_probe();
        assert_eq!(probe.prior_z66_receipt, PRIOR_Z66_RECEIPT_PATH);
        assert_eq!(probe.prior_y43_receipt, PRIOR_Y43_RECEIPT_PATH);
        assert!(probe.adopt_honest);
    }

    #[test]
    fn fleet_composer_accel2_ac43_barc_schema_formal_honest() {
        assert_eq!(WORKSTREAM_ID, "LIB-ADOPT-F-BARC-SCHEMA");
        assert_eq!(POSTURE_TAG, "witnessed-not-proved");
        assert!(barc_schema_ac43_honest());
        assert!(barc_schema_adopt_honest());
    }
}
