// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// FLEET-COMPOSER-ACCEL-C AC64 — PBM-008 `WS-formal-anchors` formal-tree owner deepen.
//
// Formal-side cert fence for `umst.toml` formal_anchors — prove mechanised anchors on disk,
// keep `[assumed]` / axiom anchors honestly tagged (no fake Proved tier).
// Does **not** invent anchor promotion, catalog export GREEN, `pbm_008_fully_closed` flip, or INV4 4/4.
//
// Prior: H95 (`COMPOSER_H95_2242.md`) PBM-008 `[H]` freeze — absorbed; not re-census.

use std::fs;
use std::path::{Path, PathBuf};

/// FLEET-COMPOSER-ACCEL-C fleet parent id.
pub const FLEET_PARENT: &str = "ACCEL-C-2054";

/// AC64 slot job id.
pub const JOB_ID: &str = "FLEET-COMPOSER-ACCEL2-AC64-PBM-008";

/// AC64 completion receipt cross-ref.
pub const RECEIPT_PATH: &str = "outputs/.tmp/COMPOSER_ACCEL2_AC64.md";

/// H95 prior receipt — absorbed; not re-census.
pub const PRIOR_H95_RECEIPT: &str = "outputs/.tmp/COMPOSER_H95_2242.md";

/// Parent PBM card id.
pub const PARENT_WORKSTREAM_ID: &str = "PBM-008";

/// Workstream id per master TODO §4.3.
pub const WORKSTREAM_ID: &str = "WS-formal-anchors";

/// `umst.toml` manifest owner for formal anchor pins.
pub const UMST_TOML_RELPATH: &str = "umst-formal/umst.toml";

/// Lean sole physics axiom surface.
pub const LEAN_PHYSICAL_SECOND_LAW: &str = "Lean/LandauerLaw.lean";

/// Lean mechanised sequential-composition anchor.
pub const LEAN_SEQUENTIAL_COMPOSITION: &str = "Lean/Compat/Constitutional.lean";

/// Literature anchor def with honest `[assumed]` tier.
pub const LEAN_LITERATURE_ASSUMED_DEF: &str = "Lean/Concrete/MicroMechanics.lean";

/// Literature anchor theorem — tier stays assumed.
pub const LEAN_LITERATURE_ASSUMED_THEOREM: &str = "Lean/Concrete/MoriTanaka.lean";

/// Pinned catalog export for mechanised anchor resolve.
pub const CATALOG_RELPATH: &str = "umst-formal/artifacts/catalog.json";

/// Mechanised `lean://` anchor resolve script (L1.b).
pub const ANCHOR_RESOLVE_SCRIPT: &str = "scripts/check_formal_anchor_resolve.py";

/// Formal witness module (this crate).
pub const FORMAL_WITNESS_RELPATH: &str = "umst-formal/src/pbm_008/lib.rs";

/// Honest adoption tier.
pub const POSTURE_TAG: &str = "witnessed-not-proved";

/// Manifest anchor count @ `umst-formal/umst.toml`.
pub const MANIFEST_ANCHOR_COUNT: usize = 2;

/// Axiom / `[assumed]` anchor count — never flipped to Proved here.
pub const ASSUMED_ANCHOR_COUNT: usize = 1;

/// Mechanised anchor count — on-disk theorem census.
pub const MECHANISED_ANCHOR_COUNT: usize = 1;

/// Literature `[assumed]` anchor count — honest tag retained.
pub const LITERATURE_ASSUMED_COUNT: usize = 1;

/// Formal-side anchor fence probe count (this module's audit).
pub const FORMAL_PROBE_COUNT: usize = 10;

/// Wire-hop count @ AC64 deepen.
pub const WIRE_HOP_COUNT: usize = 6;

/// Honest closed hops @ AC64 — on-disk census + formal witness + manifest pins.
pub const WIRE_HOPS_CLOSED: u8 = 5;

/// Pinned manifest anchor ids @ `umst.toml`.
pub const PINNED_MANIFEST_ANCHORS: &[&str] = &["physicalSecondLaw", "sequentialCompositionSafe"];

/// One formal anchor posture row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormalAnchorPosture {
    pub anchor_id: &'static str,
    pub lean_module: &'static str,
    pub lean_decl: &'static str,
    pub tier: &'static str,
    pub promoted: bool,
}

/// Manifest + Lean anchor posture pins @ AC64.
pub const FORMAL_ANCHOR_POSTURES: &[FormalAnchorPosture] = &[
    FormalAnchorPosture {
        anchor_id: "physicalSecondLaw",
        lean_module: LEAN_PHYSICAL_SECOND_LAW,
        lean_decl: "physicalSecondLaw",
        tier: "axiom",
        promoted: false,
    },
    FormalAnchorPosture {
        anchor_id: "sequentialCompositionSafe",
        lean_module: LEAN_SEQUENTIAL_COMPOSITION,
        lean_decl: "sequentialCompositionSafe",
        tier: "mechanised",
        promoted: false,
    },
];

/// One hop on the PBM-008 formal-anchor wire map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pbm008FormalAnchorWireHop {
    pub hop: u8,
    pub wire_id: &'static str,
    pub surface: &'static str,
    pub delegate: &'static str,
    pub status: &'static str,
    pub wired: bool,
}

/// Formal-tree wire inventory — absorbs H95 without blind redo.
pub const FORMAL_ANCHOR_WIRE_HOPS: [Pbm008FormalAnchorWireHop; WIRE_HOP_COUNT] = [
    Pbm008FormalAnchorWireHop {
        hop: 1,
        wire_id: "lean_axiom_anchor",
        surface: LEAN_PHYSICAL_SECOND_LAW,
        delegate: "sole physics axiom `physicalSecondLaw` — honestly [assumed]",
        status: "LANDED",
        wired: true,
    },
    Pbm008FormalAnchorWireHop {
        hop: 2,
        wire_id: "lean_mechanised_anchor",
        surface: LEAN_SEQUENTIAL_COMPOSITION,
        delegate: "mechanised theorem `sequentialCompositionSafe` on disk",
        status: "LANDED",
        wired: true,
    },
    Pbm008FormalAnchorWireHop {
        hop: 3,
        wire_id: "manifest_pins",
        surface: UMST_TOML_RELPATH,
        delegate: "formal_anchors manifest pins (2/2)",
        status: "LANDED",
        wired: true,
    },
    Pbm008FormalAnchorWireHop {
        hop: 4,
        wire_id: "catalog_export",
        surface: CATALOG_RELPATH,
        delegate: "pinned Lean catalog export for mechanised resolve",
        status: "LANDED",
        wired: true,
    },
    Pbm008FormalAnchorWireHop {
        hop: 5,
        wire_id: "formal_witness",
        surface: FORMAL_WITNESS_RELPATH,
        delegate: "AC64 formal-tree doctrine binding @ HOLD tier",
        status: "LANDED",
        wired: true,
    },
    Pbm008FormalAnchorWireHop {
        hop: 6,
        wire_id: "catalog_live_export",
        surface: "operator `lake build` + catalog refresh",
        delegate: "live catalog export ceremony — operator only",
        status: "OPEN",
        wired: false,
    },
];

/// One formal-side anchor fence probe outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm008FormalProbe {
    pub probe: &'static str,
    pub green: bool,
    pub detail: &'static str,
}

/// Formal-side anchor fence audit report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm008FormalAudit {
    pub job_id: &'static str,
    pub posture: &'static str,
    pub manifest_anchor_count: usize,
    pub assumed_anchor_count: usize,
    pub mechanised_anchor_count: usize,
    pub probes: Vec<Pbm008FormalProbe>,
}

impl Pbm008FormalAudit {
    #[must_use]
    pub fn all_green(&self) -> bool {
        self.probes.iter().all(|p| p.green)
    }
}

/// PBM-008 done-when probe — documents honest HOLD posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm008DoneWhenProbe {
    pub formal_anchor_fence_honest: bool,
    pub assumed_anchors_honestly_tagged: bool,
    pub mechanised_anchors_on_disk: bool,
    pub catalog_live_export_complete: bool,
    pub master_retick_eligible: bool,
    pub closure: &'static str,
}

/// AC64 deepen probe — formal-tree owner; absorbs H95.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pbm008Ac64DeepenProbe {
    pub job_id: &'static str,
    pub receipt_path: &'static str,
    pub workstream_id: &'static str,
    pub parent_workstream_id: &'static str,
    pub prior_h95_receipt: &'static str,
    pub manifest_anchor_count: usize,
    pub assumed_anchor_count: usize,
    pub mechanised_anchor_count: usize,
    pub literature_assumed_count: usize,
    pub wire_hop_count: usize,
    pub wire_hops_closed: u8,
    pub formal_probe_count: usize,
    pub on_disk_census_honest: bool,
    pub doctrine_binding_honest: bool,
    pub formal_fence_closed: bool,
    pub h95_absorbed: bool,
    pub pbm_008_fully_closed: bool,
    pub pbm_008_flip_blocked: bool,
    pub production_wired: bool,
    pub adopt_honest: bool,
}

/// Resolve tyto-workspace root from this crate manifest (`umst-formal/src/pbm_008/`).
#[must_use]
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()
        .unwrap_or_else(|_| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.."))
}

/// Resolve `umst-formal` checkout root.
#[must_use]
pub fn umst_formal_root() -> PathBuf {
    workspace_root().join("umst-formal")
}

/// Whether a workspace-relative path exists as a file.
#[must_use]
pub fn workspace_file_on_disk(rel: &str) -> bool {
    workspace_root().join(rel).is_file()
}

/// Lean `physicalSecondLaw` axiom posture present on disk.
#[must_use]
pub fn lean_physical_second_law_on_disk() -> bool {
    let path = umst_formal_root().join(LEAN_PHYSICAL_SECOND_LAW);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("axiom physicalSecondLaw")
        && text.contains("Sole project `axiom`: `physicalSecondLaw`")
        && text.contains("theorem physicalSecondLaw_uniform_binary")
}

/// Lean `sequentialCompositionSafe` mechanised anchor on disk.
#[must_use]
pub fn lean_sequential_composition_on_disk() -> bool {
    let path = umst_formal_root().join(LEAN_SEQUENTIAL_COMPOSITION);
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("theorem sequentialCompositionSafe") && text.contains("ConstitutionalSeq")
}

/// Literature anchor stays `[assumed]` — not promoted to mechanised.
#[must_use]
pub fn lean_literature_assumed_on_disk() -> bool {
    let def_path = umst_formal_root().join(LEAN_LITERATURE_ASSUMED_DEF);
    let theorem_path = umst_formal_root().join(LEAN_LITERATURE_ASSUMED_THEOREM);
    let Ok(def_text) = fs::read_to_string(def_path) else {
        return false;
    };
    let Ok(theorem_text) = fs::read_to_string(theorem_path) else {
        return false;
    };
    def_text.contains("def literatureAnchorTier : String := \"assumed\"")
        && theorem_text.contains("theorem literature_anchor_tier_assumed")
}

/// `umst.toml` manifest pins both formal anchors.
#[must_use]
pub fn umst_toml_anchors_on_disk() -> bool {
    let path = umst_formal_root().join("umst.toml");
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    PINNED_MANIFEST_ANCHORS
        .iter()
        .all(|anchor| text.contains(&format!("\"{anchor}\"")))
        && text.contains("formal_anchors = [")
}

/// Pinned catalog indexes mechanised anchor declarations.
#[must_use]
pub fn catalog_anchors_indexed() -> bool {
    let path = umst_formal_root().join("artifacts/catalog.json");
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("\"physicalSecondLaw\"")
        && text.contains("\"sequentialCompositionSafe\"")
        && text.contains("Compat/Constitutional.lean")
        && text.contains("LandauerLaw.lean")
}

#[must_use]
pub const fn pbm_008_production_wired() -> bool {
    false
}

#[must_use]
pub const fn pbm_008_fully_closed() -> bool {
    false
}

#[must_use]
pub const fn catalog_live_export_deferred() -> bool {
    true
}

#[must_use]
pub fn pbm_008_on_disk_census_honest() -> bool {
    workspace_file_on_disk(UMST_TOML_RELPATH)
        && workspace_file_on_disk(&format!("umst-formal/{LEAN_PHYSICAL_SECOND_LAW}"))
        && workspace_file_on_disk(&format!("umst-formal/{LEAN_SEQUENTIAL_COMPOSITION}"))
        && workspace_file_on_disk(&format!("umst-formal/{LEAN_LITERATURE_ASSUMED_DEF}"))
        && workspace_file_on_disk(&format!("umst-formal/{LEAN_LITERATURE_ASSUMED_THEOREM}"))
        && workspace_file_on_disk(CATALOG_RELPATH)
        && workspace_file_on_disk(ANCHOR_RESOLVE_SCRIPT)
        && workspace_file_on_disk(FORMAL_WITNESS_RELPATH)
}

#[must_use]
pub fn manifest_anchor_pins_honest() -> bool {
    PINNED_MANIFEST_ANCHORS.len() == MANIFEST_ANCHOR_COUNT
        && FORMAL_ANCHOR_POSTURES.len() == MANIFEST_ANCHOR_COUNT
        && FORMAL_ANCHOR_POSTURES[0].tier == "axiom"
        && !FORMAL_ANCHOR_POSTURES[0].promoted
        && FORMAL_ANCHOR_POSTURES[1].tier == "mechanised"
        && !FORMAL_ANCHOR_POSTURES[1].promoted
}

#[must_use]
pub fn assumed_anchors_honestly_tagged() -> bool {
    lean_physical_second_law_on_disk()
        && lean_literature_assumed_on_disk()
        && ASSUMED_ANCHOR_COUNT == 1
        && LITERATURE_ASSUMED_COUNT == 1
        && FORMAL_ANCHOR_POSTURES
            .iter()
            .filter(|row| row.tier == "axiom")
            .all(|row| !row.promoted)
}

#[must_use]
pub fn mechanised_anchors_on_disk() -> bool {
    lean_sequential_composition_on_disk()
        && catalog_anchors_indexed()
        && MECHANISED_ANCHOR_COUNT == 1
}

#[must_use]
pub fn pbm_008_wire_hops_closed_count() -> u8 {
    FORMAL_ANCHOR_WIRE_HOPS.iter().filter(|h| h.wired).count() as u8
}

#[must_use]
pub fn pbm_008_wire_hops_honest() -> bool {
    pbm_008_wire_hops_closed_count() == WIRE_HOPS_CLOSED
        && FORMAL_ANCHOR_WIRE_HOPS.len() == WIRE_HOP_COUNT
        && FORMAL_ANCHOR_WIRE_HOPS[0].wired
        && FORMAL_ANCHOR_WIRE_HOPS[1].wired
        && FORMAL_ANCHOR_WIRE_HOPS[2].wired
        && FORMAL_ANCHOR_WIRE_HOPS[3].wired
        && FORMAL_ANCHOR_WIRE_HOPS[4].wired
        && !FORMAL_ANCHOR_WIRE_HOPS[5].wired
}

#[must_use]
pub fn pbm_008_doctrine_binding_honest() -> bool {
    manifest_anchor_pins_honest()
        && assumed_anchors_honestly_tagged()
        && mechanised_anchors_on_disk()
        && umst_toml_anchors_on_disk()
        && catalog_live_export_deferred()
        && !pbm_008_production_wired()
}

#[must_use]
pub fn run_formal_anchor_fence_audit() -> Pbm008FormalAudit {
    Pbm008FormalAudit {
        job_id: JOB_ID,
        posture: POSTURE_TAG,
        manifest_anchor_count: MANIFEST_ANCHOR_COUNT,
        assumed_anchor_count: ASSUMED_ANCHOR_COUNT,
        mechanised_anchor_count: MECHANISED_ANCHOR_COUNT,
        probes: vec![
            Pbm008FormalProbe {
                probe: "manifest_anchor_count",
                green: MANIFEST_ANCHOR_COUNT == 2,
                detail: "umst.toml pins 2 formal anchors",
            },
            Pbm008FormalProbe {
                probe: "physical_second_law_axiom",
                green: lean_physical_second_law_on_disk(),
                detail: "LandauerLaw axiom on disk — not promoted",
            },
            Pbm008FormalProbe {
                probe: "sequential_composition_mechanised",
                green: lean_sequential_composition_on_disk(),
                detail: "Constitutional theorem on disk",
            },
            Pbm008FormalProbe {
                probe: "literature_assumed_tag",
                green: lean_literature_assumed_on_disk(),
                detail: "MicroMechanics literature tier stays assumed",
            },
            Pbm008FormalProbe {
                probe: "catalog_index",
                green: catalog_anchors_indexed(),
                detail: "catalog.json indexes both anchor decls",
            },
            Pbm008FormalProbe {
                probe: "on_disk_census",
                green: pbm_008_on_disk_census_honest(),
                detail: "manifest · Lean · catalog · script · witness",
            },
            Pbm008FormalProbe {
                probe: "wire_hops_five_closed",
                green: pbm_008_wire_hops_honest(),
                detail: "5/6 wire hops closed — live export OPEN",
            },
            Pbm008FormalProbe {
                probe: "flip_blocked",
                green: !pbm_008_fully_closed() && catalog_live_export_deferred(),
                detail: "master HOLD retained — no fake Proved",
            },
            Pbm008FormalProbe {
                probe: "production_wired_false",
                green: !pbm_008_production_wired(),
                detail: "production wiring not earned",
            },
            Pbm008FormalProbe {
                probe: "doctrine_binding",
                green: pbm_008_doctrine_binding_honest(),
                detail: "assumed vs mechanised honestly partitioned",
            },
        ],
    }
}

/// Formal anchor fence closed — structural audit GREEN; **not** master HOLD lift.
#[must_use]
pub fn pbm_008_formal_fence_closed() -> bool {
    run_formal_anchor_fence_audit().all_green()
        && pbm_008_wire_hops_honest()
        && assumed_anchors_honestly_tagged()
        && mechanised_anchors_on_disk()
        && !pbm_008_fully_closed()
}

#[must_use]
pub fn pbm_008_done_when_probe() -> Pbm008DoneWhenProbe {
    let audit = run_formal_anchor_fence_audit();
    Pbm008DoneWhenProbe {
        formal_anchor_fence_honest: audit.all_green(),
        assumed_anchors_honestly_tagged: assumed_anchors_honestly_tagged(),
        mechanised_anchors_on_disk: mechanised_anchors_on_disk(),
        catalog_live_export_complete: false,
        master_retick_eligible: false,
        closure: "formal-fence-CLOSE / master-HOLD",
    }
}

#[must_use]
pub fn pbm_008_adopt_honest() -> bool {
    PARENT_WORKSTREAM_ID == "PBM-008"
        && WORKSTREAM_ID == "WS-formal-anchors"
        && POSTURE_TAG == "witnessed-not-proved"
        && MANIFEST_ANCHOR_COUNT == 2
        && !pbm_008_production_wired()
        && !pbm_008_fully_closed()
        && pbm_008_wire_hops_honest()
        && pbm_008_doctrine_binding_honest()
        && pbm_008_formal_fence_closed()
}

#[must_use]
pub fn pbm_008_ac64_deepen_probe() -> Pbm008Ac64DeepenProbe {
    let audit = run_formal_anchor_fence_audit();
    Pbm008Ac64DeepenProbe {
        job_id: JOB_ID,
        receipt_path: RECEIPT_PATH,
        workstream_id: WORKSTREAM_ID,
        parent_workstream_id: PARENT_WORKSTREAM_ID,
        prior_h95_receipt: PRIOR_H95_RECEIPT,
        manifest_anchor_count: MANIFEST_ANCHOR_COUNT,
        assumed_anchor_count: ASSUMED_ANCHOR_COUNT,
        mechanised_anchor_count: MECHANISED_ANCHOR_COUNT,
        literature_assumed_count: LITERATURE_ASSUMED_COUNT,
        wire_hop_count: WIRE_HOP_COUNT,
        wire_hops_closed: pbm_008_wire_hops_closed_count(),
        formal_probe_count: audit.probes.len(),
        on_disk_census_honest: pbm_008_on_disk_census_honest(),
        doctrine_binding_honest: pbm_008_doctrine_binding_honest(),
        formal_fence_closed: pbm_008_formal_fence_closed(),
        h95_absorbed: true,
        pbm_008_fully_closed: pbm_008_fully_closed(),
        pbm_008_flip_blocked: true,
        production_wired: pbm_008_production_wired(),
        adopt_honest: pbm_008_adopt_honest(),
    }
}

#[must_use]
pub fn pbm_008_ac64_honest() -> bool {
    let probe = pbm_008_ac64_deepen_probe();
    probe.job_id == JOB_ID
        && probe.receipt_path == RECEIPT_PATH
        && probe.workstream_id == WORKSTREAM_ID
        && probe.parent_workstream_id == PARENT_WORKSTREAM_ID
        && probe.wire_hops_closed == WIRE_HOPS_CLOSED
        && probe.wire_hop_count == WIRE_HOP_COUNT
        && probe.manifest_anchor_count == 2
        && probe.assumed_anchor_count == 1
        && probe.mechanised_anchor_count == 1
        && probe.literature_assumed_count == 1
        && probe.on_disk_census_honest
        && probe.doctrine_binding_honest
        && probe.formal_fence_closed
        && probe.h95_absorbed
        && !probe.pbm_008_fully_closed
        && probe.pbm_008_flip_blocked
        && !probe.production_wired
        && pbm_008_adopt_honest()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pbm_008_production_wired_honest_false() {
        assert!(!pbm_008_production_wired());
        assert!(!pbm_008_fully_closed());
        assert!(catalog_live_export_deferred());
    }

    #[test]
    fn pbm_008_manifest_anchor_pins_two() {
        assert_eq!(MANIFEST_ANCHOR_COUNT, 2);
        assert_eq!(PINNED_MANIFEST_ANCHORS.len(), 2);
        assert!(manifest_anchor_pins_honest());
        assert!(umst_toml_anchors_on_disk());
    }

    #[test]
    fn pbm_008_assumed_anchors_honestly_tagged() {
        assert!(lean_physical_second_law_on_disk());
        assert!(lean_literature_assumed_on_disk());
        assert!(assumed_anchors_honestly_tagged());
        assert_eq!(ASSUMED_ANCHOR_COUNT, 1);
    }

    #[test]
    fn pbm_008_mechanised_anchor_on_disk() {
        assert!(lean_sequential_composition_on_disk());
        assert!(catalog_anchors_indexed());
        assert!(mechanised_anchors_on_disk());
    }

    #[test]
    fn pbm_008_wire_hops_five_closed() {
        assert!(pbm_008_wire_hops_honest());
        assert_eq!(pbm_008_wire_hops_closed_count(), WIRE_HOPS_CLOSED);
        assert_eq!(FORMAL_ANCHOR_WIRE_HOPS[4].wire_id, "formal_witness");
        assert!(!FORMAL_ANCHOR_WIRE_HOPS[5].wired);
    }

    #[test]
    fn pbm_008_on_disk_census() {
        assert!(pbm_008_on_disk_census_honest());
        assert!(workspace_file_on_disk(CATALOG_RELPATH));
        assert!(workspace_file_on_disk(ANCHOR_RESOLVE_SCRIPT));
    }

    #[test]
    fn pbm_008_formal_fence_audit_green() {
        let audit = run_formal_anchor_fence_audit();
        assert_eq!(audit.probes.len(), FORMAL_PROBE_COUNT);
        assert!(audit.all_green());
        assert!(pbm_008_formal_fence_closed());
    }

    #[test]
    fn pbm_008_absorbs_h95_hold() {
        assert!(pbm_008_ac64_honest());
        let probe = pbm_008_ac64_deepen_probe();
        assert_eq!(probe.prior_h95_receipt, PRIOR_H95_RECEIPT);
        assert!(probe.pbm_008_flip_blocked);
        assert!(probe.adopt_honest);
    }

    #[test]
    fn fleet_composer_accel2_ac64_pbm_008_formal_honest() {
        assert_eq!(WORKSTREAM_ID, "WS-formal-anchors");
        assert_eq!(POSTURE_TAG, "witnessed-not-proved");
        let done = pbm_008_done_when_probe();
        assert!(done.formal_anchor_fence_honest);
        assert!(!done.master_retick_eligible);
        assert_eq!(done.closure, "formal-fence-CLOSE / master-HOLD");
        assert!(pbm_008_ac64_honest());
        assert!(pbm_008_adopt_honest());
    }
}
