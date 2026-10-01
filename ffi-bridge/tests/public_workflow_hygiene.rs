// SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
// SPDX-License-Identifier: MIT
//
// public_workflow_hygiene: path-triggered GitHub workflow guards for public CI posture.

use std::fs;
use std::path::PathBuf;

fn formal_repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("ffi-bridge parent is umst-formal root")
        .to_path_buf()
}

#[test]
fn path_triggered_workflows_run_tracked_artefact_guard() {
    let root = formal_repo_root();
    for wf in [
        ".github/workflows/ci.yml",
        ".github/workflows/formal.yml",
        ".github/workflows/lean.yml",
        ".github/workflows/extract-haskell-from-lean.yml",
    ] {
        let body = fs::read_to_string(root.join(wf)).unwrap_or_else(|e| {
            panic!("read {wf}: {e}");
        });
        assert!(
            body.contains("check_tracked_build_artefacts.sh"),
            "{wf} must call scripts/check_tracked_build_artefacts.sh (W-68)"
        );
    }
}

#[test]
fn extract_haskell_workflow_declares_job_timeout() {
    let body = fs::read_to_string(
        formal_repo_root().join(".github/workflows/extract-haskell-from-lean.yml"),
    )
    .expect("extract-haskell workflow");
    assert!(
        body.contains("timeout-minutes:"),
        "Extract Haskell from Lean job needs timeout-minutes so hung lake builds fail closed"
    );
}
