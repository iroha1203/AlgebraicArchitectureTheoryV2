use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};

fn temp_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("archsig-authoring-{name}-{nanos}"));
    fs::create_dir_all(&path).expect("temporary directory can be created");
    path
}

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig command runs")
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json artifact can be read"))
        .expect("json artifact parses")
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/ag_measurement")
}

#[test]
fn scope_manifest_cli_is_deterministic_for_selected_sources() {
    let repo = temp_dir("scope-manifest-deterministic");
    fs::create_dir_all(repo.join("src")).expect("src directory exists");
    fs::write(repo.join("src/a.rs"), "pub fn a() {}\n").expect("a source writes");
    fs::write(repo.join("src/b.rs"), "pub fn b() {}\n").expect("b source writes");

    let first = repo.join("scope-first.json");
    let second = repo.join("scope-second.json");
    let base = [
        "scope-manifest",
        "--repo-root",
        repo.to_str().expect("repo path is utf-8"),
        "--include",
        "src/**/*.rs",
        "--id",
        "scope:test",
        "--revision-override",
        "git:test",
        "--dirty-override",
        "false",
    ];
    let mut first_args = base.to_vec();
    first_args.extend(["--out", first.to_str().expect("first path is utf-8")]);
    let mut second_args = base.to_vec();
    second_args.extend(["--out", second.to_str().expect("second path is utf-8")]);

    assert!(run(&first_args).status.success());
    assert!(run(&second_args).status.success());
    assert_eq!(
        fs::read(&first).expect("first manifest reads"),
        fs::read(&second).expect("second manifest reads")
    );
    assert_eq!(read_json(&first)["schema"], "archmap-scope-manifest/v0.5.4");
}

#[test]
fn scope_manifest_cli_rejects_evidence_outside_repository() {
    let repo = temp_dir("scope-manifest-outside-repo");
    fs::create_dir_all(repo.join("src")).expect("src directory exists");
    fs::write(repo.join("src/a.rs"), "pub fn a() {}\n").expect("source writes");
    let outside = temp_dir("scope-manifest-outside-file").join("trace.json");
    fs::write(&outside, "{}\n").expect("outside evidence writes");

    let output = run(&[
        "scope-manifest",
        "--repo-root",
        repo.to_str().expect("repo path is utf-8"),
        "--include",
        "src/**/*.rs",
        "--add-evidence",
        &format!("trace:outside={}", outside.display()),
        "--revision-override",
        "git:test",
        "--dirty-override",
        "false",
    ]);
    assert!(!output.status.success());
}

#[test]
fn archmap_cli_rejects_diagnostic_shortcut_atom_id() {
    let out_dir = temp_dir("archmap-diagnostic-shortcut");
    let mut archmap = read_json(&fixture_root().join("archmap_v2.json"));
    archmap["atoms"][0]["id"] = json!("atom:service-violation");
    for context in archmap["contexts"]
        .as_array_mut()
        .expect("contexts are array")
    {
        for atom in context["atoms"]
            .as_array_mut()
            .expect("context atoms are array")
        {
            if atom == "atom:order" {
                *atom = json!("atom:service-violation");
            }
        }
    }
    let input = out_dir.join("archmap.json");
    let report = out_dir.join("validation.json");
    fs::write(
        &input,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap writes");

    let output = run(&[
        "archmap",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(1));
    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert_eq!(
        report["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .find(|check| check["id"] == "archmap-schema052-no-diagnostic-shortcuts")
            .expect("diagnostic shortcut check exists")["result"],
        "fail"
    );
}

#[test]
fn archmap_cli_rejects_noncanonical_extraction_doctrine() {
    let out_dir = temp_dir("archmap-custom-doctrine");
    let mut archmap = read_json(&fixture_root().join("archmap_v2.json"));
    archmap["extractionDoctrineRef"] = json!({
        "doctrineId": "doctrine:custom@1",
        "fingerprint": "sha256:custom",
        "components": ["custom"]
    });
    let input = out_dir.join("archmap.json");
    let report = out_dir.join("validation.json");
    fs::write(
        &input,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap writes");

    let output = run(&[
        "archmap",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(1));
    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert_eq!(
        report["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .find(|check| check["id"] == "archmap-schema052-extraction-doctrine-ref")
            .expect("extraction doctrine check exists")["result"],
        "fail"
    );
}

#[test]
fn archmap_cli_runs_minimal_authoring_audit() {
    let out_dir = temp_dir("archmap-authoring-audit");
    let archmap = json!({
        "schema": "archmap/v0.5.4",
        "id": "archmap:authoring-audit",
        "sources": {
            "src:src/a.rs": { "kind": "file", "path": "src/a.rs" }
        },
        "atoms": [{
            "id": "atom:common",
            "kind": "semantic",
            "subject": "module:a",
            "axis": "responsibility",
            "predicate": "documents",
            "object": "authoring survey provenance",
            "refs": ["src:src/a.rs"]
        }],
        "contexts": [],
        "covers": []
    });
    let scope = json!({
        "schema": "archmap-scope-manifest/v0.5.4",
        "id": "scope:test",
        "repository": {
            "root": ".",
            "revision": "git:0000000000000000000000000000000000000000",
            "dirty": false
        },
        "scopeSpec": {
            "includeGlobs": ["src/**/*.rs"],
            "excludeGlobs": [],
            "addedEvidence": [],
            "requestedScope": "authoring audit test",
            "approvedBy": "test"
        },
        "worklist": [{
            "order": 1,
            "sourceId": "src:src/a.rs",
            "path": "src/a.rs",
            "kind": "file",
            "contentHash": "sha256:0000000000000000000000000000000000000000000000000000000000000000",
            "sizeBytes": 11,
            "authorAdded": false
        }],
        "exclusions": []
    });
    let candidate = json!({
        "schema": "archmap-candidate-packet/v0.5.4",
        "id": "candidates:pass-a",
        "scopeManifestRef": "scope:test",
        "passId": "pass-a",
        "chunk": { "worklistOrderFrom": 1, "worklistOrderTo": 1 },
        "reviewedSources": ["src:src/a.rs"],
        "candidateSources": {
            "src:src/a.rs": { "kind": "file", "path": "src/a.rs" }
        },
        "candidateAtoms": [archmap["atoms"][0].clone()],
        "candidateContexts": [{
            "id": "ctx:pass-a:common",
            "atoms": ["atom:common"],
            "restrictsTo": [],
            "refs": ["src:src/a.rs"]
        }],
        "candidateCovers": [],
        "surveyRows": [{
            "sourceId": "src:src/a.rs",
            "status": "read",
            "surveyedKinds": ["semantic"],
            "candidateAtomIds": ["atom:common"],
            "notes": []
        }],
        "privateUnavailableNotes": [],
        "selfReview": {
            "notScriptGenerated": true,
            "notCoarseWhenEvidenceWasRicher": true,
            "semanticAtomsHaveUseEvidence": true,
            "noDiagnosticShortcutAtoms": true,
            "worklistChunkFullyRead": true,
            "aliasPreservingSemantics": true
        }
    });
    let ledger = json!({
        "schema": "archmap-coverage-ledger/v0.5.4",
        "id": "coverage:test",
        "scopeManifestRef": "scope:test",
        "archmapRef": "archmap:authoring-audit",
        "passRefs": ["candidates:pass-a"],
        "rows": [{
            "sourceId": "src:src/a.rs",
            "surveyStatus": "surveyed",
            "passes": ["pass-a"],
            "surveyedKinds": ["semantic"],
            "adoptedAtomIds": ["atom:common"]
        }],
        "claimBoundary": "Rows record the authoring survey of the selected scope at the recorded revision. They do not assert extraction completeness."
    });
    let paths = [
        ("archmap.json", archmap),
        ("scope.json", scope),
        ("candidate.json", candidate),
        ("ledger.json", ledger),
    ];
    for (name, value) in paths {
        fs::write(
            out_dir.join(name),
            serde_json::to_vec_pretty(&value).expect("authoring artifact serializes"),
        )
        .expect("authoring artifact writes");
    }
    let report = out_dir.join("validation.json");
    let output = run(&[
        "archmap",
        "--input",
        out_dir
            .join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--scope-manifest",
        out_dir
            .join("scope.json")
            .to_str()
            .expect("scope path is utf-8"),
        "--candidate-packets",
        out_dir
            .join("candidate.json")
            .to_str()
            .expect("candidate path is utf-8"),
        "--coverage-ledger",
        out_dir
            .join("ledger.json")
            .to_str()
            .expect("ledger path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(output.status.success());
    assert_eq!(read_json(&report)["summary"]["result"], "pass");
}

#[test]
fn archmap_cli_accepts_line_suffixed_source_refs_in_authoring_audit() {
    let out_dir = temp_dir("archmap-authoring-audit-line-refs");
    let atom = json!({
        "id": "atom:common",
        "kind": "semantic",
        "subject": "module:a",
        "axis": "responsibility",
        "predicate": "documents",
        "object": "authoring survey provenance",
        "refs": ["src:src/a.rs:42"]
    });
    let archmap = json!({
        "schema": "archmap/v0.5.4",
        "id": "archmap:authoring-audit-line",
        "sources": {
            "src:src/a.rs": { "kind": "file", "path": "src/a.rs" }
        },
        "atoms": [atom],
        "contexts": [],
        "covers": []
    });
    let scope = json!({
        "schema": "archmap-scope-manifest/v0.5.4",
        "id": "scope:test",
        "repository": {
            "root": ".",
            "revision": "git:0000000000000000000000000000000000000000",
            "dirty": false
        },
        "scopeSpec": {
            "includeGlobs": ["src/**/*.rs"],
            "excludeGlobs": [],
            "addedEvidence": [],
            "requestedScope": "authoring audit line-ref test",
            "approvedBy": "test"
        },
        "worklist": [{
            "order": 1,
            "sourceId": "src:src/a.rs",
            "path": "src/a.rs",
            "kind": "file",
            "contentHash": "sha256:0000000000000000000000000000000000000000000000000000000000000000",
            "sizeBytes": 11,
            "authorAdded": false
        }],
        "exclusions": []
    });
    let candidate = json!({
        "schema": "archmap-candidate-packet/v0.5.4",
        "id": "candidates:pass-a",
        "scopeManifestRef": "scope:test",
        "passId": "pass-a",
        "chunk": { "worklistOrderFrom": 1, "worklistOrderTo": 1 },
        "reviewedSources": ["src:src/a.rs"],
        "candidateSources": {
            "src:src/a.rs": { "kind": "file", "path": "src/a.rs" }
        },
        "candidateAtoms": [archmap["atoms"][0].clone()],
        "candidateContexts": [],
        "candidateCovers": [],
        "surveyRows": [{
            "sourceId": "src:src/a.rs",
            "status": "read",
            "surveyedKinds": ["semantic"],
            "candidateAtomIds": ["atom:common"],
            "notes": []
        }],
        "privateUnavailableNotes": [],
        "selfReview": {
            "notScriptGenerated": true,
            "notCoarseWhenEvidenceWasRicher": true,
            "semanticAtomsHaveUseEvidence": true,
            "noDiagnosticShortcutAtoms": true,
            "worklistChunkFullyRead": true,
            "aliasPreservingSemantics": true
        }
    });
    let ledger = json!({
        "schema": "archmap-coverage-ledger/v0.5.4",
        "id": "coverage:test",
        "scopeManifestRef": "scope:test",
        "archmapRef": "archmap:authoring-audit-line",
        "passRefs": ["candidates:pass-a"],
        "rows": [{
            "sourceId": "src:src/a.rs",
            "surveyStatus": "surveyed",
            "passes": ["pass-a"],
            "surveyedKinds": ["semantic"],
            "adoptedAtomIds": ["atom:common"]
        }],
        "claimBoundary": "Rows record the authoring survey of the selected scope at the recorded revision. They do not assert extraction completeness."
    });
    let paths = [
        ("archmap.json", archmap.clone()),
        ("scope.json", scope),
        ("candidate.json", candidate),
        ("ledger.json", ledger),
    ];
    for (name, value) in paths {
        fs::write(
            out_dir.join(name),
            serde_json::to_vec_pretty(&value).expect("authoring artifact serializes"),
        )
        .expect("authoring artifact writes");
    }
    let report = out_dir.join("validation.json");
    let output = run(&[
        "archmap",
        "--input",
        out_dir
            .join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--scope-manifest",
        out_dir
            .join("scope.json")
            .to_str()
            .expect("scope path is utf-8"),
        "--candidate-packets",
        out_dir
            .join("candidate.json")
            .to_str()
            .expect("candidate path is utf-8"),
        "--coverage-ledger",
        out_dir
            .join("ledger.json")
            .to_str()
            .expect("ledger path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(output.status.success());
    assert_eq!(read_json(&report)["summary"]["result"], "pass");

    // A line suffix must not resurrect a source that was never declared.
    let mut unknown = archmap;
    unknown["atoms"][0]["refs"] = json!(["src:src/missing.rs:7"]);
    fs::write(
        out_dir.join("archmap-unknown.json"),
        serde_json::to_vec_pretty(&unknown).expect("unknown archmap serializes"),
    )
    .expect("unknown archmap writes");
    let unknown_report = out_dir.join("validation-unknown.json");
    let unknown_output = run(&[
        "archmap",
        "--input",
        out_dir
            .join("archmap-unknown.json")
            .to_str()
            .expect("unknown archmap path is utf-8"),
        "--out",
        unknown_report.to_str().expect("report path is utf-8"),
    ]);
    assert!(!unknown_output.status.success() || {
        read_json(&unknown_report)["summary"]["result"] != "pass"
    });
    assert_eq!(read_json(&unknown_report)["summary"]["result"], "fail");
}
