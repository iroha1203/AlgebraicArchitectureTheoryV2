use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal")
}

#[test]
fn cli_help_excludes_fieldsig_owned_commands() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    for command in [
        "intent-map",
        "intent-forecast",
        "operation-support-estimate",
        "forecast-cone-skeleton",
        "consequence-envelope",
        "sft-forecast",
        "ai-proposal-governance",
        "dataset",
        "pr-history-dataset",
        "architecture-field-snapshot",
        "architecture-dynamics-metrics",
    ] {
        assert!(
            !stdout.contains(command),
            "ArchSig help still exposes FieldSig-owned command {command}\n{stdout}"
        );
    }
}

#[test]
fn cli_extracts_and_validates_sig0() {
    let out_dir = temp_dir("sig0");
    let sig0 = out_dir.join("sig0.json");
    let validation = out_dir.join("validation.json");

    run_sig0(&[
        "--root",
        fixture_root().to_str().expect("fixture path is utf-8"),
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    let sig_json = read_json(&sig0);
    assert_eq!(sig_json["schemaVersion"], "archsig-sig0-v0");

    run_sig0(&[
        "validate",
        "--input",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
        "--universe-mode",
        "local-only",
    ]);
    let validation_json = read_json(&validation);
    assert_eq!(
        validation_json["schemaVersion"],
        "component-universe-validation-report-v0"
    );
}

#[test]
fn cli_validates_archmap_and_projects_to_air() {
    let out_dir = temp_dir("archmap-air");
    let root = fixture_root();
    let archmap = root.join("archmap.json");
    let validation = out_dir.join("archmap-validation.json");
    let air = out_dir.join("archmap-air.json");

    run_sig0(&[
        "archmap",
        "--input",
        archmap.to_str().expect("archmap path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    let validation_json = read_json(&validation);
    assert_eq!(
        validation_json["schemaVersion"],
        "archmap-validation-report-v0"
    );
    assert!(
        matches!(
            validation_json["summary"]["result"].as_str(),
            Some("pass" | "warn")
        ),
        "ArchMap validation should complete without failing"
    );

    run_sig0(&[
        "air-from-archmap",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--validation",
        validation.to_str().expect("validation path is utf-8"),
        "--out",
        air.to_str().expect("air path is utf-8"),
    ]);
    let air_json = read_json(&air);
    assert_eq!(air_json["schemaVersion"], "aat-air-v0");
}

#[test]
fn cli_schema_catalog_is_archsig_owned() {
    let out_dir = temp_dir("schema-catalog");
    let catalog = out_dir.join("schema-version-catalog.json");
    run_sig0(&[
        "schema-catalog",
        "--out",
        catalog.to_str().expect("catalog path is utf-8"),
    ]);
    let json = read_json(&catalog);
    let artifacts = json["artifacts"].as_array().expect("artifacts are array");
    let ids = artifacts
        .iter()
        .map(|entry| entry["artifactId"].as_str().expect("artifact id"))
        .collect::<Vec<_>>();
    assert!(ids.contains(&"signature-artifact"));
    assert!(ids.contains(&"archmap"));
    for fieldsig_id in [
        "intentmap",
        "operation-support-estimate",
        "forecast-cone-skeleton",
        "consequence-envelope-report",
        "ai-proposal-governance",
    ] {
        assert!(
            !ids.contains(&fieldsig_id),
            "ArchSig catalog still owns FieldSig artifact {fieldsig_id}"
        );
    }
}

fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("archsig-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temporary directory can be created");
    dir
}

fn run_sig0(args: &[&str]) {
    let output = run_sig0_output(args);
    assert!(
        output.status.success(),
        "archsig {:?} failed\nstdout:\n{}\nstderr:\n{}",
        args,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_sig0_output(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig command runs")
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json fixture can be read"))
        .expect("json fixture parses")
}
