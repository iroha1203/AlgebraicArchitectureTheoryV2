use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

#[test]
fn cli_emits_and_validates_software_field_measurement_and_run_manifest() {
    let out_dir = temp_dir("software-field-measurement");
    let measurement = out_dir.join("software-field-measurement.json");
    let measurement_validation = out_dir.join("software-field-measurement-validation.json");
    let manifest = out_dir.join("fieldsig-run-manifest.json");
    let manifest_validation = out_dir.join("fieldsig-run-manifest-validation.json");

    run_fieldsig(&[
        "software-field-measurement",
        "--fixture",
        "--out",
        measurement.to_str().expect("measurement path is utf-8"),
    ]);
    let measurement_json = read_json(&measurement);
    assert_eq!(
        measurement_json["schemaVersion"],
        "software-field-measurement-v0"
    );
    assert!(
        measurement_json["archsigArtifactRefs"]
            .as_array()
            .expect("archsig refs")
            .iter()
            .any(|entry| entry["producer"] == "archsig")
    );
    assert!(
        measurement_json["workflowEvidenceRefs"]
            .as_array()
            .expect("workflow refs")
            .len()
            >= 3
    );
    assert!(
        measurement_json["unknownRemainder"]
            .as_array()
            .expect("unknown remainder")
            .len()
            >= 1
    );
    assert!(
        measurement_json["nonConclusions"]
            .as_array()
            .expect("non conclusions")
            .iter()
            .any(|entry| entry == "FieldSig does not prove forecast correctness")
    );

    run_fieldsig(&[
        "software-field-measurement",
        "--input",
        measurement.to_str().expect("measurement path is utf-8"),
        "--out",
        measurement_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    let validation_json = read_json(&measurement_validation);
    assert_eq!(
        validation_json["schemaVersion"],
        "software-field-measurement-validation-report-v0"
    );
    assert_eq!(validation_json["summary"]["result"], "pass");
    assert!(
        validation_json["checks"]
            .as_array()
            .expect("checks")
            .iter()
            .any(|check| check["id"] == "software-field-measurement-archsig-ref-boundary")
    );

    run_fieldsig(&[
        "fieldsig-run-manifest",
        "--fixture",
        "--out",
        manifest.to_str().expect("manifest path is utf-8"),
    ]);
    let manifest_json = read_json(&manifest);
    assert_eq!(manifest_json["schemaVersion"], "fieldsig-run-manifest-v0");
    assert!(
        manifest_json["inputArtifactRefs"]
            .as_array()
            .expect("input refs")
            .len()
            >= 2
    );
    assert!(
        manifest_json["generatedOutputRefs"]
            .as_array()
            .expect("output refs")
            .iter()
            .any(|entry| entry["schemaVersion"] == "software-field-measurement-v0")
    );

    run_fieldsig(&[
        "fieldsig-run-manifest",
        "--input",
        manifest.to_str().expect("manifest path is utf-8"),
        "--out",
        manifest_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    let manifest_validation_json = read_json(&manifest_validation);
    assert_eq!(
        manifest_validation_json["schemaVersion"],
        "fieldsig-run-manifest-validation-report-v0"
    );
    assert_eq!(manifest_validation_json["summary"]["result"], "pass");
}

fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("fieldsig-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temporary directory can be created");
    dir
}

fn run_fieldsig(args: &[&str]) {
    let output = Command::new(env!("CARGO_BIN_EXE_fieldsig"))
        .args(args)
        .output()
        .expect("fieldsig command runs");
    assert!(
        output.status.success(),
        "fieldsig {:?} failed\nstdout:\n{}\nstderr:\n{}",
        args,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json fixture can be read"))
        .expect("json fixture parses")
}
