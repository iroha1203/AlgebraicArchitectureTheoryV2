use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::{AirDocumentV0, MetricStatus, unmeasured_status};

pub(crate) fn fixture_root() -> PathBuf {
    manifest_root().join("tests/fixtures/minimal")
}

pub(crate) fn air_fixture_document(fixture: &str) -> AirDocumentV0 {
    let path = manifest_root().join("tests/fixtures/air").join(fixture);
    let contents = std::fs::read_to_string(&path).expect("AIR fixture is readable");
    serde_json::from_str(&contents).expect("AIR fixture parses")
}

pub(crate) fn insert_unmeasured_policy_status(metric_status: &mut BTreeMap<String, MetricStatus>) {
    metric_status.insert(
        "boundaryViolationCount".to_string(),
        unmeasured_status("policy file not provided".to_string()),
    );
    metric_status.insert(
        "abstractionViolationCount".to_string(),
        unmeasured_status("policy file not provided".to_string()),
    );
}

fn manifest_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}
