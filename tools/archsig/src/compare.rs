use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::path::Path;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED, ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA,
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ArchSigMeasurementPacketV1, NORMALIZED_ARCHMAP_V2_SCHEMA, validate_measurement_packet_value_v1,
};

const RECORD_DISCIPLINE: &str = "Comparison is a record-level juxtaposition of two ArchSig runs. It does not claim class transport, causal repair, semantic equivalence, or preserved obstruction identity.";

pub fn build_comparison_artifacts_v1(
    base_run: &Path,
    head_run: &Path,
) -> Result<(Value, Value), Box<dyn Error>> {
    let base_manifest = read_run_json(base_run, "archsig-run-manifest.json")?;
    let head_manifest = read_run_json(head_run, "archsig-run-manifest.json")?;
    require_schema(
        &base_manifest,
        ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
        "base run manifest",
    )?;
    require_schema(
        &head_manifest,
        ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
        "head run manifest",
    )?;
    let base_normalized = read_run_json(base_run, "normalized-archmap.json")?;
    let head_normalized = read_run_json(head_run, "normalized-archmap.json")?;
    require_schema(
        &base_normalized,
        NORMALIZED_ARCHMAP_V2_SCHEMA,
        "base normalized archmap",
    )?;
    require_schema(
        &head_normalized,
        NORMALIZED_ARCHMAP_V2_SCHEMA,
        "head normalized archmap",
    )?;
    let base_packet = read_run_json(base_run, "archsig-measurement-packet.json")?;
    let head_packet = read_run_json(head_run, "archsig-measurement-packet.json")?;
    require_schema(
        &base_packet,
        ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
        "base measurement packet",
    )?;
    require_schema(
        &head_packet,
        ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
        "head measurement packet",
    )?;
    validate_compare_packet(&base_packet, "base measurement packet")?;
    validate_compare_packet(&head_packet, "head measurement packet")?;

    let archmap_diff = build_archmap_diff(base_run, head_run, &base_normalized, &head_normalized)?;
    let comparability = comparability(&base_manifest, &head_manifest);
    let cover_or_context_changed =
        diff_has_changes(&archmap_diff, "contexts") || diff_has_changes(&archmap_diff, "covers");
    let verdict_transitions = verdict_transitions(
        &base_packet,
        &head_packet,
        &archmap_diff,
        &comparability,
        cover_or_context_changed,
    );
    let conclusion_code = conclusion_code(&comparability, &verdict_transitions);
    let boundary_statements = comparison_boundaries(&comparability, cover_or_context_changed);

    let report = json!({
        "schema": ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "conclusionCode": conclusion_code,
        "comparability": comparability,
        "discipline": RECORD_DISCIPLINE,
        "inputDigests": {
            "baseRun": run_digest(base_run, &base_manifest),
            "headRun": run_digest(head_run, &head_manifest)
        },
        "artifactRefs": {
            "archmapDiff": "archmap-diff.json",
            "baseMeasurementPacket": "base-run/archsig-measurement-packet.json",
            "headMeasurementPacket": "head-run/archsig-measurement-packet.json"
        },
        "independentConclusions": {
            "base": run_conclusion(&base_manifest, &base_packet),
            "head": run_conclusion(&head_manifest, &head_packet)
        },
        "verdictTransitions": verdict_transitions,
        "boundaryStatements": boundary_statements,
        "nonConclusions": [
            "Comparison report records run-local verdict rows and deterministic ArchMap diff intersections.",
            "Comparison report does not implement class transport, obstruction identity transport, repair causality, or semantic equivalence.",
            "Cover or context changes are boundary data and map to other_transition for gate policy evaluation."
        ]
    });
    Ok((archmap_diff, report))
}

fn build_archmap_diff(
    base_run: &Path,
    head_run: &Path,
    base: &Value,
    head: &Value,
) -> Result<Value, Box<dyn Error>> {
    Ok(json!({
        "schema": ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "basis": "deterministic JSON comparison of normalized-archmap/v0.5.0 sources, atoms, contexts, and covers",
        "inputDigests": {
            "baseNormalizedArchmap": {
                "path": artifact_ref(base_run, "normalized-archmap.json"),
                "sha256": canonical_json_file_digest(&base_run.join("normalized-archmap.json"))?
            },
            "headNormalizedArchmap": {
                "path": artifact_ref(head_run, "normalized-archmap.json"),
                "sha256": canonical_json_file_digest(&head_run.join("normalized-archmap.json"))?
            }
        },
        "sources": diff_sources(base, head),
        "atoms": diff_array_by_id(base, head, "atoms", "normalizedAtomId"),
        "contexts": diff_array_by_id(base, head, "contexts", "normalizedContextId"),
        "covers": diff_array_by_id(base, head, "covers", "normalizedCoverId"),
        "nonConclusions": [
            "ArchMap diff is computed from normalized artifacts; it is not an observation artifact.",
            "Diff operations are mechanical record intersections, not causal claims."
        ]
    }))
}

fn comparability(base: &Value, head: &Value) -> Value {
    let same_tool = text_at(base, &["toolVersion"]) == text_at(head, &["toolVersion"]);
    let same_archmap = digest_at(base, "archmap") == digest_at(head, "archmap");
    let same_law_policy = digest_at(base, "lawPolicy") == digest_at(head, "lawPolicy");
    let same_profile =
        digest_at(base, "profileFingerprint") == digest_at(head, "profileFingerprint");
    let same_cover = digest_at(base, "siteCoverDigest") == digest_at(head, "siteCoverDigest");
    let level = if same_tool && same_archmap && same_law_policy && same_profile {
        "identical"
    } else if same_tool && same_profile && same_cover {
        "verdict-row"
    } else {
        "not-comparable"
    };
    json!({
        "level": level,
        "sameToolVersion": same_tool,
        "sameArchmapDigest": same_archmap,
        "sameLawPolicyDigest": same_law_policy,
        "sameProfileFingerprint": same_profile,
        "sameSiteCoverDigest": same_cover,
        "basis": "identical requires archmap and LawPolicy digests, profile fingerprint, and tool version equality; verdict-row requires profile fingerprint, site cover digest, and tool version equality"
    })
}

fn verdict_transitions(
    base_packet: &Value,
    head_packet: &Value,
    archmap_diff: &Value,
    comparability: &Value,
    cover_or_context_changed: bool,
) -> Vec<Value> {
    let base_rows = verdict_row_map(base_packet);
    let head_rows = verdict_row_map(head_packet);
    let keys = base_rows
        .keys()
        .chain(head_rows.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    keys.into_iter()
        .map(|key| {
            let base = base_rows.get(&key);
            let head = head_rows.get(&key);
            let base_verdict = base
                .and_then(|row| row.get("verdict").and_then(Value::as_str))
                .unwrap_or("absent");
            let head_verdict = head
                .and_then(|row| row.get("verdict").and_then(Value::as_str))
                .unwrap_or("absent");
            let (transition, category) = transition_kind(
                base_verdict,
                head_verdict,
                comparability,
                cover_or_context_changed,
            );
            json!({
                "rowKey": key,
                "baseRowRef": base.map(verdict_ref).unwrap_or(Value::Null),
                "headRowRef": head.map(verdict_ref).unwrap_or(Value::Null),
                "baseVerdict": base_verdict,
                "headVerdict": head_verdict,
                "transition": transition,
                "introducedByChangeCategory": category,
                "deltaRefs": delta_refs_for_row(&key, archmap_diff),
                "discipline": RECORD_DISCIPLINE
            })
        })
        .collect()
}

fn transition_kind(
    base: &str,
    head: &str,
    comparability: &Value,
    cover_or_context_changed: bool,
) -> (&'static str, &'static str) {
    if comparability["level"].as_str() == Some("not-comparable") || cover_or_context_changed {
        return ("other_transition", "other");
    }
    match (base, head) {
        ("absent", _) => ("new_recorded_row", "new"),
        (_, "absent") => ("removed_recorded_row", "removed"),
        ("measured_nonzero", "measured_zero") => {
            ("measured_obstruction_no_longer_recorded", "cleared")
        }
        ("measured_zero", "measured_nonzero") => {
            ("measured_obstruction_recorded_after_change", "new")
        }
        _ if base == head => ("preexisting_recorded_row", "preexisting"),
        _ => ("other_transition", "other"),
    }
}

fn conclusion_code(comparability: &Value, transitions: &[Value]) -> &'static str {
    if comparability["level"].as_str() == Some("not-comparable") {
        return ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA;
    }
    if transitions
        .iter()
        .any(|transition| transition["transition"] == "measured_obstruction_recorded_after_change")
    {
        return ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE;
    }
    if transitions
        .iter()
        .any(|transition| transition["transition"] == "measured_obstruction_no_longer_recorded")
    {
        return ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE;
    }
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED
}

fn comparison_boundaries(comparability: &Value, cover_or_context_changed: bool) -> Vec<Value> {
    if comparability["level"].as_str() != Some("not-comparable") && !cover_or_context_changed {
        return Vec::new();
    }
    let kind = if cover_or_context_changed {
        "cover_changed_between_runs"
    } else {
        "runs_not_comparable_without_comparison_data"
    };
    vec![json!({
        "id": format!("boundary:comparison:{kind}"),
        "kind": kind,
        "reason": "comparison data does not support class transport or causal transition claims",
        "scopeRefs": ["comparison:run-pair"],
        "text": "Runs are recorded side by side only; the comparison does not transport classes or identify the same obstruction across runs."
    })]
}

fn diff_sources(base: &Value, head: &Value) -> Value {
    let base_sources = source_refs(base);
    let head_sources = source_refs(head);
    diff_scalar_set(&base_sources, &head_sources, "source")
}

fn source_refs(value: &Value) -> BTreeSet<String> {
    ["atoms", "contexts", "covers"]
        .into_iter()
        .flat_map(|field| value[field].as_array().into_iter().flatten())
        .flat_map(|item| item["sourceRefs"].as_array().into_iter().flatten())
        .filter_map(Value::as_str)
        .map(str::to_string)
        .collect()
}

fn diff_scalar_set(base: &BTreeSet<String>, head: &BTreeSet<String>, kind: &str) -> Value {
    let added = head
        .difference(base)
        .map(|id| json!({ "op": "added", "kind": kind, "id": id }))
        .collect::<Vec<_>>();
    let removed = base
        .difference(head)
        .map(|id| json!({ "op": "removed", "kind": kind, "id": id }))
        .collect::<Vec<_>>();
    json!({
        "added": added,
        "removed": removed,
        "modified": []
    })
}

fn diff_array_by_id(base: &Value, head: &Value, field: &str, id_field: &str) -> Value {
    let base_items = map_by_id(base, field, id_field);
    let head_items = map_by_id(head, field, id_field);
    let keys = base_items
        .keys()
        .chain(head_items.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut modified = Vec::new();
    for key in keys {
        match (base_items.get(&key), head_items.get(&key)) {
            (None, Some(head_value)) => {
                added.push(json!({ "op": "added", "kind": field, "id": key, "head": head_value }));
            }
            (Some(base_value), None) => {
                removed
                    .push(json!({ "op": "removed", "kind": field, "id": key, "base": base_value }));
            }
            (Some(base_value), Some(head_value))
                if canonical_value(base_value) != canonical_value(head_value) =>
            {
                modified.push(json!({
                    "op": "modified",
                    "kind": field,
                    "id": key,
                    "base": base_value,
                    "head": head_value
                }));
            }
            _ => {}
        }
    }
    json!({
        "added": added,
        "removed": removed,
        "modified": modified
    })
}

fn map_by_id(value: &Value, field: &str, id_field: &str) -> BTreeMap<String, Value> {
    value[field]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| {
            item[id_field]
                .as_str()
                .map(|id| (id.to_string(), item.clone()))
        })
        .collect()
}

fn diff_has_changes(diff: &Value, field: &str) -> bool {
    ["added", "removed", "modified"].into_iter().any(|op| {
        diff[field][op]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    })
}

fn verdict_row_map(packet: &Value) -> BTreeMap<String, Value> {
    packet["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|row| (row_key(row), row.clone()))
        .collect()
}

fn validate_compare_packet(packet: &Value, label: &str) -> Result<(), Box<dyn Error>> {
    serde_json::from_value::<ArchSigMeasurementPacketV1>(packet.clone())
        .map_err(|error| format!("{label} shape is invalid: {error}"))?;
    let failed = validate_measurement_packet_value_v1(packet)
        .into_iter()
        .any(|check| check.result == "fail");
    if failed {
        return Err(format!("{label} failed measurement packet validation").into());
    }
    if packet["structuralVerdict"]
        .as_array()
        .is_none_or(|rows| rows.is_empty())
    {
        return Err(format!("{label} must contain at least one structuralVerdict row").into());
    }
    Ok(())
}

fn row_key(row: &Value) -> String {
    let evaluator = row["evaluator"].as_str().unwrap_or("unknown-evaluator");
    let law = row["law"].as_str().unwrap_or("unknown-law");
    let target = if row.get("target").is_some() {
        let mut target = row["target"].clone();
        if let Some(target_object) = target.as_object_mut() {
            target_object.remove("classRef");
        }
        canonical_value(&target)
    } else {
        row["verdictRef"]
            .as_str()
            .or_else(|| row["structuralVerdictRef"].as_str())
            .map(str::to_string)
            .unwrap_or_else(|| {
                row["verdictData"]["methodStatus"]
                    .as_str()
                    .or_else(|| row["methodStatus"].as_str())
                    .unwrap_or("unknown-target")
                    .to_string()
            })
    };
    format!("{evaluator}|{law}|{target}")
}

fn delta_refs_for_row(key: &str, archmap_diff: &Value) -> Vec<Value> {
    let tokens = key
        .split(|character: char| {
            !character.is_ascii_alphanumeric()
                && character != ':'
                && character != '-'
                && character != '_'
        })
        .filter(|token| !token.is_empty())
        .collect::<BTreeSet<_>>();
    let mut refs = Vec::new();
    for field in ["sources", "atoms", "contexts", "covers"] {
        for op in ["added", "removed", "modified"] {
            for item in archmap_diff[field][op].as_array().into_iter().flatten() {
                let id = item["id"].as_str().unwrap_or("");
                if tokens.contains(id) {
                    refs.push(json!({
                        "diffRef": format!("archmap-diff/{field}/{op}/{id}"),
                        "op": op,
                        "kind": field,
                        "id": id
                    }));
                }
            }
        }
    }
    refs
}

fn verdict_ref(row: &Value) -> Value {
    json!(
        row["verdictRef"]
            .as_str()
            .or_else(|| row["structuralVerdictRef"].as_str())
            .map(str::to_string)
            .unwrap_or_else(|| {
                format!(
                    "structuralVerdict/{}/{}/{}",
                    row["evaluator"].as_str().unwrap_or("unknown-evaluator"),
                    row["law"].as_str().unwrap_or("unknown-law"),
                    row["verdictData"]["methodStatus"]
                        .as_str()
                        .or_else(|| row["methodStatus"].as_str())
                        .unwrap_or("unknown-status")
                )
            })
    )
}

fn run_digest(run: &Path, manifest: &Value) -> Value {
    json!({
        "path": artifact_ref(run, "archsig-run-manifest.json"),
        "runId": manifest["runId"],
        "toolVersion": manifest["toolVersion"],
        "archmap": manifest["inputDigests"]["archmap"],
        "lawPolicy": manifest["inputDigests"]["lawPolicy"],
        "profileFingerprint": manifest["inputDigests"]["profileFingerprint"],
        "siteCoverDigest": manifest["inputDigests"]["siteCoverDigest"],
        "measurementPacket": {
            "path": artifact_ref(run, "archsig-measurement-packet.json"),
            "sha256": canonical_json_file_digest(&run.join("archsig-measurement-packet.json")).unwrap_or_default()
        }
    })
}

fn run_conclusion(manifest: &Value, packet: &Value) -> Value {
    let verdict_counts = packet["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| row["verdict"].as_str())
        .fold(BTreeMap::<String, usize>::new(), |mut counts, verdict| {
            *counts.entry(verdict.to_string()).or_default() += 1;
            counts
        });
    json!({
        "runId": manifest["runId"],
        "mode": manifest["mode"],
        "conclusionCode": manifest["conclusionCode"],
        "structuralVerdictCounts": verdict_counts
    })
}

fn digest_at(value: &Value, key: &str) -> Option<String> {
    value["inputDigests"][key]["sha256"]
        .as_str()
        .map(str::to_string)
}

fn text_at(value: &Value, path: &[&str]) -> Option<String> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    current.as_str().map(str::to_string)
}

fn require_schema(value: &Value, expected: &str, label: &str) -> Result<(), Box<dyn Error>> {
    if value.get("schema").and_then(Value::as_str) != Some(expected) {
        return Err(format!("{label} must have schema {expected}").into());
    }
    Ok(())
}

fn read_run_json(run: &Path, name: &str) -> Result<Value, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(run.join(name))?)?)
}

fn artifact_ref(run: &Path, name: &str) -> String {
    let run_name = run
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("run");
    format!("{run_name}/{name}")
}

fn canonical_json_file_digest(path: &Path) -> Result<String, Box<dyn Error>> {
    let value: Value = serde_json::from_reader(File::open(path)?)?;
    let bytes = serde_json::to_vec(&value)?;
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    Ok(format!("{:x}", hasher.finalize()))
}

fn canonical_value(value: &Value) -> String {
    serde_json::to_string(value).unwrap_or_else(|_| "null".to_string())
}
