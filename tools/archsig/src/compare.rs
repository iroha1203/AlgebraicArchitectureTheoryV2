use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::Path;

use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};

use crate::validate_refinement_comparison_v1;
use crate::{
    ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA, ARCHSIG_CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT,
    ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED, ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA,
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY, ArchSigMeasurementPacketV1,
    NORMALIZED_ARCHMAP_V2_SCHEMA, validate_measurement_packet_value_v1,
};

const RECORD_DISCIPLINE: &str = "Comparison is a record-level juxtaposition of two ArchSig runs. It does not claim causal repair, semantic equivalence, or preserved obstruction identity; a class-zero reading is available only under a checked coarse-to-fine refinement contract.";

pub fn build_comparison_artifacts_v1(
    base_run: &Path,
    head_run: &Path,
) -> Result<(Value, Value), Box<dyn Error>> {
    build_comparison_artifacts_with_refinement_v1(base_run, head_run, None)
}

pub fn build_comparison_artifacts_with_refinement_v1(
    base_run: &Path,
    head_run: &Path,
    refinement_path: Option<&Path>,
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
    validate_run_manifest_shape(&base_manifest, "base run manifest")?;
    validate_run_manifest_shape(&head_manifest, "head run manifest")?;
    validate_component_fingerprints(&base_manifest, "base run manifest")?;
    validate_component_fingerprints(&head_manifest, "head run manifest")?;
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
    let base_normalized_digest = validate_compare_normalized_archmap(
        &base_normalized,
        &base_manifest,
        "base normalized archmap",
    )?;
    let head_normalized_digest = validate_compare_normalized_archmap(
        &head_normalized,
        &head_manifest,
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
    validate_compare_packet(
        &base_packet,
        &base_manifest,
        "base measurement packet",
    )?;
    validate_compare_packet(
        &head_packet,
        &head_manifest,
        "head measurement packet",
    )?;

    let archmap_diff = build_archmap_diff(
        base_run,
        head_run,
        &base_normalized,
        &head_normalized,
        &base_normalized_digest,
        &head_normalized_digest,
    )?;
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
    let class_transport = if let Some(refinement_path) = refinement_path {
        let refinement = read_run_json_path(refinement_path)?;
        validate_refinement_comparison_v1(&refinement)?;
        let run_binding =
            validate_refinement_complex_fingerprints(&base_manifest, &head_manifest, &refinement)?;
        class_transport(
            &base_packet,
            &head_packet,
            &comparability,
            &refinement,
            &run_binding,
        )
    } else {
        json!({
            "status": "silence_by_design",
            "reason": "refinement_data_not_supplied",
            "nonConclusion": "comparison does not identify or transport a class without a checked coarse-to-fine refinement artifact"
        })
    };
    let profile_conclusion_code = (refinement_path.is_none()
        && comparability["level"].as_str() == Some("not-comparable"))
    .then_some(ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY);

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
        "classTransport": class_transport,
        "profileConclusionCode": profile_conclusion_code,
        "nonConclusions": [
            "Comparison report records run-local verdict rows and deterministic ArchMap diff intersections.",
            "Comparison report does not infer class transport, obstruction identity transport, repair causality, or semantic equivalence without the checked refinement or comparison contract that supplies the corresponding data.",
            "Cover or context changes are boundary data and map to other_transition for gate policy evaluation."
        ]
    });
    Ok((archmap_diff, report))
}

fn class_transport(
    base_packet: &Value,
    head_packet: &Value,
    comparability: &Value,
    refinement: &Value,
    run_binding: &Value,
) -> Value {
    let class = |packet: &Value| {
        packet["computedInvariants"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|invariant| invariant["invariantId"] == "saga-descent:residual-class")
            .and_then(|invariant| invariant["residualClassSupport"]["nonZero"].as_bool())
    };
    let Some(base_nonzero) = class(base_packet) else {
        return json!({
            "status": "not_computed",
            "reason": "base_class_not_supplied"
        });
    };
    let Some(head_nonzero) = class(head_packet) else {
        return json!({
            "status": "not_computed",
            "reason": "head_class_not_supplied"
        });
    };
    let zero_preserved = !base_nonzero && !head_nonzero;
    json!({
        "status": if zero_preserved { "established" } else { "not_computed" },
        "conclusionCode": zero_preserved.then_some(ARCHSIG_CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT),
        "schema": "refinement-comparison/v0.5.4",
        "direction": refinement["direction"],
        "recordComparability": comparability["level"],
        "comparabilityBasis": "checked_refinement_complex_fingerprints_bind_each_run",
        "runBinding": run_binding,
        "sourceClassNonZero": base_nonzero,
        "targetClassNonZero": head_nonzero,
        "zeroPreserved": zero_preserved,
        "boundaryStatement": if zero_preserved { Value::Null } else { json!({
            "kind": "class_zero_transport_not_established",
            "scopeRefs": ["comparison:run-pair"],
            "reason": "the supplied refinement contract does not establish coarse-zero to fine-zero",
            "text": "The checked refinement supplies a class-zero reading only when both supplied residual classes are zero."
        }) },
        "nonConclusion": "transport is limited to the supplied residual class zero predicate under the checked coarse-to-fine comparison"
    })
}

fn validate_refinement_complex_fingerprints(
    base_manifest: &Value,
    head_manifest: &Value,
    refinement: &Value,
) -> Result<Value, Box<dyn Error>> {
    let mut bindings = serde_json::Map::new();
    for (side, manifest, digest_label) in [
        ("coarse", base_manifest, "base"),
        ("fine", head_manifest, "head"),
    ] {
        let expected = digest_at(manifest, "siteCoverDigest").ok_or_else(|| {
            format!(
                "{ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION}: {digest_label} run lacks siteCoverDigest.sha256 for refinement binding"
            )
        })?;
        let supplied = refinement[side]["complexFingerprint"]
            .as_str()
            .ok_or_else(|| {
                format!(
                    "{ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION}: refinement.{side}.complexFingerprint is required"
                )
            })?;
        if supplied != expected {
            return Err(format!(
                "{ARCHSIG_COMPARISON_DATA_CONTRACT_VIOLATION}: refinement.{side}.complexFingerprint does not match {digest_label} run inputDigests.siteCoverDigest.sha256"
            )
            .into());
        }
        bindings.insert(
            side.to_string(),
            json!({
                "complexFingerprint": supplied,
                "runDigest": {"field": "inputDigests.siteCoverDigest.sha256", "side": digest_label}
            }),
        );
    }
    Ok(Value::Object(bindings))
}

fn read_run_json_path(path: &Path) -> Result<Value, Box<dyn Error>> {
    let text = std::fs::read_to_string(path)?;
    reject_duplicate_keys(&text)?;
    Ok(serde_json::from_str(&text)?)
}

fn build_archmap_diff(
    base_run: &Path,
    head_run: &Path,
    base: &Value,
    head: &Value,
    base_normalized_digest: &str,
    head_normalized_digest: &str,
) -> Result<Value, Box<dyn Error>> {
    Ok(json!({
        "schema": ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "basis": "deterministic JSON comparison of normalized-archmap/v0.5.4 sources, atoms, contexts, and covers",
        "inputDigests": {
            "baseNormalizedArchmap": {
                "path": artifact_ref(base_run, "normalized-archmap.json"),
                "sha256": base_normalized_digest
            },
            "headNormalizedArchmap": {
                "path": artifact_ref(head_run, "normalized-archmap.json"),
                "sha256": head_normalized_digest
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
    let same_repair_plan = digest_at(base, "repairPlan") == digest_at(head, "repairPlan");
    let same_component_fingerprints = component_fingerprints_at(base)
        .zip(component_fingerprints_at(head))
        .is_some_and(|(base, head)| base == head);
    let same_law_surface = component_fingerprints_at(base).is_some()
        && component_fingerprints_at(head).is_some()
        && component_fingerprint_at(base, "lawSurface")
            == component_fingerprint_at(head, "lawSurface");
    let level = if same_tool
        && same_archmap
        && same_law_policy
        && same_profile
        && same_component_fingerprints
        && same_repair_plan
    {
        "identical"
    } else if same_tool
        && same_profile
        && same_cover
        && same_law_surface
        && same_component_fingerprints
    {
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
        "sameComponentFingerprints": same_component_fingerprints,
        "sameLawSurfaceFingerprint": same_law_surface,
        "sameSiteCoverDigest": same_cover,
        "sameRepairPlanDigest": same_repair_plan,
        "basis": "identical requires archmap, LawPolicy, law-surface, MeasurementProfile, and optional RepairPlan input digests plus tool version equality; verdict-row requires all three LawPolicy, law-surface, and MeasurementProfile component fingerprints, site cover digest, and tool version equality, while recording whether the optional RepairPlan digest changed"
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
    let mut boundaries = Vec::new();
    if comparability["level"].as_str() == Some("not-comparable") || cover_or_context_changed {
        let kind = if cover_or_context_changed {
            "cover_changed_between_runs"
        } else {
            "runs_not_comparable_without_comparison_data"
        };
        boundaries.push(json!({
            "id": format!("boundary:comparison:{kind}"),
            "kind": kind,
            "reason": "record-level comparison data does not support class identity or causal transition claims outside classTransport's checked refinement contract",
            "scopeRefs": ["comparison:run-pair"],
            "text": "Record transitions remain side by side; any class-zero reading is limited to classTransport's checked coarse-to-fine refinement contract."
        }));
    }
    if comparability["sameRepairPlanDigest"] == Value::Bool(false) {
        boundaries.push(json!({
            "id": "boundary:comparison:repair-plan-changed-between-runs",
            "kind": "repair_plan_changed_between_runs",
            "reason": "the compared runs bind different RepairPlan input digests",
            "scopeRefs": ["comparison:run-pair"],
            "text": "Record-level verdict rows remain comparable under the shared policy, law-surface, profile, and site-cover contract; the RepairPlan change is recorded and does not establish causal repair."
        }));
    }
    boundaries
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

fn validate_compare_packet(
    packet: &Value,
    manifest: &Value,
    label: &str,
) -> Result<(), Box<dyn Error>> {
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
    validate_compare_run_contract(packet, manifest, label)?;
    validate_manifest_artifact_digest(packet, manifest, "measurementPacket", label)?;
    Ok(())
}

fn validate_compare_normalized_archmap(
    normalized_archmap: &Value,
    manifest: &Value,
    label: &str,
) -> Result<String, Box<dyn Error>> {
    validate_compare_run_contract(normalized_archmap, manifest, label)?;
    validate_manifest_artifact_digest(normalized_archmap, manifest, "normalizedArchmap", label)
}

fn validate_compare_run_contract(
    artifact: &Value,
    manifest: &Value,
    label: &str,
) -> Result<(), Box<dyn Error>> {
    for field in ["toolVersion", "runId", "inputDigests", "componentFingerprints"] {
        if artifact.get(field) != manifest.get(field) {
            return Err(format!(
                "{label} {field} must match its run manifest provenance"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_manifest_artifact_digest(
    artifact: &Value,
    manifest: &Value,
    artifact_key: &str,
    label: &str,
) -> Result<String, Box<dyn Error>> {
    let expected_digest = manifest["artifactDigests"][artifact_key]["sha256"]
        .as_str()
        .ok_or_else(|| format!("{label} run manifest requires artifactDigests.{artifact_key}.sha256"))?;
    let actual_digest = canonical_json_value_digest(artifact)?;
    if expected_digest != actual_digest {
        return Err(format!(
            "{label} digest does not match its run manifest artifactDigests.{artifact_key}.sha256"
        )
        .into());
    }
    Ok(actual_digest)
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
        "componentFingerprints": manifest["componentFingerprints"],
        "siteCoverDigest": manifest["inputDigests"]["siteCoverDigest"],
        "repairPlan": manifest["inputDigests"]["repairPlan"],
        "normalizedArchmap": manifest["artifactDigests"]["normalizedArchmap"],
        "measurementPacket": manifest["artifactDigests"]["measurementPacket"]
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

fn component_fingerprints_at(value: &Value) -> Option<&Value> {
    value
        .get("componentFingerprints")
        .filter(|value| value.is_object())
}

fn component_fingerprint_at<'a>(value: &'a Value, component: &str) -> Option<&'a str> {
    component_fingerprints_at(value)?.get(component)?.as_str()
}

#[cfg(test)]
mod tests {
    use super::{comparability, validate_component_fingerprints};
    use serde_json::json;

    fn manifest(law_surface: &str) -> serde_json::Value {
        json!({
            "toolVersion": "0.5.4",
            "inputDigests": {
                "archmap": {"sha256": "same-archmap"},
                "lawPolicy": {"sha256": "same-policy"},
                "profileFingerprint": {"sha256": "same-profile"},
                "siteCoverDigest": {"sha256": "same-cover"}
            },
            "componentFingerprints": {
                "lawPolicy": "sha256:same-policy",
                "lawSurface": law_surface,
                "measurementProfile": "sha256:same-profile"
            }
        })
    }

    #[test]
    fn law_surface_fingerprint_change_blocks_identical_and_row_comparability() {
        let base = manifest("sha256:surface-a");
        let head = manifest("sha256:surface-b");
        let result = comparability(&base, &head);
        assert_eq!(result["level"], "not-comparable");
        assert_eq!(result["sameComponentFingerprints"], false);
        assert_eq!(result["sameLawSurfaceFingerprint"], false);
    }

    #[test]
    fn law_policy_fingerprint_change_blocks_row_comparability() {
        let mut base = manifest("sha256:surface-a");
        let mut head = manifest("sha256:surface-a");
        base["componentFingerprints"]["lawPolicy"] = json!("sha256:policy-a");
        head["componentFingerprints"]["lawPolicy"] = json!("sha256:policy-b");
        let result = comparability(&base, &head);
        assert_eq!(result["level"], "not-comparable");
        assert_eq!(result["sameComponentFingerprints"], false);
    }

    #[test]
    fn repair_plan_digest_change_excludes_identical_but_keeps_verdict_row_comparability() {
        let mut base = manifest("sha256:surface-a");
        let mut head = manifest("sha256:surface-a");
        base["inputDigests"]["repairPlan"] = json!({"sha256": "repair-plan-a"});
        head["inputDigests"]["repairPlan"] = json!({"sha256": "repair-plan-b"});
        let result = comparability(&base, &head);
        assert_eq!(result["level"], "verdict-row");
        assert_eq!(result["sameRepairPlanDigest"], false);
    }

    #[test]
    fn malformed_component_fingerprints_are_rejected() {
        let mut value = manifest("sha256:surface-a");
        value["componentFingerprints"] = json!({});
        assert!(validate_component_fingerprints(&value, "test manifest").is_err());
    }
}

fn require_schema(value: &Value, expected: &str, label: &str) -> Result<(), Box<dyn Error>> {
    if value.get("schema").and_then(Value::as_str) != Some(expected) {
        return Err(format!("{label} must have schema {expected}").into());
    }
    Ok(())
}

fn read_run_json(run: &Path, name: &str) -> Result<Value, Box<dyn Error>> {
    let text = std::fs::read_to_string(run.join(name))?;
    reject_duplicate_keys(&text)?;
    Ok(serde_json::from_str(&text)?)
}

fn validate_component_fingerprints(manifest: &Value, label: &str) -> Result<(), Box<dyn Error>> {
    let object = manifest
        .get("componentFingerprints")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{label} requires componentFingerprints"))?;
    let expected = BTreeSet::from([
        "lawPolicy".to_string(),
        "lawSurface".to_string(),
        "measurementProfile".to_string(),
    ]);
    let actual = object.keys().cloned().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(format!(
            "{label} componentFingerprints keys must be lawPolicy, lawSurface, measurementProfile"
        )
        .into());
    }
    for (component, value) in object {
        let fingerprint = value
            .as_str()
            .ok_or_else(|| format!("{label} componentFingerprints.{component} must be a string"))?;
        if fingerprint.len() != 71
            || !fingerprint.starts_with("sha256:")
            || !fingerprint[7..]
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(format!(
                "{label} componentFingerprints.{component} must be sha256:<64 hex chars>"
            )
            .into());
        }
    }
    let input_digests = manifest
        .get("inputDigests")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{label} requires inputDigests object"))?;
    let required_digest_keys = BTreeSet::from([
        "archmap",
        "lawPolicy",
        "lawSurface",
        "measurementProfile",
        "profileFingerprint",
        "siteCoverDigest",
    ]);
    let allowed_digest_keys = BTreeSet::from([
        "archmap",
        "lawPolicy",
        "lawSurface",
        "measurementProfile",
        "measurementProfiles",
        "profileFingerprint",
        "repairPlan",
        "residualPacket",
        "siteCoverDigest",
    ]);
    let actual_digest_keys = input_digests
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if actual_digest_keys
        .difference(&allowed_digest_keys)
        .next()
        .is_some()
    {
        return Err(format!("{label} inputDigests contains unknown keys").into());
    }
    if required_digest_keys
        .difference(&actual_digest_keys)
        .next()
        .is_some()
    {
        return Err(format!("{label} inputDigests is missing required keys").into());
    }
    for key in &actual_digest_keys {
        if *key == "measurementProfiles" {
            let entries = input_digests
                .get(*key)
                .and_then(Value::as_array)
                .ok_or_else(|| {
                    format!("{label} inputDigests.measurementProfiles must be an array")
                })?;
            if entries.is_empty() {
                return Err(
                    format!("{label} inputDigests.measurementProfiles must not be empty").into(),
                );
            }
            for entry in entries {
                let object = entry.as_object().ok_or_else(|| {
                    format!("{label} inputDigests.measurementProfiles entries must be objects")
                })?;
                let keys = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
                if keys != BTreeSet::from(["path", "sha256"]) {
                    return Err(format!(
                        "{label} inputDigests.measurementProfiles entry has invalid fields"
                    )
                    .into());
                }
                if !object.get("path").is_some_and(Value::is_string)
                    || !object
                        .get("sha256")
                        .and_then(Value::as_str)
                        .is_some_and(|digest| {
                            digest.len() == 64
                                && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
                        })
                {
                    return Err(format!(
                        "{label} inputDigests.measurementProfiles entry is invalid"
                    )
                    .into());
                }
            }
            continue;
        }
        let entry = input_digests
            .get(*key)
            .and_then(Value::as_object)
            .ok_or_else(|| format!("{label} inputDigests.{key} must be an object"))?;
        let digest = entry
            .get("sha256")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{label} inputDigests.{key}.sha256 is required"))?;
        if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!("{label} inputDigests.{key}.sha256 must be 64 hex chars").into());
        }
        let expected_entry_keys = match *key {
            "profileFingerprint" => BTreeSet::from(["basis", "sha256"]),
            "siteCoverDigest" => BTreeSet::from(["basis", "sha256", "status"]),
            _ => BTreeSet::from(["path", "sha256"]),
        };
        let actual_entry_keys = entry.keys().map(String::as_str).collect::<BTreeSet<_>>();
        if actual_entry_keys
            .difference(&expected_entry_keys)
            .next()
            .is_some()
            || expected_entry_keys
                .difference(&actual_entry_keys)
                .next()
                .is_some()
        {
            return Err(format!("{label} inputDigests.{key} has invalid fields").into());
        }
        for field in expected_entry_keys {
            if field != "sha256" && !entry.get(field).is_some_and(Value::is_string) {
                return Err(format!("{label} inputDigests.{key}.{field} must be a string").into());
            }
        }
    }
    let repair_plan_input = manifest.get("repairPlanInputPath");
    let repair_plan_path = repair_plan_input.and_then(Value::as_str);
    let repair_plan_digest = input_digests.get("repairPlan");
    match (repair_plan_path, repair_plan_digest) {
        (Some(path), Some(digest)) if digest["path"].as_str() == Some(path) => {}
        (Some(_), Some(_)) => {
            return Err(format!(
                "{label} inputDigests.repairPlan.path must match repairPlanInputPath"
            )
            .into());
        }
        (Some(_), None) => {
            return Err(format!(
                "{label} requires inputDigests.repairPlan when repairPlanInputPath is present"
            )
            .into());
        }
        (None, Some(_)) => {
            return Err(format!(
                "{label} must not contain inputDigests.repairPlan without repairPlanInputPath"
            )
            .into());
        }
        (None, None) => {}
    }
    for (component, digest_key) in [
        ("lawPolicy", "lawPolicy"),
        ("lawSurface", "lawSurface"),
        ("measurementProfile", "measurementProfile"),
    ] {
        let digest = input_digests
            .get(digest_key)
            .and_then(|value| value.get("sha256"))
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{label} requires inputDigests.{digest_key}.sha256"))?;
        if fingerprint_value(object, component) != Some(digest) {
            return Err(format!(
                "{label} componentFingerprints.{component} must match inputDigests.{digest_key}.sha256"
            )
            .into());
        }
    }
    Ok(())
}

fn fingerprint_value<'a>(
    object: &'a serde_json::Map<String, Value>,
    component: &str,
) -> Option<&'a str> {
    object
        .get(component)
        .and_then(Value::as_str)
        .and_then(|value| value.strip_prefix("sha256:"))
}

fn validate_run_manifest_shape(manifest: &Value, label: &str) -> Result<(), Box<dyn Error>> {
    let object = manifest
        .as_object()
        .ok_or_else(|| format!("{label} must be a JSON object"))?;
    let allowed = BTreeSet::from([
        "schema",
        "toolVersion",
        "runId",
        "inputDigests",
        "artifactDigests",
        "componentFingerprints",
        "commandName",
        "mode",
        "conclusionCode",
        "archmapInputPath",
        "lawPolicyInputPath",
        "lawSurfaceInputPath",
        "measurementProfileInputPath",
        "measurementProfileInputPaths",
        "repairPlanInputPath",
        "rawArtifactRetention",
        "generatedArtifacts",
        "omittedArtifacts",
        "artifactLinks",
        "validationReports",
        "rawArtifactPaths",
        "validationResultSummary",
        "nonConclusions",
    ]);
    let required = BTreeSet::from([
        "schema",
        "toolVersion",
        "runId",
        "inputDigests",
        "artifactDigests",
        "componentFingerprints",
        "commandName",
        "mode",
        "conclusionCode",
        "archmapInputPath",
        "lawPolicyInputPath",
        "rawArtifactRetention",
        "generatedArtifacts",
        "omittedArtifacts",
        "artifactLinks",
        "validationReports",
        "validationResultSummary",
        "nonConclusions",
    ]);
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    if actual.difference(&allowed).next().is_some() {
        return Err(format!("{label} contains unknown top-level manifest fields").into());
    }
    if required.difference(&actual).next().is_some() {
        return Err(format!("{label} is missing required top-level manifest fields").into());
    }
    let artifact_digests = manifest
        .get("artifactDigests")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{label} artifactDigests must be an object"))?;
    let expected_artifacts = if manifest["mode"].as_str() == Some("measurement") {
        BTreeSet::from(["measurementPacket", "normalizedArchmap"])
    } else {
        BTreeSet::new()
    };
    let actual_artifacts = artifact_digests
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if actual_artifacts != expected_artifacts {
        return Err(format!(
            "{label} artifactDigests must match artifacts emitted by its run mode"
        )
        .into());
    }
    for (artifact_key, artifact_path) in [
        ("measurementPacket", "archsig-measurement-packet.json"),
        ("normalizedArchmap", "normalized-archmap.json"),
    ] {
        let artifact = artifact_digests
            .get(artifact_key)
            .ok_or_else(|| format!("{label} artifactDigests.{artifact_key} is required"))?;
        let object = artifact
            .as_object()
            .ok_or_else(|| format!("{label} artifactDigests.{artifact_key} must be an object"))?;
        if object.keys().map(String::as_str).collect::<BTreeSet<_>>()
            != BTreeSet::from(["path", "sha256"])
            || object.get("path").and_then(Value::as_str)
                != Some(artifact_path)
            || !object
                .get("sha256")
                .and_then(Value::as_str)
                .is_some_and(|digest| {
                    digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
                })
        {
            return Err(format!(
                "{label} artifactDigests.{artifact_key} must contain its artifact path and sha256 digest"
            )
            .into());
        }
    }
    Ok(())
}

fn reject_duplicate_keys(text: &str) -> Result<(), Box<dyn Error>> {
    let mut deserializer = serde_json::Deserializer::from_str(text);
    serde::de::Deserializer::deserialize_any(&mut deserializer, DuplicateKeyVisitor)?;
    Ok(())
}

struct DuplicateKeySeed;

impl<'de> DeserializeSeed<'de> for DuplicateKeySeed {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(DuplicateKeyVisitor)
    }
}

struct DuplicateKeyVisitor;

impl<'de> Visitor<'de> for DuplicateKeyVisitor {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, _: bool) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_i64<E>(self, _: i64) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_u64<E>(self, _: u64) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_f64<E>(self, _: f64) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_str<E>(self, _: &str) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_string<E>(self, _: String) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(DuplicateKeyVisitor)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        while sequence.next_element_seed(DuplicateKeySeed)?.is_some() {}
        Ok(())
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON object key: {key}"
                )));
            }
            map.next_value_seed(DuplicateKeySeed)?;
        }
        Ok(())
    }
}

fn artifact_ref(run: &Path, name: &str) -> String {
    let run_name = run
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("run");
    format!("{run_name}/{name}")
}

fn canonical_json_value_digest(value: &Value) -> Result<String, Box<dyn Error>> {
    let bytes = serde_json::to_vec(&canonical_json_value(value))?;
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    Ok(format!("{:x}", hasher.finalize()))
}

fn canonical_json_value(value: &Value) -> Value {
    match value {
        Value::Array(items) => Value::Array(items.iter().map(canonical_json_value).collect()),
        Value::Object(object) => {
            let sorted = object
                .iter()
                .map(|(key, value)| (key.clone(), canonical_json_value(value)))
                .collect::<BTreeMap<_, _>>();
            let mut map = Map::new();
            for (key, value) in sorted {
                map.insert(key, value);
            }
            Value::Object(map)
        }
        _ => value.clone(),
    }
}

fn canonical_value(value: &Value) -> String {
    serde_json::to_string(value).unwrap_or_else(|_| "null".to_string())
}
