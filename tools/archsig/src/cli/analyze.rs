use std::collections::BTreeMap;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::Serialize;
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone)]
pub(crate) struct AnalyzeRunContract {
    pub tool_version: String,
    pub run_id: String,
    pub input_digests: Value,
}

impl AnalyzeRunContract {
    pub(crate) fn from_inputs(
        archmap: &Path,
        law_policy: &Path,
        profile_fingerprint: Value,
        site_cover_digest: Value,
        stamp: bool,
    ) -> Result<Self, Box<dyn Error>> {
        let archmap_digest = canonical_json_file_digest(archmap)?;
        let law_policy_digest = canonical_json_file_digest(law_policy)?;
        let tool_version = env!("CARGO_PKG_VERSION").to_string();
        let run_seed = format!("{archmap_digest}|{law_policy_digest}|{tool_version}");
        let run_hash = sha256_hex(run_seed.as_bytes());
        let mut run_id = format!("run:{}", &run_hash[..12]);
        if stamp {
            let seconds = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
            run_id.push_str(&format!("-stamp:{seconds}"));
        }
        Ok(Self {
            tool_version,
            run_id,
            input_digests: serde_json::json!({
                "archmap": {
                    "path": artifact_input_ref(archmap),
                    "sha256": archmap_digest
                },
                "lawPolicy": {
                    "path": artifact_input_ref(law_policy),
                    "sha256": law_policy_digest
                },
                "profileFingerprint": profile_fingerprint,
                "siteCoverDigest": site_cover_digest
            }),
        })
    }
}

pub(crate) fn contract_profile_fingerprint(
    law_policy: &Value,
    archmap_is_v1: bool,
) -> Result<Value, Box<dyn Error>> {
    let measurement_profile_ref = law_policy
        .get("measurementProfileRef")
        .cloned()
        .unwrap_or(Value::Null);
    let selected_measurement_profiles = law_policy
        .get("measurementProfiles")
        .and_then(Value::as_array)
        .map(|profiles| {
            profiles
                .iter()
                .filter(|profile| profile.get("profileId") == Some(&measurement_profile_ref))
                .cloned()
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let profile = serde_json::json!({
        "archmapShape": if archmap_is_v1 { "structural" } else { "finite-poset-site" },
        "distanceProfileRef": law_policy.get("distanceProfileRef").cloned().unwrap_or(Value::Null),
        "measurementProfileRef": measurement_profile_ref,
        "selectedMeasurementProfiles": selected_measurement_profiles,
    });
    let canonical = canonical_json_bytes(&profile)?;
    Ok(serde_json::json!({
        "sha256": sha256_hex(&canonical),
        "basis": "archmap shape + selected LawPolicy profile refs and selected profile objects"
    }))
}

pub(crate) fn contract_site_cover_digest(
    archmap: &Value,
    archmap_is_v1: bool,
) -> Result<Value, Box<dyn Error>> {
    let basis = "normalized contexts + covers + derived finite cover nerve";
    if archmap_is_v1 {
        return Ok(serde_json::json!({
            "status": "not_applicable",
            "basis": basis,
            "reason": "structural ArchMap shape has no finite-poset-site contexts or covers"
        }));
    }
    let contexts = normalized_site_contexts(archmap);
    let covers = normalized_site_covers(archmap);
    let derived_nerve = derived_site_cover_nerve(&contexts, &covers);
    let material = serde_json::json!({
        "contexts": contexts,
        "covers": covers,
        "derivedNerve": derived_nerve
    });
    let canonical = canonical_json_bytes(&material)?;
    Ok(serde_json::json!({
        "status": "computed",
        "basis": basis,
        "sha256": sha256_hex(&canonical)
    }))
}

fn normalized_site_contexts(archmap: &Value) -> Vec<Value> {
    let mut rows = archmap["contexts"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|context| {
            let id = context["id"].as_str()?;
            let atom_ids = sorted_prefixed_strings(&context["atoms"], "atom");
            let restricts_to = sorted_prefixed_strings(&context["restrictsTo"], "ctx");
            Some(serde_json::json!({
                "contextRef": prefixed("ctx", id),
                "atomRefs": atom_ids,
                "restrictsTo": restricts_to
            }))
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| row["contextRef"].as_str().unwrap_or_default().to_string());
    rows
}

fn normalized_site_covers(archmap: &Value) -> Vec<Value> {
    let mut rows = archmap["covers"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|cover| {
            let id = cover["id"].as_str()?;
            let context_refs = sorted_prefixed_strings(&cover["contexts"], "ctx");
            Some(serde_json::json!({
                "coverRef": prefixed("cover", id),
                "contextRefs": context_refs
            }))
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| row["coverRef"].as_str().unwrap_or_default().to_string());
    rows
}

fn derived_site_cover_nerve(contexts: &[Value], covers: &[Value]) -> Vec<Value> {
    let context_atoms = contexts
        .iter()
        .filter_map(|context| {
            let context_ref = context["contextRef"].as_str()?.to_string();
            let atoms = string_set(&context["atomRefs"]);
            Some((context_ref, atoms))
        })
        .collect::<BTreeMap<_, _>>();
    let context_restrictions = contexts
        .iter()
        .filter_map(|context| {
            let context_ref = context["contextRef"].as_str()?.to_string();
            let restricts_to = string_set(&context["restrictsTo"]);
            Some((context_ref, restricts_to))
        })
        .collect::<BTreeMap<_, _>>();

    covers
        .iter()
        .map(|cover| {
            let cover_ref = cover["coverRef"].as_str().unwrap_or_default().to_string();
            let context_refs = string_vec(&cover["contextRefs"]);
            let selected = context_refs.iter().cloned().collect::<std::collections::BTreeSet<_>>();
            let mut edges = Vec::new();
            for source in &context_refs {
                let Some(targets) = context_restrictions.get(source) else {
                    continue;
                };
                for target in targets.iter().filter(|target| selected.contains(*target)) {
                    let mut pair = [source.clone(), target.clone()];
                    pair.sort();
                    edges.push(pair);
                }
            }
            edges.sort();
            edges.dedup();

            let mut faces = Vec::new();
            for left in 0..context_refs.len() {
                for middle in left + 1..context_refs.len() {
                    for right in middle + 1..context_refs.len() {
                        let refs = [
                            context_refs[left].clone(),
                            context_refs[middle].clone(),
                            context_refs[right].clone(),
                        ];
                        let Some(shared) = shared_atoms(&context_atoms, &refs) else {
                            continue;
                        };
                        if !shared.is_empty() {
                            faces.push(serde_json::json!({
                                "contextRefs": refs,
                                "sharedAtomRefs": shared
                            }));
                        }
                    }
                }
            }
            serde_json::json!({
                "coverRef": cover_ref,
                "vertices": context_refs,
                "restrictionEdges": edges,
                "tripleOverlaps": faces
            })
        })
        .collect()
}

fn sorted_prefixed_strings(value: &Value, prefix: &str) -> Vec<String> {
    let mut rows = string_vec(value)
        .into_iter()
        .map(|item| prefixed(prefix, &item))
        .collect::<Vec<_>>();
    rows.sort();
    rows.dedup();
    rows
}

fn string_vec(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item.as_str().map(ToOwned::to_owned))
        .collect()
}

fn string_set(value: &Value) -> std::collections::BTreeSet<String> {
    string_vec(value).into_iter().collect()
}

fn shared_atoms(
    context_atoms: &BTreeMap<String, std::collections::BTreeSet<String>>,
    refs: &[String; 3],
) -> Option<Vec<String>> {
    let mut shared = context_atoms.get(&refs[0])?.clone();
    for context_ref in &refs[1..] {
        shared = shared
            .intersection(context_atoms.get(context_ref)?)
            .cloned()
            .collect();
    }
    Some(shared.into_iter().collect())
}

fn prefixed(prefix: &str, id: &str) -> String {
    if id.starts_with(&format!("{prefix}:")) {
        id.to_string()
    } else {
        format!("{prefix}:{id}")
    }
}

pub(crate) fn artifact_input_ref(path: &Path) -> String {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(|name| format!("input:{name}"))
        .unwrap_or_else(|| "input:unnamed-json".to_string())
}

pub(crate) fn with_run_contract<T: Serialize>(
    artifact: &T,
    contract: &AnalyzeRunContract,
) -> Result<Value, Box<dyn Error>> {
    let mut value = serde_json::to_value(artifact)?;
    attach_run_contract(&mut value, contract);
    Ok(value)
}

pub(crate) fn attach_run_contract(value: &mut Value, contract: &AnalyzeRunContract) {
    if let Some(object) = value.as_object_mut() {
        object.insert(
            "toolVersion".to_string(),
            Value::String(contract.tool_version.clone()),
        );
        object.insert("runId".to_string(), Value::String(contract.run_id.clone()));
        object.insert("inputDigests".to_string(), contract.input_digests.clone());
    }
}

fn canonical_json_file_digest(path: &Path) -> Result<String, Box<dyn Error>> {
    let value: Value = serde_json::from_slice(&std::fs::read(path)?)?;
    Ok(sha256_hex(&canonical_json_bytes(&value)?))
}

fn canonical_json_bytes(value: &Value) -> Result<Vec<u8>, Box<dyn Error>> {
    let canonical = canonical_json_value(value);
    Ok(serde_json::to_vec(&canonical)?)
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

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(digest.len() * 2);
    for byte in digest {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

pub(crate) fn build_analyze_run_manifest_v1(
    contract: &AnalyzeRunContract,
    archmap: &Path,
    law_policy: &Path,
    mode: &str,
    conclusion_code: Option<&str>,
    emit_raw_artifacts: bool,
    archmap_validation_summary: Value,
    law_policy_validation_summary: Value,
    analysis_validation_summary: Value,
) -> serde_json::Value {
    let mut generated_artifacts = vec![
        "archmap-validation.json",
        "law-policy-validation.json",
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "architecture-distance.json",
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ];
    let mut omitted_artifacts = Vec::new();
    if emit_raw_artifacts {
        generated_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    } else {
        omitted_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    }

    let mut manifest = serde_json::json!({
        "schema": "archsig-run-manifest/v0.5.0",
        "toolVersion": contract.tool_version.clone(),
        "runId": contract.run_id.clone(),
        "inputDigests": contract.input_digests.clone(),
        "commandName": "analyze",
        "mode": mode,
        "conclusionCode": conclusion_code,
        "archmapInputPath": artifact_input_ref(archmap),
        "lawPolicyInputPath": artifact_input_ref(law_policy),
        "rawArtifactRetention": if emit_raw_artifacts { "full" } else { "omitted" },
        "generatedArtifacts": generated_artifacts,
        "omittedArtifacts": omitted_artifacts,
        "artifactLinks": {
            "summary": "archsig-analysis-summary.json",
            "viewerData": "archsig-atom-viewer-data.json",
            "typedEvaluatorResults": "typed-evaluator-results.json",
            "architectureDistance": "architecture-distance.json"
        },
        "validationReports": {
            "archmap": "archmap-validation.json",
            "lawPolicy": "law-policy-validation.json",
            "analysis": "archsig-analysis-validation.json"
        },
        "rawArtifactPaths": if emit_raw_artifacts {
            serde_json::json!({
                "analysisPacket": "archsig-analysis-packet.json",
                "analysisDetailIndex": "archsig-analysis-detail-index.json",
                "llmInterpretationPacket": "llm-interpretation-packet.json"
            })
        } else {
            serde_json::Value::Null
        },
        "validationResultSummary": {
            "archmap": archmap_validation_summary,
            "lawPolicy": law_policy_validation_summary,
            "analysis": analysis_validation_summary
        },
        "nonConclusions": [
            "v1 run manifest records generated and omitted typed evaluator artifacts for this ArchSig analyze run",
            "manifest paths are artifact navigation aids, not source completeness proof",
            "ArchSig v1 run manifest does not claim Lean theorem discharge"
        ]
    });
    if mode == "validation-failure" {
        manifest["artifactLinks"] = serde_json::json!({
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md",
            "viewerData": "archsig-atom-viewer-data.json"
        });
        manifest["rawArtifactRetention"] = Value::String("not-computed".to_string());
        manifest["rawArtifactPaths"] = Value::Null;
    }
    manifest
}
