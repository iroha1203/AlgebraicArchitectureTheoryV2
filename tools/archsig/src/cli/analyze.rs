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
    pub component_fingerprints: Option<Value>,
}

impl AnalyzeRunContract {
    pub(crate) fn from_inputs(
        archmap: &Path,
        law_policy: &Path,
        law_surface: Option<&Path>,
        measurement_profiles: &[&Path],
        residual_packet: Option<&Path>,
        repair_plan: Option<&Path>,
        profile_fingerprint: Value,
        site_cover_digest: Value,
        component_fingerprints: Option<Value>,
        stamp: bool,
    ) -> Result<Self, Box<dyn Error>> {
        let archmap_digest = canonical_json_file_digest(archmap)?;
        let law_policy_digest = canonical_json_file_digest(law_policy)?;
        let law_surface_digest = law_surface
            .map(canonical_json_file_digest)
            .transpose()?;
        let measurement_profile_digests = measurement_profiles
            .iter()
            .map(|path| canonical_json_file_digest(path))
            .collect::<Result<Vec<_>, _>>()?;
        let measurement_profile_digest = measurement_profile_digests
            .first()
            .cloned()
            .ok_or("at least one measurement profile input is required")?;
        let tool_version = env!("CARGO_PKG_VERSION").to_string();
        let residual_packet_digest = residual_packet
            .map(canonical_json_file_digest)
            .transpose()?;
        let repair_plan_digest = repair_plan.map(canonical_json_file_digest).transpose()?;
        let run_seed = match (
            law_surface_digest.as_deref(),
            residual_packet_digest.as_deref(),
        ) {
            (Some(law_surface_digest), Some(residual_packet_digest)) => format!(
                "{archmap_digest}|{law_policy_digest}|{law_surface_digest}|{}|{residual_packet_digest}|{tool_version}",
                measurement_profile_digests.join("|")
            ),
            (Some(law_surface_digest), None) => format!(
                "{archmap_digest}|{law_policy_digest}|{law_surface_digest}|{}|{tool_version}",
                measurement_profile_digests.join("|")
            ),
            (None, Some(residual_packet_digest)) => format!(
                "{archmap_digest}|{law_policy_digest}|{}|{residual_packet_digest}|{tool_version}",
                measurement_profile_digests.join("|")
            ),
            (None, None) => format!(
                "{archmap_digest}|{law_policy_digest}|{}|{tool_version}",
                measurement_profile_digests.join("|")
            ),
        };
        let run_seed = repair_plan_digest
            .as_deref()
            .map(|digest| format!("{run_seed}|repairPlan:{digest}"))
            .unwrap_or(run_seed);
        let run_hash = sha256_hex(run_seed.as_bytes());
        let mut run_id = format!("run:{}", &run_hash[..12]);
        if stamp {
            let seconds = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
            run_id.push_str(&format!("-stamp:{seconds}"));
        }
        let mut input_digests = serde_json::json!({
            "archmap": {
                "path": artifact_input_ref(archmap),
                "sha256": archmap_digest
            },
            "lawPolicy": {
                "path": artifact_input_ref(law_policy),
                "sha256": law_policy_digest
            },
            "measurementProfile": {
                "path": artifact_input_ref(measurement_profiles[0]),
                "sha256": measurement_profile_digest
            },
            "measurementProfiles": measurement_profiles
                .iter()
                .zip(measurement_profile_digests.iter())
                .map(|(path, digest)| serde_json::json!({
                    "path": artifact_input_ref(path),
                    "sha256": digest
                }))
                .collect::<Vec<_>>(),
            "profileFingerprint": profile_fingerprint,
            "siteCoverDigest": site_cover_digest
        });
        if let (Some(path), Some(digest)) = (law_surface, law_surface_digest) {
            input_digests["lawSurface"] = serde_json::json!({
                "path": artifact_input_ref(path),
                "sha256": digest
            });
        }
        if let Some(residual_packet_digest) = residual_packet_digest {
            input_digests["residualPacket"] = serde_json::json!({
                "path": artifact_input_ref(residual_packet.expect("residual packet path is present")),
                "sha256": residual_packet_digest
            });
        }
        if let (Some(path), Some(digest)) = (repair_plan, repair_plan_digest) {
            input_digests["repairPlan"] = serde_json::json!({
                "path": artifact_input_ref(path),
                "sha256": digest
            });
        }
        Ok(Self {
            tool_version,
            run_id,
            input_digests,
            component_fingerprints,
        })
    }
}

pub(crate) fn contract_profile_fingerprint(
    law_policy: &Value,
    measurement_profiles: &[Value],
) -> Result<Value, Box<dyn Error>> {
    let measurement_profile_ref = law_policy
        .get("measurementProfileRef")
        .cloned()
        .unwrap_or(Value::Null);
    let mut profile = serde_json::json!({
        "archmapShape": "finite-poset-site",
        "measurementProfileRef": measurement_profile_ref,
        "selectedMeasurementProfile": measurement_profiles.first().cloned().unwrap_or(Value::Null),
    });
    if measurement_profiles.len() > 1 {
        profile["selectedMeasurementProfiles"] = serde_json::json!(measurement_profiles);
    }
    let canonical = canonical_json_bytes(&profile)?;
    Ok(serde_json::json!({
        "sha256": sha256_hex(&canonical),
        "basis": "archmap shape + LawPolicy measurementProfileRef + external MeasurementProfile artifact"
    }))
}

pub(crate) fn contract_site_cover_digest(archmap: &Value) -> Result<Value, Box<dyn Error>> {
    let basis = "normalized contexts + covers + derived finite cover nerve";
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
        if let Some(component_fingerprints) = &contract.component_fingerprints {
            object.insert(
                "componentFingerprints".to_string(),
                component_fingerprints.clone(),
            );
        }
    }
}

pub(crate) fn canonical_json_file_digest(path: &Path) -> Result<String, Box<dyn Error>> {
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
