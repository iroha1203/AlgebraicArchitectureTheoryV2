use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};

pub const ARCHSIG_POLICY_BUNDLE_V1_SCHEMA: &str = "archsig-policy-bundle/v0.5.4";
pub const ARCHSIG_POLICY_BUNDLE_VALIDATION_REPORT_SCHEMA: &str =
    "archsig-policy-bundle-validation-report/v0.5.4";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchSigPolicyBundleV1 {
    pub schema: String,
    pub id: String,
    pub law_policy_ref: String,
    pub law_surface_ref: String,
    pub measurement_profile_ref: String,
    pub component_fingerprints: ComponentFingerprintsV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ComponentFingerprintsV1 {
    pub law_policy: String,
    pub law_surface: String,
    pub measurement_profile: String,
}

#[derive(Debug, Clone)]
pub struct ResolvedPolicyBundle {
    pub bundle: ArchSigPolicyBundleV1,
    pub law_policy: PathBuf,
    pub law_surface: PathBuf,
    pub measurement_profile: PathBuf,
    pub report: Value,
}

pub fn build_policy_bundle(
    law_policy: &Path,
    law_surface: &Path,
    measurement_profile: &Path,
    bundle_output: Option<&Path>,
    bundle_id: &str,
) -> Result<ArchSigPolicyBundleV1, Box<dyn Error>> {
    let fingerprints = component_fingerprints(law_policy, law_surface, measurement_profile)?;
    Ok(ArchSigPolicyBundleV1 {
        schema: ARCHSIG_POLICY_BUNDLE_V1_SCHEMA.to_string(),
        id: bundle_id.to_string(),
        law_policy_ref: component_ref(law_policy, bundle_output),
        law_surface_ref: component_ref(law_surface, bundle_output),
        measurement_profile_ref: component_ref(measurement_profile, bundle_output),
        component_fingerprints: ComponentFingerprintsV1 {
            law_policy: fingerprints["lawPolicy"].clone(),
            law_surface: fingerprints["lawSurface"].clone(),
            measurement_profile: fingerprints["measurementProfile"].clone(),
        },
    })
}

pub fn resolve_and_verify_policy_bundle(
    bundle_path: &Path,
    law_policy_override: Option<&Path>,
    law_surface_override: Option<&Path>,
    measurement_profile_override: Option<&Path>,
) -> Result<ResolvedPolicyBundle, Box<dyn Error>> {
    let raw = parse_json_file(bundle_path)?;
    if raw.get("schema").and_then(Value::as_str) != Some(ARCHSIG_POLICY_BUNDLE_V1_SCHEMA) {
        return Err(format!("policy bundle requires {ARCHSIG_POLICY_BUNDLE_V1_SCHEMA}").into());
    }
    let bundle: ArchSigPolicyBundleV1 = serde_json::from_value(raw)?;
    let law_policy = law_policy_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| resolve_ref(bundle_path, &bundle.law_policy_ref));
    let law_surface = law_surface_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| resolve_ref(bundle_path, &bundle.law_surface_ref));
    let measurement_profile = measurement_profile_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| resolve_ref(bundle_path, &bundle.measurement_profile_ref));
    let actual = component_fingerprints(&law_policy, &law_surface, &measurement_profile)?;
    let mut checks = Vec::new();
    for (component, expected) in [
        (
            "lawPolicy",
            bundle.component_fingerprints.law_policy.as_str(),
        ),
        (
            "lawSurface",
            bundle.component_fingerprints.law_surface.as_str(),
        ),
        (
            "measurementProfile",
            bundle.component_fingerprints.measurement_profile.as_str(),
        ),
    ] {
        let found = actual
            .get(component)
            .map(String::as_str)
            .unwrap_or("missing");
        checks.push(serde_json::json!({
            "id": format!("policy-bundle-v052-{component}-fingerprint"),
            "result": if expected == found { "pass" } else { "fail" },
            "component": component,
            "expected": expected,
            "actual": found
        }));
    }
    let failed_check_count = checks
        .iter()
        .filter(|check| check["result"].as_str() == Some("fail"))
        .count();
    let failed = failed_check_count > 0;
    let report = serde_json::json!({
        "schema": ARCHSIG_POLICY_BUNDLE_VALIDATION_REPORT_SCHEMA,
        "input": {"schema": bundle.schema.clone(), "path": input_ref(bundle_path), "id": bundle.id.clone()},
        "checks": checks,
        "summary": {
            "result": if failed { "fail" } else { "pass" },
            "failedCheckCount": failed_check_count,
            "warningCheckCount": 0
        }
    });
    Ok(ResolvedPolicyBundle {
        bundle,
        law_policy,
        law_surface,
        measurement_profile,
        report,
    })
}

pub fn component_fingerprints(
    law_policy: &Path,
    law_surface: &Path,
    measurement_profile: &Path,
) -> Result<BTreeMap<String, String>, Box<dyn Error>> {
    ensure_component_schemas(law_policy, law_surface, measurement_profile)?;
    Ok(BTreeMap::from([
        (
            "lawPolicy".to_string(),
            format!("sha256:{}", canonical_json_file_digest(law_policy)?),
        ),
        (
            "lawSurface".to_string(),
            format!("sha256:{}", canonical_json_file_digest(law_surface)?),
        ),
        (
            "measurementProfile".to_string(),
            format!(
                "sha256:{}",
                canonical_json_file_digest(measurement_profile)?
            ),
        ),
    ]))
}

fn ensure_component_schemas(
    law_policy: &Path,
    law_surface: &Path,
    measurement_profile: &Path,
) -> Result<(), Box<dyn Error>> {
    let law_policy_value = parse_json_file(law_policy)?;
    if law_policy_value.get("schema").and_then(Value::as_str) != Some(crate::LAW_POLICY_V1_SCHEMA) {
        return Err(format!("law-policy requires {}", crate::LAW_POLICY_V1_SCHEMA).into());
    }
    serde_json::from_value::<crate::LawPolicyDocumentV1>(law_policy_value)?;

    let law_surface_value = parse_json_file(law_surface)?;
    if law_surface_value.get("schema").and_then(Value::as_str)
        != Some(crate::LAW_EQUATION_SURFACE_V1_SCHEMA)
    {
        return Err(format!(
            "law-surface requires {}",
            crate::LAW_EQUATION_SURFACE_V1_SCHEMA
        )
        .into());
    }
    serde_json::from_value::<crate::LawEquationSurfaceV1>(law_surface_value)?;

    let measurement_profile_value = parse_json_file(measurement_profile)?;
    if measurement_profile_value
        .get("schema")
        .and_then(Value::as_str)
        != Some(crate::MEASUREMENT_PROFILE_V1_SCHEMA)
    {
        return Err(format!(
            "measurement-profile requires {}",
            crate::MEASUREMENT_PROFILE_V1_SCHEMA
        )
        .into());
    }
    serde_json::from_value::<crate::MeasurementProfileV1>(measurement_profile_value)?;
    Ok(())
}

pub fn canonical_json_bytes(value: &Value) -> Result<Vec<u8>, Box<dyn Error>> {
    serde_json::to_vec(&canonical_json_value(value)).map_err(Into::into)
}

fn canonical_json_file_digest(path: &Path) -> Result<String, Box<dyn Error>> {
    let value = parse_json_file(path)?;
    Ok(sha256_hex(&canonical_json_bytes(&value)?))
}

fn parse_json_file(path: &Path) -> Result<Value, Box<dyn Error>> {
    let text = std::fs::read_to_string(path)?;
    let mut deserializer = serde_json::Deserializer::from_str(&text);
    serde::de::Deserializer::deserialize_any(&mut deserializer, StrictValueVisitor)?;
    Ok(serde_json::from_str(&text)?)
}

struct StrictValueSeed;

impl<'de> serde::de::DeserializeSeed<'de> for StrictValueSeed {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(StrictValueVisitor)
    }
}

struct StrictValueVisitor;

impl<'de> serde::de::Visitor<'de> for StrictValueVisitor {
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
        deserializer.deserialize_any(StrictValueVisitor)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        while sequence.next_element_seed(StrictValueSeed)?.is_some() {}
        Ok(())
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON object key: {key}"
                )));
            }
            map.next_value_seed(StrictValueSeed)?;
        }
        Ok(())
    }
}

fn canonical_json_value(value: &Value) -> Value {
    match value {
        Value::Array(items) => Value::Array(items.iter().map(canonical_json_value).collect()),
        Value::Object(object) => {
            let mut sorted = object.iter().collect::<Vec<_>>();
            sorted.sort_by(|left, right| left.0.cmp(right.0));
            let mut map = Map::new();
            for (key, item) in sorted {
                map.insert(key.clone(), canonical_json_value(item));
            }
            Value::Object(map)
        }
        _ => value.clone(),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn input_ref(path: &Path) -> String {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(|name| name.to_string())
        .unwrap_or_else(|| "input:unnamed-json".to_string())
}

fn component_ref(path: &Path, bundle_output: Option<&Path>) -> String {
    let Some(bundle_output) = bundle_output else {
        return input_ref(path);
    };
    let base = bundle_output.parent().unwrap_or_else(|| Path::new("."));
    relative_path(&absolute_path(base), &absolute_path(path))
}

fn absolute_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    }
}

fn relative_path(base: &Path, target: &Path) -> String {
    let base = base.components().collect::<Vec<_>>();
    let target = target.components().collect::<Vec<_>>();
    let common = base
        .iter()
        .zip(&target)
        .take_while(|(left, right)| left == right)
        .count();
    let mut parts = Vec::<String>::new();
    parts.extend(std::iter::repeat_n(
        "..".to_string(),
        base.len().saturating_sub(common),
    ));
    parts.extend(
        target[common..]
            .iter()
            .map(|component| component.as_os_str().to_string_lossy().to_string()),
    );
    if parts.is_empty() {
        ".".to_string()
    } else {
        parts.join("/")
    }
}

fn resolve_ref(bundle_path: &Path, reference: &str) -> PathBuf {
    let name = reference.strip_prefix("input:").unwrap_or(reference);
    bundle_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(name)
}

#[cfg(test)]
mod tests {
    use super::{canonical_json_bytes, canonical_json_file_digest, component_ref};
    use serde_json::json;
    use std::fs;
    use std::path::PathBuf;

    #[test]
    fn canonical_json_fingerprint_ignores_object_order_and_whitespace() {
        let left =
            serde_json::from_str::<serde_json::Value>(r#"{ "b": 2, "a": [3, {"d":4,"c":5}] }"#)
                .expect("left JSON parses");
        let right = serde_json::from_str::<serde_json::Value>(
            r#"{
                "a": [3, {"c": 5, "d": 4}],
                "b": 2
            }"#,
        )
        .expect("right JSON parses");
        assert_eq!(
            canonical_json_bytes(&left).unwrap(),
            canonical_json_bytes(&right).unwrap()
        );
        assert_eq!(left, json!({"b": 2, "a": [3, {"d": 4, "c": 5}]}));

        let dir = std::env::temp_dir().join(format!(
            "archsig-policy-bundle-canonical-{}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("canonical test directory creates");
        let left_path: PathBuf = dir.join("left.json");
        let right_path = dir.join("right.json");
        fs::write(&left_path, r#"{ "b": 2, "a": [3, {"d":4,"c":5}] }"#)
            .expect("left canonical fixture writes");
        fs::write(
            &right_path,
            "{\n  \"a\": [3, {\"c\": 5, \"d\": 4}],\n  \"b\": 2\n}\n",
        )
        .expect("right canonical fixture writes");
        assert_eq!(
            canonical_json_file_digest(&left_path).unwrap(),
            canonical_json_file_digest(&right_path).unwrap()
        );
        fs::remove_dir_all(dir).expect("canonical test directory removes");
    }

    #[test]
    fn component_refs_are_stable_for_mixed_absolute_and_relative_paths() {
        let component = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/ag_measurement/law_policy_ag.json");
        let bundle = PathBuf::from("target/policy-bundle-mixed/bundle.json");
        let reference = component_ref(&component, Some(&bundle));
        assert!(reference.starts_with("../"));
        std::fs::create_dir_all(bundle.parent().expect("bundle parent creates"))
            .expect("bundle parent creates");
        let resolved = bundle.parent().expect("bundle parent").join(&reference);
        assert_eq!(
            std::fs::canonicalize(resolved).expect("mixed path resolves"),
            std::fs::canonicalize(component).expect("component resolves")
        );
    }
}
