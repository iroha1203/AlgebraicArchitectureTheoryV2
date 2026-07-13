use serde_json::{Value, json};

pub(crate) const REFACTOR_MORPHISM_SCHEMA: &str = "refactor-morphism/v0.5.2";
pub(crate) const REFINEMENT_COMPARISON_SCHEMA: &str = "refinement-comparison/v0.5.2";

pub fn validate_refactor_morphism_v1(raw: &Value) -> Result<Value, String> {
    let object = raw
        .as_object()
        .ok_or_else(|| "refactor-morphism must be an object".to_string())?;
    reject_unknown(
        object,
        &[
            "schema",
            "id",
            "siteMorphism",
            "lawCompatibility",
            "coefficientCompatibility",
            "witnessCompatibility",
        ],
        "refactor-morphism",
    )?;
    if object.get("schema").and_then(Value::as_str) != Some(REFACTOR_MORPHISM_SCHEMA) {
        return Err("refactor-morphism schema must be refactor-morphism/v0.5.2".to_string());
    }
    require_string(object, "id", "refactor-morphism")?;
    let site = object
        .get("siteMorphism")
        .and_then(Value::as_object)
        .ok_or_else(|| "refactor-morphism requires siteMorphism".to_string())?;
    reject_unknown(
        site,
        &[
            "sourceSiteRef",
            "targetSiteRef",
            "direction",
            "contextMap",
            "coverMap",
        ],
        "siteMorphism",
    )?;
    for field in ["sourceSiteRef", "targetSiteRef", "direction"] {
        require_string(site, field, "siteMorphism")?;
    }
    if site.get("direction").and_then(Value::as_str) != Some("source-to-target") {
        return Err("siteMorphism.direction must be source-to-target".to_string());
    }
    require_nonempty_array(site, "contextMap", "siteMorphism")?;
    require_nonempty_array(site, "coverMap", "siteMorphism")?;
    let law = object
        .get("lawCompatibility")
        .and_then(Value::as_object)
        .ok_or_else(|| "refactor-morphism requires lawCompatibility".to_string())?;
    reject_unknown(
        law,
        &["sourceLawSurfaceRef", "targetLawSurfaceRef", "lawPairs"],
        "lawCompatibility",
    )?;
    require_nonempty_array(law, "lawPairs", "lawCompatibility")?;
    let coefficient = object
        .get("coefficientCompatibility")
        .and_then(Value::as_object)
        .ok_or_else(|| "refactor-morphism requires coefficientCompatibility".to_string())?;
    reject_unknown(
        coefficient,
        &["kind", "source", "target"],
        "coefficientCompatibility",
    )?;
    if coefficient.get("kind").and_then(Value::as_str) != Some("f2-additive") {
        return Err("coefficientCompatibility.kind must be f2-additive".to_string());
    }
    let witness = object
        .get("witnessCompatibility")
        .and_then(Value::as_object)
        .ok_or_else(|| "refactor-morphism requires witnessCompatibility".to_string())?;
    reject_unknown(witness, &["kind", "variableMap"], "witnessCompatibility")?;
    if witness.get("kind").and_then(Value::as_str) != Some("finite-support") {
        return Err("witnessCompatibility.kind must be finite-support".to_string());
    }
    require_nonempty_array(witness, "variableMap", "witnessCompatibility")?;
    Ok(json!({
        "schema": REFACTOR_MORPHISM_SCHEMA,
        "id": object["id"],
        "validated": true,
        "sourceSiteRef": site["sourceSiteRef"],
        "targetSiteRef": site["targetSiteRef"],
        "lawPairCount": law["lawPairs"].as_array().map(Vec::len).unwrap_or_default(),
        "witnessMapCount": witness["variableMap"].as_array().map(Vec::len).unwrap_or_default()
    }))
}

pub fn validate_refinement_comparison_v1(raw: &Value) -> Result<Value, String> {
    let object = raw
        .as_object()
        .ok_or_else(|| "refinement-comparison must be an object".to_string())?;
    reject_unknown(
        object,
        &[
            "schema",
            "id",
            "direction",
            "coarse",
            "fine",
            "zeroTransport",
        ],
        "refinement-comparison",
    )?;
    if object.get("schema").and_then(Value::as_str) != Some(REFINEMENT_COMPARISON_SCHEMA) {
        return Err(
            "refinement-comparison schema must be refinement-comparison/v0.5.2".to_string(),
        );
    }
    require_string(object, "id", "refinement-comparison")?;
    if object.get("direction").and_then(Value::as_str) != Some("coarse-to-fine") {
        return Err("refinement-comparison.direction must be coarse-to-fine".to_string());
    }
    for side in ["coarse", "fine"] {
        let side_object = object
            .get(side)
            .and_then(Value::as_object)
            .ok_or_else(|| format!("refinement-comparison requires {side}"))?;
        reject_unknown(
            side_object,
            &["siteRef", "coverRef", "complexFingerprint"],
            side,
        )?;
        for field in ["siteRef", "coverRef", "complexFingerprint"] {
            require_string(side_object, field, side)?;
        }
    }
    let transport = object
        .get("zeroTransport")
        .and_then(Value::as_object)
        .ok_or_else(|| "refinement-comparison requires zeroTransport".to_string())?;
    reject_unknown(transport, &["kind", "checked", "map"], "zeroTransport")?;
    if transport.get("kind").and_then(Value::as_str) != Some("class-zero-preservation")
        || transport.get("checked").and_then(Value::as_bool) != Some(true)
    {
        return Err("zeroTransport must be checked class-zero-preservation".to_string());
    }
    Ok(json!({
        "schema": REFINEMENT_COMPARISON_SCHEMA,
        "id": object["id"],
        "validated": true,
        "direction": "coarse-to-fine",
        "zeroTransportChecked": true
    }))
}

fn require_string(
    object: &serde_json::Map<String, Value>,
    field: &str,
    owner: &str,
) -> Result<(), String> {
    if object
        .get(field)
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
    {
        return Err(format!("{owner}.{field} must be a non-empty string"));
    }
    Ok(())
}

fn require_nonempty_array(
    object: &serde_json::Map<String, Value>,
    field: &str,
    owner: &str,
) -> Result<(), String> {
    if object
        .get(field)
        .and_then(Value::as_array)
        .is_none_or(Vec::is_empty)
    {
        return Err(format!("{owner}.{field} must be a non-empty array"));
    }
    Ok(())
}

fn reject_unknown(
    object: &serde_json::Map<String, Value>,
    allowed: &[&str],
    owner: &str,
) -> Result<(), String> {
    if let Some(field) = object
        .keys()
        .find(|field| !allowed.contains(&field.as_str()))
    {
        return Err(format!("{owner} contains unknown field {field}"));
    }
    Ok(())
}
