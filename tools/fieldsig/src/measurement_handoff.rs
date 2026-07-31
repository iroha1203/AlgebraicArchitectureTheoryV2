use std::collections::BTreeSet;
use std::fmt;
use std::path::Path;

use serde::de::{DeserializeSeed, Error as DeError, MapAccess, SeqAccess, Visitor};

use crate::{
    ARTIFACT_DESCRIPTOR_SCHEMA_VERSION, ArchMapLeanPreservationVocabularyEntry,
    CandidateOperationFamilyV0, KnownForbiddenOperationSupportV0,
    OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION, OperationSupportDescriptorRefV0,
    OperationSupportEstimateV0, OperationSupportEvidenceBoundaryV0,
    OperationSupportPolicyConstraintV0, OperationSupportUnknownRemainderV0,
};

const OPERATION_SUPPORT_REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "operation support estimate is a bounded tooling estimate, not accepted PR history",
    "operation support estimate is not actual future support",
    "unknown support is not measured zero",
    "policy constraints do not prove global policy safety",
    "operation support estimate does not prove future trajectory safety",
];

const OPERATION_SUPPORT_EVIDENCE_BOUNDARY_NON_CONCLUSIONS: [&str; 3] = [
    "confidence is relative to retained descriptor source refs",
    "evidence boundary does not complete extractor coverage",
    "unsupported constructs remain forecast boundary items",
];

const ARCHSIG_COMPUTED_INVARIANT_KINDS: [&str; 17] = [
    "measurement-invariant",
    "cech-h1-rank",
    "minimal-forbidden-supports",
    "tor1-class-support",
    "boundary-residue-rank",
    "residual-boundary-membership",
    "selected-cover-edge-support",
    "coherence-obstruction-count",
    "restriction-compatibility-rank",
    "section-factorization-rank",
    "sheaf-laplacian-spectrum",
    "period-stokes-pairing",
    "period-stokes-audit",
    "support-transfer-rank",
    "topological-debt-capacity",
    "saga-grounded-conclusions",
    "h1-comparison-transfer",
];

const ARCHSIG_SUPPLIED_DATA_KINDS: [&str; 5] = [
    "archmap",
    "law-policy",
    "measurement-profile",
    "law-equation-surface",
    "repair-plan",
];

pub fn read_archsig_measurement_packet(
    path: &Path,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let source = std::fs::read_to_string(path)?;
    let mut deserializer = serde_json::Deserializer::from_str(&source);
    let value = NoDuplicateJsonSeed.deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

struct NoDuplicateJsonSeed;

impl<'de> DeserializeSeed<'de> for NoDuplicateJsonSeed {
    type Value = serde_json::Value;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(NoDuplicateJsonVisitor)
    }
}

struct NoDuplicateJsonVisitor;

impl<'de> Visitor<'de> for NoDuplicateJsonVisitor {
    type Value = serde_json::Value;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value with unique object keys")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::Bool(value))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::Number(value.into()))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::Number(value.into()))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        let number = serde_json::Number::from_f64(value)
            .ok_or_else(|| E::custom("JSON number must be finite"))?;
        Ok(serde_json::Value::Number(number))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::String(value.to_string()))
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::String(value))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::Null)
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        Ok(serde_json::Value::Null)
    }

    fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::new();
        while let Some(value) = access.next_element_seed(NoDuplicateJsonSeed)? {
            values.push(value);
        }
        Ok(serde_json::Value::Array(values))
    }

    fn visit_map<A>(self, mut access: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut object = serde_json::Map::new();
        while let Some(key) = access.next_key::<String>()? {
            if object.contains_key(&key) {
                return Err(A::Error::custom(format!(
                    "duplicate JSON object key {key}"
                )));
            }
            let value = access.next_value_seed(NoDuplicateJsonSeed)?;
            object.insert(key, value);
        }
        Ok(serde_json::Value::Object(object))
    }
}

pub fn build_operation_support_estimate_from_archsig_measurement_packet(
    packet: &serde_json::Value,
    input_path: &str,
) -> Result<OperationSupportEstimateV0, Box<dyn std::error::Error>> {
    let schema_version = packet
        .get("schema")
        .or_else(|| packet.get("schema"))
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if schema_version != "archsig-measurement-packet/v0.5.4" {
        return Err(format!(
            "FieldSig ArchSig measurement handoff requires archsig-measurement-packet/v0.5.4, got {schema_version}"
        )
        .into());
    }
    validate_archsig_measurement_packet_handoff_shape(packet)?;

    let packet_id = packet
        .get("packetId")
        .and_then(|value| value.as_str())
        .unwrap_or("archsig-measurement-packet");
    let source_ref_ids = archsig_measurement_packet_sft_source_refs(packet, input_path);
    let action_class_candidate_ids = archsig_measurement_packet_action_candidate_ids(packet);
    let candidate_operation_families = archsig_measurement_packet_candidate_families(
        packet,
        &source_ref_ids,
        &action_class_candidate_ids,
    );
    let family_ids = candidate_operation_families
        .iter()
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();
    let non_conclusions = archsig_measurement_packet_sft_non_conclusions(packet);

    Ok(OperationSupportEstimateV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
        estimate_id: format!("estimate:archsig-measurement:{}", stable_id(packet_id)),
        descriptor_ref: OperationSupportDescriptorRefV0 {
            descriptor_schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
            descriptor_id: format!("descriptor:archsig-measurement:{packet_id}"),
            artifact_kind: "archsig-measurement-packet".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            action_class_candidate_ids: action_class_candidate_ids.clone(),
            non_conclusions: non_conclusions.clone(),
        },
        candidate_operation_families,
        policy_constraints: vec![OperationSupportPolicyConstraintV0 {
            constraint_id: "constraint:archsig-measurement:no-forecast-truth-promotion"
                .to_string(),
            constraint_kind: "claim-boundary".to_string(),
            applies_to_family_ids: family_ids.clone(),
            source_ref_ids: source_ref_ids.clone(),
            rule: "ArchSig measurement packet is current AG measurement state for SFT evolution input, not forecast truth".to_string(),
            safety_claim_boundary:
                "SFT consumes selected structural verdict, computed invariant, analytic reading, and assumption refs as bounded coordinates only"
                    .to_string(),
            policy_refs: vec!["policy:archsig-measurement-sft-boundary".to_string()],
            support_disposition: "conditionallyAllowed".to_string(),
            governance_action_refs: vec![
                "governance:review-archsig-measurement-handoff".to_string(),
            ],
            non_conclusions: non_conclusions.clone(),
        }],
        known_forbidden_support: vec![KnownForbiddenOperationSupportV0 {
            forbidden_id: "forbidden:raw-archmap-forecast-truth".to_string(),
            operation_family: "raw-archmap-truth-promotion".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            constraint_refs: vec![
                "constraint:archsig-measurement:no-forecast-truth-promotion".to_string(),
            ],
            reason: "ArchSig measurement packets do not assert SFT forecast correctness or raw ArchMap truth".to_string(),
            boundary: "FieldSig must keep measurement packet refs as bounded current AG structural state, not ground truth, causal proof, or diff analysis".to_string(),
            non_conclusions: non_conclusions.clone(),
        }],
        unknown_remainder: archsig_measurement_packet_unknown_remainders(
            packet,
            &family_ids,
            &source_ref_ids,
        ),
        evidence_boundary: OperationSupportEvidenceBoundaryV0 {
            boundary_id: format!("boundary:archsig-measurement:{}:sft-input", stable_id(packet_id)),
            source_ref_ids,
            measurement_boundary_refs: archsig_measurement_packet_measurement_boundary_refs(packet),
            confidence_boundary:
                "ArchSig measurement packet statuses are selected finite-measurement evidence, not probability"
                    .to_string(),
            evidence_kinds: vec![
                "archsig-measurement-packet/v0.5.4".to_string(),
                "measurement-profile/v0.5.4".to_string(),
                "structural-verdict".to_string(),
                "computed-invariant".to_string(),
                "analytic-reading".to_string(),
                "assumption-ledger".to_string(),
            ],
            unsupported_constructs: vec![
                "raw ArchMap observation completeness".to_string(),
                "SFT forecast correctness".to_string(),
                "causal repair safety".to_string(),
                "global architecture safety".to_string(),
            ],
            assumptions: vec![
                "FieldSig reads ArchSig measurement packet refs as current AG measurement state".to_string(),
                "PR, diff, change-vector, forecast, governance, and operational evolution remain FieldSig readings".to_string(),
                "analytic readings and theorem-candidate readings are retained as analytic state, not structural verdicts".to_string(),
                "not_computed verdicts and violated assumptions remain unknown remainder, not measured zero".to_string(),
            ],
            non_conclusions: archsig_measurement_packet_evidence_boundary_non_conclusions(packet),
        },
        non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
    })
}

fn json_path_string(packet: &serde_json::Value, path: &[&str], key: &str) -> Option<String> {
    let mut current = packet;
    for segment in path {
        current = current.get(*segment)?;
    }
    current.get(key)?.as_str().map(ToOwned::to_owned)
}

fn validate_archsig_measurement_packet_handoff_shape(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let schema = packet
        .get("schema")
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if schema != "archsig-measurement-packet/v0.5.4" {
        return Err(
            "FieldSig ArchSig measurement handoff requires archsig-measurement-packet/v0.5.4"
                .into(),
        );
    }
    let packet_id = packet
        .get("packetId")
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if packet_id.trim().is_empty() {
        return Err("FieldSig ArchSig measurement handoff requires non-empty packetId".into());
    }
    let fingerprints = packet
        .get("componentFingerprints")
        .and_then(|value| value.as_object())
        .ok_or("FieldSig ArchSig measurement handoff requires componentFingerprints object")?;
    let expected = BTreeSet::from(["lawPolicy", "lawSurface", "measurementProfile"]);
    let actual = fingerprints
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(
            "FieldSig ArchSig measurement handoff componentFingerprints must contain exactly lawPolicy, lawSurface, measurementProfile".into(),
        );
    }
    for component in expected {
        let fingerprint = fingerprints
            .get(component)
            .and_then(|value| value.as_str())
            .ok_or_else(|| format!("FieldSig ArchSig measurement handoff componentFingerprints.{component} must be a string"))?;
        if fingerprint.len() != 71
            || !fingerprint.starts_with("sha256:")
            || !fingerprint[7..]
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(format!(
                "FieldSig ArchSig measurement handoff componentFingerprints.{component} must be sha256:<64 hex chars>"
            ).into());
        }
    }
    let profile = packet
        .get("profile")
        .and_then(|value| value.as_object())
        .ok_or("FieldSig ArchSig measurement handoff requires profile object")?;
    if profile.get("schema").and_then(|value| value.as_str()) != Some("measurement-profile/v0.5.4")
    {
        return Err(
            "FieldSig ArchSig measurement handoff requires profile schema measurement-profile/v0.5.4"
                .into(),
        );
    }
    if profile.contains_key("witnessFamily") {
        return Err(
            "FieldSig ArchSig measurement handoff rejects profile witnessFamily; use the law-equation-surface input"
                .into(),
        );
    }
    validate_handoff_top_level_fields(packet)?;
    validate_handoff_nested_fields(packet)?;
    let profile_id = profile
        .get("profileId")
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if profile_id.trim().is_empty() {
        return Err("FieldSig ArchSig measurement handoff requires profile.profileId".into());
    }
    for key in [
        "structuralVerdict",
        "computedInvariants",
        "analyticReadings",
        "assumptions",
        "suppliedData",
        "boundaryStatements",
        "nonConclusions",
    ] {
        if !packet.get(key).is_some_and(|value| value.is_array()) {
            return Err(
                format!("FieldSig ArchSig measurement handoff requires {key} array").into(),
            );
        }
    }
    validate_archsig_measurement_packet_structural_verdicts(packet)?;
    validate_archsig_measurement_packet_computed_invariants(packet)?;
    validate_archsig_measurement_packet_analytic_readings(packet)?;
    validate_archsig_measurement_packet_assumptions(packet)?;
    validate_archsig_measurement_packet_supplied_data(packet)?;
    Ok(())
}

fn validate_archsig_measurement_packet_structural_verdicts(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let invariant_ids = archsig_measurement_computed_invariant_ids(packet).collect::<BTreeSet<_>>();
    let mut verdict_refs = BTreeSet::new();
    for (index, row) in packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let verdict_ref = required_string(row, "verdictRef").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        if !verdict_refs.insert(verdict_ref) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] duplicates verdictRef {verdict_ref}"
            )
            .into());
        }
        let evaluator = required_string(row, "evaluator").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        required_string(row, "law").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        let verdict = required_string(row, "verdict").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        if !matches!(
            verdict,
            "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
        ) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] has unsupported verdict {verdict}"
            )
            .into());
        }
        let data = row
            .get("verdictData")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] requires verdictData object"
                )
            })?;
        let zero = required_bool(data, "zero").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        let non_zero = required_bool(data, "nonZero").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        required_bool(data, "inScope").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        required_object_string(data, "methodStatus").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        let target = row
            .get("target")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] requires target object"
                )
            })?;
        for field in ["kind", "coverRef", "coefficient"] {
            required_object_string(target, field).map_err(|message| {
                format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] target {message}")
            })?;
        }
        target
            .get("scopeSize")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] target requires scopeSize object"
                )
            })?;
        let evidence = row
            .get("evidence")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] requires evidence object"
                )
            })?;
        evidence
            .get("computedInvariantRefs")
            .and_then(|value| value.as_array())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence requires computedInvariantRefs array"
                )
            })?;
        let computed_refs = required_unique_string_array(
            evidence,
            "computedInvariantRefs",
            &format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence"
            ),
        )?;
        for computed_ref in &computed_refs {
            if !invariant_ids.contains(computed_ref) {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence.computedInvariantRefs entry {computed_ref} does not resolve to computedInvariants[].invariantId"
                )
                .into());
            }
            if let Some(invariant_evaluator) =
                archsig_measurement_computed_invariant_evaluator(packet, computed_ref)
                && invariant_evaluator != evaluator
            {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence.computedInvariantRefs entry {computed_ref} has evaluator {invariant_evaluator}, expected {evaluator}"
                )
                .into());
            }
        }
        let source_refs = required_unique_string_array(
            evidence,
            "sourceRefs",
            &format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence"
            ),
        )?;
        if matches!(verdict, "measured_zero" | "measured_nonzero") && source_refs.is_empty() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} requires non-empty evidence.sourceRefs"
            )
            .into());
        }
        if zero && non_zero {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] for {evaluator} marks both zero and nonZero"
            )
            .into());
        }
        match verdict {
            "measured_zero" if !zero || non_zero => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] measured_zero requires zero=true and nonZero=false"
                )
                .into());
            }
            "measured_nonzero" if zero || !non_zero => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] measured_nonzero requires zero=false and nonZero=true"
                )
                .into());
            }
            "unknown" | "unmeasured" | "not_computed" if zero || non_zero => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} must not carry zero/nonZero measured flags"
                )
                .into());
            }
            _ => {}
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero") && computed_refs.is_empty() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} requires non-empty evidence.computedInvariantRefs"
            )
            .into());
        }
        if verdict == "measured_nonzero" {
            let class_ref = target
                .get("classRef")
                .and_then(|value| value.as_str())
                .unwrap_or_default();
            let resolves = invariant_ids.contains(class_ref)
                || class_ref
                    .strip_prefix("computedInvariants/")
                    .is_some_and(|id| invariant_ids.contains(id));
            if !resolves {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] measured_nonzero target.classRef {class_ref} does not resolve to computed invariant evidence"
                )
                .into());
            }
            let class_ref_id = class_ref
                .strip_prefix("computedInvariants/")
                .unwrap_or(class_ref);
            if let Some(invariant_evaluator) =
                archsig_measurement_computed_invariant_evaluator(packet, class_ref_id)
                && invariant_evaluator != evaluator
            {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] target.classRef has evaluator {invariant_evaluator}, expected {evaluator}"
                )
                .into());
            }
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero") {
            if let Some(cert_ref) = data.get("certRef").and_then(|value| value.as_str()) {
                let cert_ref_id = cert_ref
                    .strip_prefix("computedInvariants/")
                    .unwrap_or(cert_ref);
                if let Some(invariant_evaluator) =
                    archsig_measurement_computed_invariant_evaluator(packet, cert_ref_id)
                    && invariant_evaluator != evaluator
                {
                    return Err(format!(
                        "FieldSig ArchSig measurement handoff structuralVerdict[{index}] certRef has evaluator {invariant_evaluator}, expected {evaluator}"
                    )
                    .into());
                }
            }
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero")
            && !archsig_measurement_verdict_has_evidence(packet, row, evaluator)
        {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} requires certRef or matching computed invariant evidence"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_archsig_measurement_packet_computed_invariants(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut invariant_ids = BTreeSet::new();
    for (index, row) in packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        for field in ["invariantId", "kind"] {
            required_string(row, field).map_err(|message| {
                format!(
                    "FieldSig ArchSig measurement handoff computedInvariants[{index}] {message}"
                )
            })?;
        }
        let invariant_id = row["invariantId"].as_str().unwrap_or_default();
        if !invariant_ids.insert(invariant_id) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] duplicates invariantId {invariant_id}"
            )
            .into());
        }
        let kind = row["kind"].as_str().unwrap_or_default();
        if !ARCHSIG_COMPUTED_INVARIANT_KINDS.contains(&kind) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] has unsupported kind {kind}"
            )
            .into());
        }
        if row.get("value").is_none() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] requires value"
            )
            .into());
        }
        if row.get("representation").is_none() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] requires representation"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_archsig_measurement_packet_analytic_readings(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut reading_ids = BTreeSet::new();
    for (index, row) in packet
        .get("analyticReadings")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let reading_id = required_string(row, "readingId").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        if !reading_ids.insert(reading_id) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff analyticReadings[{index}] duplicates readingId {reading_id}"
            )
            .into());
        }
        required_string(row, "evaluator").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        let claim_status = required_string(row, "claimStatus").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        if !matches!(claim_status, "certified" | "candidate") {
            return Err(format!(
                "FieldSig ArchSig measurement handoff analyticReadings[{index}] has unsupported claimStatus {claim_status}"
            )
            .into());
        }
        let fidelity = required_string(row, "fidelity").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        if !matches!(fidelity, "faithful" | "proxy") {
            return Err(format!(
                "FieldSig ArchSig measurement handoff analyticReadings[{index}] has unsupported fidelity {fidelity}"
            )
            .into());
        }
    }
    Ok(())
}

fn archsig_measurement_verdict_has_evidence(
    packet: &serde_json::Value,
    row: &serde_json::Value,
    evaluator: &str,
) -> bool {
    let invariant_ids = archsig_measurement_computed_invariant_ids(packet).collect::<BTreeSet<_>>();
    if let Some(cert_ref) = row
        .get("verdictData")
        .and_then(|data| data.get("certRef"))
        .and_then(|value| value.as_str())
    {
        let cert_ref = cert_ref.trim();
        if cert_ref.is_empty() {
            return false;
        }
        return cert_ref
            .strip_prefix("computedInvariants/")
            .is_some_and(|invariant_id| invariant_ids.contains(invariant_id));
    }
    let computed_refs = row["evidence"]["computedInvariantRefs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str())
        .collect::<Vec<_>>();
    if !computed_refs.is_empty() {
        return computed_refs.iter().all(|id| invariant_ids.contains(id));
    }
    let certificate_prefixes = archsig_measurement_certificate_invariant_prefixes(evaluator);
    packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .any(|invariant| {
            invariant
                .get("evaluator")
                .and_then(|value| value.as_str())
                .is_some_and(|value| value == evaluator)
                && ["invariantId", "readingId", "id"].iter().any(|key| {
                    invariant
                        .get(*key)
                        .and_then(|value| value.as_str())
                        .is_some_and(|value| {
                            let value = value.trim();
                            if value.is_empty() {
                                return false;
                            }
                            certificate_prefixes
                                .map(|prefixes| {
                                    prefixes.iter().any(|prefix| value.starts_with(prefix))
                                })
                                .unwrap_or(true)
                        })
                })
        })
}

fn archsig_measurement_computed_invariant_ids(
    packet: &serde_json::Value,
) -> impl Iterator<Item = &str> {
    packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .flat_map(|invariant| {
            ["invariantId", "readingId", "id"]
                .into_iter()
                .filter_map(|key| {
                    invariant
                        .get(key)
                        .and_then(|value| value.as_str())
                        .map(str::trim)
                        .filter(|value| !value.is_empty())
                })
        })
}

fn archsig_measurement_computed_invariant_evaluator(
    packet: &serde_json::Value,
    reference: &str,
) -> Option<String> {
    packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .find(|invariant| {
            ["invariantId", "readingId", "id"].iter().any(|key| {
                invariant
                    .get(*key)
                    .and_then(|value| value.as_str())
                    .is_some_and(|value| value == reference)
            })
        })
        .and_then(|invariant| invariant.get("evaluator"))
        .and_then(|value| value.as_str())
        .map(ToOwned::to_owned)
}

fn archsig_measurement_certificate_invariant_prefixes(
    evaluator: &str,
) -> Option<&'static [&'static str]> {
    match evaluator {
        "ag.cech-obstruction" => Some(&["cech-cohomology:"]),
        "ag.law-conflict-tor" => Some(&["law-conflict-tor:"]),
        "ag.square-free-repair" => Some(&["square-free-repair:"]),
        "ag.restriction-compatibility" => Some(&["restriction-compatibility:"]),
        "ag.section-factorization" => Some(&["section-factorization:"]),
        "ag.boundary-residue" => Some(&["boundary-residue:"]),
        "ag.coherence-obstruction" => Some(&["coherence-obstruction:"]),
        _ => None,
    }
}

fn validate_archsig_measurement_packet_assumptions(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut assumption_ids = BTreeSet::new();
    let mut violated_assumption_ids = BTreeSet::new();
    for (index, row) in packet
        .get("assumptions")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let assumption_id = required_string(row, "assumptionId").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        let _theorem_ref = required_string(row, "theoremRef").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        if !assumption_ids.insert(assumption_id.to_string()) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff assumptions[{index}] duplicates assumptionId {assumption_id}"
            )
            .into());
        }
        required_string(row, "assumption").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        let status = required_string(row, "status").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        match status {
            "checked" => {
                required_string(row, "checkedBy").map_err(|message| {
                    format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
                })?;
            }
            "assumed" => {
                required_string(row, "assumedBy").map_err(|message| {
                    format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
                })?;
            }
            "violated" => {
                violated_assumption_ids.insert(assumption_id.to_string());
            }
            _ => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff assumptions[{index}] has unsupported status {status}"
                )
                .into());
            }
        }
    }
    for (index, row) in packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let verdict = row
            .get("verdict")
            .and_then(|value| value.as_str())
            .unwrap_or_default();
        for dependency in row
            .get("dependsOnAssumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|value| value.as_str())
        {
            if !assumption_ids.contains(dependency) {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] dependsOnAssumptions entry {dependency} does not resolve to an assumptionId"
                )
                .into());
            }
            if matches!(verdict, "measured_zero" | "measured_nonzero")
                && violated_assumption_ids.contains(dependency)
            {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] keeps measured verdict while depending on violated assumption {dependency}"
                )
                .into());
            }
        }
    }
    Ok(())
}

fn validate_archsig_measurement_packet_supplied_data(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let supplied = packet
        .get("suppliedData")
        .and_then(|value| value.as_array())
        .ok_or("FieldSig ArchSig measurement handoff requires suppliedData array")?;
    if supplied.is_empty() {
        return Err(
            "FieldSig ArchSig measurement handoff requires non-empty suppliedData ledger".into(),
        );
    }
    let mut supplied_ids = BTreeSet::new();
    let mut supplied_kinds = BTreeSet::new();
    for (index, row) in supplied.iter().enumerate() {
        let supplied_id = required_string(row, "suppliedId").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff suppliedData[{index}] {message}")
        })?;
        if !supplied_ids.insert(supplied_id) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData[{index}] duplicates suppliedId {supplied_id}"
            )
            .into());
        }
        let _source_artifact_ref = required_string(row, "sourceArtifactRef").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff suppliedData[{index}] {message}")
        })?;
        let kind = required_string(row, "kind").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff suppliedData[{index}] {message}")
        })?;
        if !supplied_kinds.insert(kind) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData[{index}] duplicates kind {kind}"
            )
            .into());
        }
        if !ARCHSIG_SUPPLIED_DATA_KINDS.contains(&kind) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData[{index}] has unsupported kind {kind}"
            )
            .into());
        }
        let conformance = row
            .get("conformance")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff suppliedData[{index}] requires conformance object"
                )
            })?;
        let status = conformance
            .get("status")
            .and_then(|value| value.as_str())
            .unwrap_or_default();
        if status.trim().is_empty() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData[{index}] requires conformance.status"
            )
            .into());
        }
    }
    for required_kind in [
        "archmap",
        "law-policy",
        "law-equation-surface",
        "measurement-profile",
    ] {
        if !supplied_kinds.contains(required_kind) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData is missing required kind {required_kind}"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_handoff_top_level_fields(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    const ALLOWED_FIELDS: &[&str] = &[
        "schema",
        "packetId",
        "profile",
        "profiles",
        "structuralVerdict",
        "computedInvariants",
        "analyticReadings",
        "assumptions",
        "suppliedData",
        "boundaryStatements",
        "nonConclusions",
        "toolVersion",
        "runId",
        "inputDigests",
        "componentFingerprints",
    ];
    let object = packet
        .as_object()
        .ok_or("FieldSig ArchSig measurement handoff requires a top-level object")?;
    if let Some(unknown) = object
        .keys()
        .find(|key| !ALLOWED_FIELDS.contains(&key.as_str()))
    {
        return Err(format!(
            "FieldSig ArchSig measurement handoff rejects unknown top-level field {unknown}"
        )
        .into());
    }
    Ok(())
}

fn validate_handoff_nested_fields(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    const PROFILE_FIELDS: &[&str] = &[
        "schema",
        "profileId",
        "siteRef",
        "coverRef",
        "coefficient",
        "effCoeff",
        "resolutionSelector",
        "domain",
        "zeroPredicate",
        "nonZeroPredicate",
        "certSelector",
        "verdictDiscipline",
        "diagnosticCeiling",
        "analytic",
        "finiteBounds",
    ];
    const STRUCTURAL_FIELDS: &[&str] = &[
        "verdictRef",
        "evaluator",
        "law",
        "target",
        "verdict",
        "verdictData",
        "dependsOnAssumptions",
        "evidence",
        "reason",
    ];
    const TARGET_FIELDS: &[&str] = &[
        "kind",
        "coverRef",
        "coefficient",
        "scopeSize",
        "classRef",
    ];
    const SCOPE_FIELDS: &[&str] = &["contexts", "edges", "triangles"];
    const VERDICT_DATA_FIELDS: &[&str] = &[
        "inScope",
        "zero",
        "nonZero",
        "methodStatus",
        "certRef",
    ];
    const EVIDENCE_FIELDS: &[&str] = &["computedInvariantRefs", "sourceRefs"];
    const READING_FIELDS: &[&str] = &[
        "readingId",
        "evaluator",
        "claimStatus",
        "fidelity",
        "value",
        "regime",
        "structuralVerdictRef",
    ];
    const ASSUMPTION_FIELDS: &[&str] = &[
        "assumptionId",
        "theoremRef",
        "assumption",
        "status",
        "checkedBy",
        "assumedBy",
        "scopeRefs",
    ];
    const SUPPLIED_FIELDS: &[&str] = &[
        "suppliedId",
        "kind",
        "sourceArtifactRef",
        "conformance",
    ];
    const CONFORMANCE_FIELDS: &[&str] = &["status", "checkRef", "boundary"];
    const BOUNDARY_FIELDS: &[&str] = &["id", "kind", "scopeRefs", "reason", "text"];

    reject_unknown_object_fields(packet.get("profile"), "profile", PROFILE_FIELDS)?;
    if let Some(profiles) = packet.get("profiles").and_then(|value| value.as_array()) {
        for (index, profile) in profiles.iter().enumerate() {
            reject_unknown_object_fields(
                Some(profile),
                &format!("profiles[{index}]"),
                PROFILE_FIELDS,
            )?;
        }
    }
    for (index, row) in packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let prefix = format!("structuralVerdict[{index}]");
        reject_unknown_object_fields(Some(row), &prefix, STRUCTURAL_FIELDS)?;
        reject_unknown_object_fields(row.get("target"), &format!("{prefix}.target"), TARGET_FIELDS)?;
        reject_unknown_object_fields(
            row.get("target").and_then(|target| target.get("scopeSize")),
            &format!("{prefix}.target.scopeSize"),
            SCOPE_FIELDS,
        )?;
        reject_unknown_object_fields(
            row.get("verdictData"),
            &format!("{prefix}.verdictData"),
            VERDICT_DATA_FIELDS,
        )?;
        reject_unknown_object_fields(
            row.get("evidence"),
            &format!("{prefix}.evidence"),
            EVIDENCE_FIELDS,
        )?;
    }
    for (index, row) in packet
        .get("analyticReadings")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        reject_unknown_object_fields(
            Some(row),
            &format!("analyticReadings[{index}]"),
            READING_FIELDS,
        )?;
    }
    for (index, row) in packet
        .get("assumptions")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        reject_unknown_object_fields(
            Some(row),
            &format!("assumptions[{index}]"),
            ASSUMPTION_FIELDS,
        )?;
    }
    for (index, row) in packet
        .get("suppliedData")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        reject_unknown_object_fields(
            Some(row),
            &format!("suppliedData[{index}]"),
            SUPPLIED_FIELDS,
        )?;
        reject_unknown_object_fields(
            row.get("conformance"),
            &format!("suppliedData[{index}].conformance"),
            CONFORMANCE_FIELDS,
        )?;
    }
    for (index, row) in packet
        .get("boundaryStatements")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        reject_unknown_object_fields(
            Some(row),
            &format!("boundaryStatements[{index}]"),
            BOUNDARY_FIELDS,
        )?;
    }
    Ok(())
}

fn reject_unknown_object_fields(
    value: Option<&serde_json::Value>,
    path: &str,
    allowed: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    let Some(object) = value.and_then(|value| value.as_object()) else {
        return Ok(());
    };
    if let Some(unknown) = object.keys().find(|key| !allowed.contains(&key.as_str())) {
        return Err(format!(
            "FieldSig ArchSig measurement handoff rejects unknown field {path}.{unknown}"
        )
        .into());
    }
    Ok(())
}

fn required_unique_string_array<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    key: &str,
    path: &str,
) -> Result<Vec<&'a str>, Box<dyn std::error::Error>> {
    let values = object
        .get(key)
        .and_then(|value| value.as_array())
        .ok_or_else(|| format!("{path} requires {key} array"))?;
    let mut seen = BTreeSet::new();
    let mut result = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        let reference = value
            .as_str()
            .filter(|reference| !reference.trim().is_empty())
            .ok_or_else(|| format!("{path}.{key}[{index}] requires non-empty string"))?;
        if !seen.insert(reference) {
            return Err(format!("{path}.{key}[{index}] duplicates {reference}").into());
        }
        result.push(reference);
    }
    Ok(result)
}

fn required_string<'a>(
    object: &'a serde_json::Value,
    key: &str,
) -> Result<&'a str, Box<dyn std::error::Error>> {
    object
        .get(key)
        .and_then(|value| value.as_str())
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| format!("requires non-empty {key}").into())
}

fn required_bool(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<bool, Box<dyn std::error::Error>> {
    object
        .get(key)
        .and_then(|value| value.as_bool())
        .ok_or_else(|| format!("requires boolean verdictData.{key}").into())
}

fn required_object_string<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<&'a str, Box<dyn std::error::Error>> {
    object
        .get(key)
        .and_then(|value| value.as_str())
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| format!("requires non-empty verdictData.{key}").into())
}

fn archsig_measurement_packet_sft_source_refs(
    packet: &serde_json::Value,
    input_path: &str,
) -> Vec<String> {
    let mut refs = vec![format!(
        "source:archsig-measurement-packet:{}",
        stable_input_ref(input_path)
    )];
    if let Some(packet_id) = packet.get("packetId").and_then(|value| value.as_str()) {
        refs.push(format!("archsigMeasurementPacket:{packet_id}"));
    }
    if let Some(profile_id) = json_path_string(packet, &["profile"], "profileId") {
        refs.push(format!("archsigMeasurementProfile:{profile_id}"));
    }
    if let Some(fingerprints) = packet
        .get("componentFingerprints")
        .and_then(|value| value.as_object())
    {
        for component in ["lawPolicy", "lawSurface", "measurementProfile"] {
            if let Some(fingerprint) = fingerprints.get(component).and_then(|value| value.as_str())
            {
                refs.push(format!(
                    "archsigMeasurementComponentFingerprint:{component}:{fingerprint}"
                ));
            }
        }
    }
    refs.extend(
        packet
            .get("suppliedData")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|entry| entry.get("sourceArtifactRef").and_then(|value| value.as_str()))
            .map(sanitize_artifact_ref),
    );
    refs.extend(
        packet
            .get("suppliedData")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter(|entry| {
                entry.get("kind").and_then(|value| value.as_str()) == Some("law-equation-surface")
            })
            .filter_map(|entry| {
                entry
                    .get("sourceArtifactRef")
                    .and_then(|value| value.as_str())
                    .map(|source| {
                        format!(
                            "archsigMeasurementLawSurface:{}",
                            sanitize_artifact_ref(source)
                        )
            })
            }),
    );
    refs.extend(
        packet
            .get("structuralVerdict")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|verdict| {
                let mut refs = Vec::new();
                refs.extend(
                    verdict
                        .get("evidence")
                        .and_then(|evidence| evidence.get("sourceRefs"))
                        .and_then(|value| value.as_array())
                        .into_iter()
                        .flatten()
                        .filter_map(|value| value.as_str())
                        .map(sanitize_artifact_ref),
                );
                if let Some(verdict_ref) =
                    verdict.get("verdictRef").and_then(|value| value.as_str())
                {
                    refs.push(format!("archsigMeasurementStructuralVerdict:{verdict_ref}"));
                }
                if let Some(evaluator) = verdict.get("evaluator").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementStructuralEvaluator:{evaluator}"));
                }
                if let Some(law) = verdict.get("law").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementStructuralLaw:{law}"));
                }
                if let Some(cert_ref) = verdict
                    .get("verdictData")
                    .and_then(|data| data.get("certRef"))
                    .and_then(|value| value.as_str())
                {
                    refs.push(format!("archsigMeasurementCert:{cert_ref}"));
                }
                refs
            }),
    );
    refs.extend(
        packet
            .get("computedInvariants")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|invariant| {
                let mut refs = Vec::new();
                refs.extend(
                    invariant
                        .get("sourceRefs")
                        .and_then(|value| value.as_array())
                        .into_iter()
                        .flatten()
                        .filter_map(|value| value.as_str())
                        .map(sanitize_artifact_ref),
                );
                for key in ["invariantId", "readingId", "id"] {
                    if let Some(id) = invariant.get(key).and_then(|value| value.as_str()) {
                        refs.push(format!("archsigMeasurementComputedInvariant:{id}"));
                    }
                }
                if let Some(evaluator) = invariant.get("evaluator").and_then(|value| value.as_str())
                {
                    refs.push(format!("archsigMeasurementComputedEvaluator:{evaluator}"));
                }
                refs
            }),
    );
    refs.extend(
        packet
            .get("analyticReadings")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|reading| {
                let mut refs = Vec::new();
                if let Some(id) = reading.get("readingId").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementAnalyticReading:{id}"));
                }
                if let Some(evaluator) = reading.get("evaluator").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementAnalyticEvaluator:{evaluator}"));
                }
                refs
            }),
    );
    refs.extend(
        packet
            .get("assumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|assumption| {
                let assumption_id = assumption.get("assumptionId")?.as_str()?;
                let status = assumption
                    .get("status")
                    .and_then(|value| value.as_str())
                    .unwrap_or("unknown");
                Some(format!(
                    "archsigMeasurementAssumption:{assumption_id}:{status}"
                ))
            }),
    );
    refs.extend(
        packet
            .get("boundaryStatements")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|boundary| {
                let mut refs = Vec::new();
                if let Some(id) = boundary.get("id").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryStatement:{id}"));
                }
                if let Some(kind) = boundary.get("kind").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryKind:{kind}"));
                }
                refs
            }),
    );
    unique_strings(refs)
}

fn stable_input_ref(input_path: &str) -> String {
    Path::new(input_path)
        .file_name()
        .and_then(|name| name.to_str())
        .filter(|name| !name.is_empty())
        .map(|name| format!("input:{name}"))
        .unwrap_or_else(|| "input:archsig-measurement-packet.json".to_string())
}

fn sanitize_artifact_ref(reference: &str) -> String {
    if is_local_or_private_ref(reference) {
        "artifact-ref:redacted-local-path".to_string()
    } else {
        reference.to_string()
    }
}

fn is_local_or_private_ref(reference: &str) -> bool {
    reference.starts_with('/')
        || reference.starts_with("~/")
        || reference.starts_with("../")
        || reference.contains("/../")
        || reference.contains('\\')
        || (reference.len() >= 3
            && reference.as_bytes()[0].is_ascii_alphabetic()
            && reference.as_bytes()[1] == b':'
            && matches!(reference.as_bytes()[2], b'/' | b'\\'))
        || reference
            .split(['/', '\\'])
            .any(|segment| segment.starts_with('.') && segment != "." && segment != "..")
}

fn archsig_measurement_packet_action_candidate_ids(packet: &serde_json::Value) -> Vec<String> {
    let mut ids = json_object_string_array(packet, &["structuralVerdict"], "evaluator");
    ids.extend(json_object_string_array(
        packet,
        &["structuralVerdict"],
        "law",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["computedInvariants"],
        "evaluator",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["analyticReadings"],
        "evaluator",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["computedInvariants"],
        "invariantId",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["analyticReadings"],
        "readingId",
    ));
    if ids.is_empty() {
        ids.push(
            packet
                .get("packetId")
                .and_then(|value| value.as_str())
                .unwrap_or("archsig-measurement-packet")
                .to_string(),
        );
    }
    unique_strings(ids)
}

fn archsig_measurement_packet_candidate_families(
    packet: &serde_json::Value,
    source_ref_ids: &[String],
    action_class_candidate_ids: &[String],
) -> Vec<CandidateOperationFamilyV0> {
    let non_conclusions = archsig_measurement_packet_sft_non_conclusions(packet);
    let mut families = packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, row)| {
            let evaluator = row
                .get("evaluator")
                .and_then(|value| value.as_str())
                .unwrap_or("ag-structural-evaluator");
            let law = row
                .get("law")
                .and_then(|value| value.as_str())
                .unwrap_or("selected-ag-law");
            let verdict = row
                .get("verdict")
                .and_then(|value| value.as_str())
                .unwrap_or("not_computed");
            let row_key = archsig_measurement_structural_row_key(index, row);
            CandidateOperationFamilyV0 {
                family_id: format!("family:archsig-measurement:{}", stable_id(&row_key)),
                operation_family: format!("review-ag-structural-{verdict}"),
                support_kind: "measurement-packet-structural-verdict".to_string(),
                action_class_candidate_ids: vec![evaluator.to_string(), law.to_string()],
                source_ref_ids: archsig_measurement_packet_row_source_refs(row, source_ref_ids),
                confidence: if matches!(verdict, "measured_zero" | "measured_nonzero") {
                    "medium"
                } else {
                    "low"
                }
                .to_string(),
                rationale:
                    "structural verdict is read from ArchSig measurement packet as current AG measurement state"
                        .to_string(),
                assumptions: Vec::new(),
                non_conclusions: non_conclusions.clone(),
            }
        })
        .collect::<Vec<_>>();
    families.extend(
        packet
            .get("analyticReadings")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|reading| {
                let reading_id = reading.get("readingId")?.as_str()?;
                let evaluator = reading
                    .get("evaluator")
                    .and_then(|value| value.as_str())
                    .unwrap_or("ag-analytic-evaluator");
                let regime = reading
                    .get("regime")
                    .and_then(|value| value.as_str())
                    .unwrap_or("analytic");
                Some(CandidateOperationFamilyV0 {
                    family_id: format!(
                        "family:archsig-measurement-analytic:{}",
                        stable_id(reading_id)
                    ),
                    operation_family: format!("review-ag-analytic-{regime}"),
                    support_kind: "measurement-packet-analytic-reading".to_string(),
                    action_class_candidate_ids: vec![reading_id.to_string(), evaluator.to_string()],
                    source_ref_ids: source_ref_ids.to_vec(),
                    confidence: "low".to_string(),
                    rationale:
                        "analytic reading is retained as bounded measurement state, not converted into a structural verdict"
                            .to_string(),
                    assumptions: Vec::new(),
                    non_conclusions: non_conclusions.clone(),
                })
            }),
    );
    if families.is_empty() {
        families.push(CandidateOperationFamilyV0 {
            family_id: "family:archsig-measurement-review-only".to_string(),
            operation_family: "review-selected-archsig-measurement".to_string(),
            support_kind: "measurement-packet-review-boundary".to_string(),
            action_class_candidate_ids: action_class_candidate_ids.to_vec(),
            source_ref_ids: source_ref_ids.to_vec(),
            confidence: "low".to_string(),
            rationale:
                "no structural verdict or analytic reading is present; FieldSig keeps the packet as review input"
                    .to_string(),
            assumptions: vec!["selected MeasurementProfile may not cover all future SFT axes"
                .to_string()],
            non_conclusions,
        });
    }
    families
}

fn archsig_measurement_packet_row_source_refs(
    row: &serde_json::Value,
    packet_source_ref_ids: &[String],
) -> Vec<String> {
    let mut refs = row
        .get("evidence")
        .and_then(|evidence| evidence.get("sourceRefs"))
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str())
        .map(sanitize_artifact_ref)
        .collect::<Vec<_>>();
    refs.extend(
        packet_source_ref_ids
            .iter()
            .filter(|reference| reference.starts_with("source:archsig-measurement-packet:"))
            .cloned(),
    );
    unique_strings(refs)
}

fn archsig_measurement_structural_row_key(index: usize, row: &serde_json::Value) -> String {
    let evaluator = row
        .get("evaluator")
        .and_then(|value| value.as_str())
        .unwrap_or("ag-structural-evaluator");
    let law = row
        .get("law")
        .and_then(|value| value.as_str())
        .unwrap_or("selected-ag-law");
    let verdict = row
        .get("verdict")
        .and_then(|value| value.as_str())
        .unwrap_or("not_computed");
    let cert_ref = row
        .get("verdictData")
        .and_then(|value| value.get("certRef"))
        .and_then(|value| value.as_str())
        .unwrap_or("no-cert");
    format!("{index}:{evaluator}:{law}:{verdict}:{cert_ref}")
}

fn archsig_measurement_packet_unknown_remainders(
    packet: &serde_json::Value,
    family_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<OperationSupportUnknownRemainderV0> {
    let mut remainders = Vec::new();
    remainders.extend(
        packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
        .filter_map(|(index, row)| {
            let verdict = row.get("verdict")?.as_str()?;
            if !matches!(verdict, "not_computed" | "unknown" | "unmeasured") {
                return None;
            }
                let evaluator = row
                    .get("evaluator")
                    .and_then(|value| value.as_str())
                    .unwrap_or("ag-structural-evaluator");
                let reason = row
                .get("reason")
                .and_then(|value| value.as_str())
                .unwrap_or("structural verdict is outside the selected finite measurement boundary");
            let row_key = archsig_measurement_structural_row_key(index, row);
            Some(OperationSupportUnknownRemainderV0 {
                remainder_id: format!(
                    "unknown:archsig-measurement:structural:{}",
                    stable_id(&row_key)
                ),
                    affected_family_ids: family_ids.to_vec(),
                    source_ref_ids: source_ref_ids.to_vec(),
                    unknown_axes: vec![verdict.to_string()],
                    reason: format!("ArchSig measurement evaluator {evaluator} returned {verdict}: {reason}"),
                    treatment: "carry as unknown remainder; do not round to absence, zero-valued support, forecast truth, or repair safety".to_string(),
                    non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
                })
            }),
    );
    remainders.extend(
        packet
            .get("computedInvariants")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|invariant| {
                let status = invariant.get("status")?.as_str()?;
                if status != "not_computed" {
                    return None;
                }
                let id = invariant
                    .get("invariantId")
                    .or_else(|| invariant.get("id"))
                    .and_then(|value| value.as_str())
                    .unwrap_or("computed-invariant");
                Some(OperationSupportUnknownRemainderV0 {
                    remainder_id: format!(
                        "unknown:archsig-measurement:computed:{}",
                        stable_id(id)
                    ),
                    affected_family_ids: family_ids.to_vec(),
                    source_ref_ids: source_ref_ids.to_vec(),
                    unknown_axes: vec!["computedInvariant:not_computed".to_string()],
                    reason: format!("ArchSig measurement computed invariant {id} is not_computed"),
                    treatment: "carry as unknown remainder; do not synthesize zero analytic or structural support".to_string(),
                    non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
                })
            }),
    );
    remainders.extend(
        packet
            .get("assumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .enumerate()
            .filter_map(|(index, assumption)| {
                let status = assumption.get("status")?.as_str()?;
                if status == "checked" {
                    return None;
                }
                let assumption_id = assumption
                    .get("assumptionId")
                    .and_then(|value| value.as_str())
                    .unwrap_or("assumption");
                let theorem_ref = assumption
                    .get("theoremRef")
                    .and_then(|value| value.as_str())
                    .unwrap_or("assumption");
                let assumption_text = assumption
                    .get("assumption")
                    .and_then(|value| value.as_str())
                    .unwrap_or("assumption");
                let assumption_key = format!("{index}:{assumption_id}:{theorem_ref}:{assumption_text}:{status}");
                Some(OperationSupportUnknownRemainderV0 {
                    remainder_id: format!(
                        "unknown:archsig-measurement:assumption:{}",
                        stable_id(&assumption_key)
                    ),
                    affected_family_ids: family_ids.to_vec(),
                    source_ref_ids: source_ref_ids.to_vec(),
                    unknown_axes: vec![format!("assumption:{status}")],
                    reason: format!("ArchSig measurement assumption {assumption_id} ({theorem_ref}) is {status}: {assumption_text}"),
                    treatment: "retain assumption status as boundary data; do not promote it to proof, forecast truth, or repair safety".to_string(),
                    non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
                })
            }),
    );
    remainders.push(OperationSupportUnknownRemainderV0 {
        remainder_id: "unknown:archsig-measurement:fieldsig-evolution-boundary".to_string(),
        affected_family_ids: family_ids.to_vec(),
        source_ref_ids: source_ref_ids.to_vec(),
        unknown_axes: vec![
            "PR diff evidence".to_string(),
            "workflow history".to_string(),
            "operational outcome".to_string(),
            "unselected laws outside MeasurementProfile".to_string(),
        ],
        reason:
            "ArchSig measurement packet records current AG measurement state, not FieldSig evolution evidence"
                .to_string(),
        treatment:
            "retain as FieldSig-side unknown remainder; require separate workflow evidence before forecast or governance readings"
                .to_string(),
        non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
    });
    remainders
}

fn archsig_measurement_packet_measurement_boundary_refs(packet: &serde_json::Value) -> Vec<String> {
    let mut refs = Vec::new();
    if let Some(profile_id) = json_path_string(packet, &["profile"], "profileId") {
        refs.push(format!("archsigMeasurementProfile:{profile_id}"));
    }
    refs.extend(
        packet
            .get("structuralVerdict")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|row| {
                let evaluator = row.get("evaluator")?.as_str()?;
                let verdict = row
                    .get("verdict")
                    .and_then(|value| value.as_str())
                    .unwrap_or("unknown");
                Some(format!("archsigMeasurementVerdict:{evaluator}:{verdict}"))
            }),
    );
    refs.extend(
        packet
            .get("computedInvariants")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|invariant| {
                let id = invariant
                    .get("invariantId")
                    .or_else(|| invariant.get("id"))?
                    .as_str()?;
                let status = invariant
                    .get("status")
                    .and_then(|value| value.as_str())
                    .unwrap_or("computed");
                Some(format!("archsigMeasurementInvariant:{id}:{status}"))
            }),
    );
    refs.extend(
        packet
            .get("analyticReadings")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|reading| {
                let id = reading.get("readingId")?.as_str()?;
                let regime = reading
                    .get("regime")
                    .and_then(|value| value.as_str())
                    .unwrap_or("analytic");
                Some(format!("archsigMeasurementAnalytic:{id}:{regime}"))
            }),
    );
    refs.extend(
        packet
            .get("assumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|assumption| {
                let assumption_id = assumption.get("assumptionId")?.as_str()?;
                let status = assumption
                    .get("status")
                    .and_then(|value| value.as_str())
                    .unwrap_or("unknown");
                Some(format!(
                    "archsigMeasurementAssumptionBoundary:{assumption_id}:{status}"
                ))
            }),
    );
    refs.extend(
        packet
            .get("boundaryStatements")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|boundary| {
                let mut refs = Vec::new();
                if let Some(id) = boundary.get("id").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryStatement:{id}"));
                }
                if let Some(kind) = boundary.get("kind").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryKind:{kind}"));
                }
                if let Some(scope_refs) =
                    boundary.get("scopeRefs").and_then(|value| value.as_array())
                {
                    refs.extend(scope_refs.iter().filter_map(|scope| {
                        scope
                            .as_str()
                            .map(|scope| format!("archsigMeasurementBoundaryScope:{scope}"))
                    }));
                }
                refs
            }),
    );
    unique_strings(refs)
}

fn archsig_measurement_packet_sft_non_conclusions(packet: &serde_json::Value) -> Vec<String> {
    let mut values = json_string_array(packet, &["nonConclusions"]);
    values.extend(
        OPERATION_SUPPORT_REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string()),
    );
    values.extend([
        "ArchSig measurement packet is FieldSig input state, not forecast correctness".to_string(),
        "raw ArchMap observations are not promoted to SFT ground truth".to_string(),
        "analytic readings are not converted into structural verdicts".to_string(),
        "not_computed measurements and violated assumptions are unknown remainder, not measured zero".to_string(),
        "FieldSig handoff does not prove causal correctness, repair safety, or global architecture safety".to_string(),
    ]);
    unique_strings(values)
}

fn archsig_measurement_packet_evidence_boundary_non_conclusions(
    packet: &serde_json::Value,
) -> Vec<String> {
    let mut values = json_string_array(packet, &["nonConclusions"]);
    values.extend(
        OPERATION_SUPPORT_EVIDENCE_BOUNDARY_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string()),
    );
    values.extend([
        "ArchSig measurement packet evidence boundary does not complete ArchMap observation coverage".to_string(),
        "FieldSig handoff evidence boundary does not prove forecast correctness".to_string(),
        "unsupported constructs remain outside the selected measurement profile".to_string(),
    ]);
    unique_strings(values)
}

pub fn archmap_lean_preservation_vocabulary() -> Vec<ArchMapLeanPreservationVocabularyEntry> {
    vec![
        lean_vocabulary_entry(
            "archmap-object-preservation",
            "mappingKind=object or targetRef.kind=air-component",
            "ObjectPreservation",
            "selected ArchMap object candidate preserves a bounded Lean object field",
        ),
        lean_vocabulary_entry(
            "archmap-relation-preservation",
            "mappingKind=relation or targetRef.kind=air-relation",
            "RelationPreservation",
            "selected ArchMap relation candidate preserves a bounded Lean relation field",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-diagram-preservation",
            "mappingKind=semanticDiagram or targetRef.kind=semantic-diagram",
            "SemanticDiagramPreservation",
            "selected semantic diagram candidate preserves a bounded diagram field",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-commutation-preservation",
            "mappingKind=semanticCommutationClaim",
            "SemanticCommutationPreservation",
            "selected commutation claim candidate is tracked without proving commutation",
        ),
        lean_vocabulary_entry(
            "archmap-nonfillability-witness-preservation",
            "mappingKind=nonfillabilityWitness or targetRef.kind=nonfillability-witness",
            "NonfillabilityWitnessPreservation",
            "selected non-fillability witness candidate is preserved as review evidence",
        ),
        lean_vocabulary_entry(
            "archmap-law-policy-preservation",
            "mappingKind=policyBoundary, targetRef.layer=policy, or preserves[] contains Layered Architecture / SRP responsibility",
            "LawPolicyPreservation",
            "selected policy boundary candidate is tracked as supplied policy evidence",
        ),
        lean_vocabulary_entry(
            "archmap-contract-observation-preservation",
            "preserves[] contains contract preservation, contract-test observation, observation equivalence, or event sourcing projection",
            "SemanticDiagramPreservation",
            "selected contract or event-projection candidate is tracked as bounded semantic diagram evidence",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-non-commutation-boundary",
            "preserves[] contains semantic non-commutation, saga compensation, or nonfillability witness",
            "NonfillabilityWitnessPreservation",
            "selected non-commutation or compensation candidate is preserved as bounded obstruction evidence",
        ),
        lean_vocabulary_entry(
            "archmap-flatness-precondition-preservation",
            "targetRef.subjectRef contains flatnessPrecondition or preserves contains flatness precondition boundary",
            "FlatnessPreconditionPreservation",
            "selected flatness precondition candidate is tracked without discharging flatness",
        ),
        lean_vocabulary_entry(
            "archmap-runtime-static-disagreement-boundary",
            "preserves[] contains runtime/static disagreement, framework convention boundary, or dynamic plugin blind spot",
            "CoverageExactnessBoundary",
            "review-only coverage boundary remains explicit and is not promoted to a preservation proof",
        ),
        lean_vocabulary_entry(
            "archmap-coverage-boundary",
            "coverage, missingEvidence, nonConclusions",
            "CoverageExactnessBoundary",
            "coverage gaps, exactness limits, missing evidence, and non-conclusions remain explicit",
        ),
    ]
}

fn json_string_array(packet: &serde_json::Value, path: &[&str]) -> Vec<String> {
    let mut current = packet;
    for key in path {
        let Some(next) = current.get(*key) else {
            return Vec::new();
        };
        current = next;
    }
    current
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str().map(ToOwned::to_owned))
        .collect()
}

fn json_object_string_array(packet: &serde_json::Value, path: &[&str], key: &str) -> Vec<String> {
    let mut current = packet;
    for segment in path {
        let Some(next) = current.get(*segment) else {
            return Vec::new();
        };
        current = next;
    }
    current
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.get(key)?.as_str().map(ToOwned::to_owned))
        .collect()
}

fn lean_vocabulary_entry(
    vocabulary_id: &str,
    archmap_selector: &str,
    lean_package_field: &str,
    preservation_role: &str,
) -> ArchMapLeanPreservationVocabularyEntry {
    ArchMapLeanPreservationVocabularyEntry {
        vocabulary_id: vocabulary_id.to_string(),
        archmap_selector: archmap_selector.to_string(),
        lean_package_field: lean_package_field.to_string(),
        preservation_role: preservation_role.to_string(),
        report_boundary:
            "tooling vocabulary records a preservation candidate; it is not a Lean proof witness"
                .to_string(),
    }
}

fn stable_id(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect()
}

fn unique_strings(values: Vec<String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    values
        .into_iter()
        .filter(|value| seen.insert(value.clone()))
        .collect()
}
