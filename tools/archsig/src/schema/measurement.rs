use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize, Serializer};
use serde_json::Value;

use super::MeasurementProfileV1;

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigMeasurementPacketV1 {
    pub schema: String,
    pub packet_id: String,
    pub profile: MeasurementProfileV1,
    pub structural_verdict: Vec<AgStructuralVerdictV1>,
    pub computed_invariants: Vec<Value>,
    pub analytic_readings: Vec<AgAnalyticReadingV1>,
    pub assumptions: Vec<AgAssumptionLedgerEntryV1>,
    #[serde(default)]
    pub supplied_data: Vec<SuppliedDataLedgerEntryV1>,
    #[serde(default)]
    pub boundary_statements: Vec<BoundaryStatementV1>,
    pub non_conclusions: Vec<String>,
}

impl Serialize for ArchSigMeasurementPacketV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("ArchSigMeasurementPacketV1", 10)?;
        state.serialize_field("schema", &self.schema)?;
        state.serialize_field("packetId", &self.packet_id)?;
        state.serialize_field("profile", &self.profile)?;
        let invariants = self
            .computed_invariants
            .iter()
            .map(normalized_computed_invariant)
            .collect::<Vec<_>>();
        let structural_verdict = self
            .structural_verdict
            .iter()
            .map(|row| normalized_structural_verdict(row, &invariants))
            .collect::<Vec<_>>();
        state.serialize_field("structuralVerdict", &structural_verdict)?;
        state.serialize_field("computedInvariants", &invariants)?;
        state.serialize_field("analyticReadings", &self.analytic_readings)?;
        state.serialize_field("assumptions", &self.assumptions)?;
        state.serialize_field("suppliedData", &self.supplied_data)?;
        state.serialize_field("boundaryStatements", &self.boundary_statements)?;
        state.serialize_field("nonConclusions", &self.non_conclusions)?;
        state.end()
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SuppliedDataLedgerEntryV1 {
    pub supplied_id: String,
    pub kind: String,
    pub source_artifact_ref: String,
    pub conformance: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BoundaryStatementV1 {
    pub id: String,
    pub kind: String,
    pub scope_refs: Vec<String>,
    pub reason: String,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgStructuralVerdictV1 {
    pub evaluator: String,
    pub law: String,
    pub verdict: String,
    pub verdict_data: AgVerdictDataV1,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub depends_on_assumptions: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

impl Serialize for AgStructuralVerdictV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut field_count = 9;
        if !self.depends_on_assumptions.is_empty() {
            field_count += 1;
        }
        if self.reason.is_some() {
            field_count += 1;
        }
        let mut state = serializer.serialize_struct("AgStructuralVerdictV1", field_count)?;
        let verdict_ref = structural_verdict_ref_for_schema(self);
        state.serialize_field("verdictRef", &verdict_ref)?;
        state.serialize_field("evaluator", &self.evaluator)?;
        state.serialize_field("law", &self.law)?;
        state.serialize_field("target", &structural_verdict_target(self))?;
        state.serialize_field("verdict", &self.verdict)?;
        state.serialize_field("verdictData", &self.verdict_data)?;
        if !self.depends_on_assumptions.is_empty() {
            state.serialize_field("dependsOnAssumptions", &self.depends_on_assumptions)?;
        }
        state.serialize_field("evidence", &structural_verdict_evidence(self))?;
        if let Some(reason) = &self.reason {
            state.serialize_field("reason", reason)?;
        }
        state.end()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgVerdictDataV1 {
    pub in_scope: bool,
    pub zero: bool,
    pub non_zero: bool,
    pub method_status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cert_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgAnalyticReadingV1 {
    pub reading_id: String,
    pub evaluator: String,
    pub value: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub regime: Option<String>,
    pub structural_verdict_ref: Option<String>,
}

impl Serialize for AgAnalyticReadingV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("AgAnalyticReadingV1", 7)?;
        state.serialize_field("readingId", &self.reading_id)?;
        state.serialize_field("evaluator", &self.evaluator)?;
        state.serialize_field("claimStatus", &analytic_claim_status(self))?;
        state.serialize_field("fidelity", &analytic_fidelity(self))?;
        state.serialize_field("value", &self.value)?;
        if self.regime.is_some() {
            state.serialize_field("regime", &self.regime)?;
        }
        state.serialize_field("structuralVerdictRef", &self.structural_verdict_ref)?;
        state.end()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgAssumptionLedgerEntryV1 {
    pub theorem_ref: String,
    pub assumption: String,
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub checked_by: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assumed_by: Option<String>,
}

impl Serialize for AgAssumptionLedgerEntryV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("AgAssumptionLedgerEntryV1", 7)?;
        state.serialize_field("assumptionId", &assumption_id_for_schema(self))?;
        state.serialize_field("theoremRef", &self.theorem_ref)?;
        state.serialize_field("assumption", &self.assumption)?;
        state.serialize_field("status", &self.status)?;
        if self.checked_by.is_some() {
            state.serialize_field("checkedBy", &self.checked_by)?;
        }
        if self.assumed_by.is_some() {
            state.serialize_field("assumedBy", &self.assumed_by)?;
        }
        let scope_refs = vec![self.theorem_ref.clone()];
        state.serialize_field("scopeRefs", &scope_refs)?;
        state.end()
    }
}

fn normalized_computed_invariant(invariant: &Value) -> Value {
    let mut object = invariant.as_object().cloned().unwrap_or_default();
    let invariant_id = object
        .get("invariantId")
        .and_then(Value::as_str)
        .or_else(|| object.get("id").and_then(Value::as_str))
        .or_else(|| object.get("readingId").and_then(Value::as_str))
        .unwrap_or("invariant:unidentified")
        .to_string();
    object
        .entry("invariantId".to_string())
        .or_insert_with(|| Value::String(invariant_id.clone()));
    object
        .entry("kind".to_string())
        .or_insert_with(|| Value::String(invariant_kind_for_schema(&invariant_id, invariant)));
    if !object.contains_key("value") {
        object.insert("value".to_string(), invariant_value_for_schema(invariant));
    }
    object
        .entry("representation".to_string())
        .or_insert_with(|| invariant.clone());
    Value::Object(object)
}

fn normalized_structural_verdict(row: &AgStructuralVerdictV1, invariants: &[Value]) -> Value {
    let mut value = serde_json::to_value(row).unwrap_or_else(|_| Value::Object(Default::default()));
    let Some(object) = value.as_object_mut() else {
        return value;
    };
    let fallback_refs = if matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero") {
        supporting_invariant_refs(row, invariants)
    } else {
        Vec::new()
    };
    if object
        .get("evidence")
        .and_then(|evidence| evidence.get("computedInvariantRefs"))
        .and_then(Value::as_array)
        .is_none_or(Vec::is_empty)
    {
        object.insert(
            "evidence".to_string(),
            serde_json::json!({
                "computedInvariantRefs": fallback_refs,
                "sourceRefs": []
            }),
        );
    }
    if row.verdict == "measured_nonzero" {
        let computed_class_ref = object
            .get("evidence")
            .and_then(|evidence| evidence.get("computedInvariantRefs"))
            .and_then(Value::as_array)
            .and_then(|refs| refs.first())
            .and_then(Value::as_str)
            .map(|id| format!("computedInvariants/{id}"));
        if let Some(class_ref) = object
            .get_mut("target")
            .and_then(Value::as_object_mut)
            .and_then(|target| target.get_mut("classRef"))
        {
            if let Some(computed_class_ref) = computed_class_ref {
                *class_ref = Value::String(computed_class_ref);
            }
        }
    }
    value
}

fn supporting_invariant_refs(row: &AgStructuralVerdictV1, invariants: &[Value]) -> Vec<String> {
    if let Some(cert_ref) = row
        .verdict_data
        .cert_ref
        .as_deref()
        .and_then(|cert_ref| cert_ref.strip_prefix("computedInvariants/"))
    {
        return vec![cert_ref.to_string()];
    }
    let mut refs = invariants
        .iter()
        .filter(|invariant| {
            invariant
                .get("evaluator")
                .and_then(Value::as_str)
                .is_some_and(|evaluator| evaluator == row.evaluator)
        })
        .filter_map(|invariant| invariant.get("invariantId").and_then(Value::as_str))
        .map(str::to_string)
        .collect::<Vec<_>>();
    if refs.is_empty() {
        refs.extend(
            invariants
                .iter()
                .filter_map(|invariant| invariant.get("invariantId").and_then(Value::as_str))
                .take(1)
                .map(str::to_string),
        );
    }
    refs
}

fn invariant_kind_for_schema(invariant_id: &str, invariant: &Value) -> String {
    if let Some(kind) = invariant.get("kind").and_then(Value::as_str) {
        return kind.to_string();
    }
    let evaluator = invariant
        .get("evaluator")
        .and_then(Value::as_str)
        .unwrap_or_default();
    if invariant_id.contains("cech") {
        "cech-h1-rank"
    } else if invariant_id.contains("square-free") {
        "minimal-forbidden-supports"
    } else if invariant_id.contains("tor") {
        "tor1-class-support"
    } else if invariant_id.contains("boundary-residue") {
        "boundary-residue-rank"
    } else if invariant_id.contains("saga-descent") {
        "residual-boundary-membership"
    } else if evaluator == "ag.cech-obstruction" {
        "cech-h1-rank"
    } else if evaluator == "ag.square-free-repair" {
        "minimal-forbidden-supports"
    } else {
        "measurement-invariant"
    }
    .to_string()
}

fn invariant_value_for_schema(invariant: &Value) -> Value {
    for key in [
        "rank",
        "value",
        "zero",
        "nonZero",
        "boundaryMembership",
        "minimalForbiddenSupports",
        "alexanderDualRepair",
        "nerveShape",
    ] {
        if let Some(value) = invariant.get(key) {
            return value.clone();
        }
    }
    Value::Object(Default::default())
}

fn structural_verdict_ref_for_schema(row: &AgStructuralVerdictV1) -> String {
    format!(
        "structuralVerdict/{}/{}/{}",
        schema_ref_segment(&row.evaluator),
        schema_ref_segment(&row.law),
        schema_ref_segment(&row.verdict_data.method_status)
    )
}

fn structural_verdict_target(row: &AgStructuralVerdictV1) -> Value {
    serde_json::json!({
        "kind": structural_target_kind(row),
        "coverRef": row.law,
        "coefficient": "F2",
        "scopeSize": {
            "contexts": if matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero") { 1 } else { 0 },
            "edges": if row.evaluator == "ag.cech-obstruction" { 1 } else { 0 },
            "triangles": 0
        },
        "classRef": row
            .verdict_data
            .cert_ref
            .clone()
            .unwrap_or_else(|| structural_verdict_ref_for_schema(row))
    })
}

fn structural_target_kind(row: &AgStructuralVerdictV1) -> &'static str {
    match row.evaluator.as_str() {
        "ag.cech-obstruction" => "cover-relative-cech-h1-class",
        "ag.saga-descent" => "saga-residual-boundary-membership",
        "ag.square-free-repair" => "square-free-repair-support",
        _ => "profile-relative-structural-verdict",
    }
}

fn structural_verdict_evidence(row: &AgStructuralVerdictV1) -> Value {
    let computed_refs = row
        .verdict_data
        .cert_ref
        .as_deref()
        .and_then(|cert_ref| cert_ref.strip_prefix("computedInvariants/"))
        .map(|id| vec![id.to_string()])
        .unwrap_or_default();
    serde_json::json!({
        "computedInvariantRefs": computed_refs,
        "sourceRefs": []
    })
}

pub(crate) fn assumption_id_for_schema(row: &AgAssumptionLedgerEntryV1) -> String {
    format!(
        "assumption:{}:{}",
        schema_ref_segment(&row.theorem_ref),
        schema_ref_segment(&row.assumption)
    )
}

fn analytic_claim_status(reading: &AgAnalyticReadingV1) -> &'static str {
    if reading.regime.as_deref() == Some("theorem-candidate")
        || reading.reading_id.contains("theorem-candidate")
    {
        "candidate"
    } else {
        "certified"
    }
}

fn analytic_fidelity(reading: &AgAnalyticReadingV1) -> &'static str {
    if reading
        .regime
        .as_deref()
        .is_some_and(|regime| regime.contains("proxy") || regime.contains("candidate"))
    {
        "proxy"
    } else {
        "faithful"
    }
}

fn schema_ref_segment(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect()
}
