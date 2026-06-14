use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::MeasurementProfileV1;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
    pub boundary_statements: Vec<BoundaryStatementV1>,
    pub non_conclusions: Vec<String>,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgStructuralVerdictV1 {
    pub evaluator: String,
    pub law: String,
    pub verdict: String,
    pub verdict_data: AgVerdictDataV1,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgAnalyticReadingV1 {
    pub reading_id: String,
    pub evaluator: String,
    pub value: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub regime: Option<String>,
    pub structural_verdict_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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
