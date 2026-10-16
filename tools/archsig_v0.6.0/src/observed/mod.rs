//! 原始観測環境の三入力検査と、型付きの問いの解決。

pub mod control;
mod environment;
pub mod evaluate;
mod numeric;
pub mod result;
pub use evaluate::{evaluate_observed, evaluate_observed_bytes};
pub use result::{EvaluationFailure, ObservedEvaluation};
pub mod input;
pub mod projection;
pub mod request;

use crate::canonical::Json;
use control::Control;
use input::{CheckedInputs, InputFailure, InputSources, check_inputs};
use request::{ResolveFailure, ResolvedRequests, resolve_observed_requests_controlled};

/// 同じ検査済み三表に対して解決した、観測環境の問い。
#[derive(Debug)]
pub struct PreparedObserved {
    inputs: CheckedInputs,
    requests: ResolvedRequests,
}

impl PreparedObserved {
    pub fn inputs(&self) -> &CheckedInputs {
        &self.inputs
    }

    pub fn requests(&self) -> &ResolvedRequests {
        &self.requests
    }
}

/// 入力検査と要求解決の失敗を区別し、検査済みの入力情報を保持する。
#[derive(Debug)]
pub enum PrepareFailure {
    Inputs(Box<InputFailure>),
    Requests {
        inputs: Box<CheckedInputs>,
        failure: ResolveFailure,
    },
}

impl PrepareFailure {
    /// 適用対象の失敗だけを内部結果として表示する。適用外は専用の enum で扱う。
    pub fn wire(&self) -> Option<Json> {
        match self {
            Self::Inputs(failure) => Some(failure.wire()),
            Self::Requests { inputs, failure } => {
                let (status, requests, issues) = match failure {
                    ResolveFailure::Invalid {
                        requests,
                        issues,
                        stop_reason,
                    } => {
                        let mut wire_issues: Vec<Json> =
                            issues.iter().map(request::RequestIssue::wire).collect();
                        if let Some(reason) = stop_reason {
                            // budget_exhausted precedes both cycle and usage in the specified code order.
                            wire_issues.insert(0, reason.wire());
                        }
                        (
                            "invalid",
                            requests.iter().map(request::Request::wire).collect(),
                            wire_issues,
                        )
                    }
                    ResolveFailure::Interrupted { reason } => {
                        ("interrupted", vec![], vec![reason.wire()])
                    }
                    ResolveFailure::NotApplicable { .. } => return None,
                };
                let mut wire = inputs.metadata_wire();
                let Json::Obj(fields) = &mut wire else {
                    unreachable!("metadata は object")
                };
                fields.insert("status".into(), Json::str(status));
                fields.insert("requests".into(), Json::Arr(requests));
                fields.insert("issues".into(), Json::Arr(issues));
                fields.insert("nodes".into(), Json::Arr(vec![]));
                fields.insert("answers".into(), Json::Arr(vec![]));
                Some(wire)
            }
        }
    }
}

/// 元 byte 列の検査から、同じ観測環境での要求解決までを接続する。
pub fn prepare_observed(
    sources: InputSources,
    texts: &[&str],
    control: &mut Control,
) -> Result<PreparedObserved, PrepareFailure> {
    let inputs = check_inputs(sources, control)
        .map_err(|failure| PrepareFailure::Inputs(Box::new(failure)))?;
    prepare_checked_observed(inputs, texts, control)
}

/// 入力検査済み bundle に対し、byte 列の再読込みを行わずに問いを解決する。
pub fn prepare_checked_observed(
    inputs: CheckedInputs,
    texts: &[&str],
    control: &mut Control,
) -> Result<PreparedObserved, PrepareFailure> {
    match resolve_observed_requests_controlled(inputs.law(), inputs.archmap(), texts, control) {
        Ok(requests) => Ok(PreparedObserved { inputs, requests }),
        Err(failure) => Err(PrepareFailure::Requests {
            inputs: Box::new(inputs),
            failure,
        }),
    }
}
