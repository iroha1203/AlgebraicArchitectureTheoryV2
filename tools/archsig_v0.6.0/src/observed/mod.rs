//! 原始観測環境の三入力検査と、型付きの問いの解決。

mod affine;
mod architecture_result;
mod call;
mod circuit_pattern;
pub(crate) mod construction_result;
mod data;
mod environment;
mod equation_family;
mod equation_presentation_node;
pub mod evaluate;
mod field_fiber;
mod finite;
mod finite_integer_function;
mod finite_law_diagram;
mod integer_fiber;
mod internal_arrow_diagram;
mod law_evaluation;
mod law_family;
mod law_inapplicable;
mod law_instantiation;
mod law_proposition;
mod law_table;
mod local_result;
mod needed;
mod numeric;
pub mod numeric_transport;
mod object_component_diagram;
pub mod object_evaluate;
pub mod object_evaluation_table;
pub mod object_law_circuit_transport;
pub mod object_law_circuits;
pub mod object_law_compatibility;
pub mod object_law_residuals;
pub mod object_law_transport;
mod object_reading_evaluation;
mod object_reading_result;
mod object_transport;
pub mod object_view_compatibility;
pub(crate) mod object_view_family;
pub mod object_view_transport;
mod observable_layout;
mod path_compose;
mod path_value;
mod polynomial_law_diagram;
mod public_compare;
mod public_compose;
mod public_map;
mod public_path_compose;
mod quantifier;
pub mod result;
mod result_kind;
mod summary;
mod term;
mod value_equality;
pub mod value_transport;
mod view_family;
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub use evaluate::evaluate_observed_with_rejected_answer;
pub use evaluate::{evaluate_observed, evaluate_observed_bytes};
pub use result::{EvaluationFailure, ObservedEvaluation};
pub mod projection;
pub mod request;

use crate::canonical::Json;
use crate::control::Control;
use crate::input::{CheckedInputs, InputFailure, InputSources, check_inputs};
use request::{ResolveFailure, ResolvedRequests, resolve_observed_requests_controlled};
use std::sync::Arc;

/// 同じ検査済み三表に対して解決した、観測環境の問い。
#[derive(Debug)]
pub struct PreparedObserved {
    inputs: Arc<CheckedInputs>,
    requests: ResolvedRequests,
    object: Option<object_evaluate::ObjectContext>,
}

impl PreparedObserved {
    pub fn inputs(&self) -> &CheckedInputs {
        &self.inputs
    }

    /// 同じ不変三表を別の要求batchへ渡す。要求・回答・評価graphは共有しない。
    pub fn shared_inputs(&self) -> Arc<CheckedInputs> {
        Arc::clone(&self.inputs)
    }

    pub fn requests(&self) -> &ResolvedRequests {
        &self.requests
    }

    /// native対象読取りのcontext。通常の観測環境ではNone。
    pub fn object_identity(&self) -> Option<&crate::construction::maps::ObjectIdentity> {
        self.object.as_ref().map(|object| &object.domain.identity)
    }

    pub fn object_instance(&self) -> Option<&crate::construction::readings::ObjectInstance> {
        self.object.as_ref().map(|object| &object.instance)
    }
}

/// 入力検査と要求解決の失敗を区別し、検査済みの入力情報を保持する。
#[derive(Debug)]
pub enum PrepareFailure {
    Inputs(Box<InputFailure>),
    Requests {
        inputs: Arc<CheckedInputs>,
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
                    ResolveFailure::Invalid { requests, issues } => (
                        "invalid",
                        requests.iter().map(request::Request::wire).collect(),
                        issues.iter().map(request::RequestIssue::wire).collect(),
                    ),
                    ResolveFailure::Interrupted { reason } => {
                        ("interrupted", vec![], vec![reason.issue()])
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
    prepare_shared_observed(Arc::new(inputs), texts, control)
}

/// 同じ検査済み三表を共有し、byte列の再検査・表の複製なしに別batchを解決する。
pub fn prepare_shared_observed(
    inputs: Arc<CheckedInputs>,
    texts: &[&str],
    control: &mut Control,
) -> Result<PreparedObserved, PrepareFailure> {
    match resolve_observed_requests_controlled(inputs.law(), inputs.archmap(), texts, control) {
        Ok(requests) => Ok(PreparedObserved {
            inputs,
            requests,
            object: None,
        }),
        Err(failure) => Err(PrepareFailure::Requests { inputs, failure }),
    }
}

pub mod equation_polynomial;
pub mod object_equation_presentation;

pub mod finite_polynomial_evaluation;
pub mod object_polynomial_observable;

mod view_invariant;

mod predicate_invariant;

mod build_circuit_plan;
mod build_compare;
mod build_plan;
mod build_result;
mod change_result;
mod native_source;
mod object_law_map;
mod object_map_result;
mod object_view_map;
mod quotient_result;

#[cfg(test)]
mod numeric_tuple_change_integration_tests;

#[cfg(test)]
mod local_closure_retention_tests;

#[cfg(test)]
pub(crate) mod owner_completion_legacy;
