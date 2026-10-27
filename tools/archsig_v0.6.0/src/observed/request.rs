//! 観測環境のevaluate/checkと、依存理由を読むneeded要求。

use super::{
    control::{Checkpoint, Control, StopReason},
    projection::{self, ProjectionPlan, ProjectionStep, ProjectionType},
};
use crate::{
    archmap::{CheckedArchMap, Slot, Subject, Value},
    canonical::Json,
    law::{
        CheckedLaw,
        model::{Param, Signature},
    },
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};
#[path = "request_compare.rs"]
pub(super) mod comparison;
#[path = "request_compose.rs"]
pub(super) mod composition;
#[path = "request_map.rs"]
mod configuration_map;
#[path = "request_build.rs"]
mod build;
#[path = "request_local.rs"]
mod local;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuestionKind {
    Build,
    Evaluate,
    Check,
    Needed,
    Map,
    Compose,
    Compare,
    Solve,
    Repair,
    Quotient,
    Localize,
    Diagnose,
}
impl QuestionKind {
    pub fn wire(self) -> &'static str {
        match self {
            Self::Build => "build",
            Self::Evaluate => "evaluate",
            Self::Check => "check",
            Self::Needed => "needed",
            Self::Map => "map",
            Self::Compose => "compose",
            Self::Compare => "compare",
            Self::Solve => "solve",
            Self::Repair => "repair",
            Self::Quotient => "quotient",
            Self::Localize => "localize",
            Self::Diagnose => "diagnose",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Selector {
    Degree { value: u64 },
    Enum {
        value: String,
    },
    Declaration {
        name: String,
    },
    Subject {
        snapshot: String,
        subject: String,
    },
    Answer {
        id: String,
        path: Vec<ProjectionStep>,
    },
}
impl Selector {
    pub fn wire(&self) -> Json {
        match self {
            Self::Degree { value } => Json::obj([("kind",Json::str("degree")),("value",Json::Nat(*value))]),
            Self::Enum { value } => {
                Json::obj([("kind", Json::str("enum")), ("value", Json::str(value))])
            }
            Self::Declaration { name } => Json::obj([
                ("kind", Json::str("declaration")),
                ("name", Json::str(name)),
            ]),
            Self::Subject { snapshot, subject } => Json::obj([
                ("kind", Json::str("subject")),
                ("snapshot", Json::str(snapshot)),
                ("subject", Json::str(subject)),
            ]),
            Self::Answer { id, path } => Json::obj([
                ("kind", Json::str("answer")),
                ("id", Json::str(id)),
                (
                    "path",
                    Json::Arr(path.iter().map(ProjectionStep::wire).collect()),
                ),
            ]),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgumentOrigin {
    Explicit,
    Defaulted,
}
impl ArgumentOrigin {
    pub fn wire(self) -> &'static str {
        match self {
            Self::Explicit => "explicit",
            Self::Defaulted => "defaulted",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestArgument {
    pub name: String,
    pub value: Selector,
    pub origin: ArgumentOrigin,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RequestDefault {
    NoLawCheck,
    RequiredLaws,
    IdentityChange,
    ObservedEnvironment,
    UniversalParameters {
        declaration: String,
        parameters: Vec<String>,
    },
}
impl RequestDefault {
    pub fn wire(&self) -> Json {
        match self {
            Self::RequiredLaws => Json::obj([("rule",Json::str("required_laws"))]),
            Self::IdentityChange => Json::obj([("rule",Json::str("identity_change"))]),
            Self::NoLawCheck => Json::obj([("rule", Json::str("no_law_check"))]),
            Self::ObservedEnvironment => Json::obj([("rule", Json::str("observed_environment"))]),
            Self::UniversalParameters {
                declaration,
                parameters,
            } => Json::obj([
                ("rule", Json::str("universal_parameters")),
                ("declaration", Json::str(declaration)),
                (
                    "parameters",
                    Json::Arr(parameters.iter().map(Json::str).collect()),
                ),
            ]),
        }
    }
}

/// 実値による射影と依存 owner の確認を、通常値の消費前に実行するための制約。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BindingConstraint {
    pub parameter: String,
    pub expected: Type,
    pub selector: Selector,
    pub projection: ProjectionPlan,
    pub owner: Option<Selector>,
    /// 射影後の型内の Owned 添字を、生産側 Request の束縛へ対応付ける。
    /// 型名や添字の文字列だけで別の Request の文脈を同一視しない。
    pub projection_owners: BTreeMap<String, Selector>,
    /// 消費側 parameter 型の Owned 添字に対する明示束縛。未束縛は動的に検査する。
    pub expected_owners: BTreeMap<String, Selector>,
    pub dynamic: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub id: String,
    pub text: String,
    pub kind: QuestionKind,
    pub head: Selector,
    pub arguments: Vec<RequestArgument>,
    pub defaults: Vec<RequestDefault>,
    pub dependencies: Vec<String>,
    /// wire へ追加せず、評価時の型照合に使う内部の情報。
    pub constraints: Vec<BindingConstraint>,
}
impl Request {
    /// Law/view宣言を選ぶ問いの名前。reading・原始correspondence・問いIDは含めない。
    pub fn declaration(&self) -> Option<&str> {
        if self.kind==QuestionKind::Localize {
            return self.arguments.iter().find(|a|a.name=="law").and_then(|a|match &a.value{Selector::Declaration{name}=>Some(name.as_str()),_=>None});
        }
        if matches!(self.kind, QuestionKind::Map | QuestionKind::Build) {
            return None;
        }
        match &self.head {
            Selector::Declaration { name } => Some(name),
            _ => None,
        }
    }
    pub fn wire(&self) -> Json {
        Json::obj([
            ("id", Json::str(&self.id)),
            ("text", Json::str(&self.text)),
            ("kind", Json::str(self.kind.wire())),
            ("head", self.head.wire()),
            (
                "arguments",
                Json::Arr(
                    self.arguments
                        .iter()
                        .map(|a| {
                            Json::obj([
                                ("name", Json::str(&a.name)),
                                ("value", a.value.wire()),
                                ("origin", Json::str(a.origin.wire())),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "defaults",
                Json::Arr(self.defaults.iter().map(RequestDefault::wire).collect()),
            ),
            (
                "dependencies",
                Json::Arr(self.dependencies.iter().map(Json::str).collect()),
            ),
        ])
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequestIssueCode {
    Syntax,
    DuplicateId,
    DuplicateArgument,
    Reference,
    Type,
    Projection,
    MissingBinding,
    Cycle,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestIssue {
    pub code: RequestIssueCode,
    pub request: String,
    pub argument: String,
    pub message: String,
}
impl RequestIssue {
    pub fn wire(&self) -> Json {
        let cycle = self.code == RequestIssueCode::Cycle;
        Json::obj([
            ("code", Json::str(if cycle { "cycle" } else { "usage" })),
            ("request", Json::str(&self.request)),
            ("message", Json::str(if cycle || self.argument.is_empty() {
                self.message.clone()
            } else {
                format!("{}: {}", self.message, self.argument)
            })),
            ("dependencies", Json::Arr(vec![])),
            ("missing", Json::Arr(vec![])),
            (
                "details",
                if cycle {
                    Json::obj([])
                } else {
                    Json::obj([("argument", Json::str(&self.argument))])
                },
            ),
        ])
    }
}

#[derive(Debug)]
pub enum ResolveFailure {
    Invalid {
        requests: Vec<Request>,
        issues: Vec<RequestIssue>,
        /// A budget stop observed after an already established request error.
        stop_reason: Option<StopReason>,
    },
    /// この入口では意味を持たない問い。成功や算法非対応、公開 CLI の usage と区別する。
    NotApplicable {
        request: String,
        kind: String,
        architecture_environment: bool,
    },
    Interrupted {
        reason: StopReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedRequests {
    /// 利用者の指定順。Answer もこの順を使う。
    requests: Vec<Request>,
    /// 同順位の要求を指定順にする、依存先からの評価順。
    evaluation_order: Vec<usize>,
}
impl ResolvedRequests {
    pub fn requests(&self) -> &[Request] {
        &self.requests
    }
    pub fn evaluation_order(&self) -> &[usize] {
        &self.evaluation_order
    }
}

pub fn resolve_observed_requests(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    texts: &[&str],
) -> Result<ResolvedRequests, ResolveFailure> {
    resolve_observed_requests_controlled(law, map, texts, &mut Control::unlimited())
}

/// 入力検査と同じ中断制御で、構文・束縛・公開射影・循環を意味計算前に検査する。
pub fn resolve_observed_requests_controlled(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    texts: &[&str],
    control: &mut Control,
) -> Result<ResolvedRequests, ResolveFailure> {
    let result = resolve_inner(law, map, texts, control, None)
        .and_then(|resolved| available(resolved, control));
    finish_request(result, control, Checkpoint::Resolve)
}

// 対象別の有限関数族だけが使う経路。通常CLIの全束縛規則は変えない。
pub(super) fn resolve_object_view_requests(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    texts: &[&str],
    control: &mut Control,
    instance: &crate::construction::readings::ObjectInstance,
) -> Result<ResolvedRequests, ResolveFailure> {
    let result = resolve_inner(law, map, texts, control, Some(instance))
        .and_then(|resolved| available(resolved, control));
    finish_request(result, control, Checkpoint::Resolve)
}

#[cfg(test)]
pub(super) fn resolve_native_for_test(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    texts: &[&str],
    control: &mut Control,
) -> Result<ResolvedRequests, ResolveFailure> {
    resolve_inner(law, map, texts, control, None)
}

fn resolve_inner(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    texts: &[&str],
    control: &mut Control,
    object_view: Option<&crate::construction::readings::ObjectInstance>,
) -> Result<ResolvedRequests, ResolveFailure> {
    let mut requests = Vec::new();
    let mut names = BTreeMap::new();
    for text in texts {
        checkpoint(control)?;
        let raw = Parser::new(text, control).parse()?;
        phase(control, Checkpoint::RequestBinding)?;
        if names.contains_key(&raw.id) {
            return Err(invalid(problem(
                RequestIssueCode::DuplicateId,
                &raw.id,
                &raw.id,
                "duplicate request ID",
            )));
        }
        let kind = match raw.kind.as_str() {
            "build" => QuestionKind::Build,
            "solve" => QuestionKind::Solve,
            "repair" => QuestionKind::Repair,
            "quotient" => QuestionKind::Quotient,
            "localize" => QuestionKind::Localize,
            "diagnose" => QuestionKind::Diagnose,
            "evaluate" => QuestionKind::Evaluate,
            "check" => QuestionKind::Check,
            "needed" => QuestionKind::Needed,
            "map" => QuestionKind::Map,
            "compose" => QuestionKind::Compose,
            "compare" => QuestionKind::Compare,
            _ => {
                return Err(invalid(problem(
                    RequestIssueCode::Syntax,
                    &raw.id,
                    &raw.kind,
                    "unknown request kind",
                )));
            }
        };
        if matches!(kind, QuestionKind::Localize | QuestionKind::Diagnose) {
            let request = local::resolve(law, raw, text, control)?;
            names.insert(request.id.clone(), requests.len());
            requests.push(request);
            continue;
        }
        if kind == QuestionKind::Build {
            let request = build::resolve(law, raw, text, control)?;
            names.insert(request.id.clone(), requests.len());
            requests.push(request);
            continue;
        }
        if kind == QuestionKind::Map {
            let request = configuration_map::resolve(law, raw, text, control)?;
            names.insert(request.id.clone(), requests.len());
            requests.push(request);
            continue;
        }
        if kind == QuestionKind::Compare {
            let request = comparison::resolve(raw, text, control)?;
            names.insert(request.id.clone(), requests.len());
            requests.push(request);
            continue;
        }
        if kind == QuestionKind::Compose {
            let request = composition::resolve(raw, text, control)?;
            names.insert(request.id.clone(), requests.len());
            requests.push(request);
            continue;
        }
        if kind == QuestionKind::Needed {
            let Selector::Answer { id, path } = &raw.head else {
                return Err(invalid(problem(
                    RequestIssueCode::Reference,
                    &raw.id,
                    "head",
                    "needed requires a request ID as $Id",
                )));
            };
            if !path.is_empty() || !raw.arguments.is_empty() {
                return Err(invalid(problem(
                    RequestIssueCode::Syntax,
                    &raw.id,
                    "head",
                    "needed does not accept an output field or additional arguments",
                )));
            }
            names.insert(raw.id.clone(), requests.len());
            requests.push(Request {
                id: raw.id,
                text: (*text).into(),
                kind,
                dependencies: vec![id.clone()],
                head: raw.head,
                arguments: vec![],
                defaults: vec![],
                constraints: vec![],
            });
            phase(control, Checkpoint::RequestBinding)?;
            continue;
        }
        let Selector::Declaration { name } = &raw.head else {
            return Err(invalid(problem(
                RequestIssueCode::Reference,
                &raw.id,
                "head",
                "specify a declaration name",
            )));
        };
        let full = declaration(law, name, control, &raw.id)?;
        let params = parameters(&law.declarations[&full].signature, kind).ok_or_else(|| {
            invalid(problem(
                RequestIssueCode::Type,
                &raw.id,
                name,
                "request and declaration kinds do not match",
            ))
        })?;
        let view_params = params;
        let selected_law = if kind == QuestionKind::Quotient {
            raw.arguments.iter().find(|(key, _)| key == "law").map(|(_, value)| {
                let Selector::Declaration { name } = value else {
                    return Err(invalid(problem(RequestIssueCode::Type, &raw.id, "law", "law must specify a Law declaration name")));
                };
                declaration(law, name, control, &raw.id)
            }).transpose()?
        } else { None };
        let mut all_params = params.to_vec();
        if let Some(name) = &selected_law {
            let Signature::Law { params, .. } = &law.declarations[name].signature else {
                return Err(invalid(problem(RequestIssueCode::Type, &raw.id, "law", "law must specify a Law declaration")));
            };
            for param in params {
                if let Some(shared) = all_params.iter().find(|p| p.name == param.name) {
                    if shared.ty != param.ty {
                        return Err(invalid(problem(RequestIssueCode::Type, &raw.id, &param.name, "view and Law parameter types with the same name do not match")));
                    }
                } else { all_params.push(param.clone()); }
            }
        }
        let params = all_params.as_slice();
        let mut arguments = BTreeMap::new();
        let mut dependencies = BTreeSet::new();
        for (key, value) in raw.arguments {
            phase(control, Checkpoint::RequestBinding)?;
            if key == "law" && kind == QuestionKind::Quotient {
                if arguments.insert("law".into(), RequestArgument {
                    name: "law".into(), value: Selector::Declaration { name: selected_law.clone().ok_or_else(|| invalid(problem(RequestIssueCode::Reference, &raw.id, "law", "missing Law")))? },
                    origin: ArgumentOrigin::Explicit,
                }).is_some() {
                    return Err(invalid(problem(RequestIssueCode::DuplicateArgument, &raw.id, "law", "duplicate law")));
                }
                continue;
            }
            if key == "using" && matches!(kind, QuestionKind::Solve | QuestionKind::Repair) {
                let Selector::Declaration { name } = &value else {
                    return Err(invalid(problem(RequestIssueCode::Type, &raw.id, "using", "using must be a fully qualified change name")));
                };
                let change = declaration(law, name, control, &raw.id)?;
                if !matches!(law.declarations[&change].signature, Signature::Change { .. })
                    || law.declarations[&change].reading != law.declarations[&full].reading {
                    return Err(invalid(problem(RequestIssueCode::Type, &raw.id, "using", "specify a change from the same reading")));
                }
                arguments.insert("using".into(), RequestArgument {name:"using".into(), value:Selector::Declaration {name:change}, origin:ArgumentOrigin::Explicit});
                continue;
            }
            if key == "on" && matches!(kind, QuestionKind::Solve | QuestionKind::Repair)
                && matches!(value, Selector::Subject { .. }) {
                arguments.insert("on".into(),RequestArgument {name:"on".into(),value,origin:ArgumentOrigin::Explicit});
                continue;
            }
            if key == "on" {
                let Selector::Answer { id, path } = &value else {
                    return Err(invalid(problem(
                        RequestIssueCode::Type,
                        &raw.id,
                        "on",
                        if kind == QuestionKind::Quotient { "on must specify a public CandidateSpace/SolutionSet Handle" } else { "on must specify a public Architecture Handle" },
                    )));
                };
                if path.is_empty() {
                    return Err(invalid(problem(
                        RequestIssueCode::Projection,
                        &raw.id,
                        "on",
                        if kind == QuestionKind::Quotient { "on must specify a CandidateSpace/SolutionSet output field" } else { "on must specify an Architecture output field" },
                    )));
                }
                dependencies.insert(id.clone());
                if arguments
                    .insert(
                        "on".into(),
                        RequestArgument {
                            name: "on".into(),
                            value,
                            origin: ArgumentOrigin::Explicit,
                        },
                    )
                    .is_some()
                {
                    return Err(invalid(problem(
                        RequestIssueCode::DuplicateArgument,
                        &raw.id,
                        "on",
                        "duplicate on",
                    )));
                }
                continue;
            }
            let name = key.strip_prefix("bind.").unwrap_or(&key);
            checked_require(
                params,
                |p| p.name == name,
                control,
                Checkpoint::RequestBinding,
                || {
                    invalid(problem(
                        RequestIssueCode::Reference,
                        &raw.id,
                        &key,
                        "unknown parameter",
                    ))
                },
            )?;
            if matches!(value, Selector::Declaration { .. }) {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &raw.id,
                    &key,
                    "parameter requires a Handle",
                )));
            }
            if let Selector::Answer { id, path } = &value {
                phase(control, Checkpoint::RequestDependency)?;
                if path.is_empty() {
                    return Err(invalid(problem(
                        RequestIssueCode::Projection,
                        &raw.id,
                        &key,
                        "specify an output field",
                    )));
                }
                dependencies.insert(id.clone());
                phase(control, Checkpoint::RequestDependency)?;
            }
            let normalized = format!("bind.{name}");
            let duplicate = arguments
                .insert(
                    normalized.clone(),
                    RequestArgument {
                        name: normalized,
                        value,
                        origin: ArgumentOrigin::Explicit,
                    },
                )
                .is_some();
            let result = if duplicate {
                Err(invalid(problem(
                    RequestIssueCode::DuplicateArgument,
                    &raw.id,
                    &key,
                    "duplicate binding for the same parameter",
                )))
            } else {
                Ok(())
            };
            finish_request(result, control, Checkpoint::RequestBinding)?;
        }
        if matches!(kind, QuestionKind::Solve | QuestionKind::Repair)
            && (!arguments.contains_key("on") || !arguments.contains_key("using")) {
            return Err(invalid(problem(RequestIssueCode::MissingBinding, &raw.id, "on/using", "solve/repair requires on and using")));
        }
        if kind == QuestionKind::Quotient && !arguments.contains_key("on") {
            return Err(invalid(problem(RequestIssueCode::MissingBinding,&raw.id,"on","quotient requires on")));
        }
        let mut unbound = Vec::new();
        for param in params {
            phase(control, Checkpoint::RequestBinding)?;
            if !arguments.contains_key(&format!("bind.{}", param.name)) {
                if ((kind == QuestionKind::Quotient && view_params.iter().any(|p| p.name == param.name)) || kind == QuestionKind::Evaluate)
                    && !object_view.is_some_and(|instance| {
                        instance.declaration().kind == "view"
                            && instance.declaration().name == full
                            && instance.parameters().iter().any(|p| p == param)
                    })
                {
                    return finish_request(
                        Err(invalid(problem(
                            RequestIssueCode::MissingBinding,
                            &raw.id,
                            &param.name,
                            "bind all view parameters",
                        ))),
                        control,
                        Checkpoint::RequestBinding,
                    );
                }
                if kind != QuestionKind::Evaluate {
                    unbound.push(param.name.clone());
                }
            }
            phase(control, Checkpoint::RequestBinding)?;
        }
        let mut defaults = if kind == QuestionKind::Quotient && selected_law.is_none() {
            vec![RequestDefault::NoLawCheck]
        } else if arguments.contains_key("on") {
            vec![]
        } else {
            vec![RequestDefault::ObservedEnvironment]
        };
        if !unbound.is_empty() {
            defaults.push(RequestDefault::UniversalParameters {
                declaration: selected_law.clone().unwrap_or_else(|| full.clone()),
                parameters: unbound,
            });
        }
        let mut argument_list = Vec::new();
        for argument in arguments.into_values() {
            phase(control, Checkpoint::RequestBinding)?;
            argument_list.push(argument);
            phase(control, Checkpoint::RequestBinding)?;
        }
        let mut dependency_list = Vec::new();
        for dependency in dependencies {
            phase(control, Checkpoint::RequestDependency)?;
            dependency_list.push(dependency);
            phase(control, Checkpoint::RequestDependency)?;
        }
        names.insert(raw.id.clone(), requests.len());
        requests.push(Request {
            id: raw.id,
            text: (*text).to_owned(),
            kind,
            head: Selector::Declaration { name: full },
            arguments: argument_list,
            defaults,
            dependencies: dependency_list,
            constraints: vec![],
        });
        phase(control, Checkpoint::RequestBinding)?;
        checkpoint(control)?;
    }
    // 合成の出力型は元Operationの型へ再帰するため、先に依存を検査する。
    let composition_order = if requests
        .iter()
        .any(|r| {
            matches!(
                r.kind,
                QuestionKind::Build | QuestionKind::Compose | QuestionKind::Compare
                    | QuestionKind::Solve | QuestionKind::Repair | QuestionKind::Quotient | QuestionKind::Localize | QuestionKind::Diagnose
            )
        })
    {
        for request in &requests {
            for dependency in &request.dependencies {
                phase(control, Checkpoint::RequestDependency)?;
                if !names.contains_key(dependency) {
                    return Err(invalid(problem(
                        RequestIssueCode::Reference,
                        &request.id,
                        dependency,
                        "dependency request ID does not exist",
                    )));
                }
            }
        }
        let (evaluation_order, cyclic) = order(&requests, &names, control)?;
        if !cyclic.is_empty() {
            return finish_request(
                Err(cycle_failure(&requests, &cyclic)),
                control,
                Checkpoint::RequestDependency,
            );
        }
        Some(evaluation_order)
    } else {
        None
    };
    for i in 0..requests.len() {
        checkpoint(control)?;
        phase(control, Checkpoint::RequestBinding)?;
        let req = &requests[i];
        if matches!(req.kind, QuestionKind::Localize | QuestionKind::Diagnose) {
            requests[i].constraints=local::check(law, map, &requests, &names, req, control)?;
            continue;
        }
        if req.kind == QuestionKind::Build {
            build::check_on(law, map, &requests, &names, req, control)?;
            continue;
        }
        if req.kind == QuestionKind::Compare {
            requests[i].constraints =
                comparison::constraints(law, map, &requests, &names, req, control)?;
            continue;
        }
        if req.kind == QuestionKind::Compose {
            requests[i].constraints =
                composition::constraints(law, map, &requests, &names, req, control)?;
            continue;
        }
        if req.kind == QuestionKind::Map {
            let constraints =
                configuration_map::constraints(law, map, &requests, &names, req, control)?;
            requests[i].constraints = constraints;
            continue;
        }
        if req.kind == QuestionKind::Needed {
            let id = &req.dependencies[0];
            if !names.contains_key(id) {
                return Err(invalid(problem(
                    RequestIssueCode::Reference,
                    &req.id,
                    "head",
                    "request ID does not exist",
                )));
            }
            phase(control, Checkpoint::RequestDependency)?;
            continue;
        }
        let params = parameters(
            &law.declarations[req.declaration().expect("宣言headの問い")].signature,
            req.kind,
        )
        .unwrap();
        let mut all_params = params.to_vec();
        if req.kind == QuestionKind::Quotient {
            if let Some(RequestArgument { value: Selector::Declaration { name }, .. }) = req.arguments.iter().find(|a| a.name == "law") {
                if let Signature::Law { params, .. } = &law.declarations[name].signature {
                    for param in params {
                        if !all_params.iter().any(|p| p.name == param.name) { all_params.push(param.clone()); }
                    }
                }
            }
        }
        let params = all_params.as_slice();
        if let Some(on) = checked_find(
            &req.arguments,
            |a| a.name == "on",
            control,
            Checkpoint::RequestBinding,
        )? {
            let (plan, _) = selector_type(
                law,
                map,
                &requests,
                &names,
                &on.value,
                control,
                (&req.id, "on"),
            )?;
            fn architecture(ty: &ProjectionType, c: &mut Control) -> Result<bool, ResolveFailure> {
                phase(c, Checkpoint::RequestBinding)?;
                match ty {
                    ProjectionType::Architecture | ProjectionType::ArchitectureRoot(_) => Ok(true),
                    ProjectionType::Dynamic(options) => {
                        for option in options {
                            if architecture(option, c)? {
                                return Ok(true);
                            }
                        }
                        Ok(false)
                    }
                    _ => Ok(false),
                }
            }
            let change_root = if matches!(req.kind, QuestionKind::Solve | QuestionKind::Repair)
                && !architecture(&plan.ty, control)? {
                let declaration=&law.declarations[req.declaration().expect("Lawのhead")];
                let mut root_request=req.clone();
                root_request.head=Selector::Declaration {name:declaration.reading.clone()};
                build::check_on(law,map,&requests,&names,&root_request,control)?;
                true
            } else {false};
            let quotient = req.kind == QuestionKind::Quotient;
            if quotient && !matches!(plan.ty, ProjectionType::CandidateSpace(_) | ProjectionType::SolutionSet(_)) {
                return Err(invalid(problem(RequestIssueCode::Type,&req.id,"on","quotient on must be a CandidateSpace or SolutionSet")));
            }
            if !quotient && !change_root && !architecture(&plan.ty, control)? {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &req.id,
                    "on",
                    "on Handle must be an Architecture",
                )));
            }
        }
        requests[i].constraints = binding_constraints(law,map,&requests,&names,req,params,control)?;
        phase(control, Checkpoint::RequestBinding)?;
        checkpoint(control)?;
    }
    let evaluation_order = if let Some(order) = composition_order {
        order
    } else {
        let (evaluation_order, cyclic) = order(&requests, &names, control)?;
        if !cyclic.is_empty() {
            return finish_request(
                Err(cycle_failure(&requests, &cyclic)),
                control,
                Checkpoint::RequestDependency,
            );
        }
        evaluation_order
    };
    phase(control, Checkpoint::RequestDependency)?;
    Ok(ResolvedRequests {
        requests,
        evaluation_order,
    })
}

// 構文・依存・型の検査後に評価器の対応を判定する。未実装を不正入力へ変えない。
fn available(
    resolved: ResolvedRequests,
    control: &mut Control,
) -> Result<ResolvedRequests, ResolveFailure> {
    for _request in &resolved.requests {
        phase(control, Checkpoint::RequestDependency)?;
    }
    Ok(resolved)
}

fn stopped(reason: StopReason) -> ResolveFailure {
    ResolveFailure::Interrupted { reason }
}
fn phase(control: &mut Control, point: Checkpoint) -> Result<(), ResolveFailure> {
    control.checkpoint(point).map_err(stopped)
}
/// A known request error outranks a budget stop; cancellation remains first.
fn finish_request<T>(
    result: Result<T, ResolveFailure>,
    control: &mut Control,
    point: Checkpoint,
) -> Result<T, ResolveFailure> {
    match (result, control.checkpoint(point)) {
        (
            Err(ResolveFailure::Invalid {
                requests, issues, ..
            }),
            Err(reason @ StopReason::BudgetExhausted { .. }),
        ) => Err(ResolveFailure::Invalid {
            requests,
            issues,
            stop_reason: Some(reason),
        }),
        (_, Err(reason)) => Err(stopped(reason)),
        (result, Ok(())) => result,
    }
}
fn checkpoint(control: &mut Control) -> Result<(), ResolveFailure> {
    phase(control, Checkpoint::Resolve)
}
fn problem(code: RequestIssueCode, request: &str, argument: &str, message: &str) -> RequestIssue {
    RequestIssue {
        code,
        request: request.into(),
        argument: argument.into(),
        message: message.into(),
    }
}
fn invalid(issue: RequestIssue) -> ResolveFailure {
    ResolveFailure::Invalid {
        requests: vec![],
        issues: vec![issue],
        stop_reason: None,
    }
}

/// 任意検索の不一致は途中結果。必須検索は最後の候補の不一致を診断へ
/// 変換してから事後確認する。未試行の候補があれば中断を優先する。
fn checked_find_map<'a, T, R>(
    items: &'a [T],
    mut predicate: impl FnMut(&T) -> bool,
    control: &mut Control,
    point: Checkpoint,
    finish: impl FnOnce(Option<&'a T>) -> Result<R, ResolveFailure>,
) -> Result<R, ResolveFailure> {
    phase(control, point)?;
    for (index, item) in items.iter().enumerate() {
        phase(control, point)?;
        let found = predicate(item);
        if found || index + 1 == items.len() {
            return finish_request(finish(found.then_some(item)), control, point);
        }
        phase(control, point)?;
    }
    finish_request(finish(None), control, point)
}
fn checked_find<'a, T>(
    items: &'a [T],
    predicate: impl FnMut(&T) -> bool,
    control: &mut Control,
    point: Checkpoint,
) -> Result<Option<&'a T>, ResolveFailure> {
    checked_find_map(items, predicate, control, point, Ok)
}
fn checked_require<'a, T>(
    items: &'a [T],
    predicate: impl FnMut(&T) -> bool,
    control: &mut Control,
    point: Checkpoint,
    missing: impl FnOnce() -> ResolveFailure,
) -> Result<&'a T, ResolveFailure> {
    checked_find_map(items, predicate, control, point, |found| {
        found.ok_or_else(missing)
    })
}

fn declaration(
    law: &CheckedLaw,
    name: &str,
    control: &mut Control,
    request: &str,
) -> Result<String, ResolveFailure> {
    let missing = || {
        invalid(problem(
            RequestIssueCode::Reference,
            request,
            name,
            "declaration name does not exist or is ambiguous",
        ))
    };
    phase(control, Checkpoint::RequestBinding)?;
    if law.declarations.contains_key(name) {
        return finish_request(Ok(name.to_owned()), control, Checkpoint::RequestBinding);
    }
    if name.contains('.') {
        return finish_request(Err(missing()), control, Checkpoint::RequestBinding);
    }
    let mut found = None;
    for (index, candidate) in law.declarations.keys().enumerate() {
        phase(control, Checkpoint::RequestBinding)?;
        let matches = candidate.rsplit('.').next() == Some(name);
        if matches {
            if found.is_some() {
                return finish_request(Err(missing()), control, Checkpoint::RequestBinding);
            }
            found = Some(candidate.clone());
        }
        if index + 1 == law.declarations.len() {
            return finish_request(
                found.ok_or_else(missing),
                control,
                Checkpoint::RequestBinding,
            );
        }
        phase(control, Checkpoint::RequestBinding)?;
    }
    finish_request(Err(missing()), control, Checkpoint::RequestBinding)
}
fn binding_constraints(law:&CheckedLaw,map:&CheckedArchMap,requests:&[Request],names:&BTreeMap<String,usize>,req:&Request,params:&[Param],control:&mut Control)->Result<Vec<BindingConstraint>,ResolveFailure>{
    let mut constraints = Vec::new();
    let expected_owners = owner_bindings(req, control)?;
    for param in params {
        checkpoint(control)?;
        phase(control, Checkpoint::RequestBinding)?;
        let key = format!("bind.{}", param.name);
        let Some(arg) = checked_find(
            &req.arguments,
            |a| a.name == key,
            control,
            Checkpoint::RequestBinding,
        )?
        else {
            continue;
        };
        let (plan, projection_owners) = selector_type(
            law,
            map,
            &requests,
            &names,
            &arg.value,
            control,
            (&req.id, &arg.name),
        )?;
        if !projection::can_bind_controlled(&plan.ty, &param.ty, control).map_err(stopped)? {
            return Err(invalid(problem(
                RequestIssueCode::Type,
                &req.id,
                &arg.name,
                "Handle type does not match parameter type",
            )));
        }
        let owner = match &param.ty {
            Type::Owned(_, p) => {
                let key = format!("bind.{p}");
                checked_find(
                    &req.arguments,
                    |a| a.name == key,
                    control,
                    Checkpoint::RequestBinding,
                )?
                .map(|a| a.value.clone())
            }
            _ => None,
        };
        let owner_dynamic = if matches!(arg.value, Selector::Answer { .. }) {
            let relation = projection_owner_check(
                &plan.ty,
                &projection_owners,
                &param.ty,
                &expected_owners,
                control,
            )?;
            match relation {
                Some(dynamic) => dynamic,
                None => {
                    return finish_request(
                        Err(invalid(problem(
                            RequestIssueCode::Type,
                            &req.id,
                            &arg.name,
                            "dependent parameter owner does not match",
                        ))),
                        control,
                        Checkpoint::RequestBinding,
                    );
                }
            }
        } else {
            owner_check(
                map,
                &arg.value,
                &param.ty,
                owner.as_ref(),
                control,
                &req.id,
                &arg.name,
            )?
        };
        let dynamic =
            plan.conditional || matches!(plan.ty, ProjectionType::Dynamic(_)) || owner_dynamic;
        constraints.push(BindingConstraint {
            parameter: param.name.clone(),
            expected: param.ty.clone(),
            selector: arg.value.clone(),
            projection: plan,
            owner,
            projection_owners,
            expected_owners: owner_bindings(req, control)?,
            dynamic,
        });
        phase(control, Checkpoint::RequestBinding)?;
        checkpoint(control)?;
    }
    Ok(constraints)
}

fn parameters(sig: &Signature, kind: QuestionKind) -> Option<&[Param]> {
    match (sig, kind) {
        (Signature::View { params, .. }, QuestionKind::Evaluate | QuestionKind::Quotient)
        | (Signature::Law { params, .. }, QuestionKind::Check | QuestionKind::Solve | QuestionKind::Repair) => Some(params),
        _ => None,
    }
}

fn subject<'a>(
    map: &'a CheckedArchMap,
    snapshot: &str,
    id: &str,
    control: &mut Control,
    context: (&str, &str),
) -> Result<&'a Subject, ResolveFailure> {
    let missing = || {
        invalid(problem(
            RequestIssueCode::Reference,
            context.0,
            context.1,
            "subject does not exist",
        ))
    };
    let snapshot = checked_require(
        &map.snapshots,
        |s| s.id == snapshot,
        control,
        Checkpoint::RequestBinding,
        missing,
    )?;
    checked_require(
        &snapshot.subjects,
        |s| s.id == id,
        control,
        Checkpoint::RequestBinding,
        missing,
    )
}
fn selector_type(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    selector: &Selector,
    control: &mut Control,
    context: (&str, &str),
) -> Result<(ProjectionPlan, BTreeMap<String, Selector>), ResolveFailure> {
    let (request, argument) = context;
    phase(control, Checkpoint::RequestBinding)?;
    let failure = |code, message: &str| invalid(problem(code, request, argument, message));
    let mut owners = BTreeMap::new();
    let plan = match selector {
        Selector::Subject {
            snapshot,
            subject: id,
        } => {
            let s = subject(map, snapshot, id, control, context)?;
            ProjectionPlan {
                ty: ProjectionType::Law(Type::Ref(s.ty.clone())),
                conditional: false,
            }
        }
        Selector::Answer { id, path } => {
            phase(control, Checkpoint::RequestDependency)?;
            let r = &requests[*names
                .get(id)
                .ok_or_else(|| failure(RequestIssueCode::Reference, "request ID does not exist"))?];
            if r.kind == QuestionKind::Needed {
                return Err(failure(
                    RequestIssueCode::Projection,
                    "ObservationPlan has no public projection that can bind to Law",
                ));
            }
            phase(control, Checkpoint::RequestDependency)?;
            let Some(ProjectionStep::Field(field)) = path.first() else {
                return Err(failure(
                    RequestIssueCode::Projection,
                    "specify an output field",
                ));
            };
            // 保持するのは署名と選択された Request の束縛だけであり、view の本体を
            // 評価して参照値を推測しない。後方参照でも同じ有限な表を参照する。
            owners = owner_bindings(r, control)?;
            let initial = if r.kind == QuestionKind::Build {
                build::output_type(law, map, requests, names, r, field, control)?
            } else if matches!(r.kind,QuestionKind::Solve|QuestionKind::Repair) {
                if field=="proposition" || (field=="existence" && r.kind==QuestionKind::Repair) {ProjectionType::Proposition} else {
                    let mut root_request=r.clone();
                    root_request.head=Selector::Declaration{name:law.declarations[r.declaration().expect("changeのLaw")].reading.clone()};
                    let root_types=build::root_types(law,map,requests,names,&root_request,control)?;
                    let types=root_types.into_iter().map(|root|match field.as_str() {
                        "domain"=>Ok(ProjectionType::CandidateSpace(root)),
                        "solutions"=>Ok(ProjectionType::SolutionSet(root)),
                        "object" if r.kind==QuestionKind::Repair=>Ok(ProjectionType::ArchitectureRoot(root)),
                        "repair" if r.kind==QuestionKind::Repair=>Ok(ProjectionType::Repair(root)),
                        _=>Err(failure(RequestIssueCode::Projection,"output of this change request is not public")),
                    }).collect::<Result<Vec<_>,_>>()?;
                    if types.len()==1 {types.into_iter().next().expect("一件")}else{ProjectionType::Dynamic(types)}
                }
            } else if r.kind == QuestionKind::Quotient {
                if field == "proposition" && r.arguments.iter().any(|a| a.name == "law") {
                    ProjectionType::Proposition
                } else {
                if field != "quotient" { return Err(failure(RequestIssueCode::Projection,"quotient output is not public")); }
                let on=&r.arguments.iter().find(|a|a.name=="on").ok_or_else(||failure(RequestIssueCode::MissingBinding,"missing quotient on"))?.value;
                let (plan,_)=selector_type(law,map,requests,names,on,control,(request,"on"))?;
                ProjectionType::Quotient(Box::new(plan.ty))
                }
            } else if matches!(r.kind, QuestionKind::Localize | QuestionKind::Diagnose) {
                local::output_type(r, field)?
            } else if r.kind == QuestionKind::Compare {
                comparison::output_type(r, field)?
            } else if r.kind == QuestionKind::Compose {
                composition::output_type(law, map, requests, names, r, field, control)?
            } else if r.kind == QuestionKind::Map {
                configuration_map::output_type(law, r, field, control)?
            } else {
                let sig = &law.declarations[r.declaration().expect("宣言headの問い")].signature;
                match (r.kind, field.as_str()) {
                    (QuestionKind::Evaluate, "value") => {
                        let Signature::View { returns, .. } = sig else {
                            unreachable!()
                        };
                        ProjectionType::Law(returns.clone())
                    }
                    (QuestionKind::Evaluate, "evaluation") => {
                        let Signature::View { returns, .. } = sig else {
                            unreachable!()
                        };
                        ProjectionType::Evaluation(returns.clone())
                    }
                    (QuestionKind::Check, "proposition") => ProjectionType::Proposition,
                    (QuestionKind::Check, "evaluation") => ProjectionType::Evaluation(Type::Bool),
                    _ => {
                        return Err(failure(
                            RequestIssueCode::Projection,
                            "output is not public for this request",
                        ));
                    }
                }
            };
            match projection::resolve_projection_controlled(law, initial, &path[1..], control) {
                Ok(plan) => plan,
                Err(projection::ProjectionFailure::Invalid(message)) => {
                    return Err(failure(RequestIssueCode::Projection, &message));
                }
                Err(projection::ProjectionFailure::Interrupted(reason)) => {
                    return Err(stopped(reason));
                }
            }
        }
        _ => return Err(failure(RequestIssueCode::Type, "specify a Handle")),
    };
    phase(control, Checkpoint::RequestBinding)?;
    Ok((plan, owners))
}

/// 添字の scope は Request ごとに独立。wire に追加する値入力ではなく、既存束縛の索引。
fn owner_bindings(
    request: &Request,
    control: &mut Control,
) -> Result<BTreeMap<String, Selector>, ResolveFailure> {
    let mut bindings = BTreeMap::new();
    for argument in &request.arguments {
        phase(control, Checkpoint::RequestBinding)?;
        let Some(name) = argument.name.strip_prefix("bind.") else {
            continue;
        };
        bindings.insert(name.to_owned(), clone_selector(&argument.value, control)?);
        phase(control, Checkpoint::RequestBinding)?;
    }
    Ok(bindings)
}

fn clone_selector(selector: &Selector, control: &mut Control) -> Result<Selector, ResolveFailure> {
    phase(control, Checkpoint::RequestBinding)?;
    let selector = match selector {
        Selector::Degree { value } => Selector::Degree { value: *value },
        Selector::Enum { value } => Selector::Enum {
            value: value.clone(),
        },
        Selector::Declaration { name } => Selector::Declaration { name: name.clone() },
        Selector::Subject { snapshot, subject } => Selector::Subject {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
        },
        Selector::Answer { id, path } => {
            let mut steps = Vec::new();
            for step in path {
                phase(control, Checkpoint::RequestBinding)?;
                steps.push(step.clone());
                phase(control, Checkpoint::RequestBinding)?;
            }
            Selector::Answer {
                id: id.clone(),
                path: steps,
            }
        }
    };
    phase(control, Checkpoint::RequestBinding)?;
    Ok(selector)
}

/// Some(false) は所属が型から一致、Some(true) は実値で検査、None は全候補が静的不一致。
/// 異なる Answer の値を同一とも別物とも仮定しない。
fn projection_owner_check(
    actual: &ProjectionType,
    actual_owners: &BTreeMap<String, Selector>,
    expected: &Type,
    expected_owners: &BTreeMap<String, Selector>,
    control: &mut Control,
) -> Result<Option<bool>, ResolveFailure> {
    let mut candidates = vec![actual];
    while let Some(candidate) = candidates.pop() {
        phase(control, Checkpoint::RequestBinding)?;
        let result = match candidate {
            ProjectionType::Dynamic(types) => {
                for ty in types {
                    phase(control, Checkpoint::RequestBinding)?;
                    candidates.push(ty);
                    phase(control, Checkpoint::RequestBinding)?;
                }
                None
            }
            ProjectionType::Law(ty)
                if projection::can_bind_controlled(candidate, expected, control)
                    .map_err(stopped)? =>
            {
                type_owner_check(ty, actual_owners, expected, expected_owners, control)?
            }
            _ => None,
        };
        if result.is_some() || candidates.is_empty() {
            return finish_owner_check(result, control);
        }
        // 一候補の棄却後に停止したら、未検査の候補も棄却したとはしない。
        phase(control, Checkpoint::RequestBinding)?;
    }
    finish_owner_check(None, control)
}

fn finish_owner_check(
    relation: Option<bool>,
    control: &mut Control,
) -> Result<Option<bool>, ResolveFailure> {
    match control.checkpoint(Checkpoint::RequestBinding) {
        Err(StopReason::BudgetExhausted { .. }) if relation.is_none() => Ok(None),
        Err(reason) => Err(stopped(reason)),
        Ok(()) => Ok(relation),
    }
}

fn type_owner_check(
    actual: &Type,
    actual_owners: &BTreeMap<String, Selector>,
    expected: &Type,
    expected_owners: &BTreeMap<String, Selector>,
    control: &mut Control,
) -> Result<Option<bool>, ResolveFailure> {
    let mut pending = vec![(actual, expected)];
    let mut dynamic = false;
    while let Some((actual, expected)) = pending.pop() {
        phase(control, Checkpoint::RequestBinding)?;
        match (actual, expected) {
            (Type::Owned(_, source), Type::Owned(_, target)) => {
                match owner_selector_relation(
                    actual_owners.get(source),
                    expected_owners.get(target),
                    control,
                )? {
                    Some(true) => {}
                    Some(false) => return finish_owner_check(None, control),
                    None => dynamic = true,
                }
            }
            (Type::Ref(_), Type::Owned(_, _)) => dynamic = true,
            (Type::Tuple(left), Type::Tuple(right))
            | (Type::Term(left, _), Type::Term(right, _)) => {
                for pair in left.iter().zip(right) {
                    phase(control, Checkpoint::RequestBinding)?;
                    pending.push(pair);
                    phase(control, Checkpoint::RequestBinding)?;
                }
                if let (Type::Term(_, left), Type::Term(_, right)) = (actual, expected) {
                    pending.push((left, right));
                }
            }
            (Type::List(left), Type::List(right))
            | (Type::Set(left), Type::Set(right))
            | (Type::Option(left), Type::Option(right)) => pending.push((left, right)),
            (Type::Map(a, b), Type::Map(c, d)) => {
                pending.push((a, c));
                pending.push((b, d));
            }
            _ => {}
        }
        phase(control, Checkpoint::RequestBinding)?;
    }
    finish_owner_check(Some(dynamic), control)
}

/// true/false は証明済みの参照同一性/相違。別 Answer や未束縛添字は未知。
fn owner_selector_relation(
    actual: Option<&Selector>,
    expected: Option<&Selector>,
    control: &mut Control,
) -> Result<Option<bool>, ResolveFailure> {
    phase(control, Checkpoint::RequestBinding)?;
    match (actual, expected) {
        (
            Some(Selector::Subject {
                snapshot: a,
                subject: b,
            }),
            Some(Selector::Subject {
                snapshot: c,
                subject: d,
            }),
        ) => Ok(Some(a == c && b == d)),
        (
            Some(Selector::Answer { id: a, path: left }),
            Some(Selector::Answer { id: b, path: right }),
        ) if a == b && left.len() == right.len() => {
            for (left, right) in left.iter().zip(right) {
                phase(control, Checkpoint::RequestBinding)?;
                if left != right {
                    return Ok(None);
                }
                phase(control, Checkpoint::RequestBinding)?;
            }
            Ok(Some(true))
        }
        _ => Ok(None),
    }
}

fn contains_owned(expected: &Type, control: &mut Control) -> Result<bool, ResolveFailure> {
    let mut pending = vec![expected];
    while let Some(ty) = pending.pop() {
        phase(control, Checkpoint::RequestBinding)?;
        match ty {
            Type::Owned(_, _) => {
                phase(control, Checkpoint::RequestBinding)?;
                return Ok(true);
            }
            Type::Tuple(ts) | Type::Term(ts, _) => {
                for t in ts {
                    phase(control, Checkpoint::RequestBinding)?;
                    pending.push(t);
                    phase(control, Checkpoint::RequestBinding)?;
                }
                if let Type::Term(_, ret) = ty {
                    pending.push(ret);
                }
            }
            Type::List(t) | Type::Set(t) | Type::Option(t) => pending.push(t),
            Type::Map(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            _ => {}
        }
        phase(control, Checkpoint::RequestBinding)?;
    }
    phase(control, Checkpoint::RequestBinding)?;
    Ok(false)
}

fn owner_check(
    map: &CheckedArchMap,
    value: &Selector,
    expected: &Type,
    owner: Option<&Selector>,
    control: &mut Control,
    request: &str,
    argument: &str,
) -> Result<bool, ResolveFailure> {
    phase(control, Checkpoint::RequestBinding)?;
    let Type::Owned(_, _) = expected else {
        return contains_owned(expected, control);
    };
    let (
        Selector::Subject {
            snapshot,
            subject: id,
        },
        Some(Selector::Subject {
            snapshot: os,
            subject: oi,
        }),
    ) = (value, owner)
    else {
        phase(control, Checkpoint::RequestBinding)?;
        return Ok(true);
    };
    if snapshot != os {
        let result = Err(invalid(problem(
            RequestIssueCode::Type,
            request,
            argument,
            "dependent parameter owner and subject must belong to the same snapshot",
        )));
        return finish_request(result, control, Checkpoint::RequestBinding);
    }
    let s = subject(map, snapshot, id, control, (request, argument))?;
    let field = checked_find(
        &s.fields,
        |f| f.name.rsplit('.').next() == Some("owner"),
        control,
        Checkpoint::RequestBinding,
    )?;
    let result = match field.map(|f| &f.slot) {
        Some(Slot::Known {
            value: Value::Ref { snapshot, subject },
            ..
        }) => {
            if snapshot == os && subject == oi {
                Ok(false)
            } else {
                Err(invalid(problem(
                    RequestIssueCode::Type,
                    request,
                    argument,
                    "dependent parameter owner does not match",
                )))
            }
        }
        _ => Ok(true),
    };
    finish_request(result, control, Checkpoint::RequestBinding)
}

/// Diagnostics only: the traversal has already established each listed cycle.
fn cycle_failure(requests: &[Request], cyclic: &[usize]) -> ResolveFailure {
    let mut issues = BTreeMap::new();
    for &i in cyclic {
        issues.insert(
            requests[i].id.clone(),
            problem(
                RequestIssueCode::Cycle,
                &requests[i].id,
                &requests[i].id,
                &format!(
                    "cyclic request dependencies: {}; dependency edges of {}: {}",
                    cyclic
                        .iter()
                        .map(|&j| requests[j].id.as_str())
                        .collect::<Vec<_>>()
                        .join(", "),
                    requests[i].id,
                    requests[i]
                        .dependencies
                        .iter()
                        .map(|dep| format!("{} -> {dep}", requests[i].id))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            ),
        );
    }
    ResolveFailure::Invalid {
        requests: requests.to_vec(),
        issues: issues.into_values().collect(),
        stop_reason: None,
    }
}

fn order(
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    control: &mut Control,
) -> Result<(Vec<usize>, Vec<usize>), ResolveFailure> {
    phase(control, Checkpoint::RequestDependency)?;
    let mut deps = Vec::new();
    let mut remaining = Vec::new();
    for request in requests {
        phase(control, Checkpoint::RequestDependency)?;
        let mut targets = Vec::new();
        for id in &request.dependencies {
            phase(control, Checkpoint::RequestDependency)?;
            targets.push(names[id]);
            phase(control, Checkpoint::RequestDependency)?;
        }
        remaining.push(targets.len());
        deps.push(targets);
        phase(control, Checkpoint::RequestDependency)?;
    }
    let mut done = vec![false; requests.len()];
    let mut sorted = Vec::new();
    loop {
        checkpoint(control)?;
        phase(control, Checkpoint::RequestDependency)?;
        let mut ready = None;
        for i in 0..requests.len() {
            phase(control, Checkpoint::RequestDependency)?;
            let matches = !done[i] && remaining[i] == 0;
            phase(control, Checkpoint::RequestDependency)?;
            if matches {
                ready = Some(i);
                break;
            }
        }
        let Some(i) = ready else {
            break;
        };
        done[i] = true;
        sorted.push(i);
        for j in 0..requests.len() {
            phase(control, Checkpoint::RequestDependency)?;
            if checked_find(
                &deps[j],
                |d| *d == i,
                control,
                Checkpoint::RequestDependency,
            )?
            .is_some()
            {
                remaining[j] -= 1;
            }
            phase(control, Checkpoint::RequestDependency)?;
        }
        phase(control, Checkpoint::RequestDependency)?;
        checkpoint(control)?;
    }
    // 未処理の下流も cycle とする誤りを避け、各自へ戻れる node だけを記録する。
    let mut cyclic = Vec::new();
    let result = (|| {
        for start in 0..requests.len() {
            checkpoint(control)?;
            phase(control, Checkpoint::RequestDependency)?;
            if done[start] {
                phase(control, Checkpoint::RequestDependency)?;
                continue;
            }
            let mut seen = BTreeSet::new();
            let mut stack = Vec::new();
            for &dependency in &deps[start] {
                phase(control, Checkpoint::RequestDependency)?;
                stack.push(dependency);
                phase(control, Checkpoint::RequestDependency)?;
            }
            while let Some(i) = stack.pop() {
                checkpoint(control)?;
                phase(control, Checkpoint::RequestDependency)?;
                if i == start {
                    cyclic.push(start);
                    phase(control, Checkpoint::RequestDependency)?;
                    break;
                }
                if seen.insert(i) {
                    for &dependency in &deps[i] {
                        phase(control, Checkpoint::RequestDependency)?;
                        stack.push(dependency);
                        phase(control, Checkpoint::RequestDependency)?;
                    }
                }
                phase(control, Checkpoint::RequestDependency)?;
            }
            phase(control, Checkpoint::RequestDependency)?;
        }
        phase(control, Checkpoint::RequestDependency)?;
        Ok(())
    })();
    if let Err(error) = result {
        if !cyclic.is_empty()
            && matches!(
                error,
                ResolveFailure::Interrupted {
                    reason: StopReason::BudgetExhausted { .. }
                }
            )
        {
            // Keep only the cycles already witnessed; do not continue traversal after the stop.
            return finish_request(
                Err(cycle_failure(requests, &cyclic)),
                control,
                Checkpoint::RequestDependency,
            );
        }
        return Err(error);
    }

    Ok((sorted, cyclic))
}

struct RawRequest {
    id: String,
    kind: String,
    head: Selector,
    arguments: Vec<(String, Selector)>,
}
struct Parser<'a> {
    src: &'a str,
    at: usize,
    id: String,
    control: Control,
}
impl<'a> Parser<'a> {
    // clone した制御も元と同じ probe・停止 latch を共有する。
    fn new(src: &'a str, control: &Control) -> Self {
        Self {
            src,
            at: 0,
            id: String::new(),
            control: control.clone(),
        }
    }
    fn tick(&mut self) -> Result<(), ResolveFailure> {
        phase(&mut self.control, Checkpoint::RequestSyntax)
    }
    fn error(&mut self, message: &str) -> ResolveFailure {
        let failure = invalid(problem(
            RequestIssueCode::Syntax,
            &self.id,
            self.src,
            message,
        ));
        finish_request::<()>(Err(failure), &mut self.control, Checkpoint::RequestSyntax)
            .unwrap_err()
    }

    fn ws(&mut self) -> Result<(), ResolveFailure> {
        self.tick()?;
        while self
            .src
            .as_bytes()
            .get(self.at)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.tick()?;
            self.at += 1;
            self.tick()?;
        }
        self.tick()
    }
    fn take(&mut self, c: u8) -> Result<bool, ResolveFailure> {
        self.tick()?;
        self.ws()?;
        let matched = self.src.as_bytes().get(self.at) == Some(&c);
        if matched {
            self.at += 1;
        }
        self.tick()?;
        Ok(matched)
    }
    fn expect(&mut self, c: u8) -> Result<(), ResolveFailure> {
        self.tick()?;
        self.ws()?;
        let result = if self.src.as_bytes().get(self.at) == Some(&c) {
            self.at += 1;
            Ok(())
        } else {
            Err(invalid(problem(
                RequestIssueCode::Syntax,
                &self.id,
                self.src,
                "invalid request separator",
            )))
        };
        finish_request(result, &mut self.control, Checkpoint::RequestSyntax)
    }
    fn name(&mut self, id: bool) -> Result<String, ResolveFailure> {
        self.tick()?;
        self.ws()?;
        let start = self.at;
        if !self
            .src
            .as_bytes()
            .get(self.at)
            .is_some_and(u8::is_ascii_alphabetic)
        {
            return Err(self.error("specify an identifier"));
        }
        self.at += 1;
        self.tick()?;
        while self.src.as_bytes().get(self.at).is_some_and(|b| {
            b.is_ascii_alphanumeric() || *b == b'_' || (id && matches!(b, b'.' | b'-'))
        }) {
            self.tick()?;
            self.at += 1;
            self.tick()?;
        }
        let name = self.src[start..self.at].to_owned();
        self.tick()?;
        Ok(name)
    }
    fn user_name(&mut self) -> Result<String, ResolveFailure> {
        self.tick()?;
        let name = self.name(false)?;
        let is_reserved = crate::law::parser::is_reserved(&name);
        if is_reserved {
            return Err(self.error("reserved word cannot be used as an identifier"));
        }
        self.tick()?;
        Ok(name)
    }
    fn selector(&mut self) -> Result<Selector, ResolveFailure> {
        self.tick()?;
        if self.take(b'@')? {
            let snapshot = self.name(true)?;
            self.expect(b'/')?;
            let subject = self.name(true)?;
            self.tick()?;
            return Ok(Selector::Subject { snapshot, subject });
        }
        if self.take(b'$')? {
            let id = self.user_name()?;
            let mut path = Vec::new();
            loop {
                self.tick()?;
                if self.take(b'.')? {
                    path.push(ProjectionStep::Field(self.name(false)?));
                } else if self.take(b'[')? {
                    self.ws()?;
                    let start = self.at;
                    let mut n = Some(0u64);
                    while self
                        .src
                        .as_bytes()
                        .get(self.at)
                        .is_some_and(u8::is_ascii_digit)
                    {
                        self.tick()?;
                        let digit = u64::from(self.src.as_bytes()[self.at] - b'0');
                        n = n
                            .and_then(|n| n.checked_mul(10))
                            .and_then(|n| n.checked_add(digit));
                        self.at += 1;
                        self.tick()?;
                    }
                    let digits = &self.src[start..self.at];
                    if digits.is_empty() || (digits.len() > 1 && digits.starts_with('0')) {
                        return Err(self.error("index must be a normalized nonnegative integer"));
                    }
                    let n = n
                        .filter(|n| *n <= 9_007_199_254_740_991)
                        .ok_or_else(|| self.error("index exceeds the Nat limit"))?;
                    self.expect(b']')?;
                    path.push(ProjectionStep::Index(n));
                } else {
                    self.tick()?;
                    break;
                }
                self.tick()?;
            }
            self.tick()?;
            return Ok(Selector::Answer { id, path });
        }
        let mut name = self.user_name()?;
        while self.take(b'.')? {
            self.tick()?;
            name.push('.');
            name.push_str(&self.user_name()?);
            self.tick()?;
        }
        self.tick()?;
        Ok(Selector::Declaration { name })
    }
    fn degree(&mut self) -> Result<u64, ResolveFailure> {
        self.ws()?;
        let start = self.at;
        let mut value = 0u64;
        while let Some(digit) = self.src.as_bytes().get(self.at).copied().filter(u8::is_ascii_digit) {
            self.tick()?;
            value = value.checked_mul(10).and_then(|n| n.checked_add(u64::from(digit-b'0')))
                .filter(|n| *n <= 9_007_199_254_740_991).ok_or_else(||self.error("degree exceeds the Nat limit"))?;
            self.at += 1;
        }
        if start == self.at || (self.at-start>1 && self.src.as_bytes()[start]==b'0') {return Err(self.error("degree must be a normalized nonnegative integer"));}
        Ok(value)
    }
    fn parse(mut self) -> Result<RawRequest, ResolveFailure> {
        self.tick()?;
        self.id = self.user_name()?;
        self.expect(b'=')?;
        let kind = self.name(false)?;
        self.expect(b'(')?;
        let head = self.selector()?;
        let mut arguments = Vec::new();
        let mut keys = BTreeSet::new();
        while self.take(b',')? {
            self.tick()?;
            let mut key = self.name(false)?;
            if self.take(b'.')? {
                if key != "bind" {
                    return Err(self.error("binding key prefix must be bind"));
                }
                key.push('.');
                key.push_str(&self.name(false)?);
            }
            let duplicate = !keys.insert(key.clone());
            let result = if duplicate {
                Err(invalid(problem(
                    RequestIssueCode::DuplicateArgument,
                    &self.id,
                    &key,
                    "duplicate argument name",
                )))
            } else {
                Ok(())
            };
            finish_request(result, &mut self.control, Checkpoint::RequestSyntax)?;
            self.expect(b'=')?;
            let value = if kind == "diagnose" && key == "degree" {
                Selector::Degree { value: self.degree()? }
            } else if kind == "diagnose" && key == "side" {
                Selector::Enum { value: self.name(false)? }
            } else if kind == "compare" && key == "kind" {
                // relationはLawの予約語でも、ここでは比較kindの固定語である。
                Selector::Declaration { name: self.name(false)? }
            } else {
                self.selector()?
            };
            arguments.push((key, value));
            self.tick()?;
        }
        self.expect(b')')?;
        self.ws()?;
        if self.at != self.src.len() {
            return Err(self.error("unexpected tokens after request"));
        }
        self.tick()?;
        Ok(RawRequest {
            id: self.id,
            kind,
            head,
            arguments,
        })
    }
}

#[cfg(test)]
mod required_predicate_priority_tests {
    use super::*;
    use crate::observed::control::{Limits, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};

    fn probe(point: Checkpoint, at: usize, mode: usize) -> Control {
        let seen = Rc::new(Cell::new(0));
        Control::new(
            Limits {
                time_ms: (mode == 1).then_some(1),
                memory_mib: (mode == 2).then_some(1),
            },
            move |current| {
                if current == point {
                    seen.set(seen.get() + 1);
                }
                let stop = seen.get() >= at;
                Usage {
                    signal: (stop && mode == 0).then_some(Signal::Term),
                    elapsed_ms: u128::from(stop && mode == 1),
                    memory_mib: u128::from(stop && mode == 2),
                }
            },
        )
    }
    #[test]
    fn required_and_optional_delimiter_false_have_different_priority() {
        for mode in 0..3 {
            // take/expect pre 1, ws pre/post 2/3, mismatch post 4.
            let control = probe(Checkpoint::RequestSyntax, 4, mode);
            let mut parser = Parser::new("!", &control);
            assert!(matches!(
                parser.take(b'='),
                Err(ResolveFailure::Interrupted { .. })
            ));
            let control = probe(Checkpoint::RequestSyntax, 4, mode);
            let mut parser = Parser::new("!", &control);
            parser.id = "a".into();
            let result = parser.expect(b'=').unwrap_err();
            if mode == 0 {
                assert!(matches!(result, ResolveFailure::Interrupted { .. }));
            } else {
                assert!(
                    matches!(result, ResolveFailure::Invalid { issues, stop_reason: Some(StopReason::BudgetExhausted { .. }), .. }
                    if issues == [problem(RequestIssueCode::Syntax, "a", "!", "invalid request separator")])
                );
            }
        }
    }
    #[test]
    fn required_lookup_only_promotes_the_exhausted_search_to_reference() {
        for mode in 0..3 {
            for at in [3, 5] {
                // pre 1, candidate 1 pre/post 2/3, candidate 2 pre/post 4/5.
                let mut control = probe(Checkpoint::RequestBinding, at, mode);
                let error = checked_require(
                    &[1, 2],
                    |value| *value == 3,
                    &mut control,
                    Checkpoint::RequestBinding,
                    || invalid(problem(RequestIssueCode::Reference, "a", "x", "missing")),
                )
                .unwrap_err();
                if at == 5 && mode != 0 {
                    assert!(
                        matches!(error, ResolveFailure::Invalid { issues, stop_reason: Some(StopReason::BudgetExhausted { .. }), .. }
                        if issues == [problem(RequestIssueCode::Reference, "a", "x", "missing")])
                    );
                } else {
                    assert!(matches!(error, ResolveFailure::Interrupted { .. }));
                }
                let mut control = probe(Checkpoint::RequestBinding, at, mode);
                assert!(matches!(
                    checked_find(
                        &[1, 2],
                        |value| *value == 3,
                        &mut control,
                        Checkpoint::RequestBinding
                    ),
                    Err(ResolveFailure::Interrupted { .. })
                ));
            }
        }
    }
}
