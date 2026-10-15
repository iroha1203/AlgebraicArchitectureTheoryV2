//! 観測環境の evaluate/check 要求。原文と束縛、依存順、動的な型・owner 制約を保持する。

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuestionKind {
    Evaluate,
    Check,
}
impl QuestionKind {
    pub fn wire(self) -> &'static str {
        match self {
            Self::Evaluate => "evaluate",
            Self::Check => "check",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Selector {
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
    ObservedEnvironment,
    UniversalParameters {
        declaration: String,
        parameters: Vec<String>,
    },
}
impl RequestDefault {
    pub fn wire(&self) -> Json {
        match self {
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
    pub fn declaration(&self) -> &str {
        match &self.head {
            Selector::Declaration { name } => name,
            _ => unreachable!("解決済み head"),
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
            ("message", Json::str(&self.message)),
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
    let result = resolve_inner(law, map, texts, control);
    finish_request(result, control, Checkpoint::Resolve)
}

fn resolve_inner(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    texts: &[&str],
    control: &mut Control,
) -> Result<ResolvedRequests, ResolveFailure> {
    let mut requests = Vec::new();
    let mut names = BTreeMap::new();
    for text in texts {
        checkpoint(control)?;
        let mut prefix = Parser::new(text, control);
        prefix.id = prefix.user_name()?;
        prefix.expect(b'=')?;
        let prefix_kind = prefix.name(false)?;
        prefix.expect(b'(')?;
        if matches!(
            prefix_kind.as_str(),
            "build"
                | "map"
                | "compose"
                | "compare"
                | "localize"
                | "diagnose"
                | "repair"
                | "solve"
                | "quotient"
                | "needed"
        ) {
            return Err(ResolveFailure::NotApplicable {
                request: prefix.id,
                kind: prefix_kind,
                architecture_environment: false,
            });
        }
        let raw = Parser::new(text, control).parse()?;
        phase(control, Checkpoint::RequestBinding)?;
        if names.contains_key(&raw.id) {
            return Err(invalid(problem(
                RequestIssueCode::DuplicateId,
                &raw.id,
                &raw.id,
                "問い ID が重複している",
            )));
        }
        let kind = match raw.kind.as_str() {
            "evaluate" => QuestionKind::Evaluate,
            "check" => QuestionKind::Check,
            _ => {
                return Err(invalid(problem(
                    RequestIssueCode::Syntax,
                    &raw.id,
                    &raw.kind,
                    "未知の問い kind",
                )));
            }
        };
        if checked_find(
            &raw.arguments,
            |(key, _)| key == "on",
            control,
            Checkpoint::RequestBinding,
        )?
        .is_some()
        {
            return Err(ResolveFailure::NotApplicable {
                request: raw.id,
                kind: raw.kind,
                architecture_environment: true,
            });
        }
        let Selector::Declaration { name } = &raw.head else {
            return Err(invalid(problem(
                RequestIssueCode::Reference,
                &raw.id,
                "head",
                "宣言名を指定する",
            )));
        };
        let full = declaration(law, name, control)?.ok_or_else(|| {
            invalid(problem(
                RequestIssueCode::Reference,
                &raw.id,
                name,
                "宣言名が存在しないか曖昧",
            ))
        })?;
        let params = parameters(&law.declarations[&full].signature, kind).ok_or_else(|| {
            invalid(problem(
                RequestIssueCode::Type,
                &raw.id,
                name,
                "問いと宣言の種類が合わない",
            ))
        })?;
        let mut arguments = BTreeMap::new();
        let mut dependencies = BTreeSet::new();
        for (key, value) in raw.arguments {
            phase(control, Checkpoint::RequestBinding)?;
            let name = key.strip_prefix("bind.").unwrap_or(&key);
            if checked_find(
                params,
                |p| p.name == name,
                control,
                Checkpoint::RequestBinding,
            )?
            .is_none()
            {
                return Err(invalid(problem(
                    RequestIssueCode::Reference,
                    &raw.id,
                    &key,
                    "未知の parameter",
                )));
            }
            if matches!(value, Selector::Declaration { .. }) {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &raw.id,
                    &key,
                    "parameter には Handle を指定する",
                )));
            }
            if let Selector::Answer { id, path } = &value {
                phase(control, Checkpoint::RequestDependency)?;
                if path.is_empty() {
                    return Err(invalid(problem(
                        RequestIssueCode::Projection,
                        &raw.id,
                        &key,
                        "出力 field を指定する",
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
                    "同じ parameter の束縛が重複している",
                )))
            } else {
                Ok(())
            };
            finish_request(result, control, Checkpoint::RequestBinding)?;
        }
        let mut unbound = Vec::new();
        for param in params {
            phase(control, Checkpoint::RequestBinding)?;
            if !arguments.contains_key(&format!("bind.{}", param.name)) {
                unbound.push(param.name.clone());
            }
            phase(control, Checkpoint::RequestBinding)?;
        }
        if kind == QuestionKind::Evaluate && !unbound.is_empty() {
            return Err(invalid(problem(
                RequestIssueCode::MissingBinding,
                &raw.id,
                &unbound[0],
                "view の全 parameter を束縛する",
            )));
        }
        let mut defaults = vec![RequestDefault::ObservedEnvironment];
        if !unbound.is_empty() {
            defaults.push(RequestDefault::UniversalParameters {
                declaration: full.clone(),
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
    for i in 0..requests.len() {
        checkpoint(control)?;
        phase(control, Checkpoint::RequestBinding)?;
        let req = &requests[i];
        let params = parameters(&law.declarations[req.declaration()].signature, req.kind).unwrap();
        let mut constraints = Vec::new();
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
            let plan = selector_type(
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
                    "Handle の型が parameter 型と合わない",
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
            let owner_dynamic = owner_check(
                map,
                &arg.value,
                &param.ty,
                owner.as_ref(),
                control,
                &req.id,
                &arg.name,
            )?;
            let dynamic =
                plan.conditional || matches!(plan.ty, ProjectionType::Dynamic(_)) || owner_dynamic;
            constraints.push(BindingConstraint {
                parameter: param.name.clone(),
                expected: param.ty.clone(),
                selector: arg.value.clone(),
                projection: plan,
                owner,
                dynamic,
            });
            phase(control, Checkpoint::RequestBinding)?;
            checkpoint(control)?;
        }
        requests[i].constraints = constraints;
        phase(control, Checkpoint::RequestBinding)?;
        checkpoint(control)?;
    }
    let (evaluation_order, cyclic) = order(&requests, &names, control)?;
    if !cyclic.is_empty() {
        return finish_request(
            Err(cycle_failure(&requests, &cyclic)),
            control,
            Checkpoint::RequestDependency,
        );
    }
    phase(control, Checkpoint::RequestDependency)?;
    Ok(ResolvedRequests {
        requests,
        evaluation_order,
    })
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

/// 小さい検索も早期一致・不一致を返す前に共有制御を再確認する。
fn checked_find<'a, T>(
    items: &'a [T],
    mut predicate: impl FnMut(&T) -> bool,
    control: &mut Control,
    point: Checkpoint,
) -> Result<Option<&'a T>, ResolveFailure> {
    phase(control, point)?;
    for item in items {
        phase(control, point)?;
        let found = predicate(item);
        phase(control, point)?;
        if found {
            return Ok(Some(item));
        }
    }
    phase(control, point)?;
    Ok(None)
}

fn declaration(
    law: &CheckedLaw,
    name: &str,
    control: &mut Control,
) -> Result<Option<String>, ResolveFailure> {
    phase(control, Checkpoint::RequestBinding)?;
    if law.declarations.contains_key(name) {
        phase(control, Checkpoint::RequestBinding)?;
        return Ok(Some(name.to_owned()));
    }
    if name.contains('.') {
        phase(control, Checkpoint::RequestBinding)?;
        return Ok(None);
    }
    let mut found = None;
    for candidate in law.declarations.keys() {
        phase(control, Checkpoint::RequestBinding)?;
        let matches = candidate.rsplit('.').next() == Some(name);
        phase(control, Checkpoint::RequestBinding)?;
        if matches {
            if found.is_some() {
                return Ok(None);
            }
            found = Some(candidate.clone());
        }
    }
    phase(control, Checkpoint::RequestBinding)?;
    Ok(found)
}
fn parameters(sig: &Signature, kind: QuestionKind) -> Option<&[Param]> {
    match (sig, kind) {
        (Signature::View { params, .. }, QuestionKind::Evaluate)
        | (Signature::Law { params, .. }, QuestionKind::Check) => Some(params),
        _ => None,
    }
}

fn subject<'a>(
    map: &'a CheckedArchMap,
    snapshot: &str,
    id: &str,
    control: &mut Control,
) -> Result<Option<&'a Subject>, ResolveFailure> {
    let Some(snapshot) = checked_find(
        &map.snapshots,
        |s| s.id == snapshot,
        control,
        Checkpoint::RequestBinding,
    )?
    else {
        return Ok(None);
    };
    checked_find(
        &snapshot.subjects,
        |s| s.id == id,
        control,
        Checkpoint::RequestBinding,
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
) -> Result<ProjectionPlan, ResolveFailure> {
    let (request, argument) = context;
    phase(control, Checkpoint::RequestBinding)?;
    let failure = |code, message: &str| invalid(problem(code, request, argument, message));
    let plan = match selector {
        Selector::Subject {
            snapshot,
            subject: id,
        } => {
            let s = subject(map, snapshot, id, control)?
                .ok_or_else(|| failure(RequestIssueCode::Reference, "subject が存在しない"))?;
            ProjectionPlan {
                ty: ProjectionType::Law(Type::Ref(s.ty.clone())),
                conditional: false,
            }
        }
        Selector::Answer { id, path } => {
            phase(control, Checkpoint::RequestDependency)?;
            let r = &requests[*names
                .get(id)
                .ok_or_else(|| failure(RequestIssueCode::Reference, "問い ID が存在しない"))?];
            phase(control, Checkpoint::RequestDependency)?;
            let Some(ProjectionStep::Field(field)) = path.first() else {
                return Err(failure(
                    RequestIssueCode::Projection,
                    "出力 field を指定する",
                ));
            };
            let sig = &law.declarations[r.declaration()].signature;
            let initial = match (r.kind, field.as_str()) {
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
                        "この問いで公開されていない出力",
                    ));
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
        _ => return Err(failure(RequestIssueCode::Type, "Handle を指定する")),
    };
    phase(control, Checkpoint::RequestBinding)?;
    Ok(plan)
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
            "依存 parameter の owner と subject は同じ snapshot に属する",
        )));
        return finish_request(result, control, Checkpoint::RequestBinding);
    }
    let s = subject(map, snapshot, id, control)?.ok_or_else(|| {
        invalid(problem(
            RequestIssueCode::Reference,
            request,
            argument,
            "subject が存在しない",
        ))
    })?;
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
                    "依存 parameter の owner が合わない",
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
                "問いの依存に循環がある",
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
        if self.take(c)? {
            Ok(())
        } else {
            Err(self.error("要求の区切りが不正"))
        }
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
            return Err(self.error("識別子を指定する"));
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
            return Err(self.error("予約語は識別子に使えない"));
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
                        return Err(self.error("index は正規化した非負整数で指定する"));
                    }
                    let n = n
                        .filter(|n| *n <= 9_007_199_254_740_991)
                        .ok_or_else(|| self.error("index が Nat の上限を超える"))?;
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
                    return Err(self.error("束縛 key の接頭辞は bind"));
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
                    "引数名が重複している",
                )))
            } else {
                Ok(())
            };
            finish_request(result, &mut self.control, Checkpoint::RequestSyntax)?;
            self.expect(b'=')?;
            arguments.push((key, self.selector()?));
            self.tick()?;
        }
        self.expect(b')')?;
        self.ws()?;
        if self.at != self.src.len() {
            return Err(self.error("要求の末尾に余分な字句がある"));
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
