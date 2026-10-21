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
#[path = "request_map.rs"]
mod configuration_map;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuestionKind {
    Evaluate,
    Check,
    Needed,
    Map,
}
impl QuestionKind {
    pub fn wire(self) -> &'static str {
        match self {
            Self::Evaluate => "evaluate",
            Self::Check => "check",
            Self::Needed => "needed",
            Self::Map => "map",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Selector {
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
    /// Law/view宣言を選ぶ問いの名前。原始correspondenceと問いIDのheadは含めない。
    pub fn declaration(&self) -> Option<&str> {
        if self.kind == QuestionKind::Map {
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
                | "compose"
                | "compare"
                | "localize"
                | "diagnose"
                | "repair"
                | "solve"
                | "quotient"
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
            "needed" => QuestionKind::Needed,
            "map" => QuestionKind::Map,
            _ => {
                return Err(invalid(problem(
                    RequestIssueCode::Syntax,
                    &raw.id,
                    &raw.kind,
                    "未知の問い kind",
                )));
            }
        };
        if kind == QuestionKind::Map {
            let request = configuration_map::resolve(law, raw, text, control)?;
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
                    "neededは問いIDを $Id で指定する",
                )));
            };
            if !path.is_empty() || !raw.arguments.is_empty() {
                return Err(invalid(problem(
                    RequestIssueCode::Syntax,
                    &raw.id,
                    "head",
                    "neededは出力fieldや追加引数を取らない",
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
        let full = declaration(law, name, control, &raw.id)?;
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
                        "未知の parameter",
                    ))
                },
            )?;
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
                if kind == QuestionKind::Evaluate {
                    return finish_request(
                        Err(invalid(problem(
                            RequestIssueCode::MissingBinding,
                            &raw.id,
                            &param.name,
                            "view の全 parameter を束縛する",
                        ))),
                        control,
                        Checkpoint::RequestBinding,
                    );
                }
                unbound.push(param.name.clone());
            }
            phase(control, Checkpoint::RequestBinding)?;
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
                    "問いIDが存在しない",
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
                                "依存 parameter の owner が合わない",
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
    // 共通の参照・型・公開射影・循環の検査を完了してから、未実装経路を通知する。
    for request in &requests {
        if request.kind == QuestionKind::Map
            && request.arguments.iter().any(|a| {
                a.name == "kind"
                    && matches!(&a.value,Selector::Enum {value} if value=="object_algebra")
            })
        {
            return Err(ResolveFailure::NotApplicable {
                request: request.id.clone(),
                kind: "map".into(),
                architecture_environment: false,
            });
        }
    }
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
            "宣言名が存在しないか曖昧",
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
    context: (&str, &str),
) -> Result<&'a Subject, ResolveFailure> {
    let missing = || {
        invalid(problem(
            RequestIssueCode::Reference,
            context.0,
            context.1,
            "subject が存在しない",
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
                .ok_or_else(|| failure(RequestIssueCode::Reference, "問い ID が存在しない"))?];
            if r.kind == QuestionKind::Needed {
                return Err(failure(
                    RequestIssueCode::Projection,
                    "ObservationPlanはLawへ束縛できる公開射影を持たない",
                ));
            }
            phase(control, Checkpoint::RequestDependency)?;
            let Some(ProjectionStep::Field(field)) = path.first() else {
                return Err(failure(
                    RequestIssueCode::Projection,
                    "出力 field を指定する",
                ));
            };
            // 保持するのは署名と選択された Request の束縛だけであり、view の本体を
            // 評価して参照値を推測しない。後方参照でも同じ有限な表を参照する。
            owners = owner_bindings(r, control)?;
            let initial = if r.kind == QuestionKind::Map {
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
                            "この問いで公開されていない出力",
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
        _ => return Err(failure(RequestIssueCode::Type, "Handle を指定する")),
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
            "依存 parameter の owner と subject は同じ snapshot に属する",
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
                &format!(
                    "問いの依存に循環がある: {}。{} の依存辺: {}",
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
                "要求の区切りが不正",
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
                    if issues == [problem(RequestIssueCode::Syntax, "a", "!", "要求の区切りが不正")])
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
