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
    let mut requests = Vec::new();
    let mut names = BTreeMap::new();
    for text in texts {
        checkpoint(control)?;
        let mut prefix = Parser::new(text);
        prefix.id = prefix.user_name().map_err(invalid)?;
        prefix.expect(b'=').map_err(invalid)?;
        let prefix_kind = prefix.name(false).map_err(invalid)?;
        prefix.expect(b'(').map_err(invalid)?;
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
        let raw = Parser::new(text).parse().map_err(invalid)?;
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
            "build" | "map" | "compose" | "compare" | "localize" | "diagnose" | "repair"
            | "solve" | "quotient" | "needed" => {
                return Err(ResolveFailure::NotApplicable {
                    request: raw.id,
                    kind: raw.kind,
                    architecture_environment: false,
                });
            }
            _ => {
                return Err(invalid(problem(
                    RequestIssueCode::Syntax,
                    &raw.id,
                    &raw.kind,
                    "未知の問い kind",
                )));
            }
        };
        if raw.arguments.iter().any(|(key, _)| key == "on") {
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
        let full = declaration(law, name).ok_or_else(|| {
            invalid(problem(
                RequestIssueCode::Reference,
                &raw.id,
                name,
                "宣言名が存在しないか曖昧",
            ))
        })?;
        let sig = &law.declarations[&full].signature;
        let params = parameters(sig, kind).ok_or_else(|| {
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
            let name = key.strip_prefix("bind.").unwrap_or(&key);
            if !params.iter().any(|p| p.name == name) {
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
                if path.is_empty() {
                    return Err(invalid(problem(
                        RequestIssueCode::Projection,
                        &raw.id,
                        &key,
                        "出力 field を指定する",
                    )));
                }
                dependencies.insert(id.clone());
            }
            let normalized = format!("bind.{name}");
            if arguments
                .insert(
                    normalized.clone(),
                    RequestArgument {
                        name: normalized,
                        value,
                        origin: ArgumentOrigin::Explicit,
                    },
                )
                .is_some()
            {
                return Err(invalid(problem(
                    RequestIssueCode::DuplicateArgument,
                    &raw.id,
                    &key,
                    "同じ parameter の束縛が重複している",
                )));
            }
        }
        let unbound: Vec<_> = params
            .iter()
            .filter(|p| !arguments.contains_key(&format!("bind.{}", p.name)))
            .map(|p| p.name.clone())
            .collect();
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
        names.insert(raw.id.clone(), requests.len());
        requests.push(Request {
            id: raw.id,
            text: (*text).to_owned(),
            kind,
            head: Selector::Declaration { name: full },
            arguments: arguments.into_values().collect(),
            defaults,
            dependencies: dependencies.into_iter().collect(),
            constraints: vec![],
        });
        checkpoint(control)?;
    }
    for i in 0..requests.len() {
        checkpoint(control)?;
        let req = &requests[i];
        let params = parameters(&law.declarations[req.declaration()].signature, req.kind).unwrap();
        let mut constraints = Vec::new();
        for param in params {
            checkpoint(control)?;
            let Some(arg) = req
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", param.name))
            else {
                continue;
            };
            let plan = selector_type(law, map, &requests, &names, &arg.value)
                .map_err(|(code, message)| invalid(problem(code, &req.id, &arg.name, &message)))?;
            if !projection::can_bind(&plan.ty, &param.ty) {
                return Err(invalid(problem(
                    RequestIssueCode::Type,
                    &req.id,
                    &arg.name,
                    "Handle の型が parameter 型と合わない",
                )));
            }
            let owner = match &param.ty {
                Type::Owned(_, p) => req
                    .arguments
                    .iter()
                    .find(|a| a.name == format!("bind.{p}"))
                    .map(|a| a.value.clone()),
                _ => None,
            };
            let owner_dynamic =
                owner_check(map, &arg.value, &param.ty, owner.as_ref()).map_err(|message| {
                    invalid(problem(
                        RequestIssueCode::Type,
                        &req.id,
                        &arg.name,
                        &message,
                    ))
                })?;
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
            checkpoint(control)?;
        }
        requests[i].constraints = constraints;
        checkpoint(control)?;
    }
    let (evaluation_order, cyclic) = order(&requests, &names, control)?;
    if !cyclic.is_empty() {
        let mut issues: Vec<_> = cyclic
            .into_iter()
            .map(|i| {
                problem(
                    RequestIssueCode::Cycle,
                    &requests[i].id,
                    &requests[i].id,
                    "問いの依存に循環がある",
                )
            })
            .collect();
        issues.sort_by(|a, b| a.request.cmp(&b.request));
        return Err(ResolveFailure::Invalid { requests, issues });
    }
    Ok(ResolvedRequests {
        requests,
        evaluation_order,
    })
}

fn checkpoint(control: &mut Control) -> Result<(), ResolveFailure> {
    control
        .checkpoint(Checkpoint::Resolve)
        .map_err(|reason| ResolveFailure::Interrupted { reason })
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
    }
}

fn declaration(law: &CheckedLaw, name: &str) -> Option<String> {
    if law.declarations.contains_key(name) {
        return Some(name.to_owned());
    }
    if name.contains('.') {
        return None;
    }
    let mut choices = law
        .declarations
        .keys()
        .filter(|n| n.rsplit('.').next() == Some(name));
    let first = choices.next()?;
    if choices.next().is_some() {
        None
    } else {
        Some(first.clone())
    }
}
fn parameters(sig: &Signature, kind: QuestionKind) -> Option<&[Param]> {
    match (sig, kind) {
        (Signature::View { params, .. }, QuestionKind::Evaluate)
        | (Signature::Law { params, .. }, QuestionKind::Check) => Some(params),
        _ => None,
    }
}

fn subject<'a>(map: &'a CheckedArchMap, snapshot: &str, subject: &str) -> Option<&'a Subject> {
    map.snapshots
        .iter()
        .find(|s| s.id == snapshot)?
        .subjects
        .iter()
        .find(|s| s.id == subject)
}
fn selector_type(
    law: &CheckedLaw,
    map: &CheckedArchMap,
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    selector: &Selector,
) -> Result<ProjectionPlan, (RequestIssueCode, String)> {
    let failure = |code, message: &str| (code, message.to_owned());
    match selector {
        Selector::Subject {
            snapshot,
            subject: id,
        } => {
            let s = subject(map, snapshot, id)
                .ok_or_else(|| failure(RequestIssueCode::Reference, "subject が存在しない"))?;
            Ok(ProjectionPlan {
                ty: ProjectionType::Law(Type::Ref(s.ty.clone())),
                conditional: false,
            })
        }
        Selector::Answer { id, path } => {
            let r = &requests[*names
                .get(id)
                .ok_or_else(|| failure(RequestIssueCode::Reference, "問い ID が存在しない"))?];
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
            projection::resolve_projection(law, initial, &path[1..])
                .map_err(|m| (RequestIssueCode::Projection, m))
        }
        _ => Err(failure(RequestIssueCode::Type, "Handle を指定する")),
    }
}

fn owner_check(
    map: &CheckedArchMap,
    value: &Selector,
    expected: &Type,
    owner: Option<&Selector>,
) -> Result<bool, String> {
    let Type::Owned(_, _) = expected else {
        return Ok(expected.any(&mut |t| matches!(t, Type::Owned(_, _))));
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
        return Ok(true);
    };
    let s = subject(map, snapshot, id).ok_or("subject が存在しない")?;
    let field = s
        .fields
        .iter()
        .find(|f| f.name.rsplit('.').next() == Some("owner"));
    match field.map(|f| &f.slot) {
        Some(Slot::Known {
            value: Value::Ref { snapshot, subject },
            ..
        }) => {
            if snapshot == os && subject == oi {
                Ok(false)
            } else {
                Err("依存 parameter の owner が合わない".into())
            }
        }
        _ => Ok(true),
    }
}

fn order(
    requests: &[Request],
    names: &BTreeMap<String, usize>,
    control: &mut Control,
) -> Result<(Vec<usize>, Vec<usize>), ResolveFailure> {
    let deps: Vec<Vec<usize>> = requests
        .iter()
        .map(|r| r.dependencies.iter().map(|d| names[d]).collect())
        .collect();
    let mut remaining: Vec<_> = deps.iter().map(Vec::len).collect();
    let mut done = vec![false; requests.len()];
    let mut sorted = Vec::new();
    loop {
        checkpoint(control)?;
        let Some(i) = (0..requests.len()).find(|&i| !done[i] && remaining[i] == 0) else {
            break;
        };
        done[i] = true;
        sorted.push(i);
        for j in 0..requests.len() {
            if deps[j].contains(&i) {
                remaining[j] -= 1;
            }
        }
        checkpoint(control)?;
    }
    // 未処理の下流も cycle とする誤りを避け、各自へ戻れる node だけを記録する。
    let mut cyclic = Vec::new();
    for start in 0..requests.len() {
        checkpoint(control)?;
        if done[start] {
            continue;
        }
        let mut seen = BTreeSet::new();
        let mut stack = deps[start].clone();
        while let Some(i) = stack.pop() {
            checkpoint(control)?;
            if i == start {
                cyclic.push(start);
                break;
            }
            if seen.insert(i) {
                stack.extend(&deps[i]);
            }
        }
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
}
impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src,
            at: 0,
            id: String::new(),
        }
    }
    fn error(&self, message: &str) -> RequestIssue {
        problem(RequestIssueCode::Syntax, &self.id, self.src, message)
    }
    fn ws(&mut self) {
        while self
            .src
            .as_bytes()
            .get(self.at)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.at += 1;
        }
    }
    fn take(&mut self, c: u8) -> bool {
        self.ws();
        if self.src.as_bytes().get(self.at) == Some(&c) {
            self.at += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, c: u8) -> Result<(), RequestIssue> {
        if self.take(c) {
            Ok(())
        } else {
            Err(self.error("要求の区切りが不正"))
        }
    }
    fn name(&mut self, id: bool) -> Result<String, RequestIssue> {
        self.ws();
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
        while self.src.as_bytes().get(self.at).is_some_and(|b| {
            b.is_ascii_alphanumeric() || *b == b'_' || (id && matches!(b, b'.' | b'-'))
        }) {
            self.at += 1;
        }
        Ok(self.src[start..self.at].to_owned())
    }
    fn user_name(&mut self) -> Result<String, RequestIssue> {
        let name = self.name(false)?;
        if reserved(&name) {
            return Err(self.error("予約語は識別子に使えない"));
        }
        Ok(name)
    }
    fn selector(&mut self) -> Result<Selector, RequestIssue> {
        if self.take(b'@') {
            let snapshot = self.name(true)?;
            self.expect(b'/')?;
            let subject = self.name(true)?;
            return Ok(Selector::Subject { snapshot, subject });
        }
        if self.take(b'$') {
            let id = self.user_name()?;
            let mut path = Vec::new();
            loop {
                if self.take(b'.') {
                    path.push(ProjectionStep::Field(self.name(false)?));
                } else if self.take(b'[') {
                    self.ws();
                    let start = self.at;
                    while self
                        .src
                        .as_bytes()
                        .get(self.at)
                        .is_some_and(u8::is_ascii_digit)
                    {
                        self.at += 1;
                    }
                    let digits = &self.src[start..self.at];
                    if digits.is_empty() || (digits.len() > 1 && digits.starts_with('0')) {
                        return Err(self.error("index は正規化した非負整数で指定する"));
                    }
                    let n = digits
                        .parse::<u64>()
                        .ok()
                        .filter(|n| *n <= 9_007_199_254_740_991)
                        .ok_or_else(|| self.error("index が Nat の上限を超える"))?;
                    self.expect(b']')?;
                    path.push(ProjectionStep::Index(n));
                } else {
                    break;
                }
            }
            return Ok(Selector::Answer { id, path });
        }
        let mut name = self.user_name()?;
        while self.take(b'.') {
            name.push('.');
            name.push_str(&self.user_name()?);
        }
        Ok(Selector::Declaration { name })
    }
    fn parse(mut self) -> Result<RawRequest, RequestIssue> {
        self.id = self.user_name()?;
        self.expect(b'=')?;
        let kind = self.name(false)?;
        self.expect(b'(')?;
        let head = self.selector()?;
        let mut arguments = Vec::new();
        let mut keys = BTreeSet::new();
        while self.take(b',') {
            let mut key = self.name(false)?;
            if self.take(b'.') {
                if key != "bind" {
                    return Err(self.error("束縛 key の接頭辞は bind"));
                }
                key.push('.');
                key.push_str(&self.name(false)?);
            }
            if !keys.insert(key.clone()) {
                return Err(problem(
                    RequestIssueCode::DuplicateArgument,
                    &self.id,
                    &key,
                    "引数名が重複している",
                ));
            }
            self.expect(b'=')?;
            arguments.push((key, self.selector()?));
        }
        self.expect(b')')?;
        self.ws();
        if self.at != self.src.len() {
            return Err(self.error("要求の末尾に余分な字句がある"));
        }
        Ok(RawRequest {
            id: self.id,
            kind,
            head,
            arguments,
        })
    }
}

fn reserved(name: &str) -> bool {
    crate::law::parser::is_reserved(name)
}
