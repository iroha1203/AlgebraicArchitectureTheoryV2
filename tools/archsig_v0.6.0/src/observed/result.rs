//! 評価内部の型付き DAG。JSON はこの不変データの表示に限定する。

use super::{
    PrepareFailure, PreparedObserved,
    control::{Checkpoint, Control, StopReason},
};
use crate::{canonical::Json, issue::Location, result::location_wire, types::Type};
use num_bigint::BigInt;
#[path = "completion_graph.rs"]
mod completion_graph;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub enum EvaluationFailure {
    Prepare(PrepareFailure),
    /// 段階的実装の未実装。result/2 の数学的未決や版非対応とは別の内部失敗。
    NotImplemented {
        declaration: String,
        location: Location,
        feature: String,
    },
}
impl EvaluationFailure {
    pub fn wire(&self) -> Option<Json> {
        match self {
            Self::Prepare(f) => f.wire(),
            Self::NotImplemented { .. } => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Decision {
    Established,
    Refuted,
    Undetermined,
}
impl Decision {
    pub(crate) fn wire(self) -> &'static str {
        match self {
            Self::Established => "established",
            Self::Refuted => "refuted",
            Self::Undetermined => "undetermined",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct NodeRef(pub(crate) usize);
impl NodeRef {
    pub(crate) fn wire(self) -> Json {
        Json::obj([("node", Json::str(format!("n{}", self.0)))])
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NodeType {
    Value(Type),
    Expression(Type),
    Evaluation(Type),
    LawInstance,
    Proposition,
    Evidence,
    Domain,
}
impl NodeType {
    fn wire(&self) -> Json {
        match self {
            Self::Value(t) => t.wire(),
            Self::Expression(_) => Json::str("Expression"),
            Self::Evaluation(_) => Json::str("Evaluation"),
            Self::LawInstance => Json::str("LawInstance"),
            Self::Proposition => Json::str("Proposition"),
            Self::Evidence => Json::str("Evidence"),
            Self::Domain => Json::str("Domain"),
        }
    }
}
pub(crate) enum Scalar {
    Term(Box<super::term::Term>),
    Unit,
    Text(String),
    Map {
        domain: Type,
        codomain: Type,
        pairs: Vec<(Scalar, Scalar)>,
    },
    List {
        element: Type,
        items: Vec<Scalar>,
    },
    Set {
        element: Type,
        items: Vec<Scalar>,
    },
    Option {
        element: Type,
        value: Option<Box<Scalar>>,
    },
    Z(BigInt),
    Q(BigInt, BigInt),
    Fp {
        modulus: String,
        value: BigInt,
    },
    Tuple(Vec<Scalar>),
    Data {
        family: String,
        constructor: String,
        args: Vec<Scalar>,
    },
    Bool(bool),
    Subject {
        snapshot: String,
        subject: String,
        entity: String,
    },
}
impl Scalar {
    pub(crate) fn ty(&self) -> Type {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Self::Term(t) => t.ty(),
            Self::Unit => Type::Unit,
            Self::Text(_) => Type::Text,
            Self::Map {
                domain, codomain, ..
            } => Type::Map(Box::new(domain.clone()), Box::new(codomain.clone())),
            Self::List { element, .. } => Type::List(Box::new(element.clone())),
            Self::Set { element, .. } => Type::Set(Box::new(element.clone())),
            Self::Option { element, .. } => Type::Option(Box::new(element.clone())),
            Self::Z(_) => Type::Z,
            Self::Q(_, _) => Type::Q,
            Self::Fp { modulus, .. } => Type::Fp(modulus.clone()),
            Self::Tuple(items) => Type::Tuple(items.iter().map(Scalar::ty).collect()),
            Self::Data { family, .. } => Type::Data(family.clone()),
            Self::Bool(_) => Type::Bool,
            Self::Subject { entity, .. } => Type::Ref(entity.clone()),
        })
    }
    pub(super) fn wire(&self) -> Json {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Self::Term(t) => t.wire(),
            Self::Unit => Json::Arr(vec![]),
            Self::Text(text) => Json::str(text),
            Self::Map { pairs, .. } => Json::Arr(
                pairs
                    .iter()
                    .map(|(key, value)| Json::Arr(vec![key.wire(), value.wire()]))
                    .collect(),
            ),
            Self::List { items, .. } | Self::Set { items, .. } => {
                Json::Arr(items.iter().map(Scalar::wire).collect())
            }
            Self::Option { value: None, .. } => Json::obj([("none", Json::Bool(true))]),
            Self::Option {
                value: Some(value), ..
            } => Json::obj([("some", value.wire())]),
            Self::Z(n) => Json::str(n.to_string()),
            Self::Q(n, d) => Json::Arr(vec![Json::str(n.to_string()), Json::str(d.to_string())]),
            Self::Fp { value, .. } => Json::str(value.to_string()),
            Self::Tuple(items) => Json::Arr(items.iter().map(Scalar::wire).collect()),
            Self::Data {
                constructor, args, ..
            } => Json::obj([
                (
                    "tag",
                    Json::str(constructor.rsplit('.').next().unwrap_or(constructor)),
                ),
                ("args", Json::Arr(args.iter().map(Scalar::wire).collect())),
            ]),
            Self::Bool(b) => Json::Bool(*b),
            Self::Subject {
                snapshot, subject, ..
            } => Json::Arr(vec![Json::str(snapshot), Json::str(subject)]),
        })
    }
}
// Tuple は再帰的な値。解放も表示も呼出し元のスタック深さへ依存させない。
impl Drop for Scalar {
    fn drop(&mut self) {
        fn take(value: &mut Scalar, pending: &mut Vec<Scalar>) {
            match value {
                Scalar::Map { pairs, .. } => {
                    for (key, value) in std::mem::take(pairs) {
                        pending.push(key);
                        pending.push(value);
                    }
                }
                Scalar::Tuple(items)
                | Scalar::Data { args: items, .. }
                | Scalar::List { items, .. }
                | Scalar::Set { items, .. } => pending.append(items),
                Scalar::Option { value, .. } => {
                    if let Some(value) = value.take() {
                        pending.push(*value);
                    }
                }
                _ => {}
            }
        }
        let mut pending = Vec::new();
        take(self, &mut pending);
        while let Some(mut value) = pending.pop() {
            take(&mut value, &mut pending);
        }
    }
}
impl std::fmt::Debug for Scalar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Self::Term(t) => f.debug_tuple("Term").field(t).finish(),
            Self::Unit => f.write_str("Unit"),
            Self::Text(text) => f.debug_tuple("Text").field(text).finish(),
            Self::Map {
                domain,
                codomain,
                pairs,
            } => f
                .debug_struct("Map")
                .field("domain", domain)
                .field("codomain", codomain)
                .field("pairs", pairs)
                .finish(),
            Self::List { element, items } => f
                .debug_struct("List")
                .field("element", element)
                .field("items", items)
                .finish(),
            Self::Set { element, items } => f
                .debug_struct("Set")
                .field("element", element)
                .field("items", items)
                .finish(),
            Self::Option { element, value } => f
                .debug_struct("Option")
                .field("element", element)
                .field("value", value)
                .finish(),
            Self::Z(n) => f.debug_tuple("Z").field(n).finish(),
            Self::Q(n, d) => f.debug_tuple("Q").field(n).field(d).finish(),
            Self::Fp { modulus, value } => f
                .debug_struct("Fp")
                .field("modulus", modulus)
                .field("value", value)
                .finish(),
            Self::Tuple(items) => f.debug_tuple("Tuple").field(items).finish(),
            Self::Data {
                family,
                constructor,
                args,
            } => f
                .debug_struct("Data")
                .field("family", family)
                .field("constructor", constructor)
                .field("args", args)
                .finish(),
            Self::Bool(b) => f.debug_tuple("Bool").field(b).finish(),
            Self::Subject {
                snapshot,
                subject,
                entity,
            } => f
                .debug_struct("Subject")
                .field("snapshot", snapshot)
                .field("subject", subject)
                .field("entity", entity)
                .finish(),
        })
    }
}
impl Clone for Scalar {
    fn clone(&self) -> Self {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Self::Term(t) => Self::Term(t.clone()),
            Self::Unit => Self::Unit,
            Self::Text(text) => Self::Text(text.clone()),
            Self::Map {
                domain,
                codomain,
                pairs,
            } => Self::Map {
                domain: domain.clone(),
                codomain: codomain.clone(),
                pairs: pairs.clone(),
            },
            Self::List { element, items } => Self::List {
                element: element.clone(),
                items: items.clone(),
            },
            Self::Set { element, items } => Self::Set {
                element: element.clone(),
                items: items.clone(),
            },
            Self::Option { element, value } => Self::Option {
                element: element.clone(),
                value: value.clone(),
            },
            Self::Z(n) => Self::Z(n.clone()),
            Self::Q(n, d) => Self::Q(n.clone(), d.clone()),
            Self::Fp { modulus, value } => Self::Fp {
                modulus: modulus.clone(),
                value: value.clone(),
            },
            Self::Tuple(items) => Self::Tuple(items.clone()),
            Self::Data {
                family,
                constructor,
                args,
            } => Self::Data {
                family: family.clone(),
                constructor: constructor.clone(),
                args: args.clone(),
            },
            Self::Bool(b) => Self::Bool(*b),
            Self::Subject {
                snapshot,
                subject,
                entity,
            } => Self::Subject {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                entity: entity.clone(),
            },
        })
    }
}
impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match (self, other) {
            (Self::Term(a), Self::Term(b)) => a == b,
            (Self::Unit, Self::Unit) => true,
            (Self::Text(a), Self::Text(b)) => a == b,
            (
                Self::Map {
                    domain: a,
                    codomain: b,
                    pairs: c,
                },
                Self::Map {
                    domain: d,
                    codomain: e,
                    pairs: f,
                },
            ) => a == d && b == e && c.len() == f.len() && c.iter().all(|pair| f.contains(pair)),
            (
                Self::List {
                    element: a,
                    items: b,
                },
                Self::List {
                    element: c,
                    items: d,
                },
            ) => a == c && b == d,
            (
                Self::Set {
                    element: a,
                    items: b,
                },
                Self::Set {
                    element: c,
                    items: d,
                },
            ) => a == c && b.len() == d.len() && b.iter().all(|value| d.contains(value)),
            (
                Self::Option {
                    element: a,
                    value: b,
                },
                Self::Option {
                    element: c,
                    value: d,
                },
            ) => a == c && b == d,
            (Self::Z(a), Self::Z(b)) => a == b,
            (Self::Q(a, b), Self::Q(c, d)) => a == c && b == d,
            (
                Self::Fp {
                    modulus: p,
                    value: a,
                },
                Self::Fp {
                    modulus: q,
                    value: b,
                },
            ) => p == q && a == b,
            (Self::Tuple(a), Self::Tuple(b)) => a == b,
            (
                Self::Data {
                    family: a,
                    constructor: b,
                    args: c,
                },
                Self::Data {
                    family: d,
                    constructor: e,
                    args: f,
                },
            ) => a == d && b == e && c == f,
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (
                Self::Subject {
                    snapshot: a,
                    subject: b,
                    entity: c,
                },
                Self::Subject {
                    snapshot: d,
                    subject: e,
                    entity: f,
                },
            ) => a == d && b == e && c == f,
            _ => false,
        })
    }
}
impl Eq for Scalar {}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Fact {
    pub snapshot: String,
    pub subject: String,
    pub field: Option<String>,
    pub atom: Option<String>,
}
impl Fact {
    pub(crate) fn wire(&self) -> Json {
        let mut f = BTreeMap::from([
            ("snapshot".into(), Json::str(&self.snapshot)),
            ("subject".into(), Json::str(&self.subject)),
        ]);
        if let Some(s) = &self.field {
            f.insert("field".into(), Json::str(s));
        }
        if let Some(s) = &self.atom {
            f.insert("atom".into(), Json::str(s));
        }
        Json::Obj(f)
    }
}
#[derive(Clone, Debug, Default)]
pub(crate) struct Scope {
    pub readings: BTreeSet<String>,
    pub snapshots: BTreeSet<String>,
    pub modes: BTreeSet<String>,
    pub completions: bool,
    pub assignments: bool,
    pub quantifiers: Vec<Quantifier>,
}
impl PartialEq for Scope {
    fn eq(&self, other: &Self) -> bool {
        let occurrences = |scope: &Self| {
            let mut order = Vec::new();
            for q in &scope.quantifiers {
                if !order.contains(&q.occurrence) {
                    order.push(q.occurrence);
                }
            }
            order
        };
        self.readings == other.readings
            && self.snapshots == other.snapshots
            && self.modes == other.modes
            && self.completions == other.completions
            && self.assignments == other.assignments
            && occurrences(self) == occurrences(other)
            && self.quantifiers.len() == other.quantifiers.len()
            && self.quantifiers.iter().all(|q| {
                self.quantifiers
                    .iter()
                    .filter(|actual| *actual == q)
                    .count()
                    == other
                        .quantifiers
                        .iter()
                        .filter(|actual| *actual == q)
                        .count()
            })
    }
}
impl Eq for Scope {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Quantifier {
    pub kind: crate::law::ast::QuantKind,
    pub name: String,
    pub ty: Type,
    pub domain: Option<NodeRef>,
    // 元AST出現を区別する内部索引。wireの名前だけをidentityにしない。
    pub occurrence: (usize, usize),
    pub(super) context: Option<super::call::Context>,
}
impl Quantifier {
    fn wire(&self) -> Json {
        let mut fields = BTreeMap::from([
            (
                "kind".into(),
                Json::str(if self.kind == crate::law::ast::QuantKind::Forall {
                    "forall"
                } else {
                    "exists"
                }),
            ),
            ("name".into(), Json::str(&self.name)),
            ("type".into(), self.ty.wire()),
        ]);
        if let Some(domain) = self.domain {
            fields.insert("domain".into(), domain.wire());
        }
        Json::Obj(fields)
    }
}
impl Scope {
    // 元式を展開したScopeを順序の正本にする。異なる実Context/Domainは
    // 省略せず、同じ元出現の実域間の表示順には意味を与えない。
    pub(super) fn order_quantifiers_like(&mut self, original: &Self) {
        self.quantifiers.sort_by_key(|quantifier| {
            original
                .quantifiers
                .iter()
                .position(|q| q.occurrence == quantifier.occurrence)
                .unwrap_or(original.quantifiers.len())
        });
    }
    pub(crate) fn add_quantifier(&mut self, quantifier: Quantifier) {
        let scope = Self {
            quantifiers: vec![quantifier],
            ..Self::default()
        };
        self.merge_quantifiers(&scope);
    }
    pub(crate) fn merge_quantifiers(&mut self, other: &Self) {
        for q in &other.quantifiers {
            if self.quantifiers.contains(q) {
                continue;
            }
            let same = |old: &Quantifier| {
                old.occurrence == q.occurrence
                    && old.kind == q.kind
                    && old.name == q.name
                    && old.ty == q.ty
            };
            if q.context.is_none() && q.domain.is_none() && self.quantifiers.iter().any(same) {
                continue;
            }
            if let Some(old) = self.quantifiers.iter_mut().find(|old| {
                same(old)
                    && old.domain.is_none()
                    && (old.context.is_none() || old.context == q.context)
            }) {
                *old = q.clone();
            } else if q.domain.is_some()
                || !self
                    .quantifiers
                    .iter()
                    .any(|old| same(old) && old.context == q.context)
            {
                self.quantifiers.push(q.clone());
            }
        }
    }
    pub(crate) fn source_compatible(&self, other: &Self) -> bool {
        let normalize = |scope: &Self| {
            let mut copy = scope.clone();
            let mut qs = Vec::new();
            for q in &scope.quantifiers {
                let mut q = q.clone();
                q.domain = None;
                q.context = None;
                if !qs.contains(&q) {
                    qs.push(q);
                }
            }
            copy.quantifiers = qs;
            copy
        };
        normalize(self) == normalize(other)
    }
    pub(crate) fn merge(&mut self, other: &Self) {
        self.readings.extend(other.readings.iter().cloned());
        self.snapshots.extend(other.snapshots.iter().cloned());
        self.modes.extend(other.modes.iter().cloned());
        self.completions |= other.completions;
        self.assignments |= other.assignments;
        self.merge_quantifiers(other);
    }
    pub(crate) fn wire(&self) -> Json {
        Json::obj([
            (
                "readings",
                Json::Arr(self.readings.iter().map(Json::str).collect()),
            ),
            (
                "snapshots",
                Json::Arr(self.snapshots.iter().map(Json::str).collect()),
            ),
            (
                "modes",
                Json::Arr(self.modes.iter().map(Json::str).collect()),
            ),
            (
                "domain",
                Json::str(if self.completions {
                    "all_completions"
                } else if self.assignments {
                    "all_assignments"
                } else {
                    "finite_model"
                }),
            ),
            (
                "quantifiers",
                Json::Arr(self.quantifiers.iter().map(Quantifier::wire).collect()),
            ),
            ("assumptions", Json::Arr(vec![])),
        ])
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReasonKind {
    Missing,
    ConditionFailed {
        condition: NodeRef,
        construction: &'static str,
    },
    UnsupportedAlgorithm {
        question: super::request::QuestionKind,
        operand_types: Vec<Type>,
        method: String,
    },
    Stop(StopReason),
    Internal(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Reason {
    pub kind: ReasonKind,
    pub request: String,
    pub dependencies: Vec<NodeRef>,
    pub missing: Vec<Fact>,
    pub location: Option<Location>,
}
impl Reason {
    pub(crate) fn stopped(request: &str, reason: StopReason) -> Self {
        Self {
            kind: ReasonKind::Stop(reason),
            request: request.into(),
            dependencies: vec![],
            missing: vec![],
            location: None,
        }
    }
    pub(crate) fn internal(request: &str, operation: String) -> Self {
        Self {
            kind: ReasonKind::Internal(operation),
            request: request.into(),
            dependencies: vec![],
            missing: vec![],
            location: None,
        }
    }
    pub(crate) fn code(&self) -> &str {
        match &self.kind {
            ReasonKind::Missing => "missing_observation",
            ReasonKind::ConditionFailed { .. } => "condition_failed",
            ReasonKind::UnsupportedAlgorithm { .. } => "unsupported_algorithm",
            ReasonKind::Stop(r) => r.code(),
            ReasonKind::Internal(_) => "internal",
        }
    }
    pub(crate) fn wire(&self) -> Json {
        let (message, details) = match &self.kind {
            ReasonKind::Missing => ("原始 slot の観測が必要", Json::obj([])),
            ReasonKind::ConditionFailed {
                condition,
                construction,
            } => (
                "実値が構成の適用条件を満たさない",
                Json::obj([
                    ("condition", condition.wire()),
                    ("construction", Json::str(*construction)),
                ]),
            ),
            ReasonKind::UnsupportedAlgorithm {
                question,
                operand_types,
                method,
            } => (
                "元の型付き問いに対応する算法がない",
                Json::obj([
                    ("question", Json::str(question.wire())),
                    (
                        "operand_types",
                        Json::Arr(operand_types.iter().map(Type::wire).collect()),
                    ),
                    ("method", Json::str(method)),
                ]),
            ),
            ReasonKind::Internal(op) => (
                "導出の内部照合に失敗した",
                Json::obj([("operation", Json::str(op))]),
            ),
            ReasonKind::Stop(r) => {
                let mut result = r.wire();
                let Json::Obj(wire) = &mut result else {
                    unreachable!()
                };
                wire.insert("request".into(), Json::str(&self.request));
                wire.insert("dependencies".into(), refs(&self.dependencies));
                return result;
            }
        };
        let mut wire = BTreeMap::from([
            ("code".into(), Json::str(self.code())),
            ("message".into(), Json::str(message)),
            ("request".into(), Json::str(&self.request)),
            ("dependencies".into(), refs(&self.dependencies)),
            (
                "missing".into(),
                Json::Arr(self.missing.iter().map(Fact::wire).collect()),
            ),
            ("details".into(), details),
        ]);
        if let Some(location) = &self.location {
            wire.insert("location".into(), location_wire(location));
        }
        Json::Obj(wire)
    }
}
pub(crate) fn sort_reasons(reasons: &mut Vec<Reason>) {
    fn location_key(location: &Option<Location>) -> (String, String, usize) {
        match location {
            Some(Location::Law { span }) => ("law".into(), String::new(), span.0),
            Some(Location::Definition {
                input,
                pointer,
                span,
            }) => (input.clone(), pointer.clone(), span.map_or(0, |s| s.0)),
            Some(Location::ArchMap { pointer, span }) => {
                ("archmap".into(), pointer.clone(), span.map_or(0, |s| s.0))
            }
            None => (String::new(), String::new(), 0),
        }
    }
    reasons.sort_by_key(|r| {
        (
            r.code().to_owned(),
            location_key(&r.location),
            r.request.clone(),
        )
    });
    reasons.dedup_by(|a, b| a.wire() == b.wire());
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Binding {
    pub name: String,
    pub value: NodeRef,
    pub ty: Type,
}
fn bindings_wire(bs: &[Binding]) -> Json {
    Json::Arr(
        bs.iter()
            .map(|b| Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())]))
            .collect(),
    )
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rule {
    Input {
        kind: &'static str,
        location: Location,
    },
    Construction(&'static str),
}
impl Rule {
    fn wire(&self) -> Json {
        match self {
            Self::Input { kind, location } => Json::obj([
                ("kind", Json::str(*kind)),
                ("location", location_wire(location)),
            ]),
            Self::Construction(name) => Json::obj([
                ("kind", Json::str("construction")),
                ("name", Json::str(*name)),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Part {
    pub location: Location,
    pub value: Option<NodeRef>,
    pub residual: Option<NodeRef>,
    pub children: Vec<NodeRef>,
}
/// result/2 の固定変換。差は元の左右Expressionと実子Evaluationを保持する。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransformOp {
    Not,
    And,
    Difference,
    Substitute,
}
impl TransformOp {
    fn wire(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::And => "and",
            Self::Difference => "difference",
            Self::Substitute => "substitute",
        }
    }
    pub(crate) fn arity(self) -> usize {
        match self {
            Self::Not | Self::Substitute => 1,
            Self::And | Self::Difference => 2,
        }
    }
}
pub(crate) fn conditional_bool(guard: Option<bool>, body: Option<bool>) -> Option<bool> {
    // not(and(guard, not(body)))。None を通常値にせず、slot identity は元 Source に残す。
    match (guard, body) {
        (Some(false), _) | (_, Some(true)) => Some(true),
        (Some(true), Some(false)) => Some(false),
        _ => None,
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Payload {
    CompletionSeed {
        location: Location,
        parameters: Vec<(String, Type)>,
        bindings: Vec<Binding>,
        roots: Vec<NodeRef>,
        fields: Vec<Fact>,
        sources: Vec<NodeRef>,
    },
    CompletionInstance {
        name: String,
        role: &'static str,
        bindings: Vec<Binding>,
        guard: Option<NodeRef>,
        body: NodeRef,
        occurrence: Location,
    },
    CompletionPair {
        fields: Vec<Fact>,
        first: Vec<NodeRef>,
        second: Vec<NodeRef>,
        first_result: NodeRef,
        second_result: NodeRef,
    },
    TypeDomain {
        ty: Type,
    },
    Domain {
        ty: Type,
        elements: Vec<NodeRef>,
    },
    FiniteExhaustion {
        domain: NodeRef,
        checked: usize,
        instances: Vec<NodeRef>,
    },
    Scalar(Scalar),
    Expression {
        location: Location,
        parameters: Vec<(String, Type)>,
        bindings: Vec<Binding>,
    },
    Transform {
        operation: TransformOp,
        operands: Vec<NodeRef>,
        bindings: Vec<Binding>,
    },
    ParameterizedTransform {
        operation: TransformOp,
        operands: Vec<NodeRef>,
        parameters: Vec<(String, Type)>,
        bindings: Vec<Binding>,
    },
    Evaluation {
        expression: NodeRef,
        bindings: Vec<Binding>,
        parts: Vec<Part>,
        value: Option<NodeRef>,
        applicability: &'static str,
    },
    LawInstance {
        name: String,
        role: &'static str,
        bindings: Vec<Binding>,
        guard: Option<NodeRef>,
        body: NodeRef,
        occurrence: Location,
    },
    Proposition {
        instance: NodeRef,
    },
    MapDomainCondition {
        left: NodeRef,
        right: NodeRef,
    },
    OwnedCallCondition {
        left: NodeRef,
        right: NodeRef,
    },
    OwnedCallCounterexample {
        bindings: Vec<Binding>,
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
    },
    EvaluationEvidence {
        instance: NodeRef,
        lhs: NodeRef,
        rhs: NodeRef,
        residual: Option<NodeRef>,
    },
    TermComparison {
        source: NodeRef,
        left: NodeRef,
        right: NodeRef,
        certificate: Box<super::term::affine::Certificate>,
        before: NodeRef,
        after: NodeRef,
    },
    TermCounterexample {
        bindings: Vec<Binding>,
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
    },
    Normalization {
        before: NodeRef,
        after: NodeRef,
        steps: Vec<NodeRef>,
    },
    Counterexample {
        bindings: Vec<Binding>,
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
    },
}
impl Payload {
    fn wire(&self) -> Json {
        match self {
            Self::TypeDomain { ty } => {
                Json::obj([("kind", Json::str("type")), ("type", ty.wire())])
            }
            Self::Domain { ty, elements } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(elements)),
            ]),
            Self::CompletionPair {
                fields,
                first,
                second,
                first_result,
                second_result,
            } => Json::obj([
                ("kind", Json::str("completion_pair")),
                (
                    "data",
                    Json::obj([
                        ("fields", Json::Arr(fields.iter().map(Fact::wire).collect())),
                        ("first", refs(first)),
                        ("second", refs(second)),
                        ("first_result", first_result.wire()),
                        ("second_result", second_result.wire()),
                    ]),
                ),
            ]),
            Self::FiniteExhaustion {
                domain,
                checked,
                instances,
            } => Json::obj([
                ("kind", Json::str("finite_exhaustion")),
                (
                    "data",
                    Json::obj([
                        ("domain", domain.wire()),
                        ("checked", Json::Nat(*checked as u64)),
                        ("instances", refs(instances)),
                    ]),
                ),
            ]),
            Self::Scalar(v) => v.wire(),
            Self::Expression {
                location,
                parameters,
                bindings,
            }
            | Self::CompletionSeed {
                location,
                parameters,
                bindings,
                ..
            } => Json::obj([
                ("kind", Json::str("source")),
                ("location", location_wire(location)),
                (
                    "parameters",
                    Json::Arr(
                        parameters
                            .iter()
                            .map(|(n, t)| Json::obj([("name", Json::str(n)), ("type", t.wire())]))
                            .collect(),
                    ),
                ),
                ("bindings", bindings_wire(bindings)),
            ]),
            Self::Transform {
                operation,
                operands,
                bindings,
            } => Json::obj([
                ("kind", Json::str("transform")),
                ("operation", Json::str(operation.wire())),
                ("operands", refs(operands)),
                ("parameters", Json::Arr(vec![])),
                ("bindings", bindings_wire(bindings)),
            ]),
            Self::ParameterizedTransform {
                operation,
                operands,
                parameters,
                bindings,
            } => Json::obj([
                ("kind", Json::str("transform")),
                ("operation", Json::str(operation.wire())),
                ("operands", refs(operands)),
                (
                    "parameters",
                    Json::Arr(
                        parameters
                            .iter()
                            .map(|(name, ty)| {
                                Json::obj([("name", Json::str(name)), ("type", ty.wire())])
                            })
                            .collect(),
                    ),
                ),
                ("bindings", bindings_wire(bindings)),
            ]),
            Self::Evaluation {
                expression,
                bindings,
                parts,
                value,
                applicability,
            } => {
                let mut wire = BTreeMap::from([
                    ("expression".into(), expression.wire()),
                    ("bindings".into(), bindings_wire(bindings)),
                    ("applicability".into(), Json::str(*applicability)),
                    (
                        "parts".into(),
                        Json::Arr(
                            parts
                                .iter()
                                .map(|p| {
                                    let mut f = BTreeMap::from([
                                        ("location".into(), location_wire(&p.location)),
                                        ("children".into(), refs(&p.children)),
                                    ]);
                                    if let Some(v) = p.value {
                                        f.insert("value".into(), v.wire());
                                    }
                                    if let Some(r) = p.residual {
                                        f.insert("residual".into(), r.wire());
                                    }
                                    Json::Obj(f)
                                })
                                .collect(),
                        ),
                    ),
                ]);
                if let Some(v) = value {
                    wire.insert("value".into(), v.wire());
                }
                Json::Obj(wire)
            }
            Self::LawInstance {
                name,
                role,
                bindings,
                guard,
                body,
                occurrence,
            }
            | Self::CompletionInstance {
                name,
                role,
                bindings,
                guard,
                body,
                occurrence,
            } => {
                let mut wire = BTreeMap::from([
                    ("name".into(), Json::str(name)),
                    ("role".into(), Json::str(*role)),
                    ("bindings".into(), bindings_wire(bindings)),
                    ("body".into(), body.wire()),
                    ("occurrence".into(), location_wire(occurrence)),
                ]);
                if let Some(g) = guard {
                    wire.insert("guard".into(), g.wire());
                }
                Json::Obj(wire)
            }
            Self::Proposition { instance } => Json::obj([
                ("predicate", Json::str("law_holds")),
                ("operands", refs(&[*instance])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::MapDomainCondition { left, right } | Self::OwnedCallCondition { left, right } => {
                Json::obj([
                    ("predicate", Json::str("equal")),
                    ("operands", refs(&[*left, *right])),
                    ("quantifiers", Json::Arr(vec![])),
                ])
            }
            Self::EvaluationEvidence {
                instance,
                lhs,
                rhs,
                residual,
            } => {
                let mut data = BTreeMap::from([
                    ("instance".into(), instance.wire()),
                    ("lhs".into(), lhs.wire()),
                    ("rhs".into(), rhs.wire()),
                ]);
                if let Some(r) = residual {
                    data.insert("residual".into(), r.wire());
                }
                Json::obj([("kind", Json::str("evaluation")), ("data", Json::Obj(data))])
            }
            Self::TermComparison {
                source,
                before,
                after,
                ..
            } => Json::obj([
                ("kind", Json::str("normalization")),
                (
                    "data",
                    Json::obj([
                        ("before", before.wire()),
                        ("after", after.wire()),
                        ("steps", refs(&[*source])),
                    ]),
                ),
            ]),
            Self::TermCounterexample {
                bindings,
                left,
                right,
                facts,
            }
            | Self::OwnedCallCounterexample {
                bindings,
                left,
                right,
                facts,
            } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        ("bindings", bindings_wire(bindings)),
                        ("paths", refs(&[])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
            Self::Normalization {
                before,
                after,
                steps,
            } => Json::obj([
                ("kind", Json::str("normalization")),
                (
                    "data",
                    Json::obj([
                        ("before", before.wire()),
                        ("after", after.wire()),
                        ("steps", refs(steps)),
                    ]),
                ),
            ]),
            Self::Counterexample {
                bindings,
                left,
                right,
                facts,
            } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        ("bindings", bindings_wire(bindings)),
                        ("paths", refs(&[])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Judgment {
    pub status: Decision,
    pub evidence: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Node {
    pub ty: NodeType,
    pub payload: Option<Payload>,
    pub rule: Rule,
    pub arguments: Vec<NodeRef>,
    pub support: Vec<Fact>,
    pub evidence: Vec<NodeRef>,
    pub judgment: Option<Judgment>,
    pub scope: Scope,
    pub reasons: Vec<Reason>,
}
impl Node {
    fn wire(&self, id: usize) -> Json {
        let mut wire = BTreeMap::from([
            ("id".into(), Json::str(format!("n{id}"))),
            ("type".into(), self.ty.wire()),
            (
                "state".into(),
                Json::str(if self.payload.is_some() {
                    "value"
                } else {
                    "blocked"
                }),
            ),
            ("rule".into(), self.rule.wire()),
            ("arguments".into(), refs(&self.arguments)),
            (
                "support".into(),
                Json::Arr(self.support.iter().map(Fact::wire).collect()),
            ),
            ("conditions".into(), refs(&[])),
            ("evidence".into(), refs(&self.evidence)),
            ("scope".into(), self.scope.wire()),
            (
                "reasons".into(),
                Json::Arr(self.reasons.iter().map(Reason::wire).collect()),
            ),
        ]);
        if let Some(payload) = &self.payload {
            let mut value = payload.wire();
            if matches!(
                payload,
                Payload::Proposition { .. }
                    | Payload::MapDomainCondition { .. }
                    | Payload::OwnedCallCondition { .. }
            ) && let Json::Obj(fields) = &mut value
            {
                fields.insert(
                    "quantifiers".into(),
                    Json::Arr(
                        self.scope
                            .quantifiers
                            .iter()
                            .map(Quantifier::wire)
                            .collect(),
                    ),
                );
            }
            wire.insert("value".into(), value);
        }
        if let Some(j) = &self.judgment {
            wire.insert(
                "judgment".into(),
                Json::obj([
                    ("status", Json::str(j.status.wire())),
                    ("evidence", refs(&j.evidence)),
                    (
                        "reasons",
                        Json::Arr(j.reasons.iter().map(Reason::wire).collect()),
                    ),
                ]),
            );
        }
        Json::Obj(wire)
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Answer {
    pub id: String,
    pub status: Decision,
    pub outputs: BTreeMap<String, NodeRef>,
    pub claim: Option<NodeRef>,
    pub evidence: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
    pub scope: Scope,
}
impl Answer {
    fn wire(&self) -> Json {
        let mut wire = BTreeMap::from([
            ("id".into(), Json::str(&self.id)),
            ("status".into(), Json::str(self.status.wire())),
            (
                "outputs".into(),
                Json::Obj(
                    self.outputs
                        .iter()
                        .map(|(k, v)| (k.clone(), v.wire()))
                        .collect(),
                ),
            ),
            ("evidence".into(), refs(&self.evidence)),
            (
                "reasons".into(),
                Json::Arr(self.reasons.iter().map(Reason::wire).collect()),
            ),
            ("scope".into(), self.scope.wire()),
        ]);
        if let Some(c) = self.claim {
            wire.insert("claim".into(), c.wire());
        }
        Json::Obj(wire)
    }
}

/// 数値補完の証拠内case。型全域parameterの通常Bindingや観測Factではない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct UniversalWitness {
    pub caller: super::call::Context,
    pub template: NodeRef,
    pub anchor: NodeRef,
    pub ordinal: usize,
}

/// Node/Answer は外から変更できず、検査済みの入力を所有して由来を保持する。
#[derive(Debug)]
pub struct ObservedEvaluation {
    pub(super) prepared: PreparedObserved,
    pub(crate) nodes: Vec<Node>,
    pub(crate) answers: Vec<Answer>,
    pub(crate) issues: Vec<Reason>,
    pub(crate) status: &'static str,
    #[cfg(test)]
    pub(super) contexts: Vec<super::call::Context>,
    #[cfg(test)]
    pub(super) frames: Vec<super::call::Frame>,
    #[cfg(test)]
    pub(super) iterations: Vec<super::call::Iteration>,
    #[cfg(test)]
    pub(super) instances: Vec<super::call::Instance>,
    #[cfg(test)]
    pub(super) cases: Vec<super::call::CompletionCase>,
    #[cfg(test)]
    pub(super) universal_witnesses: Vec<UniversalWitness>,
}
impl ObservedEvaluation {
    pub fn status(&self) -> &str {
        self.status
    }
    pub fn prepared(&self) -> &PreparedObserved {
        &self.prepared
    }
    pub fn wire(&self) -> Json {
        let mut result = self.prepared.inputs().metadata_wire();
        let Json::Obj(wire) = &mut result else {
            unreachable!()
        };
        wire.insert("status".into(), Json::str(self.status));
        wire.insert(
            "requests".into(),
            Json::Arr(
                self.prepared
                    .requests()
                    .requests()
                    .iter()
                    .map(|r| r.wire())
                    .collect(),
            ),
        );
        wire.insert(
            "answers".into(),
            Json::Arr(self.answers.iter().map(Answer::wire).collect()),
        );
        wire.insert(
            "nodes".into(),
            Json::Arr(
                self.nodes
                    .iter()
                    .enumerate()
                    .map(|(i, n)| n.wire(i))
                    .collect(),
            ),
        );
        wire.insert(
            "issues".into(),
            Json::Arr(self.issues.iter().map(Reason::wire).collect()),
        );
        result
    }
}

/// Ref の種類と型は挿入時に照合する。既出 node のみを参照できる。
#[derive(Debug, Default)]
pub(crate) struct Graph {
    pub nodes: Vec<Node>,
    pub(super) contexts: Vec<super::call::Context>,
    pub(super) frames: Vec<super::call::Frame>,
    pub(super) iterations: Vec<super::call::Iteration>,
    pub(super) instances: Vec<super::call::Instance>,
    pub(super) cases: Vec<super::call::CompletionCase>,
    pub(super) universal_witnesses: Vec<UniversalWitness>,
    pub(super) active: super::call::Context,
    pub(super) requests: Vec<super::request::Request>,
    control: Control,
}
#[derive(Debug)]
pub(crate) enum ValidationFailure {
    Internal(String),
    Stop(StopReason),
    /// 元式の事前分析だけが返す。生成済みnodeの照合ではInternalへ変換する。
    UnsupportedExpression {
        location: Location,
        feature: String,
    },
}
impl From<String> for ValidationFailure {
    fn from(s: String) -> Self {
        Self::Internal(s)
    }
}
impl From<&str> for ValidationFailure {
    fn from(s: &str) -> Self {
        Self::Internal(s.into())
    }
}
impl From<StopReason> for ValidationFailure {
    fn from(s: StopReason) -> Self {
        Self::Stop(s)
    }
}
impl Graph {
    pub(super) fn map_domain_counterexample_shape(
        &self,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let [source, map, key, left, right] = node.arguments.as_slice() else {
            return Ok(false);
        };
        let Some(Payload::Counterexample {
            bindings,
            left: actual,
            right: required,
            facts,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let NodeType::Evaluation(Type::Map(domain, _)) = &self.get(*map)?.ty else {
            return Ok(false);
        };
        let Some(Payload::Expression {
            bindings: original, ..
        }) = &self.get(*source)?.payload
        else {
            return Err("Map域反例の元Sourceがない".into());
        };
        if self.get(*key)?.ty != NodeType::Evaluation((**domain).clone())
            || left != actual
            || right != required
            || bindings != original
            || self.scalar(*left)?.ty() != Type::Set(domain.clone())
            || self.scalar(*right)?.ty() != Type::Set(domain.clone())
            || node.ty != NodeType::Evidence
            || !matches!(node.rule, Rule::Construction("evidence"))
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || !node.reasons.is_empty()
            || facts != &node.support
            || !matches!(self.get(*left)?.rule, Rule::Construction("evaluation"))
            || !matches!(self.get(*right)?.rule, Rule::Construction("domain"))
            || self.get(*left)?.arguments != node.arguments[..3]
            || self.get(*right)?.arguments != node.arguments[..3]
        {
            return Err("Map域反例の元実子・値型・束縛が違う".into());
        }
        Ok(true)
    }
    pub fn new(control: &Control) -> Self {
        Self {
            nodes: vec![],
            contexts: vec![],
            frames: vec![],
            iterations: vec![],
            instances: vec![],
            cases: vec![],
            universal_witnesses: vec![],
            active: super::call::Context::default(),
            requests: vec![],
            control: control.clone(),
        }
    }
    pub(super) fn context_at(&self, index: usize) -> super::call::Context {
        self.contexts.get(index).copied().unwrap_or(self.active)
    }
    pub(crate) fn tick(&self) -> Result<(), ValidationFailure> {
        self.control
            .clone()
            .checkpoint(Checkpoint::FiniteIteration)
            .map_err(ValidationFailure::Stop)
    }
    pub fn get(&self, r: NodeRef) -> Result<&Node, String> {
        self.nodes.get(r.0).ok_or_else(|| "既出でない Ref".into())
    }
    pub fn expect(&self, r: NodeRef, ty: &NodeType) -> Result<(), String> {
        if &self.get(r)?.ty == ty {
            Ok(())
        } else {
            Err("Ref の型不一致".into())
        }
    }
    pub fn scalar(&self, r: NodeRef) -> Result<&Scalar, String> {
        match &self.get(r)?.payload {
            Some(Payload::Scalar(v)) => Ok(v),
            _ => Err("通常値でない node の消費".into()),
        }
    }
    pub(crate) fn boolean(&self, value: Option<NodeRef>) -> Result<Option<bool>, String> {
        value
            .map(|reference| match self.scalar(reference)? {
                Scalar::Bool(value) => Ok(*value),
                _ => Err("Bool 評価の値が Bool でない".into()),
            })
            .transpose()
    }
    fn value(&self, r: NodeRef, ty: &Type) -> Result<(), String> {
        self.expect(r, &NodeType::Value(ty.clone()))?;
        self.scalar(r)?;
        Ok(())
    }
    fn bindings(&self, bs: &[Binding]) -> Result<(), ValidationFailure> {
        self.tick()?;
        let mut names = BTreeSet::new();
        for b in bs {
            self.tick()?;
            if !names.insert(&b.name) {
                return Err("束縛名の重複".into());
            }
            self.value(b.value, &b.ty)?;
            self.tick()?;
        }
        self.tick()?;
        Ok(())
    }
    fn reasons(&self, rs: &[Reason]) -> Result<(), ValidationFailure> {
        self.tick()?;
        for reason in rs {
            self.tick()?;
            if let ReasonKind::ConditionFailed {
                condition,
                construction,
            } = reason.kind
            {
                let proposition = self.get(condition)?;
                if construction != "evaluation"
                    || proposition.ty != NodeType::Proposition
                    || !matches!(
                        proposition.payload,
                        Some(
                            Payload::MapDomainCondition { .. } | Payload::OwnedCallCondition { .. }
                        )
                    )
                    || !proposition
                        .judgment
                        .as_ref()
                        .is_some_and(|j| j.status == Decision::Refuted)
                    || !proposition
                        .arguments
                        .first()
                        .is_some_and(|source| reason.dependencies == [*source])
                    || !reason.missing.is_empty()
                {
                    return Err("構成条件失敗の元命題・構成・依存が違う".into());
                }
            }
            if matches!(reason.kind, ReasonKind::Missing)
                && (reason.dependencies.is_empty() || reason.missing.is_empty())
            {
                return Err("canonical 欠測理由に依存式・slot がない".into());
            }
            if let ReasonKind::UnsupportedAlgorithm {
                operand_types,
                method,
                ..
            } = &reason.kind
                && (operand_types.is_empty() || method.is_empty() || reason.dependencies.is_empty())
            {
                return Err("非対応算法理由に元の型・式・方法がない".into());
            }
            for &r in &reason.dependencies {
                self.tick()?;
                let node = self.get(r)?;
                if matches!(
                    reason.kind,
                    ReasonKind::Missing | ReasonKind::UnsupportedAlgorithm { .. }
                ) && !matches!(node.ty, NodeType::Expression(_))
                {
                    return Err("欠測・非対応算法理由の依存先が元式でない".into());
                }
                self.tick()?;
            }
            self.tick()?;
        }
        self.tick()?;
        Ok(())
    }
    pub(super) fn owned_call_counterexample_shape(
        &self,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::OwnedCallCounterexample {
            bindings,
            left,
            right,
            facts,
        }) = &node.payload
        else {
            return Ok(false);
        };
        self.bindings(bindings)?;
        let n = node.arguments.len();
        if node.ty != NodeType::Evidence
            || n < 3
            || node.arguments[n - 2..] != [*left, *right]
            || !matches!(self.get(node.arguments[0])?.ty, NodeType::Expression(_))
            || !matches!(self.scalar(*left)?.ty(), Type::Ref(_) | Type::Text)
            || self.scalar(*left)?.ty() != self.scalar(*right)?.ty()
            || self.scalar(*left)? == self.scalar(*right)?
            || facts != &node.support
            || !matches!(node.rule, Rule::Construction("evidence"))
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
        {
            return Err("Owned call反例の元辺・参照型・実不等が違う".into());
        }
        for r in &node.arguments[1..n - 2] {
            self.tick()?;
            if !matches!(self.get(*r)?.ty, NodeType::Evaluation(_)) {
                return Err("Owned call反例の実子がEvaluationでない".into());
            }
        }
        for (r, rule) in [(*left, "evaluation"), (*right, "domain")] {
            let value = self.get(r)?;
            if value.arguments != node.arguments[..n - 2]
                || value.rule != Rule::Construction(rule)
                || value.support != node.support
                || value.scope != node.scope
                || !value.evidence.is_empty()
                || !value.reasons.is_empty()
                || value.judgment.is_some()
            {
                return Err("Owned call反例のowner値が元callに接続しない".into());
            }
        }
        Ok(true)
    }
    /// 添付する証拠は、同じ命題の元 LawInstance と適用評価を証明する。
    pub(crate) fn validate_proposition_evidence(
        &self,
        node: &Node,
    ) -> Result<(), ValidationFailure> {
        if let Some(Payload::OwnedCallCondition { left, right }) = &node.payload {
            let (evidence, edges) = node
                .arguments
                .split_last()
                .ok_or("Owned条件に導出辺がない")?;
            let proof = self.get(*evidence)?;
            let Some(Payload::OwnedCallCounterexample {
                left: l, right: r, ..
            }) = &proof.payload
            else {
                return Err("Owned条件に元callの反例がない".into());
            };
            let judgment = node.judgment.as_ref().ok_or("Owned条件に判断がない")?;
            if proof.ty != NodeType::Evidence
                || left != l
                || right != r
                || proof.arguments != edges
                || !self.owned_call_counterexample_shape(proof)?
                || node.evidence != [*evidence]
                || judgment.evidence != node.evidence
                || judgment.status != Decision::Refuted
                || !judgment.reasons.is_empty()
                || !node.reasons.is_empty()
                || !matches!(node.rule, Rule::Construction("proposition"))
                || node.support != proof.support
                || node.scope != proof.scope
            {
                return Err("Owned条件の反証・元辺・判断が違う".into());
            }
            return Ok(());
        }
        if let Some(Payload::MapDomainCondition { left, right }) = &node.payload {
            let [source, map, key, actual, required, evidence] = node.arguments.as_slice() else {
                return Err("Map域条件の元式・実子・反証がない".into());
            };
            let proof = self.get(*evidence)?;
            let Some(judgment) = &node.judgment else {
                return Err("Map域条件の判断がない".into());
            };
            if left != actual
                || right != required
                || node.evidence != [*evidence]
                || judgment.status != Decision::Refuted
                || judgment.evidence != node.evidence
                || !judgment.reasons.is_empty()
                || !node.reasons.is_empty()
                || !matches!(node.rule, Rule::Construction("proposition"))
                || proof.arguments != [*source, *map, *key, *actual, *required]
                || !self.map_domain_counterexample_shape(proof)?
                || proof.scope != node.scope
                || proof.support != node.support
                || super::data::equal(self.scalar(*left)?, self.scalar(*right)?, &self.control)?
            {
                return Err("Map域条件の反証・導出・Scopeが違う".into());
            }
            return Ok(());
        }
        if self.completion_proposition_evidence(node)? {
            return Ok(());
        }
        let Some(Payload::Proposition { instance }) = &node.payload else {
            return Err("証拠添付先が Proposition でない".into());
        };
        let judgment = node.judgment.as_ref().ok_or("命題に判断がない")?;
        if node.evidence != judgment.evidence {
            return Err("命題と判断の証拠列が違う".into());
        }
        if node.arguments.len() != 2 || node.arguments[0] != *instance {
            return Err("命題の証拠対象が元 LawInstance と違う".into());
        }
        let evaluation = node.arguments[1];
        let Some(Payload::LawInstance {
            bindings: instance_bindings,
            ..
        }) = &self.get(*instance)?.payload
        else {
            return Err("証拠添付先の LawInstance が値でない".into());
        };
        if self.universal_evaluation_shape(self.get(evaluation)?)? {
            let whole = self.get(evaluation)?;
            let Some(Payload::Evaluation {
                expression,
                bindings,
                value,
                ..
            }) = &whole.payload
            else {
                unreachable!()
            };
            let Some(Payload::LawInstance { body, guard, .. }) = &self.get(*instance)?.payload
            else {
                unreachable!()
            };
            let (original_body, original_guard) = self.universal_template_sources(*expression)?;
            if *body != original_body
                || *guard != original_guard
                || instance_bindings != bindings
                || node.scope != whole.scope
                || node.support != whole.support
            {
                return Err("全域命題の元LawInstance・whole・Scope・支持が違う".into());
            }
            let expected = match self.boolean(*value)? {
                Some(true) => Decision::Established,
                Some(false) => Decision::Refuted,
                None => Decision::Undetermined,
            };
            if judgment.status != expected {
                return Err("全域命題の判断が元wholeと違う".into());
            }
            match expected {
                Decision::Undetermined => {
                    if node.evidence != whole.evidence {
                        return Err("未決の全域命題が別wholeの補完証拠を指す".into());
                    }
                }
                Decision::Established => {
                    if node.evidence != whole.evidence {
                        return Err("全域成立の証拠が元whole正規化でない".into());
                    }
                }
                Decision::Refuted => {
                    let [normalization, counterexample] = node.evidence.as_slice() else {
                        return Err("全域反証に元正規化・反例がない".into());
                    };
                    let counterexample = self.get(*counterexample)?;
                    let same_normalization = match counterexample.arguments.as_slice() {
                        [source, actual_whole, actual_normalization] => {
                            source == expression
                                && *actual_whole == evaluation
                                && actual_normalization == normalization
                        }
                        [source, actual_normalization, _, _, _] => {
                            source == expression && actual_normalization == normalization
                        }
                        _ => false,
                    };
                    if whole.evidence != [*normalization]
                        || !self.universal_counterexample_shape(counterexample)?
                        || !same_normalization
                    {
                        return Err("全域反証が別のwhole・正規化の反例を指す".into());
                    }
                }
            }
            return Ok(());
        }
        if let Some(Payload::LawInstance { body, .. }) = &self.get(*instance)?.payload
            && matches!(&self.get(*body)?.payload,Some(Payload::Expression {parameters,..}) if !parameters.is_empty())
        {
            let Some(Payload::Evaluation { parts, value, .. }) = &self.get(evaluation)?.payload
            else {
                return Err("whole命題に集約評価がない".into());
            };
            let rows = &parts.first().ok_or("whole partがない")?.children;
            let mut counterexample = false;
            for &reference in &node.evidence {
                self.tick()?;
                let e = self.get(reference)?;
                match &e.payload {
                    Some(Payload::FiniteExhaustion { instances, .. })
                        if e.arguments == [*instance, evaluation] =>
                    {
                        if instances.len() != rows.len()
                            || instances.iter().any(|r| !rows.contains(r))
                        {
                            return Err("whole全検査が別のrow族".into());
                        }
                    }
                    Some(Payload::Counterexample { .. })
                        if judgment.status == Decision::Refuted
                            && self.boolean(*value)? == Some(false) =>
                    {
                        let mut connected = false;
                        for &row in rows {
                            self.tick()?;
                            if self.universal_counterexample_for_evaluation(reference, row)? {
                                connected = true;
                            } else if e.arguments.get(1) == Some(&row) {
                                let Some(&actual) = e.arguments.first() else {
                                    return Err("row反例に元instanceがない".into());
                                };
                                let Some(Payload::LawInstance { bindings, .. }) =
                                    &self.get(actual)?.payload
                                else {
                                    return Err("row反例の元LawInstanceがない".into());
                                };
                                if self.get(actual)?.arguments.is_empty() {
                                    return Err("row反例に元bodyがない".into());
                                }
                                if !matches!(&e.payload,Some(Payload::Counterexample {bindings:bs,..}) if bs==bindings)
                                {
                                    return Err("row反例bindingsが元instanceと違う".into());
                                }
                                connected = true;
                            } else if self.quantifier_counterexample_shape(e)?
                                && self.evaluation_evidence_contains(row, reference)?
                            {
                                connected = true;
                            }
                        }
                        if !connected {
                            return Err("whole反例が別のinstance".into());
                        }
                        counterexample = true;
                    }
                    _ => return Err("whole命題に別の証拠を添付した".into()),
                }
            }
            if judgment.status == Decision::Refuted && !counterexample {
                return Err("whole反証に実row反例がない".into());
            }
            return Ok(());
        }
        let mut counterexample = false;
        for &reference in &node.evidence {
            self.tick()?;
            self.expect(reference, &NodeType::Evidence)?;
            let evidence = self.get(reference)?;
            if evidence.arguments != [*instance, evaluation] {
                if judgment.status == Decision::Refuted
                    && matches!(&self.get(evaluation)?.payload,Some(Payload::Evaluation {value:Some(value),..}) if self.scalar(*value)?==&Scalar::Bool(false))
                    && self.quantifier_counterexample_shape(evidence)?
                    && self.evaluation_evidence_contains(evaluation, reference)?
                {
                    counterexample = true;
                    continue;
                }
                return Err("添付証拠が別の LawInstance・適用評価を指す".into());
            }
            match &evidence.payload {
                Some(Payload::EvaluationEvidence {
                    instance: evidence_instance,
                    ..
                }) if evidence_instance == instance => {}
                Some(Payload::Counterexample { bindings, .. }) if bindings == instance_bindings => {
                    counterexample = true
                }
                _ => return Err("命題に対応する検査済み証拠でない".into()),
            }
            self.tick()?;
        }
        if judgment.status == Decision::Refuted && !counterexample {
            return Err("反証に当該 LawInstance の反例がない".into());
        }
        Ok(())
    }
    fn quantifier_counterexample_shape(&self, node: &Node) -> Result<bool, ValidationFailure> {
        let Some(Payload::Counterexample {
            bindings,
            left,
            right,
            facts,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let [source, domain, body] = node.arguments.as_slice() else {
            return Ok(false);
        };
        let Some(Payload::Expression {
            bindings: parameters,
            ..
        }) = &self.get(*source)?.payload
        else {
            return Ok(false);
        };
        let Some(index) = self.context_at(body.0).iteration else {
            return Ok(false);
        };
        let record = self
            .iterations
            .get(index)
            .ok_or("量化反例の実binderがない")?;
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &self.get(*body)?.payload
        else {
            return Ok(false);
        };
        let Some(Payload::Domain { ty, elements }) = &self.get(*domain)?.payload else {
            return Ok(false);
        };
        let quantifier = self
            .get(*body)?
            .scope
            .quantifiers
            .iter()
            .find(|q| q.domain == Some(*domain));
        let Some(quantifier) = quantifier else {
            return Ok(false);
        };
        let mut support = self.get(*domain)?.support.clone();
        support.extend(self.get(*body)?.support.iter().cloned());
        support.sort();
        support.dedup();
        if record.source != *source
            || record.finite != Some(*domain)
            || *value != *left
            || self.scalar(*left)? != &Scalar::Bool(false)
            || self.scalar(*right)? != &Scalar::Bool(true)
            || !bindings.starts_with(parameters)
            || ty != &quantifier.ty
            || facts != &support
        {
            return Ok(false);
        }
        Ok(bindings.iter().any(|binding| {
            binding.name == quantifier.name
                && binding.ty == *ty
                && elements.contains(&binding.value)
                && match &record.member {
                    super::call::Member::SetElement(member) => {
                        self.scalar(binding.value).is_ok_and(|v| v == member)
                    }
                    _ => false,
                }
        }))
    }
    pub(crate) fn evaluation_evidence_contains(
        &self,
        root: NodeRef,
        evidence: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let mut pending = vec![root];
        let mut seen = BTreeSet::new();
        while let Some(reference) = pending.pop() {
            self.tick()?;
            if !seen.insert(reference.0) {
                continue;
            }
            let node = self.get(reference)?;
            if node.evidence.contains(&evidence) {
                return Ok(true);
            }
            if let Some(Payload::Evaluation { parts, .. }) = &node.payload {
                for part in parts {
                    for child in &part.children {
                        self.tick()?;
                        if child.0 >= reference.0 {
                            return Err("証拠への評価依存が既出でない".into());
                        }
                        pending.push(*child);
                    }
                }
            }
        }
        Ok(false)
    }
    /// Differenceだけの型と実子参照を検査する。元ASTの算術はEnvironmentで再構成する。
    fn difference_shape(&self, node: &Node) -> Result<(NodeRef, [NodeRef; 2]), ValidationFailure> {
        self.tick()?;
        let NodeType::Expression(ty) = &node.ty else {
            return Err("差のExpressionの型が違う".into());
        };
        if !super::numeric::is_numeric_type(ty, &self.control)? {
            return Err("差のExpressionが数値型でない".into());
        }
        let Some(Payload::Transform {
            operation: TransformOp::Difference,
            operands,
            bindings,
        }) = &node.payload
        else {
            return Err("差がdifference変換でない".into());
        };
        let [source, left, right] = node.arguments.as_slice() else {
            return Err("差の元Source・実左右Evaluationがない".into());
        };
        self.expect(*source, &NodeType::Expression(Type::Bool))?;
        let Some(Payload::Expression {
            bindings: source_bindings,
            ..
        }) = &self.get(*source)?.payload
        else {
            return Err("差の元比較がSourceでない".into());
        };
        if bindings != source_bindings || operands.len() != 2 {
            return Err("差の元束縛・operand数が違う".into());
        }
        self.bindings(bindings)?;
        for (&evaluation, &operand) in [*left, *right].iter().zip(operands) {
            self.tick()?;
            self.expect(evaluation, &NodeType::Evaluation(ty.clone()))?;
            self.expect(operand, &NodeType::Expression(ty.clone()))?;
            if !matches!(&self.get(evaluation)?.payload, Some(Payload::Evaluation { expression, .. }) if expression == &operand)
            {
                return Err("差のoperandが実子EvaluationのExpressionと違う".into());
            }
            self.tick()?;
        }
        Ok((*source, [*left, *right]))
    }

    /// guarded Law の全域wholeは元bodyでなく not(and(guard, not(body))) を読む。
    fn universal_template_sources(
        &self,
        template: NodeRef,
    ) -> Result<(NodeRef, Option<NodeRef>), ValidationFailure> {
        self.tick()?;
        self.expect(template, &NodeType::Expression(Type::Bool))?;
        let node = self.get(template)?;
        if matches!(&node.payload, Some(Payload::Expression { .. })) {
            return Ok((template, None));
        }
        self.parameterized_transform_shape(node)?;
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::Not,
            operands: outer,
            ..
        }) = &node.payload
        else {
            return Err("全域templateが元Source・元適用条件式でない".into());
        };
        let conjunction = self.get(outer[0])?;
        self.parameterized_transform_shape(conjunction)?;
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::And,
            operands: conjunction,
            ..
        }) = &conjunction.payload
        else {
            return Err("全域templateの元guard連言がない".into());
        };
        let guard = conjunction[0];
        let negated_body = self.get(conjunction[1])?;
        self.parameterized_transform_shape(negated_body)?;
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::Not,
            operands: body,
            ..
        }) = &negated_body.payload
        else {
            return Err("全域templateの元body否定がない".into());
        };
        let body = body[0];
        for original in [guard, body] {
            self.tick()?;
            if !matches!(
                &self.get(original)?.payload,
                Some(Payload::Expression { .. })
            ) {
                return Err("全域templateのguard/bodyが元Sourceでない".into());
            }
        }
        Ok((body, Some(guard)))
    }

    fn parameterized_transform_shape(&self, node: &Node) -> Result<(), ValidationFailure> {
        self.tick()?;
        let NodeType::Expression(ty) = &node.ty else {
            return Err("parameter変換がExpressionでない".into());
        };
        let Some(Payload::ParameterizedTransform {
            operation,
            operands,
            parameters,
            bindings,
        }) = &node.payload
        else {
            return Err("parameter変換のpayloadが違う".into());
        };
        self.bindings(bindings)?;
        let mut names = BTreeSet::new();
        for (name, _) in parameters {
            self.tick()?;
            if !names.insert(name) || bindings.iter().any(|binding| &binding.name == name) {
                return Err("自由parameterが重複または束縛済み".into());
            }
        }
        match operation {
            TransformOp::Difference => {
                if !matches!(ty, Type::Z | Type::Q) || operands.len() != 2 {
                    return Err("全域差の型・operand数が違う".into());
                }
                if node.arguments.len() < 4 {
                    return Err("全域差に元Source・型Domain・左右評価がない".into());
                }
                let source = node.arguments[0];
                self.expect(source, &NodeType::Expression(Type::Bool))?;
                let (body_source, _) = self.universal_template_sources(source)?;
                let Some(Payload::Expression {
                    bindings: fixed, ..
                }) = &self.get(body_source)?.payload
                else {
                    return Err("全域差の元式がSourceでない".into());
                };
                if bindings != fixed {
                    return Err("全域差が元固定束縛を変えた".into());
                }
                let split = node.arguments.len() - 2;
                for &domain in &node.arguments[1..split] {
                    self.tick()?;
                    self.expect(domain, &NodeType::Domain)?;
                    let domain = self.get(domain)?;
                    if !matches!(&domain.payload, Some(Payload::TypeDomain { .. }))
                        || domain.arguments != [source]
                    {
                        return Err("全域差の型Domainが別の元式を指す".into());
                    }
                }
                for (&evaluation, &operand) in node.arguments[split..].iter().zip(operands) {
                    self.tick()?;
                    self.expect(evaluation, &NodeType::Evaluation(ty.clone()))?;
                    self.expect(operand, &NodeType::Expression(ty.clone()))?;
                    if !matches!(&self.get(evaluation)?.payload, Some(Payload::Evaluation { expression, .. }) if expression == &operand)
                        || !matches!(
                            &self.get(operand)?.payload,
                            Some(Payload::Expression { .. })
                        )
                        || self.get(operand)?.arguments.first() != Some(&source)
                    {
                        return Err("全域差が元左右の実Source・Evaluationを保持しない".into());
                    }
                }
            }
            TransformOp::Substitute => {
                let [original] = operands.as_slice() else {
                    return Err("同時代入のoperand数が違う".into());
                };
                self.expect(*original, &NodeType::Expression(ty.clone()))?;
                let (original_parameters, original_bindings) = match &self.get(*original)?.payload {
                    Some(Payload::Expression {
                        parameters,
                        bindings,
                        ..
                    })
                    | Some(Payload::ParameterizedTransform {
                        parameters,
                        bindings,
                        ..
                    }) => (parameters, bindings),
                    _ => return Err("同時代入の対象が元parameter式でない".into()),
                };
                let expected_arguments: Vec<_> = std::iter::once(*original)
                    .chain(bindings.iter().map(|binding| binding.value))
                    .collect();
                if node.arguments != expected_arguments {
                    return Err("同時代入の実対象・型付き値列が違う".into());
                }
                for binding in original_bindings {
                    self.tick()?;
                    if !bindings.contains(binding) {
                        return Err("同時代入が元固定束縛を変えた".into());
                    }
                }
                for binding in bindings {
                    self.tick()?;
                    if !original_bindings.contains(binding)
                        && !original_parameters
                            .iter()
                            .any(|(name, ty)| name == &binding.name && ty == &binding.ty)
                    {
                        return Err("同時代入に元式の自由parameterでない束縛がある".into());
                    }
                }
                let remaining: Vec<_> = original_parameters
                    .iter()
                    .filter(|(name, _)| !bindings.iter().any(|binding| &binding.name == name))
                    .cloned()
                    .collect();
                if parameters != &remaining {
                    return Err("同時代入の残る自由parameterが違う".into());
                }
            }
            TransformOp::Not | TransformOp::And => {
                if *ty != Type::Bool || operands.len() != operation.arity() {
                    return Err("適用条件変換の型・operand数が違う".into());
                }
                for &operand in operands {
                    self.tick()?;
                    self.expect(operand, &NodeType::Expression(Type::Bool))?;
                    if !matches!(
                        &self.get(operand)?.payload,
                        Some(Payload::Expression { .. } | Payload::ParameterizedTransform { .. })
                    ) {
                        return Err("適用条件変換が未生成の元式を消費した".into());
                    }
                }
                let expected_arguments: Vec<_> = operands
                    .iter()
                    .copied()
                    .chain(bindings.iter().map(|binding| binding.value))
                    .collect();
                if node.arguments != expected_arguments {
                    return Err("適用条件変換の元operand・束縛値列が違う".into());
                }
            }
        }
        Ok(())
    }

    pub(super) fn universal_normalization_shape(
        &self,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Normalization {
            before,
            after,
            steps,
        }) = &node.payload
        else {
            return Ok(false);
        };
        if self.get(*before)?.ty != NodeType::Expression(Type::Bool) {
            return Ok(false);
        }
        self.tick()?;
        let source = self.get(*before)?;
        let (_, guard) = self.universal_template_sources(*before)?;
        if !source.scope.assignments || node.ty != NodeType::Evidence {
            return Err("全域正規化の元式が全代入templateでない".into());
        }
        self.value(*after, &Type::Bool)?;
        let expected_support;
        if steps.is_empty() {
            // 元Bool式の確定値はEnvironmentが全域の元入力から再構成する。
            expected_support = &node.support;
        } else if guard.is_some_and(|guard| steps == &[guard]) {
            if self.scalar(*after)? != &Scalar::Bool(true) {
                return Err("非適用全域正規化の含意がtrueでない".into());
            }
            expected_support = &source.support;
        } else {
            let [difference, substitutions @ ..] = steps.as_slice() else {
                return Err("全域正規化に元differenceがない".into());
            };
            let difference_node = self.get(*difference)?;
            if !matches!(
                &difference_node.payload,
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Difference,
                    ..
                })
            ) || difference_node.arguments.first() != Some(before)
            {
                return Err("全域正規化の差が別の元templateを指す".into());
            }
            self.parameterized_transform_shape(difference_node)?;
            let mut seen = BTreeSet::from([difference.0]);
            for &substitution in substitutions {
                self.tick()?;
                if !seen.insert(substitution.0) {
                    return Err("全域正規化のstepが重複する".into());
                }
                let step = self.get(substitution)?;
                let Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Substitute,
                    operands,
                    ..
                }) = &step.payload
                else {
                    return Err("全域正規化のstepが元同時代入でない".into());
                };
                self.parameterized_transform_shape(step)?;
                let original = self.get(operands[0])?;
                if operands[0] != *before && original.arguments.first() != Some(before) {
                    return Err("全域正規化の同時代入が別の元templateを指す".into());
                }
            }
            expected_support = if guard.is_some() {
                &source.support
            } else {
                &difference_node.support
            };
        }
        let expected_arguments: Vec<_> = [*before, *after]
            .into_iter()
            .chain(steps.iter().copied())
            .collect();
        let expected_value_arguments: Vec<_> = std::iter::once(*before)
            .chain(steps.iter().copied())
            .collect();
        let value = self.get(*after)?;
        if node.arguments != expected_arguments
            || value.arguments != expected_value_arguments
            || !matches!(value.rule, Rule::Construction("evaluation"))
            || !value.evidence.is_empty()
            || !node.scope.assignments
            || node.scope != value.scope
            || !node.scope.source_compatible(&source.scope)
            || node.support != value.support
            || &node.support != expected_support
        {
            return Err("全域正規化の導出・Scope・支持が違う".into());
        }
        self.tick()?;
        Ok(true)
    }

    fn normalization_shape(&self, node: &Node) -> Result<(), ValidationFailure> {
        self.tick()?;
        if self.universal_normalization_shape(node)? {
            return Ok(());
        }
        let Some(Payload::Normalization {
            before,
            after,
            steps,
        }) = &node.payload
        else {
            return Err("正規化証拠のpayloadが違う".into());
        };
        let difference = self.get(*before)?;
        let (source, [left, right]) = self.difference_shape(difference)?;
        let NodeType::Expression(ty) = &difference.ty else {
            unreachable!()
        };
        self.value(*after, ty)?;
        let Some(Payload::Transform { operands, .. }) = &difference.payload else {
            unreachable!()
        };
        for &step in steps {
            self.tick()?;
            self.expect(step, &NodeType::Expression(ty.clone()))?;
            self.tick()?;
        }
        if steps != &[operands[0], operands[1], *before]
            || node.arguments != [source, left, right, *before, *after]
            || self.get(*after)?.arguments != [*before, source, left, right]
            || !matches!(self.get(*after)?.rule, Rule::Construction("evaluation"))
            || node.support != difference.support
            || node.scope != difference.scope
        {
            return Err("正規化証拠の実変換・導出・支持・Scopeが違う".into());
        }
        self.tick()?;
        Ok(())
    }

    fn universal_local_header_root(
        &self,
        header: NodeRef,
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        self.tick()?;
        let node = self.get(header)?;
        if node.ty != NodeType::Expression(Type::Bool)
            || !matches!(&node.payload, Some(Payload::Expression { .. }))
        {
            return Ok(None);
        }
        let [root, domain, ..] = node.arguments.as_slice() else {
            return Ok(None);
        };
        if *root == header
            || !matches!(
                &self.get(*domain)?.payload,
                Some(Payload::TypeDomain { .. })
            )
            || self.get(*domain)?.arguments != [*root]
        {
            return Ok(None);
        }
        self.universal_template_sources(*root)?;
        Ok(Some(*root))
    }

    fn universal_local_quantifier_inputs(
        &self,
        header: NodeRef,
        domain: NodeRef,
        body: NodeRef,
        scope: &Scope,
    ) -> Result<(), ValidationFailure> {
        let root = self
            .universal_local_header_root(header)?
            .ok_or("局所数値量化の元header・root型Domainがない")?;
        let context = self.context_at(header.0);
        let domain_node = self.get(domain)?;
        let Some(Payload::TypeDomain { ty }) = &domain_node.payload else {
            return Err("局所数値量化の型Domainがない".into());
        };
        let Rule::Input {
            kind: "law",
            location: Location::Law { span: binder },
        } = &domain_node.rule
        else {
            return Err("局所数値量化の元binder位置がない".into());
        };
        self.expect(body, &NodeType::Evaluation(Type::Bool))?;
        let Some(Payload::Evaluation {
            expression: body_source,
            ..
        }) = &self.get(body)?.payload
        else {
            return Err("局所数値量化が未生成のbody評価を消費した".into());
        };
        let body_node = self.get(*body_source)?;
        if domain_node.arguments != [header]
            || self.context_at(domain.0) != context
            || self.context_at(body.0) != context
            || self.context_at(body_source.0) != context
            || body_node.arguments.first() != Some(&root)
            || !body_node.arguments.contains(&domain)
            || !matches!(&body_node.payload, Some(Payload::Expression { .. }))
            || !scope.assignments
        {
            return Err("局所数値量化の元root・body・型Domain・実Contextが違う".into());
        }
        let descriptors: Vec<_> = scope
            .quantifiers
            .iter()
            .filter(|q| q.domain == Some(domain))
            .collect();
        let [descriptor] = descriptors.as_slice() else {
            return Err("局所数値量化の実型Domainに一つのbinder descriptorがない".into());
        };
        if descriptor.kind != crate::law::ast::QuantKind::Forall
            || descriptor.ty != *ty
            || descriptor.occurrence != *binder
            || descriptor.context != Some(context)
        {
            return Err("局所数値量化の元binder・型・全称・実Contextが違う".into());
        }
        let mut expected_scope = self.get(header)?.scope.clone();
        expected_scope.merge(&self.get(body)?.scope);
        if *scope != expected_scope || !scope.source_compatible(&self.get(header)?.scope) {
            return Err("局所数値量化のScopeが元header・実bodyから精密化されていない".into());
        }
        Ok(())
    }

    fn universal_local_quantifier_value_shape(
        &self,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let [header, domain, body] = node.arguments.as_slice() else {
            return Ok(false);
        };
        if self.universal_local_header_root(*header)?.is_none()
            || !matches!(
                &self.get(*domain)?.payload,
                Some(Payload::TypeDomain { .. })
            )
            || self.get(*domain)?.arguments != [*header]
        {
            return Ok(false);
        }
        let Some(Payload::Expression { location, .. }) = &self.get(*header)?.payload else {
            unreachable!()
        };
        self.universal_local_quantifier_inputs(*header, *domain, *body, &node.scope)?;
        if node.ty != NodeType::Value(Type::Bool)
            || !matches!(&node.payload, Some(Payload::Scalar(Scalar::Bool(_))))
            || !matches!(&node.rule, Rule::Input {kind:"law",location:actual} if actual == location)
            || !node.evidence.is_empty()
            || node.support != self.get(*body)?.support
        {
            return Err("局所数値量化の確定Boolが元型・Quant位置・支持に合わない".into());
        }
        Ok(true)
    }

    fn universal_local_quantifier_evaluation_shape(
        &self,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Evaluation {
            expression: header,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let [actual_header, domain, body, values @ ..] = node.arguments.as_slice() else {
            return Ok(false);
        };
        if actual_header != header
            || self.universal_local_header_root(*header)?.is_none()
            || !matches!(
                &self.get(*domain)?.payload,
                Some(Payload::TypeDomain { .. })
            )
            || self.get(*domain)?.arguments != [*header]
        {
            return Ok(false);
        }
        self.universal_local_quantifier_inputs(*header, *domain, *body, &node.scope)?;
        let Some(Payload::Expression {
            location,
            bindings: fixed,
            ..
        }) = &self.get(*header)?.payload
        else {
            unreachable!()
        };
        let [part] = parts.as_slice() else {
            return Err("局所数値量化の元part数が違う".into());
        };
        let expected_values: Vec<_> = value.iter().copied().collect();
        if node.ty != NodeType::Evaluation(Type::Bool)
            || bindings != fixed
            || part.location != *location
            || part.value != *value
            || part.residual.is_some()
            || part.children != [*body]
            || values != expected_values
            || *applicability != "applicable"
            || !node.evidence.is_empty()
            || node.support != self.get(*body)?.support
        {
            return Err("局所数値量化の実body・元位置・値・支持が違う".into());
        }
        if let Some(value) = value {
            let scalar = self.get(*value)?;
            if !self.universal_local_quantifier_value_shape(scalar)?
                || scalar.arguments != [*header, *domain, *body]
                || scalar.scope != node.scope
                || scalar.support != node.support
            {
                return Err("局所数値量化の値が別のbody・binderで導出された".into());
            }
        }
        Ok(true)
    }

    fn universal_evaluation_shape(&self, node: &Node) -> Result<bool, ValidationFailure> {
        let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        else {
            return Ok(false);
        };
        if node.ty != NodeType::Evaluation(Type::Bool) || !node.scope.assignments {
            return Ok(false);
        }
        let residual_whole = parts.iter().any(|part| {
            part.residual.is_some_and(|residual| {
                matches!(
                    self.get(residual).map(|node| &node.ty),
                    Ok(NodeType::Evaluation(Type::Z | Type::Q))
                )
            })
        });
        let guarded_not_applicable = *applicability == "not_applicable"
            && matches!(
                &self.get(*expression)?.payload,
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Not,
                    ..
                })
            );
        let typed_whole = node.arguments.get(1).is_some_and(|domain| {
            self.get(*domain).is_ok_and(|node| {
                matches!(&node.payload, Some(Payload::TypeDomain { .. }))
                    && node.arguments == [*expression]
            })
        });
        if typed_whole && self.universal_local_header_root(*expression)?.is_some() {
            return Ok(false);
        }
        if !residual_whole && !guarded_not_applicable && !typed_whole {
            return Ok(false);
        }
        self.tick()?;
        let source = self.get(*expression)?;
        let (body_source, guard_source) = self.universal_template_sources(*expression)?;
        let Some(Payload::Expression {
            location,
            bindings: fixed,
            ..
        }) = &self.get(body_source)?.payload
        else {
            unreachable!()
        };
        let (guard_part, body_part) = if guard_source.is_some() {
            let [guard, body] = parts.as_slice() else {
                return Err("guard付き全域wholeの元part数が違う".into());
            };
            (Some(guard), body)
        } else {
            let [body] = parts.as_slice() else {
                return Err("全域wholeの元part数が違う".into());
            };
            (None, body)
        };
        if bindings != fixed
            || body_part.location != *location
            || !node.scope.source_compatible(&source.scope)
        {
            return Err("全域wholeの元位置・束縛・Scopeが違う".into());
        }
        let mut expected_arguments = vec![*expression];
        let mut domain_end = 1;
        while let Some(&domain) = node.arguments.get(domain_end) {
            self.tick()?;
            if !matches!(&self.get(domain)?.payload, Some(Payload::TypeDomain { .. })) {
                break;
            }
            if self.get(domain)?.arguments != [*expression] {
                return Err("全域wholeの型Domainが別のtemplateを指す".into());
            }
            expected_arguments.push(domain);
            domain_end += 1;
        }
        let mut guard_value = None;
        if let (Some(guard_source), Some(guard_part)) = (guard_source, guard_part) {
            let Some(Payload::Expression {
                location: guard_location,
                ..
            }) = &self.get(guard_source)?.payload
            else {
                unreachable!()
            };
            let [guard_evaluation] = guard_part.children.as_slice() else {
                return Err("全域wholeの元guard評価がない".into());
            };
            self.expect(*guard_evaluation, &NodeType::Evaluation(Type::Bool))?;
            let Some(Payload::Evaluation {
                expression: actual_guard,
                value,
                ..
            }) = &self.get(*guard_evaluation)?.payload
            else {
                return Err("全域wholeが未生成のguard評価を消費した".into());
            };
            if guard_part.location != *guard_location
                || guard_part.value != *value
                || guard_part.residual.is_some()
                || self.get(*actual_guard)?.arguments.first() != Some(expression)
            {
                return Err("全域wholeの元guard・値・実評価が違う".into());
            }
            guard_value = self.boolean(*value)?;
            expected_arguments.push(*guard_evaluation);
        }
        let expected_step;
        if guarded_not_applicable {
            if guard_value != Some(false)
                || self.boolean(*value)? != Some(true)
                || body_part.value.is_some()
                || body_part.residual.is_some()
                || !body_part.children.is_empty()
            {
                return Err("非適用全域wholeが未評価bodyを成立値として消費した".into());
            }
            expected_step = Some(guard_source.ok_or("非適用全域wholeに元guardがない")?);
        } else {
            let [body] = body_part.children.as_slice() else {
                return Err("全域wholeの元body評価がない".into());
            };
            self.expect(*body, &NodeType::Evaluation(Type::Bool))?;
            let Some(Payload::Evaluation {
                expression: actual_body,
                value: body_value,
                ..
            }) = &self.get(*body)?.payload
            else {
                return Err("全域wholeが未生成のbody評価を消費した".into());
            };
            if self.get(*actual_body)?.arguments.first() != Some(expression)
                || body_part.value
                    != if guard_source.is_some() {
                        *body_value
                    } else {
                        *value
                    }
            {
                return Err("全域wholeのbodyが別の元template・値を指す".into());
            }
            let expected_applicability = if guard_source.is_some() && guard_value.is_none() {
                "undetermined"
            } else {
                "applicable"
            };
            if *applicability != expected_applicability || guard_value == Some(false) {
                return Err("全域wholeの元guard適用性が違う".into());
            }
            if let Some(residual) = body_part.residual {
                let Some(Payload::Evaluation {
                    expression: difference,
                    ..
                }) = &self.get(residual)?.payload
                else {
                    return Err("全域wholeの残差が完成したEvaluationでない".into());
                };
                let difference_node = self.get(*difference)?;
                self.parameterized_transform_shape(difference_node)?;
                if !matches!(
                    &difference_node.payload,
                    Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Difference,
                        ..
                    })
                ) || difference_node.arguments.first() != Some(expression)
                    || difference_node.arguments[1..difference_node.arguments.len() - 2]
                        != node.arguments[1..domain_end]
                {
                    return Err("全域wholeの元差・型Domainが違う".into());
                }
                expected_step = Some(*difference);
                expected_arguments.extend([*body, residual]);
            } else {
                if value.is_some() {
                    let body_value = self.boolean(*body_value)?;
                    let expected = if guard_source.is_some() {
                        conditional_bool(guard_value, body_value)
                    } else {
                        body_value
                    };
                    if expected.is_none() || expected != self.boolean(*value)? {
                        return Err("定数論理全域wholeの元body・guard・判断が違う".into());
                    }
                } else if !node
                    .reasons
                    .iter()
                    .any(|reason| matches!(&reason.kind, ReasonKind::UnsupportedAlgorithm { .. }))
                {
                    return Err("全域wholeに正確な差も元式の非対応算法理由もない".into());
                }
                expected_step = None;
                expected_arguments.push(*body);
            }
        }
        if let Some(value) = value {
            let [normalization] = node.evidence.as_slice() else {
                return Err("確定した全域wholeに一つの正規化証拠がない".into());
            };
            let proof = self.get(*normalization)?;
            if !self.universal_normalization_shape(proof)?
                || !matches!(&proof.payload, Some(Payload::Normalization { before, after, steps }) if before == expression && after == value && steps.first() == expected_step.as_ref())
                || proof.scope != node.scope
                || proof.support != node.support
            {
                return Err("全域wholeの正規化証拠が元式・判断に合わない".into());
            }
            expected_arguments.extend([*value, *normalization]);
        } else if let [pair] = node.evidence.as_slice() {
            let proof = self.get(*pair)?;
            if !self.universal_completion_pair_shape(proof)?
                || proof.arguments.first() != Some(expression)
                || proof.support != node.support
            {
                return Err("未決の全域wholeが別template・支持の補完対を指す".into());
            }
            expected_arguments.push(*pair);
        } else if !node.evidence.is_empty() {
            return Err("未決の全域wholeに完成正規化証拠がある".into());
        }
        if node.arguments != expected_arguments {
            return Err("全域wholeの元Domain・実評価・判断の導出が違う".into());
        }
        self.tick()?;
        Ok(true)
    }

    pub(super) fn universal_witness_record(
        &self,
        anchor: NodeRef,
    ) -> Result<Option<&UniversalWitness>, ValidationFailure> {
        let mut matching = self
            .universal_witnesses
            .iter()
            .filter(|witness| witness.anchor == anchor);
        let Some(witness) = matching.next() else {
            return Ok(None);
        };
        if matching.next().is_some() || witness.ordinal > 1 {
            return Err("数値補完anchorの実case identityが重複・不正".into());
        }
        self.tick()?;
        if self
            .universal_witnesses
            .iter()
            .filter(|other| {
                other.caller == witness.caller
                    && other.template == witness.template
                    && other.ordinal == witness.ordinal
            })
            .count()
            != 1
            || self.context_at(anchor.0) != witness.caller
            || self.context_at(witness.template.0) != witness.caller
        {
            return Err("数値補完anchorが別のcaller・caseへ移された".into());
        }
        let node = self.get(anchor)?;
        self.parameterized_transform_shape(node)?;
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::Substitute,
            operands,
            parameters,
            bindings,
        }) = &node.payload
        else {
            return Err("数値補完anchorが元wholeの恒等代入でない".into());
        };
        let (original_parameters, original_bindings) = match &self.get(witness.template)?.payload {
            Some(Payload::Expression {
                parameters,
                bindings,
                ..
            })
            | Some(Payload::ParameterizedTransform {
                parameters,
                bindings,
                ..
            }) => (parameters, bindings),
            _ => return Err("数値補完anchorの元templateがExpressionでない".into()),
        };
        self.universal_template_sources(witness.template)?;
        let mut source_scope = self.get(witness.template)?.scope.clone();
        source_scope.completions = true;
        if operands != &[witness.template]
            || parameters != original_parameters
            || bindings != original_bindings
            || !node.scope.assignments
            || !node.scope.completions
            || !node.scope.source_compatible(&source_scope)
            || !matches!(node.rule, Rule::Construction("expression"))
        {
            return Err("数値補完anchorが元の型・自由parameter・固定束縛を変えた".into());
        }
        Ok(Some(witness))
    }

    fn universal_witness_value_shape(&self, node: &Node) -> Result<bool, ValidationFailure> {
        let [template, anchor, values @ ..] = node.arguments.as_slice() else {
            return Ok(false);
        };
        let Some(witness) = self.universal_witness_record(*anchor)? else {
            return Ok(false);
        };
        if witness.template != *template
            || self.active != witness.caller
            || node.scope != self.get(*anchor)?.scope
            || !matches!(node.rule, Rule::Construction("evaluation"))
            || !node.evidence.is_empty()
        {
            return Err("数値補完証拠値の元template・anchor・Scopeが違う".into());
        }
        match &node.ty {
            NodeType::Value(Type::Bool) => {
                if values.is_empty() {
                    return Err("数値補完case判断に元slot値がない".into());
                }
                for &value in values {
                    self.tick()?;
                    let scalar = self.scalar(value)?;
                    if !super::numeric::is_numeric_type(&scalar.ty(), &self.control)?
                        || !matches!(self.get(value)?.arguments.as_slice(), [source, case, _] if source == template && case == anchor)
                    {
                        return Err("数値補完case判断が別のslot代入を消費した".into());
                    }
                }
            }
            NodeType::Value(ty) if super::numeric::is_numeric_type(ty, &self.control)? => {
                let [source] = values else {
                    return Err("数値補完slot値に元field出現がない".into());
                };
                self.expect(*source, &NodeType::Expression(ty.clone()))?;
                if !matches!(
                    &self.get(*source)?.payload,
                    Some(Payload::Expression { .. })
                ) || self.get(*source)?.arguments.first() != Some(template)
                {
                    return Err("数値補完slot値の元fieldが別のtemplateを指す".into());
                }
            }
            _ => return Err("数値補完証拠値の型が数値/Boolでない".into()),
        }
        Ok(true)
    }

    fn universal_witness_evaluation_shape(&self, node: &Node) -> Result<bool, ValidationFailure> {
        let Some(Payload::Evaluation {
            expression: anchor,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let Some(witness) = self.universal_witness_record(*anchor)? else {
            return Ok(false);
        };
        self.tick()?;
        let template = witness.template;
        let (body_source, _) = self.universal_template_sources(template)?;
        let Some(Payload::Expression {
            location,
            bindings: fixed,
            ..
        }) = &self.get(body_source)?.payload
        else {
            unreachable!()
        };
        let [part] = parts.as_slice() else {
            return Err("数値補完case wholeの元part数が違う".into());
        };
        let [body] = part.children.as_slice() else {
            return Err("数値補完case wholeに元body評価がない".into());
        };
        self.expect(*body, &NodeType::Evaluation(Type::Bool))?;
        let Some(Payload::Evaluation {
            expression: actual_body,
            ..
        }) = &self.get(*body)?.payload
        else {
            return Err("数値補完caseが未生成のbodyを消費した".into());
        };
        let residual = part.residual.ok_or("数値補完caseに元残差評価がない")?;
        let NodeType::Evaluation(Type::Z | Type::Q) = self.get(residual)?.ty else {
            return Err("数値補完caseの元残差が数値Evaluationでない".into());
        };
        let Some(Payload::Evaluation {
            expression: difference,
            ..
        }) = &self.get(residual)?.payload
        else {
            return Err("数値補完caseが未生成の残差を消費した".into());
        };
        let difference_node = self.get(*difference)?;
        self.parameterized_transform_shape(difference_node)?;
        if !matches!(
            &difference_node.payload,
            Some(Payload::ParameterizedTransform {
                operation: TransformOp::Difference,
                ..
            })
        ) || difference_node.arguments.first() != Some(&template)
            || self.get(*actual_body)?.arguments.first() != Some(&template)
        {
            return Err("数値補完caseのbody・差が別のtemplateを指す".into());
        }
        let value = value.ok_or("数値補完caseのwhole判断が未完成")?;
        self.value(value, &Type::Bool)?;
        let value_node = self.get(value)?;
        if !self.universal_witness_value_shape(value_node)? {
            return Err("数値補完caseのwhole判断に型付きslot代入がない".into());
        }
        let [actual_template, actual_anchor, values @ ..] = value_node.arguments.as_slice() else {
            unreachable!()
        };
        let mut expected_arguments = vec![*anchor];
        expected_arguments
            .extend_from_slice(&difference_node.arguments[1..difference_node.arguments.len() - 2]);
        expected_arguments.extend([*body, residual]);
        expected_arguments.extend_from_slice(values);
        expected_arguments.push(value);
        if *actual_template != template
            || actual_anchor != anchor
            || node.ty != NodeType::Evaluation(Type::Bool)
            || bindings != fixed
            || part.location != *location
            || part.value != Some(value)
            || *applicability != "applicable"
            || node.arguments != expected_arguments
            || !node.evidence.is_empty()
            || node.scope != self.get(*anchor)?.scope
            || node.scope != value_node.scope
            || node.support != value_node.support
            || self.active != witness.caller
        {
            return Err("数値補完caseの元型域・slot順・whole・Scopeが違う".into());
        }
        Ok(true)
    }

    fn universal_completion_pair_shape(&self, node: &Node) -> Result<bool, ValidationFailure> {
        let Some(Payload::CompletionPair {
            fields,
            first,
            second,
            first_result,
            second_result,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let [
            template,
            first_anchor,
            second_anchor,
            first_whole,
            second_whole,
            values @ ..,
        ] = node.arguments.as_slice()
        else {
            return Ok(false);
        };
        let Some(first_witness) = self.universal_witness_record(*first_anchor)? else {
            return Ok(false);
        };
        let Some(second_witness) = self.universal_witness_record(*second_anchor)? else {
            return Ok(false);
        };
        if first_witness.template != *template
            || second_witness.template != *template
            || first_witness.caller != second_witness.caller
            || first_witness.caller != self.active
            || first_witness.ordinal != 0
            || second_witness.ordinal != 1
            || first_whole != first_result
            || second_whole != second_result
            || fields.len() != first.len()
            || fields.len() != second.len()
            || !fields.windows(2).all(|pair| pair[0] < pair[1])
            || values != first.iter().chain(second).copied().collect::<Vec<_>>()
        {
            return Err("数値補完対の元template・ordinal・slot順・case結果が違う".into());
        }
        for (anchor, whole, values) in [
            (*first_anchor, *first_whole, first),
            (*second_anchor, *second_whole, second),
        ] {
            self.tick()?;
            let whole_node = self.get(whole)?;
            if !self.universal_witness_evaluation_shape(whole_node)? {
                return Err("数値補完対のwhole caseが未完成".into());
            }
            let Some(Payload::Evaluation {
                expression,
                value: Some(value),
                ..
            }) = &whole_node.payload
            else {
                unreachable!()
            };
            let mut expected = vec![*template, anchor];
            expected.extend(values.iter().copied());
            if *expression != anchor
                || self.get(*value)?.arguments != expected
                || whole_node.scope != node.scope
                || whole_node.support != node.support
            {
                return Err("数値補完対が別caseのslot値・whole結果を指す".into());
            }
        }
        let Some(Payload::Evaluation { value: left, .. }) = &self.get(*first_result)?.payload
        else {
            unreachable!()
        };
        let Some(Payload::Evaluation { value: right, .. }) = &self.get(*second_result)?.payload
        else {
            unreachable!()
        };
        if self.boolean(*left)? == self.boolean(*right)? {
            return Err("数値補完対の全称whole判断が同じ".into());
        }
        Ok(true)
    }

    fn universal_body_contains_source(
        &self,
        body_source: NodeRef,
        call_source: NodeRef,
        caller: super::call::Context,
    ) -> Result<bool, ValidationFailure> {
        let mut body_evaluation = None;
        for (index, node) in self.nodes.iter().enumerate() {
            self.tick()?;
            if self.context_at(index) == self.context_at(body_source.0)
                && matches!(&node.payload, Some(Payload::Evaluation { expression, .. }) if *expression == body_source)
                && node.arguments.first() == Some(&body_source)
                && body_evaluation.replace(NodeRef(index)).is_some()
            {
                return Err("全域反例の元body Sourceに複数の実Evaluationがある".into());
            }
        }
        let root = body_evaluation.ok_or("全域反例の元body実Evaluationがない")?;
        let mut pending = vec![root];
        let mut seen = BTreeSet::new();
        while let Some(reference) = pending.pop() {
            self.tick()?;
            if !seen.insert(reference.0) {
                continue;
            }
            let node = self.get(reference)?;
            let Some(Payload::Evaluation {
                expression, parts, ..
            }) = &node.payload
            else {
                return Err("全域反例の元body実子が完成Evaluationでない".into());
            };
            if *expression == call_source && self.context_at(reference.0) == caller {
                if node.arguments.first() != Some(&call_source) {
                    return Err("全域反例の実call評価が元CallSourceを保持しない".into());
                }
                return Ok(true);
            }
            for part in parts {
                for &child in &part.children {
                    self.tick()?;
                    if child.0 >= reference.0
                        || !matches!(self.get(child)?.ty, NodeType::Evaluation(_))
                    {
                        return Err("全域反例の元body実子DAGが既出Evaluationでない".into());
                    }
                    pending.push(child);
                }
            }
        }
        Ok(false)
    }

    fn universal_call_descends_from(
        &self,
        callee: NodeRef,
        caller: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let target = self.context_at(caller.0);
        let mut context = self.context_at(callee.0);
        let mut source = callee;
        let mut seen = BTreeSet::new();
        while let Some(index) = context.frame {
            self.tick()?;
            if !seen.insert(index) {
                return Err("全域反例の実call frameが循環する".into());
            }
            let frame = self
                .frames
                .get(index)
                .ok_or("全域反例の実call frameがない")?;
            if self.context_at(frame.source.0) != frame.caller
                || !self.get(source)?.arguments.contains(&frame.source)
                || !matches!(
                    &self.get(frame.source)?.payload,
                    Some(Payload::Expression { .. })
                )
            {
                return Err("全域反例のcallee Sourceが元実call producerを保持しない".into());
            }
            for &argument in &frame.arguments {
                self.tick()?;
                if !matches!(
                    &self.get(argument)?.payload,
                    Some(Payload::Evaluation { .. })
                ) || !self.get(source)?.arguments.contains(&argument)
                {
                    return Err("全域反例の実call引数Evaluationが別のproducer".into());
                }
            }
            if frame.caller == target {
                return self.universal_body_contains_source(caller, frame.source, frame.caller);
            }
            source = frame.source;
            context = frame.caller;
        }
        Ok(false)
    }

    fn universal_local_binding_witness(
        &self,
        original_side: NodeRef,
        caller_body: NodeRef,
        binding: &Binding,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        let original = self.get(original_side)?;
        let Some(Payload::Expression { parameters, .. }) = &original.payload else {
            return Ok(false);
        };
        if !parameters
            .iter()
            .any(|(name, ty)| *name == binding.name && *ty == binding.ty)
        {
            return Ok(false);
        }
        let Some(&root) = original.arguments.first() else {
            return Ok(false);
        };
        self.universal_template_sources(root)?;
        let scalar = self.get(binding.value)?;
        if scalar.ty != NodeType::Value(binding.ty.clone())
            || scalar.arguments != [root, original_side]
            || self.context_at(binding.value.0) != self.context_at(caller_body.0)
        {
            return Ok(false);
        }
        for &domain in &original.arguments {
            self.tick()?;
            let domain_node = self.get(domain)?;
            let Some(Payload::TypeDomain { ty }) = &domain_node.payload else {
                continue;
            };
            let [header] = domain_node.arguments.as_slice() else {
                continue;
            };
            if self.universal_local_header_root(*header)? != Some(root)
                || *ty != binding.ty
                || self.context_at(domain.0) != self.context_at(original_side.0)
                || self.context_at(header.0) != self.context_at(original_side.0)
            {
                continue;
            }
            let Rule::Input {
                kind: "law",
                location: Location::Law { span: binder },
            } = &domain_node.rule
            else {
                continue;
            };
            if !matches!(&scalar.rule, Rule::Input {kind:"law", location:Location::Law {span}} if span == binder)
            {
                continue;
            }
            let matching = original
                .scope
                .quantifiers
                .iter()
                .filter(|q| {
                    q.domain == Some(domain)
                        && q.kind == crate::law::ast::QuantKind::Forall
                        && q.name == binding.name
                        && q.ty == binding.ty
                        && q.occurrence == *binder
                        && q.context == Some(self.context_at(original_side.0))
                })
                .count();
            if matching == 1
                && self.universal_body_contains_source(
                    caller_body,
                    *header,
                    self.context_at(original_side.0),
                )?
            {
                self.value(binding.value, &binding.ty)?;
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn universal_local_substitution_extends_caller(
        &self,
        original_side: NodeRef,
        caller_body: NodeRef,
        caller_bindings: &[Binding],
        side_bindings: &[Binding],
    ) -> Result<bool, ValidationFailure> {
        let mut local_changes = false;
        for binding in side_bindings {
            self.tick()?;
            if !caller_bindings.contains(binding) {
                if !self.universal_local_binding_witness(original_side, caller_body, binding)? {
                    return Ok(false);
                }
                local_changes = true;
            }
        }
        for original in caller_bindings {
            self.tick()?;
            if side_bindings.contains(original) {
                continue;
            }
            let mut shadowed = false;
            for binding in side_bindings
                .iter()
                .filter(|binding| binding.name == original.name)
            {
                self.tick()?;
                if self.universal_local_binding_witness(original_side, caller_body, binding)? {
                    shadowed = true;
                    break;
                }
            }
            if !shadowed {
                return Ok(false);
            }
            local_changes = true;
        }
        Ok(local_changes)
    }

    /// 有限族の各rowは、そのrowで全数値parameterを全称化したwholeを証明する。
    fn universal_counterexample_for_evaluation(
        &self,
        evidence: NodeRef,
        evaluation: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        let proof = self.get(evidence)?;
        if !self.universal_counterexample_shape(proof)? {
            return Ok(false);
        }
        let whole = self.get(evaluation)?;
        if !self.universal_evaluation_shape(whole)? {
            return Ok(false);
        }
        let Some(Payload::Evaluation {
            expression, value, ..
        }) = &whole.payload
        else {
            unreachable!()
        };
        let [normalization] = whole.evidence.as_slice() else {
            return Ok(false);
        };
        if self.boolean(*value)? != Some(false)
            || self.context_at(evidence.0) != self.context_at(evaluation.0)
            || proof.scope != whole.scope
            || proof.support != whole.support
        {
            return Ok(false);
        }
        Ok(match proof.arguments.as_slice() {
            [source, actual_whole, actual_normalization] => {
                source == expression
                    && *actual_whole == evaluation
                    && actual_normalization == normalization
            }
            [source, actual_normalization, _, _, _] => {
                source == expression && actual_normalization == normalization
            }
            _ => false,
        })
    }

    fn universal_counterexample_shape(&self, node: &Node) -> Result<bool, ValidationFailure> {
        let Some(Payload::Counterexample {
            bindings,
            left,
            right,
            facts,
        }) = &node.payload
        else {
            return Ok(false);
        };
        match node.arguments.as_slice() {
            [source, evaluation, normalization] => {
                if !matches!(&self.get(*normalization)?.payload, Some(Payload::Normalization { before, .. }) if before == source)
                    || !self.universal_normalization_shape(self.get(*normalization)?)?
                {
                    return Ok(false);
                }
                let whole = self.get(*evaluation)?;
                if !self.universal_evaluation_shape(whole)? {
                    return Err("全域反例が元whole評価を指さない".into());
                }
                let Some(Payload::Evaluation {
                    expression,
                    bindings: fixed,
                    value,
                    ..
                }) = &whole.payload
                else {
                    unreachable!()
                };
                let expected = self.get(*right)?;
                if expression != source
                    || bindings != fixed
                    || *value != Some(*left)
                    || self.scalar(*left)? != &Scalar::Bool(false)
                    || self.scalar(*right)? != &Scalar::Bool(true)
                    || whole.evidence != [*normalization]
                    || expected.arguments != node.arguments
                    || !matches!(expected.rule, Rule::Construction("proposition"))
                    || node.scope != whole.scope
                    || facts != &node.support
                    || node.support != whole.support
                {
                    return Err("全域反例の偽・要求真・正規化・支持が違う".into());
                }
                Ok(true)
            }
            [
                source,
                normalization,
                substitution,
                left_evaluation,
                right_evaluation,
            ] => {
                if !matches!(&self.get(*normalization)?.payload, Some(Payload::Normalization { before, .. }) if before == source)
                    || !self.universal_normalization_shape(self.get(*normalization)?)?
                {
                    return Ok(false);
                }
                let Some(Payload::Normalization { after, steps, .. }) =
                    &self.get(*normalization)?.payload
                else {
                    unreachable!()
                };
                if self.scalar(*after)? != &Scalar::Bool(false) {
                    return Err("具体全域反例のwholeが偽でない".into());
                }
                let [difference_step, body_substitution_step] = steps.as_slice() else {
                    return Err("具体全域反例の正規化stepが元差・caller代入でない".into());
                };
                let substitute = self.get(*substitution)?;
                self.parameterized_transform_shape(substitute)?;
                let Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Substitute,
                    operands,
                    bindings: actual,
                    ..
                }) = &substitute.payload
                else {
                    return Err("具体全域反例に元bodyの同時代入がない".into());
                };
                if substitute.ty != NodeType::Expression(Type::Bool)
                    || self.get(operands[0])?.arguments.first() != Some(source)
                    || bindings != actual
                    || body_substitution_step != substitution
                    || left != left_evaluation
                    || right != right_evaluation
                {
                    return Err("具体全域反例の元body・束縛・左右が違う".into());
                }
                let NodeType::Evaluation(ty @ (Type::Z | Type::Q)) = &self.get(*left)?.ty else {
                    return Err("具体全域反例の左辺が数値Evaluationでない".into());
                };
                self.expect(*right, &NodeType::Evaluation(ty.clone()))?;
                let Some(Payload::ParameterizedTransform {
                    operands: original_sides,
                    ..
                }) = &self.get(*difference_step)?.payload
                else {
                    return Err("具体全域反例の元差Expressionがない".into());
                };
                for (&evaluation, &original_side) in [*left, *right].iter().zip(original_sides) {
                    self.tick()?;
                    let Some(Payload::Evaluation {
                        expression,
                        bindings: evaluation_bindings,
                        ..
                    }) = &self.get(evaluation)?.payload
                    else {
                        return Err("具体全域反例が未生成の左右評価を消費した".into());
                    };
                    let expression = self.get(*expression)?;
                    self.parameterized_transform_shape(expression)?;
                    let Some(Payload::ParameterizedTransform {
                        operation: TransformOp::Substitute,
                        operands: actual_sides,
                        bindings: actual,
                        ..
                    }) = &expression.payload
                    else {
                        return Err("具体全域反例が元左右へ再代入していない".into());
                    };
                    if actual_sides != &[original_side] || actual != evaluation_bindings {
                        return Err("具体全域反例の左右が別の元式・同時代入を使う".into());
                    }
                    if self.context_at(original_side.0) == self.context_at(operands[0].0) {
                        if actual != bindings
                            && !self.universal_local_substitution_extends_caller(
                                original_side,
                                operands[0],
                                bindings,
                                actual,
                            )?
                        {
                            return Err(
                                "直接Eqの全域反例が局所型Domainによらず左右の同時代入を変えた"
                                    .into(),
                            );
                        }
                    } else if !self.universal_call_descends_from(original_side, operands[0])? {
                        return Err("具体全域反例のcalleeが元caller代入に属さない".into());
                    }
                }
                if node.scope != self.get(*normalization)?.scope
                    || node.support != self.get(*normalization)?.support
                    || facts != &node.support
                {
                    return Err("具体全域反例のScope・支持が違う".into());
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn affine_comparison_shape(
        &self,
        evaluation: NodeRef,
        left: NodeRef,
        right: NodeRef,
        residual: NodeRef,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        let NodeType::Evaluation(ty) = &self.get(left)?.ty else {
            return Err("アフィン証拠の左辺がEvaluationでない".into());
        };
        if !super::numeric::is_numeric_type(ty, &self.control)? {
            return Err("アフィン証拠の元型が数値型でない".into());
        }
        self.expect(right, &NodeType::Evaluation(ty.clone()))?;
        self.value(residual, ty)?;
        self.expect(evaluation, &NodeType::Evaluation(Type::Bool))?;
        let Some(Payload::Evaluation {
            expression,
            parts,
            value: Some(value),
            ..
        }) = &self.get(evaluation)?.payload
        else {
            return Err("アフィン証拠の元比較が確定Evaluationでない".into());
        };
        let part = parts.last().ok_or("アフィン比較の元partがない")?;
        if part.children != [left, right] || part.residual != Some(residual) {
            return Err("アフィン比較の実左右・残差が違う".into());
        }
        let result = self.get(*value)?;
        self.value(*value, &Type::Bool)?;
        let [
            source,
            lhs,
            rhs,
            difference,
            supplied_residual,
            normalization,
        ] = result.arguments.as_slice()
        else {
            return Err("アフィン比較値の導出入力が違う".into());
        };
        if source != expression
            || *lhs != left
            || *rhs != right
            || *supplied_residual != residual
            || result.evidence != [*normalization]
        {
            return Err("アフィン比較値と元評価・正規化証拠が違う".into());
        }
        let evidence = self.get(*normalization)?;
        self.expect(*normalization, &NodeType::Evidence)?;
        self.normalization_shape(evidence)?;
        if !matches!(&evidence.payload, Some(Payload::Normalization { before, after, .. }) if before == difference && *after == residual)
        {
            return Err("アフィン比較の差と正規化証拠が違う".into());
        }
        self.tick()?;
        Ok(())
    }

    pub fn push(&mut self, node: Node) -> Result<NodeRef, ValidationFailure> {
        self.push_with_metadata(node, |_| {})
    }
    /// append と metadata の確定を一つの commit とし、その後にだけ停止を調べる。
    pub(crate) fn push_with_metadata(
        &mut self,
        node: Node,
        committed: impl FnOnce(NodeRef),
    ) -> Result<NodeRef, ValidationFailure> {
        self.tick()?;
        for &r in &node.arguments {
            self.tick()?;
            self.get(r)?;
            self.tick()?;
        }
        for &r in &node.evidence {
            self.tick()?;
            self.expect(r, &NodeType::Evidence)?;
            self.tick()?;
        }
        self.reasons(&node.reasons)?;
        for (index, quantifier) in node.scope.quantifiers.iter().enumerate() {
            self.tick()?;
            if node.scope.quantifiers[..index].contains(quantifier) {
                return Err("Scopeに同じ実量化descriptorが重複する".into());
            }
            if let Some(domain) = quantifier.domain {
                self.expect(domain, &NodeType::Domain)?;
                let domain_type = match &self.get(domain)?.payload {
                    Some(Payload::TypeDomain { ty }) | Some(Payload::Domain { ty, .. }) => ty,
                    _ => return Err("Scopeが未生成の量化Domainを消費した".into()),
                };
                if domain_type != &quantifier.ty {
                    return Err("Scopeの量化型とDomain型が違う".into());
                }
            }
        }
        match (&node.ty, &node.payload) {
            (NodeType::Domain, Some(Payload::TypeDomain { ty })) => {
                if !matches!(ty, Type::Z | Type::Q) || !node.scope.assignments {
                    return Err("型全域DomainがZ/Q全代入域でない".into());
                }
                let [source] = node.arguments.as_slice() else {
                    return Err("型全域Domainに元Sourceがない".into());
                };
                self.expect(*source, &NodeType::Expression(Type::Bool))?;
                self.universal_template_sources(*source)?;
            }
            (NodeType::Domain, Some(Payload::Domain { ty, elements })) => {
                let mut values = Vec::new();
                for element in elements {
                    self.tick()?;
                    self.value(*element, ty)?;
                    let scalar = self.scalar(*element)?;
                    if super::data::contains(&values, scalar, &self.control)? {
                        return Err("Domainに意味上重複する要素がある".into());
                    }
                    values.push(scalar.clone());
                }
            }
            (
                NodeType::Evidence,
                Some(Payload::FiniteExhaustion {
                    domain,
                    checked,
                    instances,
                }),
            ) => {
                self.expect(*domain, &NodeType::Domain)?;
                let Some(Payload::Domain { elements, .. }) = &self.get(*domain)?.payload else {
                    return Err("全検査域が有限域でない".into());
                };
                if *checked != elements.len() || instances.len() != elements.len() {
                    return Err("全検査の件数と域が違う".into());
                }
                for instance in instances {
                    self.tick()?;
                    if self.get(*domain)?.arguments.first().is_some_and(|r| {
                        matches!(
                            self.get(*r).map(|n| &n.payload),
                            Ok(Some(Payload::CompletionSeed { .. }))
                        )
                    }) {
                        if !matches!(self.get(*instance)?.ty, NodeType::Evaluation(_)) {
                            return Err("補完coverageがEvaluationでない".into());
                        }
                    } else {
                        self.expect(*instance, &NodeType::Evaluation(Type::Bool))?;
                    }
                }
            }
            (NodeType::Value(t), Some(Payload::Scalar(s))) if t == &s.ty() => {
                super::data::check_shape(s, &self.control)?;
                self.universal_witness_value_shape(&node)?;
                self.universal_local_quantifier_value_shape(&node)?;
            }
            (
                NodeType::Expression(_),
                Some(
                    Payload::Expression { bindings, .. } | Payload::CompletionSeed { bindings, .. },
                ),
            ) => self.bindings(bindings)?,
            (NodeType::Expression(_), Some(Payload::ParameterizedTransform { .. })) => {
                self.parameterized_transform_shape(&node)?;
            }
            (
                NodeType::Expression(_),
                Some(Payload::Transform {
                    operation: TransformOp::Difference,
                    ..
                }),
            ) => {
                self.difference_shape(&node)?;
            }
            (
                NodeType::Expression(Type::Bool),
                Some(Payload::Transform {
                    operation,
                    operands,
                    bindings,
                }),
            ) => {
                if !matches!(operation, TransformOp::Not | TransformOp::And) {
                    return Err("Boolの既存変換がnot/andでない".into());
                }
                self.bindings(bindings)?;
                if operands.len() != operation.arity() {
                    return Err("Bool 変換の引数数が違う".into());
                }
                for &operand in operands {
                    self.tick()?;
                    self.expect(operand, &NodeType::Expression(Type::Bool))?;
                    self.tick()?;
                }
            }
            (
                NodeType::Evaluation(t),
                Some(Payload::Evaluation {
                    expression,
                    bindings,
                    parts,
                    value,
                    applicability,
                }),
            ) => {
                self.expect(*expression, &NodeType::Expression(t.clone()))?;
                if node.scope.assignments && self.get(*expression)?.payload.is_none() {
                    return Err("全域評価が未生成のExpressionを消費した".into());
                }
                self.bindings(bindings)?;
                if !["applicable", "not_applicable", "undetermined"].contains(applicability) {
                    return Err("適用表示が不正".into());
                }
                if let Some(v) = value {
                    self.value(*v, t)?;
                }
                for p in parts {
                    self.tick()?;
                    if let Some(v) = p.value {
                        self.scalar(v)?;
                    }
                    if let Some(r) = p.residual {
                        if let NodeType::Evaluation(ty @ (Type::Z | Type::Q)) = &self.get(r)?.ty {
                            if !node.scope.assignments
                                || !matches!(
                                    &self.get(r)?.payload,
                                    Some(Payload::Evaluation { .. })
                                )
                            {
                                return Err("全域残差が完成した数値Evaluationでない".into());
                            }
                            self.expect(r, &NodeType::Evaluation(ty.clone()))?;
                        } else {
                            let value = self.scalar(r)?;
                            if !super::numeric::is_numeric_type(&value.ty(), &self.control)? {
                                return Err("残差が数値型でない".into());
                            }
                            super::numeric::check(value, &self.control)?;
                        }
                    }
                    for &c in &p.children {
                        self.tick()?;
                        if !matches!(self.get(c)?.ty, NodeType::Evaluation(_)) {
                            return Err("子が Evaluation でない".into());
                        }
                        if node.scope.assignments
                            && !matches!(&self.get(c)?.payload, Some(Payload::Evaluation { .. }))
                        {
                            return Err("全域評価が未生成の子Evaluationを消費した".into());
                        }
                        self.tick()?;
                    }
                    self.tick()?;
                }
                if !self.universal_witness_evaluation_shape(&node)?
                    && !self.universal_local_quantifier_evaluation_shape(&node)?
                {
                    self.universal_evaluation_shape(&node)?;
                }
            }
            (
                NodeType::LawInstance,
                Some(
                    Payload::LawInstance {
                        bindings,
                        guard,
                        body,
                        ..
                    }
                    | Payload::CompletionInstance {
                        bindings,
                        guard,
                        body,
                        ..
                    },
                ),
            ) => {
                self.bindings(bindings)?;
                self.expect(*body, &NodeType::Expression(Type::Bool))?;
                if let Some(g) = guard {
                    self.expect(*g, &NodeType::Expression(Type::Bool))?;
                }
            }
            (NodeType::Proposition, Some(Payload::Proposition { instance })) => {
                self.expect(*instance, &NodeType::LawInstance)?
            }
            (NodeType::Proposition, Some(Payload::MapDomainCondition { left, right })) => {
                let Type::Set(ref element) = self.scalar(*left)?.ty() else {
                    return Err("Map域条件の左辺がSetでない".into());
                };
                if !matches!(element.as_ref(), Type::Ref(_)) {
                    return Err("Map域条件の要素型が参照でない".into());
                }
                self.expect(*right, &self.get(*left)?.ty)?;
            }
            (NodeType::Proposition, Some(Payload::OwnedCallCondition { left, right })) => {
                if !matches!(self.scalar(*left)?.ty(), Type::Ref(_) | Type::Text) {
                    return Err("Owned条件がowner参照・snapshot値でない".into());
                }
                self.expect(*right, &self.get(*left)?.ty)?;
            }
            (NodeType::Evidence, Some(Payload::OwnedCallCounterexample { .. })) => {
                self.owned_call_counterexample_shape(&node)?;
            }
            (
                NodeType::Evidence,
                Some(Payload::TermComparison {
                    source,
                    left,
                    right,
                    before,
                    after,
                    ..
                }),
            ) => {
                let [own, le, re, l, r, selected, normal] = node.arguments.as_slice() else {
                    return Err("Term正規化の元実辺数が違う".into());
                };
                if source != own
                    || left != l
                    || right != r
                    || before != selected
                    || after != normal
                    || !([*l, *r].contains(selected))
                    || self.get(*l)?.ty != self.get(*r)?.ty
                    || !matches!(self.get(*l)?.ty, NodeType::Value(Type::Term(..)))
                    || self.get(*le)?.ty != self.get(*re)?.ty
                    || !matches!(self.get(*le)?.ty, NodeType::Evaluation(Type::Term(..)))
                    || !matches!(self.get(*normal)?.ty, NodeType::Value(_))
                {
                    return Err("Term正規化の元型・左右が違う".into());
                }
                self.expect(*own, &NodeType::Expression(Type::Bool))?;
            }
            (
                NodeType::Evidence,
                Some(Payload::TermCounterexample {
                    bindings,
                    left,
                    right,
                    ..
                }),
            ) => {
                self.bindings(bindings)?;
                if self.get(*left)?.ty != self.get(*right)?.ty
                    || !matches!(self.get(*left)?.ty, NodeType::Value(_))
                {
                    return Err("Term相違点の左右結果型が違う".into());
                }
            }
            (NodeType::Evidence, Some(Payload::Normalization { .. })) => {
                self.normalization_shape(&node)?
            }
            (
                NodeType::Evidence,
                Some(Payload::EvaluationEvidence {
                    instance,
                    lhs,
                    rhs,
                    residual,
                }),
            ) => {
                self.expect(*instance, &NodeType::LawInstance)?;
                if matches!(self.get(*lhs)?.ty, NodeType::Evaluation(_))
                    || matches!(self.get(*rhs)?.ty, NodeType::Evaluation(_))
                {
                    let [actual_instance, evaluation] = node.arguments.as_slice() else {
                        return Err("アフィン評価証拠の元instance・評価がない".into());
                    };
                    if actual_instance != instance {
                        return Err("アフィン評価証拠のinstanceが違う".into());
                    }
                    self.affine_comparison_shape(
                        *evaluation,
                        *lhs,
                        *rhs,
                        residual.ok_or("アフィン評価証拠に残差がない")?,
                    )?;
                } else {
                    let l = self.scalar(*lhs)?;
                    let r = self.scalar(*rhs)?;
                    if l.ty() != r.ty() {
                        return Err("証拠両辺の型不一致".into());
                    }
                    if let Some(d) = residual {
                        let expected = super::numeric::binary(
                            crate::law::ast::BinOp::Sub,
                            l,
                            r,
                            &self.control,
                        )?;
                        if self.scalar(*d)? != &expected {
                            return Err("型付き残差が元の両辺に合わない".into());
                        }
                    }
                }
            }
            (
                NodeType::Evidence,
                Some(Payload::CompletionPair {
                    fields,
                    first,
                    second,
                    first_result,
                    second_result,
                }),
            ) => {
                if fields.is_empty()
                    || fields.len() != first.len()
                    || fields.len() != second.len()
                    || fields.iter().enumerate().any(|(i, f)| {
                        f.field.is_none() || f.atom.is_some() || fields[..i].contains(f)
                    })
                {
                    return Err("補完対の元slot列が不正".into());
                }
                for (&left, &right) in first.iter().zip(second) {
                    self.tick()?;
                    let ty = self.scalar(left)?.ty();
                    if self.scalar(right)?.ty() != ty {
                        return Err("補完対のslot代入型が左右で違う".into());
                    }
                    self.value(left, &ty)?;
                    self.value(right, &ty)?;
                }
                if !matches!(&self.get(*first_result)?.ty, NodeType::Evaluation(_))
                    || self.get(*first_result)?.ty != self.get(*second_result)?.ty
                {
                    return Err("補完対の結果型が違う".into());
                }
                if !self.universal_completion_pair_shape(&node)?
                    && node.scope.assignments
                    && !node.arguments.first().is_some_and(|source| {
                        matches!(
                            self.get(*source).map(|node| &node.payload),
                            Ok(Some(Payload::CompletionSeed { .. }))
                        )
                    })
                {
                    return Err("数値補完対に元whole・slot代入の専用導出がない".into());
                }
            }
            (
                NodeType::Evidence,
                Some(Payload::Counterexample {
                    bindings,
                    left,
                    right,
                    ..
                }),
            ) => {
                self.bindings(bindings)?;
                if self.map_domain_counterexample_shape(&node)? {
                    // 元Map適用に対する型付き集合等値の反例。
                } else if self.universal_counterexample_shape(&node)? {
                    // 数値値が未確定でも、元同時代入とwhole正規化を保持する専用形だけを通す。
                } else if node.scope.assignments
                    && !(matches!(node.arguments.as_slice(), [instance, evaluation]
                        if self.get(*instance)?.ty == NodeType::LawInstance
                            && self.get(*evaluation)?.ty == NodeType::Evaluation(Type::Bool))
                        || self.quantifier_counterexample_shape(&node)?)
                {
                    return Err("全域反例に元whole正規化の専用導出がない".into());
                } else if matches!(self.get(*left)?.ty, NodeType::Evaluation(_))
                    || matches!(self.get(*right)?.ty, NodeType::Evaluation(_))
                {
                    let [instance, evaluation] = node.arguments.as_slice() else {
                        return Err("アフィン反例の元instance・評価がない".into());
                    };
                    self.expect(*instance, &NodeType::LawInstance)?;
                    let Some(Payload::Evaluation { parts, value, .. }) =
                        &self.get(*evaluation)?.payload
                    else {
                        return Err("アフィン反例の元比較Evaluationがない".into());
                    };
                    let residual = parts
                        .last()
                        .and_then(|part| part.residual)
                        .ok_or("アフィン反例に元残差がない")?;
                    self.affine_comparison_shape(*evaluation, *left, *right, residual)?;
                    if self.boolean(*value)? != Some(false) {
                        return Err("アフィン反例の元比較がfalseでない".into());
                    }
                } else if self.scalar(*left)?.ty() != self.scalar(*right)?.ty() {
                    return Err("反例の型不一致".into());
                }
            }
            (_, None) if !node.reasons.is_empty() => {}
            _ => return Err("node の型と payload が合わない".into()),
        }
        if let Some(j) = &node.judgment {
            if node.ty != NodeType::Proposition {
                return Err("Proposition 以外の判断".into());
            }
            for &r in &j.evidence {
                self.tick()?;
                self.expect(r, &NodeType::Evidence)?;
                self.tick()?;
            }
            self.reasons(&j.reasons)?;
            if j.status == Decision::Refuted && j.evidence.is_empty() {
                return Err("反証の証拠がない".into());
            }
        }
        if node.ty == NodeType::Proposition {
            self.validate_proposition_evidence(&node)?;
        }
        let r = NodeRef(self.nodes.len());
        self.nodes.push(node);
        self.contexts.push(self.active);
        committed(r);
        self.tick()?;
        Ok(r)
    }
    /// Ref・出力・claim 間の構造検査。完成回答は Environment::validate_answer で
    /// 元 Request・宣言・明示束縛への意味上の帰属も必ず検査する。
    /// 構造の検査。元 Request への帰属は Environment の総合 Answer 検査で確かめる。
    pub fn validate_answer(&self, a: &Answer, check: bool) -> Result<(), ValidationFailure> {
        self.tick()?;
        self.reasons(&a.reasons)?;
        for &r in &a.evidence {
            self.tick()?;
            self.expect(r, &NodeType::Evidence)?;
            self.tick()?;
        }
        for (name, &r) in &a.outputs {
            self.tick()?;
            match name.as_str() {
                "value" => {
                    if check {
                        return Err("check に value 出力がある".into());
                    }
                    self.scalar(r)?;
                }
                "evaluation" => {
                    if !matches!(self.get(r)?.ty, NodeType::Evaluation(_)) {
                        return Err("出力 evaluation の型不一致".into());
                    }
                }
                "proposition" => {
                    if !check {
                        return Err("evaluate に proposition 出力がある".into());
                    }
                    self.expect(r, &NodeType::Proposition)?;
                }
                _ => return Err("未定義の出力欄".into()),
            }
            self.tick()?;
        }
        if a.claim.is_none()
            && !a.evidence.is_empty()
            && !a.outputs.get("evaluation").is_some_and(|r| {
                self.get(*r).is_ok_and(|n| {
                    n.arguments.first().is_some_and(|s| {
                        matches!(
                            self.get(*s).map(|n| &n.payload),
                            Ok(Some(Payload::CompletionSeed { .. }))
                        )
                    })
                })
            })
        {
            return Err("claim のない Answer に命題証拠がある".into());
        }
        if !check && (a.claim.is_some() || a.status == Decision::Refuted) {
            return Err("evaluate に命題の判断がある".into());
        }
        if let Some(&value) = a.outputs.get("value") {
            let evaluation = a.outputs.get("evaluation").ok_or("値の元評価がない")?;
            let node = self.get(*evaluation)?;
            let (
                NodeType::Evaluation(ty),
                Some(Payload::Evaluation {
                    value: Some(expected),
                    ..
                }),
            ) = (&node.ty, &node.payload)
            else {
                return Err("値の元評価に確定値がない".into());
            };
            self.value(value, ty)?;
            if value != *expected {
                return Err("Answer の値が返却評価の値と違う".into());
            }
        } else if !check && a.status == Decision::Established {
            return Err("確定 evaluate に値がない".into());
        }
        if let Some(evaluation) = a.outputs.get("evaluation")
            && self.get(*evaluation)?.scope != a.scope
        {
            return Err("Answer の範囲が返却評価と違う".into());
        }
        if let Some(c) = a.claim {
            self.expect(c, &NodeType::Proposition)?;
            if self.get(c)?.scope != a.scope {
                return Err("Answer と claim の範囲が違う".into());
            }
            let Some(j) = &self.get(c)?.judgment else {
                return Err("claim に判断がない".into());
            };
            self.validate_proposition_evidence(self.get(c)?)?;
            if a.evidence != j.evidence || a.evidence != self.get(c)?.evidence {
                return Err("Answer の証拠が claim・判断と違う".into());
            }
            if j.status != a.status || a.outputs.get("proposition") != Some(&c) {
                return Err("Answer と claim が不一致".into());
            }
            if a.outputs.get("evaluation") != self.get(c)?.arguments.get(1) {
                return Err("Answer と claim の元評価が違う".into());
            }
        }
        if check && a.status != Decision::Undetermined && a.claim.is_none() {
            return Err("確定 check に claim がない".into());
        }
        if a.status == Decision::Refuted && a.evidence.is_empty() {
            return Err("反証 Answer に証拠がない".into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod invariant_tests {
    use super::*;
    fn integer() -> Node {
        Node {
            ty: NodeType::Value(Type::Z),
            payload: Some(Payload::Scalar(Scalar::Z(2.into()))),
            rule: Rule::Construction("evaluation"),
            arguments: vec![],
            support: vec![],
            evidence: vec![],
            judgment: None,
            scope: Scope::default(),
            reasons: vec![],
        }
    }
    #[test]
    fn rejects_forward_refs_and_payload_type_mismatch() {
        let mut graph = Graph::default();
        let mut node = integer();
        node.arguments.push(NodeRef(0));
        assert!(matches!(
            graph.push(node),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(graph.nodes.is_empty());
        let mut node = integer();
        node.ty = NodeType::Value(Type::Bool);
        assert!(matches!(
            graph.push(node),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(graph.nodes.is_empty());
    }
    #[test]
    fn rejects_blocked_binding_and_judgment_on_values() {
        let mut graph = Graph::default();
        let mut node = integer();
        node.payload = None;
        node.reasons
            .push(Reason::internal("test", "blocked".into()));
        let blocked = graph.push(node).unwrap();
        let expression = Node {
            ty: NodeType::Expression(Type::Z),
            payload: Some(Payload::Expression {
                location: Location::Law { span: (1, 2) },
                parameters: vec![],
                bindings: vec![Binding {
                    name: "x".into(),
                    value: blocked,
                    ty: Type::Z,
                }],
            }),
            rule: Rule::Construction("expression"),
            arguments: vec![],
            support: vec![],
            evidence: vec![],
            judgment: None,
            scope: Scope::default(),
            reasons: vec![],
        };
        assert!(matches!(
            graph.push(expression),
            Err(ValidationFailure::Internal(_))
        ));
        let mut node = integer();
        node.judgment = Some(Judgment {
            status: Decision::Established,
            evidence: vec![],
            reasons: vec![],
        });
        assert!(matches!(
            graph.push(node),
            Err(ValidationFailure::Internal(_))
        ));
    }
}
