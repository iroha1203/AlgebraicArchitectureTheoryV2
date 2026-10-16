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
    Unit,
    Text(String),
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
            Self::Unit => Type::Unit,
            Self::Text(_) => Type::Text,
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
    fn wire(&self) -> Json {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Self::Unit => Json::Arr(vec![]),
            Self::Text(text) => Json::str(text),
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
            Self::Unit => f.write_str("Unit"),
            Self::Text(text) => f.debug_tuple("Text").field(text).finish(),
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
            Self::Unit => Self::Unit,
            Self::Text(text) => Self::Text(text.clone()),
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
            (Self::Unit, Self::Unit) => true,
            (Self::Text(a), Self::Text(b)) => a == b,
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
#[derive(Clone, Debug)]
pub(crate) enum ReasonKind {
    Missing,
    Stop(StopReason),
    Internal(String),
}
#[derive(Clone, Debug)]
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
            ReasonKind::Stop(r) => r.code(),
            ReasonKind::Internal(_) => "internal",
        }
    }
    pub(crate) fn wire(&self) -> Json {
        let (message, details) = match &self.kind {
            ReasonKind::Missing => ("原始 slot の観測が必要", Json::obj([])),
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub(crate) struct Part {
    pub location: Location,
    pub value: Option<NodeRef>,
    pub residual: Option<NodeRef>,
    pub children: Vec<NodeRef>,
}
/// result/2 の固定変換。未知値は通常値にせず、Bool の全補完での定数だけを返す。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransformOp {
    Not,
    And,
}
impl TransformOp {
    fn wire(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::And => "and",
        }
    }
    pub(crate) fn arity(self) -> usize {
        match self {
            Self::Not => 1,
            Self::And => 2,
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
#[derive(Clone, Debug)]
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
    EvaluationEvidence {
        instance: NodeRef,
        lhs: NodeRef,
        rhs: NodeRef,
        residual: Option<NodeRef>,
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
#[derive(Clone, Debug)]
pub(crate) struct Judgment {
    pub status: Decision,
    pub evidence: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
}
#[derive(Clone, Debug)]
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
            if matches!(payload, Payload::Proposition { .. })
                && let Json::Obj(fields) = &mut value
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
    pub fn new(control: &Control) -> Self {
        Self {
            nodes: vec![],
            contexts: vec![],
            frames: vec![],
            iterations: vec![],
            instances: vec![],
            cases: vec![],
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
            if matches!(reason.kind, ReasonKind::Missing)
                && (reason.dependencies.is_empty() || reason.missing.is_empty())
            {
                return Err("canonical 欠測理由に依存式・slot がない".into());
            }
            for &r in &reason.dependencies {
                self.tick()?;
                let node = self.get(r)?;
                if matches!(reason.kind, ReasonKind::Missing)
                    && !matches!(node.ty, NodeType::Expression(_))
                {
                    return Err("欠測の依存先が元式でない".into());
                }
                self.tick()?;
            }
            self.tick()?;
        }
        self.tick()?;
        Ok(())
    }
    /// 添付する証拠は、同じ命題の元 LawInstance と適用評価を証明する。
    pub(crate) fn validate_proposition_evidence(
        &self,
        node: &Node,
    ) -> Result<(), ValidationFailure> {
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
                            if e.arguments.get(1) == Some(&row) {
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
            }
        }
        match (&node.ty, &node.payload) {
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
            }
            (
                NodeType::Expression(_),
                Some(
                    Payload::Expression { bindings, .. } | Payload::CompletionSeed { bindings, .. },
                ),
            ) => self.bindings(bindings)?,
            (
                NodeType::Expression(Type::Bool),
                Some(Payload::Transform {
                    operation,
                    operands,
                    bindings,
                }),
            ) => {
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
                        let value = self.scalar(r)?;
                        if !super::numeric::is_numeric_type(&value.ty(), &self.control)? {
                            return Err("残差が数値型でない".into());
                        }
                        super::numeric::check(value, &self.control)?;
                    }
                    for &c in &p.children {
                        self.tick()?;
                        if !matches!(self.get(c)?.ty, NodeType::Evaluation(_)) {
                            return Err("子が Evaluation でない".into());
                        }
                        self.tick()?;
                    }
                    self.tick()?;
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
                let l = self.scalar(*lhs)?;
                let r = self.scalar(*rhs)?;
                if l.ty() != r.ty() {
                    return Err("証拠両辺の型不一致".into());
                }
                if let Some(d) = residual {
                    let expected =
                        super::numeric::binary(crate::law::ast::BinOp::Sub, l, r, &self.control)?;
                    if self.scalar(*d)? != &expected {
                        return Err("型付き残差が元の両辺に合わない".into());
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
                if self.scalar(*left)?.ty() != self.scalar(*right)?.ty() {
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
