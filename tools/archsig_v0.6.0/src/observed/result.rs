//! 評価内部の型付き DAG。JSON はこの不変データの表示に限定する。

use super::{
    PrepareFailure, PreparedObserved,
    control::{Checkpoint, Control, StopReason},
};
use crate::{canonical::Json, issue::Location, result::location_wire, types::Type};
use num_bigint::BigInt;
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
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Scalar {
    Z(BigInt),
    Bool(bool),
    Subject {
        snapshot: String,
        subject: String,
        entity: String,
    },
}
impl Scalar {
    pub(crate) fn ty(&self) -> Type {
        match self {
            Self::Z(_) => Type::Z,
            Self::Bool(_) => Type::Bool,
            Self::Subject { entity, .. } => Type::Ref(entity.clone()),
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Z(n) => Json::str(n.to_string()),
            Self::Bool(b) => Json::Bool(*b),
            Self::Subject {
                snapshot, subject, ..
            } => Json::Arr(vec![Json::str(snapshot), Json::str(subject)]),
        }
    }
}
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Scope {
    pub readings: BTreeSet<String>,
    pub snapshots: BTreeSet<String>,
    pub modes: BTreeSet<String>,
    pub completions: bool,
}
impl Scope {
    pub(crate) fn merge(&mut self, other: &Self) {
        self.readings.extend(other.readings.iter().cloned());
        self.snapshots.extend(other.snapshots.iter().cloned());
        self.modes.extend(other.modes.iter().cloned());
        self.completions |= other.completions;
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
            ("quantifiers", Json::Arr(vec![])),
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
#[derive(Clone, Debug)]
pub(crate) enum Payload {
    Scalar(Scalar),
    Expression {
        location: Location,
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
            Self::Scalar(v) => v.wire(),
            Self::Expression {
                location,
                parameters,
                bindings,
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
            wire.insert("value".into(), payload.wire());
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
    control: Control,
}
#[derive(Debug)]
pub(crate) enum ValidationFailure {
    Internal(String),
    Stop(StopReason),
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
            control: control.clone(),
        }
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
        let mut counterexample = false;
        for &reference in &node.evidence {
            self.tick()?;
            self.expect(reference, &NodeType::Evidence)?;
            let evidence = self.get(reference)?;
            if evidence.arguments != [*instance, evaluation] {
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
        match (&node.ty, &node.payload) {
            (NodeType::Value(t), Some(Payload::Scalar(s))) if t == &s.ty() => {}
            (NodeType::Expression(_), Some(Payload::Expression { bindings, .. })) => {
                self.bindings(bindings)?
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
                        self.value(r, &Type::Z)?;
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
                Some(Payload::LawInstance {
                    bindings,
                    guard,
                    body,
                    ..
                }),
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
                    let (Scalar::Z(l), Scalar::Z(r), Scalar::Z(d)) = (l, r, self.scalar(*d)?)
                    else {
                        return Err("整数以外の残差".into());
                    };
                    if l - r != *d {
                        return Err("残差が元の両辺に合わない".into());
                    }
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
        committed(r);
        self.tick()?;
        Ok(r)
    }
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
        if a.claim.is_none() && !a.evidence.is_empty() {
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
