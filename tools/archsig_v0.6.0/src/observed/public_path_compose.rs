//! 検査済みPathの同じ全域合成を公開要求と元Refへ接続する。
use super::{
    construction_result::{self as native, ConstructionData as D, ConstructionValue, Witness},
    control::{Checkpoint, Control, StopReason},
    environment::{AnswerBinding, Environment},
    input::CheckedInputs,
    projection::{ProjectionStep as P, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
    PreparedObserved,
};
use crate::canonical::Json;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};
#[derive(Clone, Debug)]
pub(crate) struct PathWitness {
    pub(super) inputs: Arc<CheckedInputs>,
    pub(super) request: Request,
    pub(super) support: Vec<Fact>,
    pub(super) scope: Scope,
    left: NodeRef,
    right: NodeRef,
    source: NodeRef,
    middle_left: NodeRef,
    middle_right: NodeRef,
    target: NodeRef,
    word: Vec<NodeRef>,
    value: Option<Scalar>,
    stopped: Option<StopReason>,
}
impl PartialEq for PathWitness {
    fn eq(&self, b: &Self) -> bool {
        self.inputs.sources() == b.inputs.sources()
            && self.request == b.request
            && self.support == b.support
            && self.scope == b.scope
            && (
                self.left,
                self.right,
                self.source,
                self.middle_left,
                self.middle_right,
                self.target,
            ) == (
                b.left,
                b.right,
                b.source,
                b.middle_left,
                b.middle_right,
                b.target,
            )
            && self.word == b.word
            && self.value == b.value
            && self.stopped == b.stopped
    }
}
impl Eq for PathWitness {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Part {
    Path {
        value: Scalar,
        source: NodeRef,
        target: NodeRef,
        word: Vec<NodeRef>,
        left: NodeRef,
        right: NodeRef,
        condition: NodeRef,
    },
    Claim {
        name: NodeRef,
        left: NodeRef,
        right: NodeRef,
        condition: Option<NodeRef>,
    },
    Endpoints {
        left: NodeRef,
        right: NodeRef,
    },
    Evidence {
        left: NodeRef,
        right: NodeRef,
    },
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
impl Part {
    pub fn scalar(&self) -> Option<&Scalar> {
        if let Self::Path { value, .. } = self {
            Some(value)
        } else {
            None
        }
    }
    pub fn ty(&self) -> NodeType {
        match self {
            Self::Path { value, .. } => NodeType::Value(value.ty()),
            Self::Evidence { .. } => NodeType::Evidence,
            _ => NodeType::Proposition,
        }
    }
    pub fn construction(&self) -> &'static str {
        match self {
            Self::Path { .. } => "composition",
            Self::Evidence { .. } => "evidence",
            _ => "proposition",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Path {
                source,
                target,
                word,
                left,
                right,
                condition,
                ..
            } => [*left, *right, *source, *target, *condition]
                .into_iter()
                .chain(word.iter().copied())
                .collect(),
            Self::Claim {
                name,
                left,
                right,
                condition,
            } => [*name, *left, *right]
                .into_iter()
                .chain(condition.iter().copied())
                .collect(),
            Self::Endpoints { left, right } | Self::Evidence { left, right } => vec![*left, *right],
        }
    }
    pub fn conditions(&self) -> Vec<NodeRef> {
        match self {
            Self::Path { condition, .. } => vec![*condition],
            Self::Claim { condition, .. } => condition.iter().copied().collect(),
            _ => vec![],
        }
    }
    pub fn projection_type(&self) -> Option<ProjectionType> {
        self.scalar().map(|s| ProjectionType::Law(s.ty()))
    }
    pub fn project(&self, path: &[P]) -> Option<(NodeRef, usize)> {
        let Self::Path {
            source,
            target,
            word,
            ..
        } = self
        else {
            return None;
        };
        match path.first()? {
            P::Field(f) if f == "source" => Some((*source, 1)),
            P::Field(f) if f == "target" => Some((*target, 1)),
            P::Field(f) if f == "generators" => {
                let P::Index(i) = path.get(1)? else {
                    return None;
                };
                Some((*word.get(usize::try_from(*i).ok()?)?, 2))
            }
            _ => None,
        }
    }
    pub fn wire(&self) -> Json {
        match self {
            Self::Path {
                value: Scalar::Path(path),
                source,
                target,
                word,
                ..
            } => Json::obj([
                ("reading", Json::str(&path.reading)),
                ("source", source.wire()),
                ("target", target.wire()),
                ("generators", refs(word)),
            ]),
            Self::Path { .. } => unreachable!("Pathのsealed値だけを保持する"),
            Self::Claim {
                name, left, right, ..
            } => Json::obj([
                ("predicate", Json::str("constructible")),
                ("operands", refs(&[*name, *left, *right])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Endpoints { left, right } => Json::obj([
                ("predicate", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Evidence { left, right } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        ("bindings", Json::Arr(vec![])),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                    ]),
                ),
            ]),
        }
    }
}
fn cv(graph: &Graph, r: NodeRef) -> Result<&ConstructionValue, ValidationFailure> {
    match &graph.get(r)?.payload {
        Some(Payload::Construction(v)) => Ok(v),
        _ => Err("Path合成のnative値がない".into()),
    }
}
fn part<'a>(graph: &'a Graph, r: NodeRef, w: &PathWitness) -> Result<&'a Part, ValidationFailure> {
    let v = cv(graph, r)?;
    if !matches!(&v.witness,Witness::PathCompose(c) if c.as_ref()==w) {
        return Err("Path合成の元検査が違う".into());
    }
    match &v.data {
        D::PathComposition(p) => Ok(p),
        _ => Err("Path合成の型付き値でない".into()),
    }
}
fn selector<'a>(r: &'a Request, key: &str) -> Result<&'a Selector, ValidationFailure> {
    if key == "head" {
        Ok(&r.head)
    } else {
        r.arguments
            .iter()
            .find(|a| a.name == key)
            .map(|a| &a.value)
            .ok_or_else(|| "Path合成のthenがない".into())
    }
}
fn selected(
    env: &Environment<'_>,
    graph: &mut Graph,
    r: &Request,
    key: &str,
) -> Result<NodeRef, ValidationFailure> {
    match env.answer_binding(graph, selector(r, key)?, (0, 0))? {
        AnswerBinding::Reference(r) => Ok(r),
        AnswerBinding::Projection(n) => {
            env.validate(graph, &n)?;
            graph.push(n)
        }
        AnswerBinding::Inapplicable(_) => Err("不適合なPath射影を合成へ渡した".into()),
    }
}
fn origin_ref(
    env: &Environment<'_>,
    graph: &Graph,
    s: &Selector,
    r: NodeRef,
) -> Result<bool, ValidationFailure> {
    Ok(match env.answer_binding(graph, s, (0, 0))? {
        AnswerBinding::Reference(actual) => actual == r,
        AnswerBinding::Projection(n) => graph.get(r)? == &n,
        AnswerBinding::Inapplicable(_) => false,
    })
}
pub(super) fn validate_origin(
    env: &Environment<'_>,
    graph: &Graph,
    r: &Request,
    w: &PathWitness,
) -> Result<(), ValidationFailure> {
    if r.kind != QuestionKind::Compose
        || r != &w.request
        || env.inputs.sources() != w.inputs.sources()
        || !origin_ref(env, graph, selector(r, "head")?, w.left)?
        || !origin_ref(env, graph, selector(r, "then")?, w.right)?
    {
        return Err("Path合成が現在の三入力・要求・元Refと違う".into());
    }
    Ok(())
}
fn failed(r: &Request, c: NodeRef) -> Reason {
    Reason {
        kind: ReasonKind::ConditionFailed {
            condition: c,
            construction: "composition",
        },
        request: r.id.clone(),
        dependencies: vec![c],
        missing: vec![],
        location: None,
    }
}
pub(super) fn validate_failure(
    graph: &Graph,
    r: &Reason,
    w: &PathWitness,
) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction: "composition",
    } = r.kind
    else {
        return Err("Path合成の条件理由でない".into());
    };
    if w.value.is_some()
        || r != &failed(&w.request, condition)
        || !matches!(part(graph, condition, w)?, Part::Endpoints { .. })
    {
        return Err("Path合成の反証理由が違う".into());
    }
    validate_node(graph, graph.get(condition)?, w)
}
pub(super) fn validate_node(
    graph: &Graph,
    n: &Node,
    w: &PathWitness,
) -> Result<(), ValidationFailure> {
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("Path合成のpayloadがない".into());
    };
    if n.ty != v.ty()
        || n.rule != v.rule()
        || n.arguments != v.arguments()
        || n.support != w.support
        || n.scope != w.scope
        || !n.reasons.is_empty()
    {
        return Err("Path合成の型・規則・支持・Scopeが違う".into());
    }
    for r in n
        .arguments
        .iter()
        .chain(&n.evidence)
        .chain(n.conditions().iter())
    {
        graph.get(*r)?;
    }
    let fail = || ValidationFailure::Internal("Path合成の値・条件・由来が現在の計算と違う".into());
    if let D::ConstructionLabel(s) = &v.data {
        return if s == &Scalar::Text("composition".into())
            && n.judgment.is_none()
            && n.evidence.is_empty()
        {
            Ok(())
        } else {
            Err(fail())
        };
    }
    let D::PathComposition(p) = &v.data else {
        return Err(fail());
    };
    match p {
        Part::Path {
            value,
            source,
            target,
            word,
            left,
            right,
            condition,
        } => {
            if Some(value) != w.value.as_ref()
                || (*source, *target, *left, *right) != (w.source, w.target, w.left, w.right)
                || word != &w.word
                || !matches!(
                    part(graph, *condition, w)?,
                    Part::Claim {
                        condition: None,
                        ..
                    }
                )
                || n.judgment.is_some()
                || !n.evidence.is_empty()
            {
                return Err(fail());
            }
        }
        Part::Claim {
            name,
            left,
            right,
            condition,
        } => {
            let label = cv(graph, *name)?;
            if (*left, *right) != (w.left, w.right)
                || !matches!(&label.witness,Witness::PathCompose(c) if c.as_ref()==w)
                || label.scalar() != Some(&Scalar::Text("composition".into()))
            {
                return Err(fail());
            }
            let mut reasons = vec![];
            let mut evidence = vec![];
            if w.value.is_some() {
                if condition.is_some() {
                    return Err(fail());
                }
            } else {
                let c = condition.ok_or_else(fail)?;
                if !matches!(part(graph, c, w)?, Part::Endpoints { .. }) {
                    return Err(fail());
                }
                reasons.push(failed(&w.request, c));
                evidence = graph.get(c)?.evidence.clone();
            }
            let status = if w.value.is_some() {
                Decision::Established
            } else {
                Decision::Refuted
            };
            if n.judgment
                != Some(Judgment {
                    status,
                    evidence: evidence.clone(),
                    reasons,
                })
                || n.evidence != evidence
            {
                return Err(fail());
            }
        }
        Part::Endpoints { left, right } => {
            if w.value.is_some()
                || (*left, *right) != (w.middle_left, w.middle_right)
                || graph.scalar(*left)? == graph.scalar(*right)?
            {
                return Err(fail());
            }
            let [e] = n.evidence.as_slice() else {
                return Err(fail());
            };
            if !matches!(part(graph,*e,w)?,Part::Evidence{left:a,right:b} if (a,b)==(left,right))
                || n.judgment
                    != Some(Judgment {
                        status: Decision::Refuted,
                        evidence: vec![*e],
                        reasons: vec![],
                    })
            {
                return Err(fail());
            }
        }
        Part::Evidence { left, right } => {
            if w.value.is_some()
                || (*left, *right) != (w.middle_left, w.middle_right)
                || n.judgment.is_some()
                || !n.evidence.is_empty()
            {
                return Err(fail());
            }
        }
    }
    Ok(())
}
pub(super) fn validate_answer(
    env: &Environment<'_>,
    graph: &Graph,
    r: &Request,
    a: &Answer,
    w: &PathWitness,
) -> Result<(), ValidationFailure> {
    validate_origin(env, graph, r, w)?;
    let claim = a.claim.ok_or("Path合成の命題がない")?;
    validate_node(graph, graph.get(claim)?, w)?;
    if !matches!(part(graph, claim, w)?, Part::Claim { .. }) {
        return Err("Path合成のclaimが違う".into());
    }
    let j = graph
        .get(claim)?
        .judgment
        .as_ref()
        .ok_or("Path合成の判断がない")?;
    let mut outputs = BTreeMap::from([("proposition".into(), claim)]);
    if w.value.is_some() {
        let path = *a.outputs.get("operation").ok_or("合成Pathがない")?;
        if !matches!(part(graph,path,w)?,Part::Path{condition,..} if *condition==claim) {
            return Err("Path出力の構成条件が違う".into());
        }
        outputs.insert("operation".into(), path);
    }
    let mut reasons = j.reasons.clone();
    if let Some(stop) = &w.stopped {
        reasons.push(Reason::stopped(&r.id, stop.clone()));
    }
    sort_reasons(&mut reasons);
    if a.id != r.id
        || a.outputs != outputs
        || a.status != j.status
        || a.evidence != j.evidence
        || a.reasons != reasons
        || a.scope != w.scope
    {
        return Err("Path合成回答が現在の元導出と違う".into());
    }
    Ok(())
}
fn reference(
    graph: &Graph,
    roots: &[NodeRef],
    value: &Scalar,
    control: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut pending = roots.to_vec();
    let mut seen = BTreeSet::new();
    while let Some(r) = pending.pop() {
        control.checkpoint(Checkpoint::FiniteIteration)?;
        if !seen.insert(r.0) {
            continue;
        }
        let n = graph.get(r)?;
        if n.ty == NodeType::Value(value.ty()) && graph.scalar(r).ok() == Some(value) {
            return Ok(r);
        }
        pending.extend(n.arguments.iter().copied());
    }
    Err("Path端点・生成元の既出Refがない".into())
}
fn put(
    graph: &mut Graph,
    w: &Arc<PathWitness>,
    data: D,
    evidence: Vec<NodeRef>,
    judgment: Option<Judgment>,
) -> Result<NodeRef, ValidationFailure> {
    native::retain(
        graph,
        ConstructionValue {
            witness: Witness::PathCompose(w.clone()),
            data,
        },
        vec![],
        evidence,
        judgment,
    )
}
fn node(
    graph: &mut Graph,
    w: &Arc<PathWitness>,
    p: Part,
    evidence: Vec<NodeRef>,
    judgment: Option<Judgment>,
) -> Result<NodeRef, ValidationFailure> {
    put(graph, w, D::PathComposition(p), evidence, judgment)
}
pub(super) fn evaluate(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    graph: &mut Graph,
    r: &Request,
    control: &mut Control,
) -> Result<Answer, ValidationFailure> {
    control.checkpoint(Checkpoint::FiniteIteration)?;
    env.commit_projection_conditions(graph, r)?;
    if let Some(a) = super::public_map::unavailable(env, graph, r)? {
        return Ok(a);
    }
    let left = selected(env, graph, r, "head")?;
    let right = selected(env, graph, r, "then")?;
    let (Scalar::Path(a), Scalar::Path(b)) = (graph.scalar(left)?, graph.scalar(right)?) else {
        return Err("composeの元実値がPath二つでない".into());
    };
    let source = reference(graph, &[left], &a.object(), control)?;
    let target = reference(graph, &[right], &b.target(), control)?;
    let middle_left = reference(graph, &[left], &a.target(), control)?;
    let middle_right = reference(graph, &[right], &b.object(), control)?;
    let mut word = vec![];
    for (path, root) in [(a, left), (b, right)] {
        if let Some(step) = &path.step {
            for generator in std::iter::once(&step.generator).chain(&step.word_tail) {
                word.push(reference(graph, &[root], generator, control)?);
            }
        }
    }
    let mut support = graph.get(left)?.support.clone();
    support.extend(graph.get(right)?.support.iter().cloned());
    support.sort();
    support.dedup();
    let mut scope = graph.get(left)?.scope.clone();
    scope.merge(&graph.get(right)?.scope);
    let (computed, stopped) =
        match super::path_compose::compose_retained(a, b, &a.reading, control, |_, _| {}) {
            Ok(c) => (c, None),
            Err(f) => {
                let Some(c) = f.partial else {
                    return Err(f.cause);
                };
                let ValidationFailure::Stop(stop) = f.cause else {
                    return Err(f.cause);
                };
                (c, Some(stop))
            }
        };
    let value = computed.value.map(|p| Scalar::Path(Box::new(p)));
    let w = Arc::new(PathWitness {
        inputs: prepared.shared_inputs(),
        request: r.clone(),
        support,
        scope,
        left,
        right,
        source,
        middle_left,
        middle_right,
        target,
        word,
        value,
        stopped,
    });
    let name = put(
        graph,
        &w,
        D::ConstructionLabel(Scalar::Text("composition".into())),
        vec![],
        None,
    )?;
    let mut evidence = vec![];
    let mut reasons = vec![];
    let condition = if w.value.is_none() {
        let e = node(
            graph,
            &w,
            Part::Evidence {
                left: middle_left,
                right: middle_right,
            },
            vec![],
            None,
        )?;
        evidence.push(e);
        let c = node(
            graph,
            &w,
            Part::Endpoints {
                left: middle_left,
                right: middle_right,
            },
            evidence.clone(),
            Some(Judgment {
                status: Decision::Refuted,
                evidence: evidence.clone(),
                reasons: vec![],
            }),
        )?;
        reasons.push(failed(r, c));
        Some(c)
    } else {
        None
    };
    let status = if w.value.is_some() {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let claim = node(
        graph,
        &w,
        Part::Claim {
            name,
            left,
            right,
            condition,
        },
        evidence.clone(),
        Some(Judgment {
            status,
            evidence: evidence.clone(),
            reasons: reasons.clone(),
        }),
    )?;
    let mut outputs = BTreeMap::from([("proposition".into(), claim)]);
    if let Some(value) = &w.value {
        let path = node(
            graph,
            &w,
            Part::Path {
                value: value.clone(),
                source,
                target,
                word: w.word.clone(),
                left,
                right,
                condition: claim,
            },
            vec![],
            None,
        )?;
        outputs.insert("operation".into(), path);
    }
    if let Some(stop) = &w.stopped {
        reasons.push(Reason::stopped(&r.id, stop.clone()));
    }
    sort_reasons(&mut reasons);
    Ok(Answer {
        id: r.id.clone(),
        status,
        claim: Some(claim),
        outputs,
        evidence,
        reasons,
        scope: w.scope.clone(),
    })
}
