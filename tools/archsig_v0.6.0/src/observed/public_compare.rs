//! 検査済みOperation/Pathの語・全域作用比較を型付きの元Refへ接続する。
use super::{
    construction_result::{
        self as native, ConstructionData as D, ConstructionType as T, ConstructionValue, Witness,
    },
    control::{Checkpoint, Control, StopReason},
    environment::{AnswerBinding, Environment},
    input::CheckedInputs,
    projection::ProjectionType,
    request::{QuestionKind, Request, Selector},
    result::*,
    PreparedObserved,
};
use crate::canonical::Json;
use std::{collections::BTreeMap, sync::Arc};
#[derive(Clone, Debug)]
pub(crate) struct CompareWitness {
    pub(super) inputs: Arc<CheckedInputs>,
    pub(super) request: Request,
    pub(super) support: Vec<Fact>,
    pub(super) scope: Scope,
    left: NodeRef,
    right: NodeRef,
    kind: String,
    equal: Option<bool>,
    incompatible: Option<(NodeRef, NodeRef)>,
    facts: Vec<Fact>,
    stopped: Option<StopReason>,
}
impl PartialEq for CompareWitness {
    fn eq(&self, b: &Self) -> bool {
        self.inputs.sources() == b.inputs.sources()
            && self.request == b.request
            && self.support == b.support
            && self.scope == b.scope
            && (self.left, self.right) == (b.left, b.right)
            && self.kind == b.kind
            && self.equal == b.equal
            && self.incompatible == b.incompatible
            && self.facts == b.facts
            && self.stopped == b.stopped
    }
}
impl Eq for CompareWitness {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Part {
    Comparison {
        kind: String,
        left: NodeRef,
        right: NodeRef,
    },
    Claim {
        left: NodeRef,
        right: NodeRef,
        comparison: Option<NodeRef>,
        name: Option<NodeRef>,
        condition: Option<NodeRef>,
    },
    Endpoints {
        left: NodeRef,
        right: NodeRef,
    },
    Evidence {
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
    },
}
fn refs(v: &[NodeRef]) -> Json {
    Json::Arr(v.iter().map(|r| r.wire()).collect())
}
impl Part {
    pub fn scalar(&self) -> Option<&Scalar> {
        None
    }
    pub fn ty(&self) -> NodeType {
        match self {
            Self::Comparison { .. } => NodeType::Construction(T::Comparison),
            Self::Evidence { .. } => NodeType::Evidence,
            _ => NodeType::Proposition,
        }
    }
    pub fn construction(&self) -> &'static str {
        match self {
            Self::Comparison { .. } => "comparison",
            Self::Evidence { .. } => "evidence",
            _ => "proposition",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Claim {
                left,
                right,
                comparison,
                name,
                condition,
            } => [*left, *right]
                .into_iter()
                .chain(comparison.iter().copied())
                .chain(name.iter().copied())
                .chain(condition.iter().copied())
                .collect(),
            Self::Comparison { left, right, .. }
            | Self::Endpoints { left, right }
            | Self::Evidence { left, right, .. } => vec![*left, *right],
        }
    }
    pub fn conditions(&self) -> Vec<NodeRef> {
        match self {
            Self::Claim { condition, .. } => condition.iter().copied().collect(),
            _ => vec![],
        }
    }
    pub fn projection_type(&self) -> Option<ProjectionType> {
        if matches!(self, Self::Comparison { .. }) {
            Some(ProjectionType::Comparison)
        } else {
            None
        }
    }
    pub fn project(&self, _: &[super::projection::ProjectionStep]) -> Option<(NodeRef, usize)> {
        None
    }
    pub fn wire(&self, w: &CompareWitness) -> Json {
        match self {
            Self::Comparison { kind, left, right } => Json::obj([
                ("kind", Json::str(kind)),
                ("left", left.wire()),
                ("right", right.wire()),
            ]),
            Self::Claim {
                left, right, name, ..
            } => Json::obj([
                (
                    "predicate",
                    Json::str(if name.is_some() {
                        "constructible"
                    } else if w.kind == "word" {
                        "word_equal"
                    } else {
                        "action_equal"
                    }),
                ),
                (
                    "operands",
                    refs(
                        &name
                            .iter()
                            .copied()
                            .chain([*left, *right])
                            .collect::<Vec<_>>(),
                    ),
                ),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Endpoints { left, right } => Json::obj([
                ("predicate", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Evidence { left, right, facts } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        ("bindings", Json::Arr(vec![])),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
        }
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
            .ok_or_else(|| "比較のtoがない".into())
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
        AnswerBinding::Inapplicable(_) => Err("比較へ不適合な射影を渡した".into()),
    }
}
fn origin_ref(
    env: &Environment<'_>,
    graph: &Graph,
    s: &Selector,
    r: NodeRef,
) -> Result<bool, ValidationFailure> {
    Ok(match env.answer_binding(graph, s, (0, 0))? {
        AnswerBinding::Reference(a) => a == r,
        AnswerBinding::Projection(n) => graph.get(r)? == &n,
        AnswerBinding::Inapplicable(_) => false,
    })
}
fn value(graph: &Graph, r: NodeRef) -> Result<&ConstructionValue, ValidationFailure> {
    match &graph.get(r)?.payload {
        Some(Payload::Construction(v)) => Ok(v),
        _ => Err("比較のnative値がない".into()),
    }
}
fn part<'a>(
    graph: &'a Graph,
    r: NodeRef,
    w: &CompareWitness,
) -> Result<&'a Part, ValidationFailure> {
    let v = value(graph, r)?;
    if !matches!(&v.witness,Witness::Compare(c) if c.as_ref()==w) {
        return Err("比較の元検査が違う".into());
    }
    match &v.data {
        D::Comparison(p) => Ok(p),
        _ => Err("比較の型付き値でない".into()),
    }
}
fn failed(r: &Request, c: NodeRef) -> Reason {
    Reason {
        kind: ReasonKind::ConditionFailed {
            condition: c,
            construction: "comparison",
        },
        request: r.id.clone(),
        dependencies: vec![c],
        missing: vec![],
        location: None,
    }
}
pub(super) fn validate_origin(
    env: &Environment<'_>,
    graph: &Graph,
    r: &Request,
    w: &CompareWitness,
) -> Result<(), ValidationFailure> {
    if r.kind != QuestionKind::Compare
        || r != &w.request
        || env.inputs.sources() != w.inputs.sources()
        || !origin_ref(env, graph, selector(r, "head")?, w.left)?
        || !origin_ref(env, graph, selector(r, "to")?, w.right)?
    {
        return Err("比較が現在の三入力・要求・元Refと違う".into());
    }
    Ok(())
}
pub(super) fn validate_node(
    graph: &Graph,
    n: &Node,
    w: &CompareWitness,
) -> Result<(), ValidationFailure> {
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("比較のpayloadがない".into());
    };
    if n.ty != v.ty()
        || n.rule != v.rule()
        || n.arguments != v.arguments()
        || n.support != w.support
        || n.scope != w.scope
        || !n.reasons.is_empty()
    {
        return Err("比較の型・規則・支持・Scopeが違う".into());
    }
    for r in n
        .arguments
        .iter()
        .chain(&n.evidence)
        .chain(n.conditions().iter())
    {
        graph.get(*r)?;
    }
    let fail = || ValidationFailure::Internal("比較の値・条件・由来が現在の計算と違う".into());
    if let D::ConstructionLabel(s) = &v.data {
        return if w.incompatible.is_some()
            && s == &Scalar::Text("comparison".into())
            && n.judgment.is_none()
            && n.evidence.is_empty()
        {
            Ok(())
        } else {
            Err(fail())
        };
    }
    let D::Comparison(p) = &v.data else {
        return Err(fail());
    };
    match p {
        Part::Comparison { kind, left, right } => {
            if w.equal.is_none()
                || kind != &w.kind
                || (*left, *right) != (w.left, w.right)
                || n.judgment.is_some()
                || !n.evidence.is_empty()
            {
                return Err(fail());
            }
        }
        Part::Evidence { left, right, facts } => {
            let pair = w.incompatible.unwrap_or((w.left, w.right));
            if w.equal == Some(true)
                || (*left, *right) != pair
                || facts != &w.facts
                || (w.equal == Some(false) && w.kind == "action" && facts.len() != 3)
                || n.judgment.is_some()
                || !n.evidence.is_empty()
            {
                return Err(fail());
            }
        }
        Part::Endpoints { left, right } => {
            if w.incompatible != Some((*left, *right)) || w.equal.is_some() {
                return Err(fail());
            }
            let [e] = n.evidence.as_slice() else {
                return Err(fail());
            };
            if !matches!(part(graph,*e,w)?,Part::Evidence{left:a,right:b,facts} if (a,b)==(left,right)&&facts.is_empty())
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
        Part::Claim {
            left,
            right,
            comparison,
            name,
            condition,
        } => {
            if (*left, *right) != (w.left, w.right) {
                return Err(fail());
            }
            let mut reasons = vec![];
            let evidence = if w.equal == Some(true) {
                vec![]
            } else {
                n.evidence.clone()
            };
            if w.equal.is_some() {
                let c = comparison.ok_or_else(fail)?;
                if name.is_some()
                    || condition.is_some()
                    || !matches!(part(graph, c, w)?, Part::Comparison { .. })
                {
                    return Err(fail());
                }
            } else {
                let c = condition.ok_or_else(fail)?;
                let name = name.ok_or_else(fail)?;
                let label = value(graph, name)?;
                if comparison.is_some()
                    || !matches!(&label.witness,Witness::Compare(c) if c.as_ref()==w)
                    || label.scalar() != Some(&Scalar::Text("comparison".into()))
                    || !matches!(part(graph, c, w)?, Part::Endpoints { .. })
                    || n.evidence != graph.get(c)?.evidence
                {
                    return Err(fail());
                }
                reasons.push(failed(&w.request, c));
            }
            if w.equal != Some(true) {
                let [e] = n.evidence.as_slice() else {
                    return Err(fail());
                };
                if !matches!(part(graph, *e, w)?, Part::Evidence { .. }) {
                    return Err(fail());
                }
            }
            if n.evidence != evidence
                || n.judgment
                    != Some(Judgment {
                        status: if w.equal == Some(true) {
                            Decision::Established
                        } else {
                            Decision::Refuted
                        },
                        evidence,
                        reasons,
                    })
            {
                return Err(fail());
            }
        }
    }
    Ok(())
}
pub(super) fn validate_failure(graph: &Graph, r: &Reason) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction: "comparison",
    } = r.kind
    else {
        return Err("比較の条件理由でない".into());
    };
    let v = value(graph, condition)?;
    let Witness::Compare(w) = &v.witness else {
        return Err("比較の元検査がない".into());
    };
    if w.incompatible.is_none()
        || r != &failed(&w.request, condition)
        || !matches!(part(graph, condition, w)?, Part::Endpoints { .. })
    {
        return Err("比較の反証理由が違う".into());
    }
    validate_node(graph, graph.get(condition)?, w)
}
pub(super) fn validate_answer(
    env: &Environment<'_>,
    graph: &Graph,
    r: &Request,
    a: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = super::public_map::unavailable(env, graph, r)? {
        if a != &expected {
            return Err("比較の依存停止回答が違う".into());
        }
        return Ok(());
    }
    let claim = a.claim.ok_or("比較命題がない")?;
    let v = value(graph, claim)?;
    let Witness::Compare(w) = &v.witness else {
        return Err("比較の元検査がない".into());
    };
    validate_origin(env, graph, r, w)?;
    validate_node(graph, graph.get(claim)?, w)?;
    let Part::Claim { comparison, .. } = part(graph, claim, w)? else {
        return Err("比較のclaimが違う".into());
    };
    let j = graph
        .get(claim)?
        .judgment
        .as_ref()
        .ok_or("比較の判断がない")?;
    let mut outputs = BTreeMap::from([("proposition".into(), claim)]);
    if let Some(c) = comparison {
        outputs.insert("comparison".into(), *c);
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
        return Err("比較回答が元導出と違う".into());
    }
    Ok(())
}
fn put(
    graph: &mut Graph,
    w: &Arc<CompareWitness>,
    data: D,
    evidence: Vec<NodeRef>,
    judgment: Option<Judgment>,
) -> Result<NodeRef, ValidationFailure> {
    native::retain(
        graph,
        ConstructionValue {
            witness: Witness::Compare(w.clone()),
            data,
        },
        vec![],
        evidence,
        judgment,
    )
}
fn node(
    graph: &mut Graph,
    w: &Arc<CompareWitness>,
    p: Part,
    evidence: Vec<NodeRef>,
    judgment: Option<Judgment>,
) -> Result<NodeRef, ValidationFailure> {
    put(graph, w, D::Comparison(p), evidence, judgment)
}
fn words(
    p: &super::path_value::PathValue,
    control: &mut Control,
) -> Result<Vec<Scalar>, ValidationFailure> {
    let mut out = vec![];
    if let Some(step) = &p.step {
        for s in std::iter::once(&step.generator).chain(&step.word_tail) {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            out.push(s.clone());
        }
    }
    Ok(out)
}
fn path_difference(
    a: &super::path_value::PathValue,
    b: &super::path_value::PathValue,
    control: &mut Control,
) -> Result<Option<Vec<Fact>>, ValidationFailure> {
    let Some(step) = a.step.as_ref().or(b.step.as_ref()) else {
        return Ok(None);
    };
    if let (Some(a), Some(b)) = (&a.step, &b.step) {
        if a.carrier.len() != b.carrier.len() {
            return Err("Path比較の共通carrierの件数が違う".into());
        }
        for (x, y) in a.carrier.iter().zip(&b.carrier) {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            if x != y {
                return Err("Path比較の共通carrierが違う".into());
            }
        }
    }
    for (i, fact) in step.carrier.iter().enumerate() {
        control.checkpoint(Checkpoint::FiniteIteration)?;
        let left = match &a.step {
            Some(s) => s.images.get(i).ok_or("左作用の像がない")?,
            None => fact,
        };
        let right = match &b.step {
            Some(s) => s.images.get(i).ok_or("右作用の像がない")?,
            None => fact,
        };
        if left != right {
            return Ok(Some(vec![fact.clone(), left.clone(), right.clone()]));
        }
    }
    Ok(None)
}
fn completed_operation<T>(
    outcome: Result<T, crate::construction::ConstructionFailure>,
    retained: Option<T>,
    stopped: &mut Option<StopReason>,
) -> Result<T, ValidationFailure> {
    match outcome {
        Ok(v) => Ok(v),
        Err(crate::construction::ConstructionFailure::Stopped(s)) => match retained {
            Some(v) => {
                *stopped = Some(s);
                Ok(v)
            }
            None => Err(ValidationFailure::Stop(s)),
        },
        Err(other) => Err(ValidationFailure::Internal(format!(
            "Operation比較: {other:?}"
        ))),
    }
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
    let right = selected(env, graph, r, "to")?;
    let kind = super::request::comparison::kind(r)
        .map_err(|e| ValidationFailure::Internal(format!("比較kind: {e:?}")))?
        .to_owned();
    let mut support = graph.get(left)?.support.clone();
    support.extend(graph.get(right)?.support.iter().cloned());
    support.sort();
    support.dedup();
    let mut scope = graph.get(left)?.scope.clone();
    scope.merge(&graph.get(right)?.scope);
    let mut incompatible = None;
    let mut facts = vec![];
    let mut stopped = None;
    let equal = if let Ok(Scalar::Path(a)) = graph.scalar(left) {
        let Scalar::Path(b) = graph.scalar(right)? else {
            return Err("Path比較へ別型を渡した".into());
        };
        a.check(control)?;
        b.check(control)?;
        if kind == "action" && (a.object() != b.object() || a.target() != b.target()) {
            let (x, y) = if a.object() != b.object() {
                (a.object(), b.object())
            } else {
                (a.target(), b.target())
            };
            incompatible = Some((
                super::public_path_compose::reference(graph, &[left], &x, control)?,
                super::public_path_compose::reference(graph, &[right], &y, control)?,
            ));
            None
        } else if kind == "word" {
            let a = words(a, control)?;
            let b = words(b, control)?;
            let mut same = a.len() == b.len();
            if same {
                for (x, y) in a.iter().zip(&b) {
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                    if x != y {
                        same = false;
                        break;
                    }
                }
            }
            Some(same)
        } else {
            let difference = path_difference(a, b, control)?;
            let equal = difference.is_none();
            if let Some(f) = difference {
                facts = f;
            }
            Some(equal)
        }
    } else {
        let a = super::public_compose::op(graph, left)?;
        let b = super::public_compose::op(graph, right)?;
        if kind == "action" && (a.source() != b.source() || a.target() != b.target()) {
            let (asource, atarget, _, _) = super::public_compose::components(graph, left)?;
            let (bsource, btarget, _, _) = super::public_compose::components(graph, right)?;
            incompatible = Some(if a.source() != b.source() {
                (asource, bsource)
            } else {
                (atarget, btarget)
            });
            None
        } else if kind == "word" {
            let mut retained = None;
            let outcome =
                a.word_equal_retained(prepared.inputs(), b, control, |v| retained = Some(v));
            Some(completed_operation(outcome, retained, &mut stopped)?)
        } else {
            let mut retained = None;
            let outcome = a.action_difference_retained(prepared.inputs(), b, control, |v| {
                retained = Some(v.cloned())
            });
            let difference = completed_operation(outcome, retained, &mut stopped)?;
            if let Some(d) = &difference {
                facts = vec![d.fact().clone(), d.left().clone(), d.right().clone()];
            }
            Some(difference.is_none())
        }
    };
    if stopped.is_none() {
        if let Err(s) = control.checkpoint(Checkpoint::FiniteIteration) {
            stopped = Some(s);
        }
    }
    let w = Arc::new(CompareWitness {
        inputs: prepared.shared_inputs(),
        request: r.clone(),
        support,
        scope,
        left,
        right,
        kind,
        equal,
        incompatible,
        facts,
        stopped,
    });
    let mut evidence = vec![];
    let mut reasons = vec![];
    let mut name = None;
    let mut condition = None;
    if let Some((a, b)) = w.incompatible {
        name = Some(put(
            graph,
            &w,
            D::ConstructionLabel(Scalar::Text("comparison".into())),
            vec![],
            None,
        )?);
        let e = node(
            graph,
            &w,
            Part::Evidence {
                left: a,
                right: b,
                facts: vec![],
            },
            vec![],
            None,
        )?;
        evidence.push(e);
        let c = node(
            graph,
            &w,
            Part::Endpoints { left: a, right: b },
            evidence.clone(),
            Some(Judgment {
                status: Decision::Refuted,
                evidence: evidence.clone(),
                reasons: vec![],
            }),
        )?;
        reasons.push(failed(r, c));
        condition = Some(c);
    } else if w.equal == Some(false) {
        let e = node(
            graph,
            &w,
            Part::Evidence {
                left,
                right,
                facts: w.facts.clone(),
            },
            vec![],
            None,
        )?;
        evidence.push(e);
    }
    let comparison = if w.equal.is_some() {
        Some(node(
            graph,
            &w,
            Part::Comparison {
                kind: w.kind.clone(),
                left,
                right,
            },
            vec![],
            None,
        )?)
    } else {
        None
    };
    let status = if w.equal == Some(true) {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let claim = node(
        graph,
        &w,
        Part::Claim {
            left,
            right,
            comparison,
            name,
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
    if let Some(c) = comparison {
        outputs.insert("comparison".into(), c);
    }
    if let Some(s) = &w.stopped {
        reasons.push(Reason::stopped(&r.id, s.clone()));
    }
    sort_reasons(&mut reasons);
    Ok(Answer {
        id: r.id.clone(),
        status,
        outputs,
        claim: Some(claim),
        evidence,
        reasons,
        scope: w.scope.clone(),
    })
}
