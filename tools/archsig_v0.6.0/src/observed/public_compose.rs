//! 現在入力で検査済みのOperationを合成し、元参照を保ったDAGへ転記する。
use super::{
    PreparedObserved,
    construction_result::{
        self as native, ConstructionData as D, ConstructionType as T, ConstructionValue, Witness,
    },
    control::{Checkpoint, Control, StopReason},
    environment::{AnswerBinding, Environment},
    input::CheckedInputs,
    projection::{OperationProjection, ProjectionStep as P, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{
    canonical::Json,
    construction::{ConstructionFailure, maps::ConfigurationOperation},
};
use std::{collections::BTreeMap, sync::Arc};
#[derive(Clone, Debug)]
pub(crate) struct ComposeWitness {
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
    universe: NodeRef,
    word: Vec<NodeRef>,
    shape: OperationProjection,
    operation: Option<ConfigurationOperation>,
    stopped: Option<StopReason>,
}
impl PartialEq for ComposeWitness {
    fn eq(&self, b: &Self) -> bool {
        self.inputs.sources() == b.inputs.sources()
            && self.request == b.request
            && self.support == b.support
            && self.scope == b.scope
            && self.left == b.left
            && self.right == b.right
            && self.source == b.source
            && self.middle_left == b.middle_left
            && self.middle_right == b.middle_right
            && self.target == b.target
            && self.universe == b.universe
            && self.word == b.word
            && self.shape == b.shape
            && self.operation == b.operation
            && self.stopped == b.stopped
    }
}
impl Eq for ComposeWitness {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Part {
    Action {
        universe: NodeRef,
        images: Vec<Fact>,
    },
    Candidate {
        source: NodeRef,
        target: NodeRef,
        action: NodeRef,
        left: NodeRef,
        right: NodeRef,
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
    Preservation {
        candidate: NodeRef,
        composition: NodeRef,
    },
    Map {
        candidate: NodeRef,
        preservation: NodeRef,
    },
    Operation {
        source: NodeRef,
        target: NodeRef,
        candidate: NodeRef,
        map: NodeRef,
        action: NodeRef,
        preservation: NodeRef,
        left: NodeRef,
        right: NodeRef,
        word: Vec<NodeRef>,
    },
}
fn refs(r: &[NodeRef]) -> Json {
    Json::Arr(r.iter().map(|r| r.wire()).collect())
}
impl Part {
    pub fn ty(&self) -> NodeType {
        match self {
            Self::Action { .. } => NodeType::Construction(T::AtomMap),
            Self::Candidate { .. } => NodeType::Construction(T::MapCandidate),
            Self::Claim { .. } | Self::Endpoints { .. } | Self::Preservation { .. } => {
                NodeType::Proposition
            }
            Self::Evidence { .. } => NodeType::Evidence,
            Self::Map { .. } => NodeType::Construction(T::ConfigurationMap),
            Self::Operation { .. } => NodeType::Construction(T::Operation),
        }
    }
    pub fn construction(&self) -> &'static str {
        match self {
            Self::Action { .. } => "atom_map",
            Self::Candidate { .. } => "map_candidate",
            Self::Claim { .. } | Self::Endpoints { .. } | Self::Preservation { .. } => {
                "proposition"
            }
            Self::Evidence { .. } => "evidence",
            Self::Map { .. } => "configuration_map",
            Self::Operation { .. } => "operation",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Action { universe, .. } => vec![*universe],
            Self::Candidate {
                source,
                target,
                action,
                left,
                right,
            } => vec![*left, *right, *source, *target, *action],
            Self::Claim {
                name,
                left,
                right,
                condition,
            } => [*name, *left, *right]
                .into_iter()
                .chain(condition.iter().copied())
                .collect(),
            Self::Endpoints { left, right } => vec![*left, *right],
            Self::Evidence { left, right } => vec![*left, *right],
            Self::Preservation {
                candidate,
                composition,
            } => vec![*candidate, *composition],
            Self::Map { candidate, .. } => vec![*candidate],
            Self::Operation {
                source,
                target,
                candidate,
                map,
                action,
                left,
                right,
                word,
                ..
            } => [*left, *right, *source, *target, *candidate, *map, *action]
                .into_iter()
                .chain(word.iter().copied())
                .collect(),
        }
    }
    pub fn conditions(&self) -> Vec<NodeRef> {
        match self {
            Self::Claim { condition, .. } => condition.iter().copied().collect(),
            Self::Map { preservation, .. } | Self::Operation { preservation, .. } => {
                vec![*preservation]
            }
            Self::Preservation { composition, .. } => vec![*composition],
            _ => vec![],
        }
    }
    pub fn projection_type(&self, c: &ComposeWitness) -> Option<ProjectionType> {
        match self {
            Self::Action { .. } => Some(ProjectionType::AtomMap),
            Self::Candidate { .. } => Some(ProjectionType::ComposedCandidate(c.shape.clone())),
            Self::Map { .. } => Some(ProjectionType::ComposedMap(c.shape.clone())),
            Self::Operation { .. } => Some(ProjectionType::ComposedOperation(c.shape.clone())),
            _ => None,
        }
    }
    pub fn project(&self, path: &[P]) -> Option<(NodeRef, usize)> {
        let P::Field(f) = path.first()? else {
            return None;
        };
        let r = match (self, f.as_str()) {
            (Self::Candidate { source, .. } | Self::Operation { source, .. }, "source") => *source,
            (Self::Candidate { target, .. } | Self::Operation { target, .. }, "target") => *target,
            (Self::Candidate { action, .. } | Self::Operation { action, .. }, "action") => *action,
            (Self::Map { candidate, .. } | Self::Operation { candidate, .. }, "candidate") => {
                *candidate
            }
            (Self::Operation { map, .. }, "configuration_map") => *map,
            (Self::Operation { word, .. }, "word") => {
                let P::Index(i) = path.get(1)? else {
                    return None;
                };
                return Some((*word.get(usize::try_from(*i).ok()?)?, 2));
            }
            _ => return None,
        };
        Some((r, 1))
    }
    pub fn wire(&self) -> Json {
        match self {
            Self::Action { universe, images } => Json::obj([
                ("universe", universe.wire()),
                ("images", Json::Arr(images.iter().map(Fact::wire).collect())),
            ]),
            Self::Candidate {
                source,
                target,
                action,
                ..
            } => Json::obj([
                ("source", source.wire()),
                ("target", target.wire()),
                ("action", action.wire()),
            ]),
            Self::Endpoints { left, right } => Json::obj([
                ("predicate", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Claim {
                name, left, right, ..
            } => Json::obj([
                ("predicate", Json::str("constructible")),
                ("operands", refs(&[*name, *left, *right])),
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
                        ("facts", Json::Arr(vec![])),
                    ]),
                ),
            ]),
            Self::Preservation { candidate, .. } => Json::obj([
                ("predicate", Json::str("configuration_preserved")),
                ("operands", refs(&[*candidate])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Map { candidate, .. } => Json::obj([("candidate", candidate.wire())]),
            Self::Operation {
                source,
                target,
                candidate,
                map,
                action,
                left,
                right,
                word,
                ..
            } => Json::obj([
                ("source", source.wire()),
                ("target", target.wire()),
                ("candidate", candidate.wire()),
                ("configuration_map", map.wire()),
                ("action", action.wire()),
                (
                    "name",
                    Json::obj([
                        ("kind", Json::str("word")),
                        ("generators", refs(&[*left, *right])),
                    ]),
                ),
                ("word", refs(word)),
            ]),
        }
    }
}
fn value(graph: &Graph, r: NodeRef) -> Result<&ConstructionValue, ValidationFailure> {
    match &graph.get(r)?.payload {
        Some(Payload::Construction(v)) => Ok(v),
        _ => Err("合成の元値がnative構成でない".into()),
    }
}
fn op(graph: &Graph, r: NodeRef) -> Result<&ConfigurationOperation, ValidationFailure> {
    let v = value(graph, r)?;
    match (&v.data, &v.witness) {
        (D::Operation { .. }, Witness::Map(m)) => {
            m.operation().ok_or("元mapのOperationがない".into())
        }
        (D::Composition(Part::Operation { .. }), Witness::Compose(c)) => {
            c.operation.as_ref().ok_or("元合成のOperationがない".into())
        }
        _ => Err("未確認候補・PathをOperationへ昇格した".into()),
    }
}
fn components(
    graph: &Graph,
    r: NodeRef,
) -> Result<(NodeRef, NodeRef, NodeRef, Vec<NodeRef>), ValidationFailure> {
    match &value(graph, r)?.data {
        D::Operation {
            source,
            target,
            action,
            subject,
            ..
        } => Ok((*source, *target, *action, vec![*subject])),
        D::Composition(Part::Operation {
            source,
            target,
            action,
            word,
            ..
        }) => Ok((*source, *target, *action, word.clone())),
        _ => Err("Operationの実体がない".into()),
    }
}
fn universe(graph: &Graph, r: NodeRef) -> Result<NodeRef, ValidationFailure> {
    match &value(graph, r)?.data {
        D::AtomMap { universe, .. } | D::Composition(Part::Action { universe, .. }) => {
            Ok(*universe)
        }
        _ => Err("総作用の元Uがない".into()),
    }
}
fn selector<'a>(request: &'a Request, key: &str) -> Result<&'a Selector, ValidationFailure> {
    if key == "head" {
        return Ok(&request.head);
    }
    request
        .arguments
        .iter()
        .find(|a| a.name == key)
        .map(|a| &a.value)
        .ok_or("合成の固定引数がない".into())
}
fn selected(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    key: &str,
) -> Result<NodeRef, ValidationFailure> {
    match environment.answer_binding(graph, selector(request, key)?, (0, 0))? {
        AnswerBinding::Reference(r) => Ok(r),
        _ => Err("composeのHandleが確認済みOperationでない".into()),
    }
}
pub(super) fn validate_origin(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    c: &ComposeWitness,
) -> Result<(), ValidationFailure> {
    if request.kind != QuestionKind::Compose
        || &c.request != request
        || c.inputs.sources() != environment.inputs.sources()
        || selected(environment, graph, request, "head")? != c.left
        || selected(environment, graph, request, "then")? != c.right
    {
        return Err("合成の現在入力・元要求・元Operationが違う".into());
    }
    Ok(())
}
fn part<'a>(
    graph: &'a Graph,
    r: NodeRef,
    c: &ComposeWitness,
) -> Result<&'a Part, ValidationFailure> {
    let v = value(graph, r)?;
    if !matches!(&v.witness,Witness::Compose(actual) if actual.as_ref()==c) {
        return Err("合成の由来が別の要求・操作である".into());
    }
    let D::Composition(p) = &v.data else {
        return Err("合成の型付き部分がない".into());
    };
    Ok(p)
}
fn established(node: &Node) -> bool {
    node.judgment
        == Some(Judgment {
            status: Decision::Established,
            evidence: vec![],
            reasons: vec![],
        })
        && node.evidence.is_empty()
}
pub(super) fn validate_node(
    graph: &Graph,
    node: &Node,
    c: &ComposeWitness,
) -> Result<(), ValidationFailure> {
    let Some(Payload::Construction(v)) = &node.payload else {
        return Err("合成payloadがない".into());
    };
    if node.ty != v.ty()
        || node.rule != v.rule()
        || node.arguments != v.arguments()
        || node.support != c.support
        || node.scope != c.scope
        || !node.reasons.is_empty()
    {
        return Err("合成の型・規則・引数・支持・Scope・理由が違う".into());
    }
    for r in node
        .arguments
        .iter()
        .chain(&node.evidence)
        .chain(node.conditions().iter())
    {
        graph.get(*r)?;
    }
    let fail =
        || ValidationFailure::Internal("合成の値・由来・保存条件が現在の検査結果と違う".into());
    if let D::ConstructionLabel(label) = &v.data {
        return if label == &Scalar::Text("composition".into())
            && node.judgment.is_none()
            && node.evidence.is_empty()
        {
            Ok(())
        } else {
            Err(fail())
        };
    }
    let D::Composition(p) = &v.data else {
        return Err(fail());
    };
    if !matches!(
        p,
        Part::Claim { .. } | Part::Endpoints { .. } | Part::Preservation { .. }
    ) && (node.judgment.is_some() || !node.evidence.is_empty())
    {
        return Err(fail());
    }
    match p {
        Part::Action { universe, images } => {
            let result = c.operation.as_ref().ok_or_else(fail)?;
            if *universe != c.universe || images != result.map().candidate().images() {
                return Err(fail());
            }
        }
        Part::Candidate {
            source,
            target,
            action,
            left,
            right,
        } => {
            if c.operation.is_none()
                || (*source, *target, *left, *right) != (c.source, c.target, c.left, c.right)
                || !matches!(part(graph, *action, c)?, Part::Action { .. })
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
            if (*left, *right) != (c.left, c.right)
                || graph.scalar(*name)? != &Scalar::Text("composition".into())
            {
                return Err(fail());
            }
            let label = value(graph, *name)?;
            if !matches!(&label.witness,Witness::Compose(actual) if actual.as_ref()==c) {
                return Err(fail());
            }
            let expected = if c.operation.is_some() {
                Decision::Established
            } else {
                Decision::Refuted
            };
            if node.judgment.as_ref().is_none_or(|j| {
                j.status != expected
                    || j.evidence != node.evidence
                    || j.reasons
                        != condition
                            .map(|r| vec![failed_reason(&c.request, r)])
                            .unwrap_or_default()
            }) {
                return Err(fail());
            }
            if expected == Decision::Refuted {
                let endpoint = condition.ok_or_else(fail)?;
                if !matches!(part(graph, endpoint, c)?, Part::Endpoints { .. })
                    || graph.get(endpoint)?.evidence != node.evidence
                {
                    return Err(fail());
                }
                if node.evidence.len() != 1
                    || !matches!(part(graph, node.evidence[0], c)?, Part::Evidence { .. })
                {
                    return Err(fail());
                }
            } else if condition.is_some() || !node.evidence.is_empty() {
                return Err(fail());
            }
        }
        Part::Endpoints { left, right } => {
            if c.operation.is_some()
                || (*left, *right) != (c.middle_left, c.middle_right)
                || node.evidence.len() != 1
                || !matches!(part(graph, node.evidence[0], c)?, Part::Evidence { .. })
                || node.judgment
                    != Some(Judgment {
                        status: Decision::Refuted,
                        evidence: node.evidence.clone(),
                        reasons: vec![],
                    })
            {
                return Err(fail());
            }
        }
        Part::Evidence { left, right } => {
            if c.operation.is_some()
                || (*left, *right) != (c.middle_left, c.middle_right)
                || op(graph, c.left)?.target() == op(graph, c.right)?.source()
            {
                return Err(fail());
            }
        }
        Part::Preservation {
            candidate,
            composition,
        } => {
            if !matches!(part(graph, *candidate, c)?, Part::Candidate { .. })
                || !matches!(part(graph, *composition, c)?, Part::Claim { .. })
                || !established(graph.get(*composition)?)
                || !established(node)
            {
                return Err(fail());
            }
        }
        Part::Map {
            candidate,
            preservation,
        } => {
            if !matches!(part(graph,*preservation,c)?,Part::Preservation{candidate:r,..} if r==candidate)
                || !established(graph.get(*preservation)?)
            {
                return Err(fail());
            }
        }
        Part::Operation {
            source,
            target,
            candidate,
            map,
            action,
            preservation,
            left,
            right,
            word,
        } => {
            if c.operation.is_none()
                || (*source, *target, *left, *right) != (c.source, c.target, c.left, c.right)
                || word != &c.word
                || !matches!(part(graph,*map,c)?,Part::Map{candidate:r,preservation:p} if r==candidate&&p==preservation)
                || !matches!(part(graph,*candidate,c)?,Part::Candidate{source:s,target:t,action:a,..} if s==source&&t==target&&a==action)
            {
                return Err(fail());
            }
        }
    }
    Ok(())
}
fn put(
    graph: &mut Graph,
    c: &Arc<ComposeWitness>,
    data: D,
    evidence: Vec<NodeRef>,
    judgment: Option<Judgment>,
) -> Result<NodeRef, ValidationFailure> {
    native::retain(
        graph,
        ConstructionValue {
            witness: Witness::Compose(c.clone()),
            data,
        },
        vec![],
        evidence,
        judgment,
    )
}
fn add(graph: &mut Graph, c: &Arc<ComposeWitness>, p: Part) -> Result<NodeRef, ValidationFailure> {
    put(graph, c, D::Composition(p), vec![], None)
}
fn claim(
    graph: &mut Graph,
    c: &Arc<ComposeWitness>,
    p: Part,
    status: Decision,
    evidence: Vec<NodeRef>,
) -> Result<NodeRef, ValidationFailure> {
    let reasons = match &p {
        Part::Claim {
            condition: Some(r), ..
        } => vec![failed_reason(&c.request, *r)],
        _ => vec![],
    };
    put(
        graph,
        c,
        D::Composition(p),
        evidence.clone(),
        Some(Judgment {
            status,
            evidence,
            reasons,
        }),
    )
}
fn failed_reason(request: &Request, condition: NodeRef) -> Reason {
    Reason {
        kind: ReasonKind::ConditionFailed {
            condition,
            construction: "composition",
        },
        request: request.id.clone(),
        dependencies: vec![condition],
        missing: vec![],
        location: None,
    }
}
pub(super) fn validate_failure(graph: &Graph, reason: &Reason) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction: "composition",
    } = reason.kind
    else {
        return Err("合成条件の理由でない".into());
    };
    let v = value(graph, condition)?;
    let Witness::Compose(c) = &v.witness else {
        return Err("合成の元証拠がない".into());
    };
    if c.operation.is_some()
        || c.request.id != reason.request
        || &failed_reason(&c.request, condition) != reason
        || !matches!(v.data, D::Composition(Part::Endpoints { .. }))
    {
        return Err("合成失敗の由来・理由が違う".into());
    }
    validate_node(graph, graph.get(condition)?, c)
}
pub(super) fn validate_answer(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    answer: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = super::public_map::unavailable(environment, graph, request)? {
        return if answer == &expected {
            Ok(())
        } else {
            Err("合成の依存停止理由が元結果と違う".into())
        };
    }
    let p = answer.claim.ok_or("合成の構成命題がない")?;
    let v = value(graph, p)?;
    let Witness::Compose(c) = &v.witness else {
        return Err("合成の元検査がない".into());
    };
    validate_origin(environment, graph, request, c)?;
    validate_node(graph, graph.get(p)?, c)?;
    let j = graph
        .get(p)?
        .judgment
        .as_ref()
        .ok_or("合成命題の判断がない")?;
    let mut outputs = BTreeMap::from([("proposition".into(), p)]);
    if c.operation.is_some() {
        let operation = *answer
            .outputs
            .get("operation")
            .ok_or("合成Operationがない")?;
        let Part::Operation { map, .. } = part(graph, operation, c)? else {
            return Err("合成出力がOperationでない".into());
        };
        outputs.insert("operation".into(), operation);
        outputs.insert("map".into(), *map);
    }
    let mut reasons = j.reasons.clone();
    if let Some(stop) = &c.stopped {
        reasons.push(Reason::stopped(&request.id, stop.clone()));
    }
    sort_reasons(&mut reasons);
    if answer.id != request.id
        || answer.outputs != outputs
        || answer.status != j.status
        || answer.evidence != j.evidence
        || answer.reasons != reasons
        || answer.scope != c.scope
    {
        return Err("合成回答の状態・値・証拠・Scopeが元検査と違う".into());
    }
    Ok(())
}
pub(super) fn evaluate(
    prepared: &PreparedObserved,
    environment: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    control: &mut Control,
) -> Result<Answer, ValidationFailure> {
    control.checkpoint(Checkpoint::ConfigurationOperation)?;
    if let Some(answer) = super::public_map::unavailable(environment, graph, request)? {
        return Ok(answer);
    }
    let left = selected(environment, graph, request, "head")?;
    let right = selected(environment, graph, request, "then")?;
    let (source, middle_left, action, mut word) = components(graph, left)?;
    let (middle_right, target, _, right_word) = components(graph, right)?;
    word.extend(right_word);
    let universe = universe(graph, action)?;
    let mut support = graph.get(left)?.support.clone();
    support.extend(graph.get(right)?.support.iter().cloned());
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    let mut scope = graph.get(left)?.scope.clone();
    scope.merge(&graph.get(right)?.scope);
    let first = op(graph, left)?;
    let then = op(graph, right)?;
    let mut types = Vec::new();
    for r in &word {
        control.checkpoint(Checkpoint::ConfigurationOperation)?;
        let Scalar::Subject { entity, .. } = graph.scalar(*r)? else {
            return Err("合成語が原始参照でない".into());
        };
        types.push(entity.clone());
    }
    let root_type = |r: NodeRef| -> Result<String, ValidationFailure> {
        let D::Architecture { root, .. } = value(graph, r)?.data else {
            return Err("Operationの端点がArchitectureでない".into());
        };
        let Scalar::Subject { entity, .. } = graph.scalar(root)? else {
            return Err("Architecture rootが原始参照でない".into());
        };
        Ok(entity.clone())
    };
    let shape = OperationProjection {
        source: root_type(source)?,
        target: root_type(target)?,
        reading: first.source().reading().into(),
        to_reading: then.target().reading().into(),
        word: types,
    };
    let (operation, stopped) = match first.compose_retained(prepared.inputs(), then, control) {
        Ok(op) => (Some(op), None),
        Err(f) => match f.cause() {
            ConstructionFailure::Stopped(stop) => {
                let Some(op) = f.partial() else {
                    return Err(stop.clone().into());
                };
                (Some(op.clone()), Some(stop.clone()))
            }
            ConstructionFailure::InvalidSelection(_) if first.target() != then.source() => {
                (None, None)
            }
            other => return Err(format!("native compose: {other:?}").into()),
        },
    };
    let c = Arc::new(ComposeWitness {
        inputs: prepared.shared_inputs(),
        request: request.clone(),
        support,
        scope,
        left,
        right,
        source,
        middle_left,
        middle_right,
        target,
        universe,
        word,
        shape,
        operation,
        stopped,
    });
    let name = put(
        graph,
        &c,
        D::ConstructionLabel(Scalar::Text("composition".into())),
        vec![],
        None,
    )?;
    let evidence = if c.operation.is_none() {
        vec![add(
            graph,
            &c,
            Part::Evidence {
                left: middle_left,
                right: middle_right,
            },
        )?]
    } else {
        vec![]
    };
    let status = if c.operation.is_some() {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let condition = if c.operation.is_none() {
        Some(claim(
            graph,
            &c,
            Part::Endpoints {
                left: middle_left,
                right: middle_right,
            },
            Decision::Refuted,
            evidence.clone(),
        )?)
    } else {
        None
    };
    let proposition = claim(
        graph,
        &c,
        Part::Claim {
            name,
            left,
            right,
            condition,
        },
        status,
        evidence.clone(),
    )?;
    let mut outputs = BTreeMap::from([("proposition".into(), proposition)]);
    if let Some(operation) = &c.operation {
        let action = add(
            graph,
            &c,
            Part::Action {
                universe,
                images: operation.map().candidate().images().to_vec(),
            },
        )?;
        let candidate = add(
            graph,
            &c,
            Part::Candidate {
                source,
                target,
                action,
                left,
                right,
            },
        )?;
        let preservation = claim(
            graph,
            &c,
            Part::Preservation {
                candidate,
                composition: proposition,
            },
            Decision::Established,
            vec![],
        )?;
        let map = add(
            graph,
            &c,
            Part::Map {
                candidate,
                preservation,
            },
        )?;
        let operation = add(
            graph,
            &c,
            Part::Operation {
                source,
                target,
                candidate,
                map,
                action,
                preservation,
                left,
                right,
                word: c.word.clone(),
            },
        )?;
        outputs.insert("map".into(), map);
        outputs.insert("operation".into(), operation);
    }
    let mut reasons = condition
        .map(|r| vec![failed_reason(request, r)])
        .unwrap_or_default();
    if let Some(stop) = &c.stopped {
        reasons.push(Reason::stopped(&request.id, stop.clone()));
    }
    sort_reasons(&mut reasons);
    Ok(Answer {
        id: request.id.clone(),
        status,
        outputs,
        claim: Some(proposition),
        evidence,
        reasons,
        scope: c.scope.clone(),
    })
}
