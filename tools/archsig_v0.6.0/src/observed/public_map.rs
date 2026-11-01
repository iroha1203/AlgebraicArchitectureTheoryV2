//! 原始correspondenceのnative検査と公開DAGの接続。
use super::{
    PreparedObserved,
    architecture_result::architecture,
    construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        MapWitness, Witness,
    },
    environment::{AnswerBinding, Environment},
    projection::ProjectionStep as P,
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::control::{Checkpoint, Control};
use crate::{
    archmap::{Slot, Value},
    construction::ConstructionFailure,
};
use std::collections::BTreeMap;

fn tick(control: &mut Control) -> Result<(), ValidationFailure> {
    control.checkpoint(Checkpoint::ConfigurationMap)?;
    Ok(())
}
fn failure(cause: ConstructionFailure) -> ValidationFailure {
    match cause {
        ConstructionFailure::Stopped(stop) => stop.into(),
        other => ValidationFailure::Internal(format!("native map: {other:?}")),
    }
}
fn field(name: &str) -> Vec<P> {
    vec![P::Field(name.into())]
}
fn put(
    graph: &mut Graph,
    witness: &Witness,
    data: D,
    reasons: Vec<Reason>,
) -> Result<NodeRef, ValidationFailure> {
    native::retain(
        graph,
        ConstructionValue {
            witness: witness.clone(),
            data,
        },
        reasons,
        vec![],
        None,
    )
}
fn raw(graph: &mut Graph, witness: &Witness, fact: &Fact) -> Result<NodeRef, ValidationFailure> {
    native::retain(
        graph,
        native::subject_value(witness.clone(), fact)?,
        vec![],
        vec![],
        None,
    )
}
fn subject<'a>(
    environment: &'a Environment<'_>,
    fact: &Fact,
) -> Result<&'a crate::archmap::Subject, ValidationFailure> {
    environment.indexes.subject(&fact.snapshot, &fact.subject)
        .map_err(Into::into)
}
pub(super) fn selected(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
) -> Result<Fact, ValidationFailure> {
    let selector = &request
        .arguments
        .iter()
        .find(|a| a.name == "on")
        .ok_or("mapのonがない")?
        .value;
    let (snapshot, subject) = match selector {
        Selector::Subject { snapshot, subject } => (snapshot.clone(), subject.clone()),
        Selector::Answer { .. } => {
            let binding = environment.answer_binding(graph, selector, (0, 0))?;
            let value = match &binding {
                AnswerBinding::Reference(r) => graph.scalar(*r)?,
                AnswerBinding::Projection(node) => {
                    let Some(Payload::Scalar(value)) = &node.payload else {
                        return Err("mapのonの射影が原始値でない".into());
                    };
                    value
                }
                AnswerBinding::Inapplicable(_) => {
                    return Err("mapのonが原始correspondence参照を提供しない".into());
                }
            };
            let Scalar::Subject {
                snapshot, subject, ..
            } = value
            else {
                return Err("mapのonが原始参照でない".into());
            };
            (snapshot.clone(), subject.clone())
        }
        _ => return Err("mapのonがHandleでない".into()),
    };
    let fact = Fact {
        snapshot,
        subject,
        field: None,
        atom: None,
    };
    let original = environment.indexes.subject(&fact.snapshot, &fact.subject)?;
    let Selector::Declaration { name } = &request.head else {
        return Err("mapのheadが宣言でない".into());
    };
    if &original.ty != name {
        return Err("mapのonと原始correspondenceの型が違う".into());
    }
    Ok(fact)
}

fn empty(request: &Request, reasons: Vec<Reason>) -> Answer {
    Answer {
        id: request.id.clone(),
        status: Decision::Undetermined,
        outputs: BTreeMap::new(),
        claim: None,
        evidence: vec![],
        reasons,
        scope: Scope::default(),
    }
}
pub(super) fn validate_origin(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    value: &ConstructionValue,
) -> Result<(), ValidationFailure> {
    if matches!(request.kind,QuestionKind::Localize|QuestionKind::Diagnose)
        || (request.kind == QuestionKind::Compare
            && super::request::comparison::kind(request).is_ok_and(|k| k == "diagnostics"))
    {return super::local_result::validate_origin(environment,request,value);}
    if request.kind == QuestionKind::Quotient {return super::quotient_result::validate_origin(environment,request,value);}
    if matches!(request.kind,QuestionKind::Build|QuestionKind::Solve|QuestionKind::Repair) {
        return super::architecture_result::validate_build_origin(
            environment,
            graph,
            request,
            value,
        );
    }
    if let Witness::PathCompose(c) = &value.witness { return super::public_path_compose::validate_origin(environment,graph,request,c); }
    if let Witness::Compare(c) = &value.witness {
        if let D::Comparison(super::public_compare::Part::RelationSource(data)) = &value.data {
            let family = c.relation_family.as_ref().ok_or("relation Sourceの元族がない")?;
            environment.recheck_relation_source(family, data.scalar())?;
        }
        if c.relation_plan.is_some() { environment.recheck_relation_comparison(graph, c)?; }
        return super::public_compare::validate_origin(environment,graph,request,c);
    }
    if let Witness::Compose(c) = &value.witness {
        return super::public_compose::validate_origin(environment, graph, request, c);
    }
    if request.kind != QuestionKind::Map
        || value.witness.request() != request
        || value.witness.inputs().sources() != environment.indexes.inputs.sources()
    {
        return Err("native構成が現在の三入力・map要求に属さない".into());
    }
    let on = selected(environment, graph, request)?;
    let selected_ref = match &value.data {
        D::MapCandidate { subject, .. }
        | D::Operation { subject, .. }
        | D::Counterexample { subject, .. }
        | D::CandidateCondition { subject, .. } => Some(*subject),
        D::Pending {
            ty: T::MapCandidate,
            parts,
        } => parts
            .iter()
            .find(|(p, _)| p == &field("subject"))
            .map(|(_, r)| *r),
        _ => None,
    };
    if let Some(reference) = selected_ref
        && let Some(argument) = request.arguments.iter().find(|a| a.name == "on")
        && matches!(argument.value, Selector::Answer { .. })
    {
        environment.answer_binding_matches(graph, &argument.value, reference, (0, 0))?;
    }
    match &value.witness {
        Witness::Compose(_) | Witness::PathCompose(_) | Witness::Compare(_) => unreachable!(),
        Witness::Map(m) => {
            if m.subject() != &on
                || m.result().reading() != native::reading_name(request, "reading")?
                || m.result().to_reading() != native::reading_name(request, "to_reading")?
            {
                return Err("候補が現在のon・readingに属さない".into());
            }
        }
        Witness::Architecture(a) => {
            let holder = subject(environment, &on)?;
            let mut matches = false;
            for (key, reading_key) in [("from", "reading"), ("to", "to_reading")] {
                let Some(endpoint) = holder
                    .fields
                    .iter()
                    .find(|f| f.name.short() == key)
                else {
                    continue;
                };
                if let Slot::Known {
                    value: Value::Ref { snapshot, subject },
                    ..
                } = &endpoint.slot
                    && &a.construction().root().snapshot == snapshot
                    && &a.construction().root().subject == subject
                    && a.construction().reading() == native::reading_name(request, reading_key)?
                {
                    matches = true;
                }
            }
            if !matches {
                return Err("Architectureが現在の対応の始終root・readingでない".into());
            }
        }
    }
    Ok(())
}
pub(super) fn validate_configuration_answer(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    answer: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = unavailable(environment, graph, request)? {
        if answer != &expected {
            return Err("mapの依存停止回答が元出力・理由と違う".into());
        }
        return Ok(());
    }
    if answer.id != request.id {
        return Err("map回答のIDが違う".into());
    }
    let candidate = *answer
        .outputs
        .get("candidate")
        .ok_or("map回答に元候補がない")?;
    let claim = *answer
        .outputs
        .get("proposition")
        .ok_or("map回答に保存命題がない")?;
    let Some(Payload::Construction(c)) = &graph.get(candidate)?.payload else {
        return Err("map候補がnative構成でない".into());
    };
    let Witness::Map(m) = &c.witness else {
        return Err("map候補の元検査がない".into());
    };
    validate_origin(environment, graph, request, c)?;
    let Some(Payload::Construction(p)) = &graph.get(claim)?.payload else {
        return Err("保存命題がnative構成でない".into());
    };
    let linked = match &p.data {
        D::Preservation { candidate: r } => *r == candidate,
        D::PendingPreservation { parts } => parts == &vec![(field("candidate"), candidate)],
        D::CandidateCondition { .. } => m.failed_candidate()
            && graph.get(candidate)?.reasons.iter().any(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { condition, construction: "map_candidate" } if condition==claim)),
        _ => false,
    };
    if !linked || p.witness != c.witness || answer.claim != Some(claim) {
        return Err("保存命題が元候補に属さない".into());
    }
    let judgment = graph
        .get(claim)?
        .judgment
        .as_ref()
        .ok_or("保存命題に判断がない")?;
    let mut expected_outputs = BTreeMap::from([
        ("candidate".into(), candidate),
        ("proposition".into(), claim),
    ]);
    let mut map_ref = None;
    let mut op_ref = None;
    for (i, node) in graph.nodes.iter().enumerate() {
        let Some(Payload::Construction(v)) = &node.payload else {
            continue;
        };
        if v.witness != c.witness {
            continue;
        }
        match v.data {
            D::ConfigurationMap { candidate: r, .. } if r == candidate => {
                if map_ref.replace(NodeRef(i)).is_some() {
                    return Err("mapが重複している".into());
                }
            }
            D::Operation { candidate: r, .. } if r == candidate => {
                if op_ref.replace(NodeRef(i)).is_some() {
                    return Err("Operationが重複している".into());
                }
            }
            _ => {}
        }
    }
    if !c.is_blocked() && m.result().map().is_some() {
        expected_outputs.insert("map".into(), map_ref.ok_or("確認済みmapを落とした")?);
        if m.operation().is_some() {
            expected_outputs.insert(
                "operation".into(),
                op_ref.ok_or("確認済みOperationを落とした")?,
            );
        }
    } else if map_ref.is_some() || op_ref.is_some() {
        return Err("未決・反証候補からmap/Operationを公開した".into());
    }
    let reasons = if c.is_blocked() {
        graph.get(candidate)?.reasons.clone()
    } else {
        m.reasons()
    };
    if answer.outputs != expected_outputs
        || answer.status != judgment.status
        || answer.evidence != judgment.evidence
        || answer.reasons != reasons
        || answer.scope != graph.get(claim)?.scope
    {
        return Err("map回答の出力・判断・証拠・理由・Scopeが元検査と違う".into());
    }
    Ok(())
}
pub(super) fn unavailable(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
) -> Result<Option<Answer>, ValidationFailure> {
    let current = graph
        .requests
        .iter()
        .position(|r| r == request)
        .ok_or("元Requestがない")?;
    let mut reasons = vec![];
    let mut scope = Scope::default();
    if let Some(name) = request.declaration() {
        scope.readings.insert(
            environment
                .indexes.inputs
                .law()
                .declarations()
                .get(name)
                .map(|d| d.reading.clone())
                .unwrap_or_else(|| name.to_owned()),
        );
    }
    let selectors = request.arguments.iter().map(|a| &a.value).chain(
        matches!(request.kind, QuestionKind::Compose | QuestionKind::Compare | QuestionKind::Localize | QuestionKind::Diagnose)
            .then_some(&request.head),
    );
    for selector in selectors {
        let Selector::Answer { id, .. } = selector else {
            continue;
        };
        let producer_index = graph
            .requests
            .iter()
            .position(|r| &r.id == id)
            .ok_or("依存元Requestがない")?;
        if !request
            .arguments
            .iter()
            .any(|a| a.name == "on" && &a.value == selector)
            && !matches!(
                request.kind,
                QuestionKind::Map | QuestionKind::Compose | QuestionKind::Compare | QuestionKind::Quotient | QuestionKind::Localize | QuestionKind::Diagnose
            )
            && !matches!(
                graph.requests[producer_index].kind,
                QuestionKind::Map | QuestionKind::Compose | QuestionKind::Compare
            )
        {
            continue;
        }
        let producer = environment.answer_binding_source(graph, current, id, (0, 0))?;
        let available = match environment.answer_binding(graph, selector, (0, 0)) {
            Ok(AnswerBinding::Reference(r)) => {
                !matches!(&graph.get(r)?.payload,Some(Payload::Construction(v)) if v.is_blocked())
            }
            Ok(AnswerBinding::Projection(_)) => true,
            Ok(AnswerBinding::Inapplicable(_)) => continue,
            Err(ValidationFailure::UnsupportedExpression { .. }) => false,
            Err(other) => return Err(other),
        };
        if available {
            continue;
        }
        scope.merge(&producer.scope);
        reasons.extend(producer.reasons.iter().cloned());
        let mut dependencies = producer
            .outputs
            .values()
            .copied()
            .chain(producer.claim)
            .chain(producer.evidence.iter().copied())
            .collect::<Vec<_>>();
        dependencies.sort_by_key(|r| r.0);
        dependencies.dedup();
        reasons.push(Reason {
            kind: ReasonKind::DependencyBlocked {
                request: id.clone(),
            },
            request: request.id.clone(),
            dependencies,
            missing: vec![],
            location: None,
        });
    }
    if matches!(request.kind, QuestionKind::Map | QuestionKind::Compose | QuestionKind::Compare | QuestionKind::Quotient | QuestionKind::Localize | QuestionKind::Diagnose) {
        let (projection_reasons, projection_scope) =
            environment.projection_failure_reasons(graph, request)?;
        reasons.extend(projection_reasons);
        scope.merge(&projection_scope);
    }
    if reasons.is_empty() {
        return Ok(None);
    }
    sort_reasons(&mut reasons);
    let mut answer = empty(request, reasons);
    answer.scope = scope;
    Ok(Some(answer))
}

pub(super) fn evaluate_configuration(
    prepared: &PreparedObserved,
    environment: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    control: &mut Control,
) -> Result<Answer, ValidationFailure> {
    tick(control)?;
    environment.commit_projection_conditions(graph, request)?;
    if let Some(answer) = unavailable(environment, graph, request)? {
        return Ok(answer);
    }
    let selected_reference = if let Some(argument) =
        request.arguments.iter().find(|a| a.name == "on")
        && matches!(argument.value, Selector::Answer { .. })
    {
        match environment.answer_binding(graph, &argument.value, (0, 0))? {
            AnswerBinding::Reference(r) => Some(r),
            AnswerBinding::Projection(node) => {
                environment.validate(graph, &node)?;
                Some(graph.push(node)?)
            }
            AnswerBinding::Inapplicable(_) => {
                return Err("不適合なmap射影を通常計算へ渡した".into());
            }
        }
    } else {
        None
    };
    let on = selected(environment, graph, request)?;
    let holder = subject(environment, &on)?;
    let mut architectures = [None, None];
    for (i, key) in ["from", "to"].into_iter().enumerate() {
        tick(control)?;
        let endpoint = holder
            .fields
            .iter()
            .find(|f| f.name.short() == key)
            .ok_or("correspondenceの端点slotがない")?;
        if let Slot::Known {
            value: Value::Ref { snapshot, subject },
            ..
        } = &endpoint.slot
        {
            let root = Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            };
            let reading =
                native::reading_name(request, if i == 0 { "reading" } else { "to_reading" })?;
            let witness = ArchitectureWitness::compute(
                prepared.shared_inputs(),
                request,
                reading,
                &root,
                control,
            )
            .map_err(failure)?;
            architectures[i] = Some(architecture(graph, witness, control)?);
        }
    }
    let (m, stopped) = MapWitness::compute(
        prepared.shared_inputs(),
        request,
        on.clone(),
        architectures
            .iter()
            .flatten()
            .next()
            .map(|a| a.witness.as_ref()),
        control,
    )
    .map_err(failure)?;
    let witness = Witness::Map(m.clone());
    let subject = match selected_reference {
        Some(reference) => reference,
        None => raw(graph, &witness, &on)?,
    };
    let mut reasons = native::missing(request, m.result().missing().to_vec());
    for a in architectures.iter().flatten() {
        reasons.extend(a.reasons.iter().cloned());
    }
    if let Some(stop) = stopped {
        reasons.push(Reason::stopped(&request.id, stop));
    }
    sort_reasons(&mut reasons);
    let source = architectures[0].as_ref();
    let target = architectures[1].as_ref();
    let action = if let (Some(candidate), Some(a)) = (m.result().candidate(), source) {
        Some(put(
            graph,
            &witness,
            D::AtomMap {
                universe: a.universe,
                images: candidate.images().to_vec(),
            },
            vec![],
        )?)
    } else {
        None
    };
    let mut evidence = vec![];
    for (index, counterexample) in m.result().counterexamples().iter().enumerate() {
        let left = source.ok_or("反例の元Architectureがない")?.root;
        let right = target.ok_or("反例の先Architectureがない")?.root;
        evidence.push(put(
            graph,
            &witness,
            D::Counterexample {
                index,
                subject,
                left,
                right,
                facts: native::counterexample_facts(counterexample),
            },
            vec![],
        )?);
    }
    let failed_condition = if m.failed_candidate() {
        let name = put(
            graph,
            &witness,
            D::ConstructionLabel(Scalar::Text("map_candidate".into())),
            vec![],
        )?;
        let condition = native::retain(
            graph,
            ConstructionValue {
                witness: witness.clone(),
                data: D::CandidateCondition {
                    name,
                    subject,
                    source: source.ok_or("構成反証の元Architectureがない")?.reference,
                    target: target.ok_or("構成反証の先Architectureがない")?.reference,
                },
            },
            vec![],
            evidence.clone(),
            Some(Judgment {
                status: Decision::Refuted,
                evidence: evidence.clone(),
                reasons: vec![],
            }),
        )?;
        reasons.push(Reason {
            kind: ReasonKind::ConditionFailed {
                condition,
                construction: "map_candidate",
            },
            request: request.id.clone(),
            dependencies: vec![condition],
            missing: vec![],
            location: None,
        });
        sort_reasons(&mut reasons);
        Some(condition)
    } else {
        None
    };
    let complete = m.result().candidate().is_some()
        && source.is_some_and(|a| a.complete)
        && target.is_some_and(|a| a.complete);
    let candidate = if complete {
        put(
            graph,
            &witness,
            D::MapCandidate {
                declaration: m.shape().declaration.clone(),
                subject,
                source: source.unwrap().reference,
                target: target.unwrap().reference,
                action: action.ok_or("完成候補の総作用がない")?,
            },
            vec![],
        )?
    } else {
        let mut parts = vec![(field("subject"), subject)];
        if let Some(a) = source {
            parts.push((field("source"), a.reference));
        }
        if let Some(a) = target {
            parts.push((field("target"), a.reference));
        }
        if let Some(a) = action {
            parts.push((field("action"), a));
        }
        if reasons.is_empty() {
            return Err("候補が未完成だが元理由がない".into());
        }
        put(
            graph,
            &witness,
            D::Pending {
                ty: T::MapCandidate,
                parts,
            },
            reasons.clone(),
        )?
    };
    let reasons = if complete {
        reasons
    } else {
        graph.get(candidate)?.reasons.clone()
    };
    let status = if failed_condition.is_some() {
        Decision::Refuted
    } else if !complete {
        Decision::Undetermined
    } else if m.result().map().is_some() {
        Decision::Established
    } else if !evidence.is_empty() {
        Decision::Refuted
    } else {
        Decision::Undetermined
    };
    let data = if complete {
        D::Preservation { candidate }
    } else {
        D::PendingPreservation {
            parts: vec![(field("candidate"), candidate)],
        }
    };
    let claim = if let Some(condition) = failed_condition {
        condition
    } else {
        native::retain(
            graph,
            ConstructionValue {
                witness: witness.clone(),
                data,
            },
            if complete { vec![] } else { reasons.clone() },
            evidence.clone(),
            Some(Judgment {
                status,
                evidence: evidence.clone(),
                reasons: if status == Decision::Undetermined {
                    reasons.clone()
                } else {
                    vec![]
                },
            }),
        )?
    };
    let mut outputs = BTreeMap::from([
        ("candidate".into(), candidate),
        ("proposition".into(), claim),
    ]);
    if complete && m.result().map().is_some() {
        let map = put(
            graph,
            &witness,
            D::ConfigurationMap {
                candidate,
                preservation: claim,
            },
            vec![],
        )?;
        outputs.insert("map".into(), map);
        if m.operation().is_some() {
            let operation = put(
                graph,
                &witness,
                D::Operation {
                    source: source.unwrap().reference,
                    target: target.unwrap().reference,
                    candidate,
                    configuration_map: map,
                    preservation: claim,
                    action: action.unwrap(),
                    subject,
                },
                vec![],
            )?;
            outputs.insert("operation".into(), operation);
        }
    }
    let scope = graph.get(claim)?.scope.clone();
    Ok(Answer {
        id: request.id.clone(),
        status,
        outputs,
        claim: Some(claim),
        evidence,
        reasons,
        scope,
    })
}

fn object_algebra(request: &Request) -> bool {
    request.arguments.iter().any(|a| {
        a.name == "kind"
            && matches!(&a.value, Selector::Enum { value } if value == "object_algebra")
    })
}
pub(super) fn evaluate(
    prepared: &PreparedObserved,
    environment: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    control: &mut Control,
) -> Result<Answer, ValidationFailure> {
    let answer = evaluate_configuration(prepared, environment, graph, request, control)?;
    if object_algebra(request) && answer.outputs.contains_key("operation") {
        match super::object_map_result::extend(
            prepared,
            environment,
            graph,
            request,
            answer.clone(),
            control,
        ) {
            Err(ValidationFailure::Stop(stop)) => {
                let mut partial = answer;
                partial.outputs.remove("map");
                partial.outputs.remove("proposition");
                partial.claim = None;
                partial.status = Decision::Undetermined;
                partial.reasons.push(Reason::stopped(&request.id, stop));
                Ok(partial)
            }
            result => result,
        }
    } else {
        Ok(answer)
    }
}
pub(super) fn validate_answer(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    answer: &Answer,
) -> Result<(), ValidationFailure> {
    if object_algebra(request) && answer.outputs.contains_key("operation") {
        super::object_map_result::validate_answer(environment, graph, request, answer)
    } else {
        validate_configuration_answer(environment, graph, request, answer)
    }
}
