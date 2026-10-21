//! 原始correspondenceのnative検査と公開DAGの接続。
use super::{
    PreparedObserved,
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, MapWitness, Witness,
    },
    control::{Checkpoint, Control},
    environment::{AnswerBinding, Environment},
    projection::ProjectionStep as P,
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{
    archmap::{Slot, Value},
    construction::ConstructionFailure,
    issue::Location,
    law::model::ExpressionKind,
};
use std::{collections::BTreeMap, sync::Arc};

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
fn indexed(name: &str, i: usize) -> Vec<P> {
    vec![P::Field(name.into()), P::Index(i as u64)]
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
fn known_atom(
    graph: &mut Graph,
    witness: &Witness,
    fact: &Fact,
    control: &Control,
) -> Result<NodeRef, ValidationFailure> {
    native::retain(
        graph,
        native::atom_value(witness.clone(), fact, control)?,
        vec![],
        vec![],
        None,
    )
}
fn subject<'a>(
    environment: &'a Environment<'_>,
    fact: &Fact,
) -> Result<&'a crate::archmap::Subject, ValidationFailure> {
    environment
        .subject(&fact.snapshot, &fact.subject)
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
            let value = match environment.answer_binding(graph, selector, (0, 0))? {
                AnswerBinding::Reference(r) => graph.scalar(r)?,
                AnswerBinding::Projection(_) | AnswerBinding::Inapplicable(_) => {
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
    let original = environment.subject(&fact.snapshot, &fact.subject)?;
    let Selector::Declaration { name } = &request.head else {
        return Err("mapのheadが宣言でない".into());
    };
    if &original.ty != name {
        return Err("mapのonと原始correspondenceの型が違う".into());
    }
    Ok(fact)
}

struct Architecture {
    witness: Arc<ArchitectureWitness>,
    reference: NodeRef,
    root: NodeRef,
    universe: NodeRef,
    complete: bool,
    reasons: Vec<Reason>,
}
fn architecture(
    graph: &mut Graph,
    witness: Arc<ArchitectureWitness>,
    control: &mut Control,
) -> Result<Architecture, ValidationFailure> {
    tick(control)?;
    let a = witness.clone();
    let witness = Witness::Architecture(witness);
    let construction = a.construction();
    let root = raw(graph, &witness, construction.root())?;
    let universe = if let Some((i,_)) = graph.nodes.iter().enumerate().find(|(_,n)|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(&v.data,D::AtomUniverse(atoms) if atoms==construction.universe()))) {
        NodeRef(i)
    } else { put(graph,&witness,D::AtomUniverse(construction.universe().to_vec()),vec![])? };
    let mut reasons = native::missing(
        witness.request(),
        construction.base().blocking_slots().to_vec(),
    );
    let configuration = if let Some(c) = construction.base().configuration() {
        put(graph, &witness, D::Configuration(c.clone()), vec![])?
    } else {
        let known = construction.base().known();
        let mut parts = vec![];
        for (i, fact) in known.family().iter().enumerate() {
            tick(control)?;
            parts.push((
                indexed("family", i),
                known_atom(graph, &witness, fact, control)?,
            ));
        }
        for (name, pairs) in [
            ("relations", known.relations()),
            ("identifications", known.identifications()),
        ] {
            for (i, (left, right)) in pairs.iter().enumerate() {
                tick(control)?;
                for (j, fact) in [left, right].into_iter().enumerate() {
                    let mut path = indexed(name, i);
                    path.push(P::Index(j as u64));
                    parts.push((path, known_atom(graph, &witness, fact, control)?));
                }
            }
        }
        put(
            graph,
            &witness,
            D::Pending {
                ty: T::Configuration,
                parts,
            },
            reasons.clone(),
        )?
    };
    let mut laws = vec![];
    let mut laws_complete = true;
    for (instance, row) in a
        .readings()
        .instances()
        .iter()
        .enumerate()
        .filter(|(_, r)| r.declaration().kind == "law")
    {
        tick(control)?;
        let mut bindings = vec![];
        for b in row.bindings() {
            tick(control)?;
            bindings.push(Binding {
                name: b.parameter().name.clone(),
                ty: b.parameter().ty.erase(),
                value: raw(graph, &witness, b.subject())?,
            });
        }
        let parameters = row
            .parameters()
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        let mut body = None;
        let mut guard = None;
        for expression in &row.declaration().expressions {
            let is_guard = match expression.kind {
                ExpressionKind::Guard => true,
                ExpressionKind::Body => false,
                _ => continue,
            };
            tick(control)?;
            let r = put(
                graph,
                &witness,
                D::Source {
                    instance,
                    guard: is_guard,
                    location: Location::Law {
                        span: expression.span,
                    },
                    bindings: bindings.clone(),
                    parameters: parameters.clone(),
                },
                vec![],
            )?;
            if is_guard {
                guard = Some(r);
            } else {
                body = Some(r);
            }
        }
        let body = body.ok_or("Law instanceの元bodyがない")?;
        let pending = native::missing(witness.request(), native::instance_missing(row));
        let law = if pending.is_empty() {
            put(
                graph,
                &witness,
                D::LawInstance {
                    instance,
                    name: row.declaration().name.clone(),
                    role: row.declaration().role.ok_or("Lawのroleがない")?,
                    occurrence: Location::Law {
                        span: row.declaration().span,
                    },
                    bindings,
                    guard,
                    body,
                },
                vec![],
            )?
        } else {
            laws_complete = false;
            reasons.extend(pending.iter().cloned());
            let mut parts = vec![(field("body"), body)];
            if let Some(guard) = guard {
                parts.push((field("guard"), guard));
            }
            for (i, b) in bindings.iter().enumerate() {
                parts.push((indexed("bindings", i), b.value));
            }
            put(
                graph,
                &witness,
                D::PendingLawInstance { instance, parts },
                pending,
            )?
        };
        laws.push(law);
    }
    let mut arrows = vec![];
    for fact in a.arrows() {
        tick(control)?;
        arrows.push(raw(graph, &witness, fact)?);
    }
    sort_reasons(&mut reasons);
    let complete = construction.base().configuration().is_some() && laws_complete;
    let data = if complete {
        D::Architecture {
            reading: construction.reading().into(),
            root,
            configuration,
            laws,
            arrows,
        }
    } else {
        let mut parts = vec![
            (field("root"), root),
            (field("configuration"), configuration),
        ];
        parts.extend(
            laws.into_iter()
                .enumerate()
                .map(|(i, r)| (indexed("laws", i), r)),
        );
        parts.extend(
            arrows
                .into_iter()
                .enumerate()
                .map(|(i, r)| (indexed("internal_arrows", i), r)),
        );
        D::Pending {
            ty: T::Architecture,
            parts,
        }
    };
    let reference = put(graph, &witness, data, reasons.clone())?;
    let reasons = graph.get(reference)?.reasons.clone();
    tick(control)?;
    Ok(Architecture {
        witness: a,
        reference,
        root,
        universe,
        complete,
        reasons,
    })
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
    if request.kind != QuestionKind::Map
        || value.witness.request() != request
        || value.witness.inputs().sources() != environment.inputs.sources()
    {
        return Err("native構成が現在の三入力・map要求に属さない".into());
    }
    let on = selected(environment, graph, request)?;
    match &value.witness {
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
                    .find(|f| f.name.rsplit('.').next() == Some(key))
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
pub(super) fn validate_answer(
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
            D::ConfigurationMap { candidate: r } if r == candidate => {
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
        scope
            .readings
            .insert(environment.inputs.law().declarations[name].reading.clone());
    }
    for argument in &request.arguments {
        let Selector::Answer { id, .. } = &argument.value else {
            continue;
        };
        let producer_index = graph
            .requests
            .iter()
            .position(|r| &r.id == id)
            .ok_or("依存元Requestがない")?;
        if request.kind != QuestionKind::Map
            && graph.requests[producer_index].kind != QuestionKind::Map
        {
            continue;
        }
        let producer = environment.answer_binding_source(graph, current, id, (0, 0))?;
        let available = match environment.answer_binding(graph, &argument.value, (0, 0)) {
            Ok(AnswerBinding::Reference(r)) => {
                !matches!(&graph.get(r)?.payload,Some(Payload::Construction(v)) if v.is_blocked())
            }
            Ok(AnswerBinding::Projection(_)) => true,
            Ok(AnswerBinding::Inapplicable(_))
            | Err(ValidationFailure::UnsupportedExpression { .. }) => false,
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
    if reasons.is_empty() {
        return Ok(None);
    }
    sort_reasons(&mut reasons);
    let mut answer = empty(request, reasons);
    answer.scope = scope;
    Ok(Some(answer))
}

pub(super) fn evaluate(
    prepared: &PreparedObserved,
    environment: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    control: &mut Control,
) -> Result<Answer, ValidationFailure> {
    tick(control)?;
    if let Some(answer) = unavailable(environment, graph, request)? {
        return Ok(answer);
    }
    let on = selected(environment, graph, request)?;
    let holder = subject(environment, &on)?;
    let mut architectures = [None, None];
    for (i, key) in ["from", "to"].into_iter().enumerate() {
        tick(control)?;
        let endpoint = holder
            .fields
            .iter()
            .find(|f| f.name.rsplit('.').next() == Some(key))
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
    let subject = raw(graph, &witness, &on)?;
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
    let status = if !complete {
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
    let claim = native::retain(
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
    )?;
    let mut outputs = BTreeMap::from([
        ("candidate".into(), candidate),
        ("proposition".into(), claim),
    ]);
    if complete && m.result().map().is_some() {
        let map = put(graph, &witness, D::ConfigurationMap { candidate }, vec![])?;
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
