//! 元の三入力とRequestからArchitectureを組み立て、その由来を再検査する。
use super::{
    construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    environment::{AnswerBinding, Environment},
    projection::ProjectionStep as P,
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{construction::ConstructionFailure, issue::Location, law::model::ExpressionKind};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use std::sync::Arc;

fn tick(control: &mut Control) -> Result<(), ValidationFailure> {
    control.checkpoint(Checkpoint::ConfigurationMap)?;
    Ok(())
}
fn failure(cause: ConstructionFailure) -> ValidationFailure {
    match cause {
        ConstructionFailure::Stopped(stop) => stop.into(),
        other => ValidationFailure::Internal(format!("native Architecture: {other:?}")),
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
#[derive(Debug)]
pub(super) struct Architecture {
    pub(super) witness: Arc<ArchitectureWitness>,
    pub(super) reference: NodeRef,
    pub(super) root: NodeRef,
    pub(super) universe: NodeRef,
    pub(super) complete: bool,
    pub(super) reasons: Vec<Reason>,
}
pub(super) fn architecture(
    graph: &mut Graph,
    witness: Arc<ArchitectureWitness>,
    control: &mut Control,
) -> Result<Architecture, ValidationFailure> {
    architecture_with_root(graph, witness, None, control)
}
fn architecture_with_root(
    graph: &mut Graph,
    witness: Arc<ArchitectureWitness>,
    selected_root: Option<NodeRef>,
    control: &mut Control,
) -> Result<Architecture, ValidationFailure> {
    tick(control)?;
    let a = witness.clone();
    let witness = Witness::Architecture(witness);
    let construction = a.construction();
    let root = match selected_root {
        Some(root) => root,
        None => raw(graph, &witness, construction.root())?,
    };
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

/// 公開buildの有効化に先立ち、検査済みbuild Requestのnative構成を保持する。
fn request_reading<'a>(inputs: &'a CheckedInputs, request: &'a Request) -> Result<&'a str, ValidationFailure> {
    let Selector::Declaration { name }=&request.head else { return Err("Architectureの元headが宣言でない".into()); };
    match request.kind {
        QuestionKind::Build=>Ok(name),
        QuestionKind::Solve|QuestionKind::Repair=>inputs.law().declarations.get(name)
            .map(|d| d.reading.as_str()).ok_or_else(|| "変更対象の元Lawがない".into()),
        _=>Err("Architectureの元要求が対象構成でない".into()),
    }
}
pub(super) fn build(
    inputs: Arc<CheckedInputs>,
    environment: &Environment<'_>,
    graph: &mut Graph,
    request: &Request,
    control: &mut Control,
) -> Result<Architecture, ValidationFailure> {
    tick(control)?;
    if inputs.sources() != environment.indexes.inputs.sources()
        || graph.requests.get(graph.active.request) != Some(request)
        || graph.active.frame.is_some()
        || graph.active.iteration.is_some()
        || graph.active.instance.is_some()
        || graph.active.case.is_some()
    {
        return Err("build生成が元三入力・Requestのroot contextでない".into());
    }
    environment.with_request_context(graph, request, || Ok(()))?;
    let root = selected_build(environment, graph, request)?;
    let reading = request_reading(&inputs, request)?.to_owned();
    let witness =
        ArchitectureWitness::compute(inputs, request, &reading, &root, control).map_err(failure)?;
    let on = &request.arguments.iter().find(|a| a.name=="on").ok_or("対象構成のonがない")?.value;
    let selected_root = match on {
        selector @ Selector::Answer { .. } => {
            Some(match environment.answer_binding(graph, selector, (0, 0))? {
                AnswerBinding::Reference(r) => selected_root_reference(graph,r,request)?,
                AnswerBinding::Projection(node) => {
                    environment.validate(graph, &node)?;
                    graph.push(node)?
                }
                AnswerBinding::Inapplicable(_) => return Err("buildのroot射影が不適合".into()),
            })
        }
        _ => None,
    };
    architecture_with_root(graph, witness, selected_root, control)
}

fn selected_root_reference(graph:&Graph,r:NodeRef,request:&Request)->Result<NodeRef,ValidationFailure> {
    if matches!(request.kind,QuestionKind::Solve|QuestionKind::Repair) {
        if let Some(Payload::Construction(v))=&graph.get(r)?.payload {
            if graph.get(r)?.ty==NodeType::Construction(T::Architecture) {
                let law=request.declaration().ok_or("changeのLawがない")?;
                let reading=&v.witness.inputs().law().declarations[law].reading;
                if let Witness::Architecture(w)=&v.witness {if w.construction().reading()!=reading {return Err("changeと元Architectureのreadingが違う".into());}}
                if let Some((root,1))=v.project(&[P::Field("root".into())]) {return Ok(root);}
            }
        }
    }
    Ok(r)
}

pub(super) fn selected_build(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
) -> Result<Fact, ValidationFailure> {
    let reading = request_reading(environment.indexes.inputs, request)?;
    let mut on = request.arguments.iter().filter(|a| a.name == "on");
    let argument = on.next().ok_or("buildのonがない")?;
    if on.next().is_some() || (request.kind == QuestionKind::Build && request.arguments.len() != 1) {
        return Err("buildの固定引数がon一件でない".into());
    }
    let root = match &argument.value {
        Selector::Subject { snapshot, subject } => Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None,
        },
        selector @ Selector::Answer { .. } => {
            let binding = environment.answer_binding(graph, selector, (0, 0))?;
            let value = match &binding {
                AnswerBinding::Reference(r) => graph.scalar(selected_root_reference(graph,*r,request)?)?,
                AnswerBinding::Projection(node) => {
                    let Some(Payload::Scalar(value)) = &node.payload else {
                        return Err("buildのroot射影が原始値でない".into());
                    };
                    value
                }
                AnswerBinding::Inapplicable(_) => return Err("buildのroot射影が不適合".into()),
            };
            let Scalar::Subject {
                snapshot, subject, ..
            } = value
            else {
                return Err("buildのonが原始root参照でない".into());
            };
            Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            }
        }
        _ => return Err("buildのonが原始rootか公開Handleでない".into()),
    };
    let subject = environment.indexes.subject(&root.snapshot, &root.subject)?;
    let declaration = environment
        .indexes.inputs
        .definitions()
        .declarations
        .get(subject.ty.as_str())
        .ok_or("buildのroot型がない")?;
    let visible = crate::construction::reading_namespaces(
        environment.indexes.inputs.law(),
        reading,
        &mut environment.control.clone(),
    )
    .map_err(failure)?;
    if !visible.contains(&declaration.namespace)
        || !matches!(
            declaration.signature,
            crate::definition::PrimitiveSignature::Entity { owner: None, .. }
        )
    {
        return Err("buildのonがreading内のownerなしentityでない".into());
    }
    Ok(root)
}

pub(super) fn validate_build_origin(
    environment: &Environment<'_>,
    graph: &Graph,
    request: &Request,
    value: &ConstructionValue,
) -> Result<(), ValidationFailure> {
    if value.witness.request() != request
        || value.witness.inputs().sources() != environment.indexes.inputs.sources()
    {
        return Err("build構成が元三入力・Requestに属さない".into());
    }
    let Witness::Architecture(a) = &value.witness else {
        return Err("build構成の元Architectureがない".into());
    };
    let root = selected_build(environment, graph, request)?;
    let reading = request_reading(environment.indexes.inputs, request)?;
    let on=&request.arguments.iter().find(|a| a.name=="on").ok_or("対象構成の元onがない")?.value;
    if let Selector::Answer { .. } = on {
        let reference = match &value.data {
            D::Architecture { root, .. } => Some(*root),
            D::Pending {
                ty: T::Architecture,
                parts,
            } => parts
                .iter()
                .find(|(path, _)| path == &field("root"))
                .map(|(_, r)| *r),
            _ => None,
        };
        if let Some(reference) = reference {
            if matches!(request.kind,QuestionKind::Solve|QuestionKind::Repair) {
                if let AnswerBinding::Reference(original)=environment.answer_binding(graph,on,(0,0))? {
                    if selected_root_reference(graph,original,request)?!=reference {return Err("changeの元root参照が違う".into());}
                } else {environment.answer_binding_matches(graph,on,reference,(0,0))?;}
            } else {environment.answer_binding_matches(graph,on,reference,(0,0))?;}
        }
    }
    if !a.construction().resolved_owners().is_empty() {
        let regenerated = ArchitectureWitness::compute(
            Witness::Architecture(a.clone()).shared_inputs(), request, reading, &root, &mut environment.control.clone(),
        ).map_err(failure)?;
        if **a != *regenerated { return Err("owner補完Architectureの再構成が違う".into()); }
    }
    if a.construction().root() != &root || a.construction().reading() != reading {
        return Err("build構成が元root・readingに属さない".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
