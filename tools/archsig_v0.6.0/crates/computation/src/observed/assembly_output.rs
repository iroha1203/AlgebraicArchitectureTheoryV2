//! 組立ての共有計画を、既存buildの型付き公開recordへ配送する。
use super::{
    assembly_plan::{Assembly, Failure},
    build_plan::Plan,
    build_result::Builder,
    construction_result::{self as native, ConstructionType as T},
    environment::Environment,
    request::Request,
    result::*,
};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
    issue::Location,
    types::Type,
};
use std::collections::BTreeMap;
fn field<'a>(e: &'a Environment<'_>, r: &Request, key: &str) -> Result<&'a str, ValidationFailure> {
    let name = if key == "head" {
        r.declaration().ok_or(internal!("組立てViewがない"))?
    } else {
        let Some(super::request::Selector::Declaration { name }) =
            r.arguments.iter().find(|a| a.name == key).map(|a| &a.value)
        else {
            return Err(internal!("組立てViewの宣言がない").into());
        };
        name
    };
    e.indexes
        .inputs
        .law()
        .declarations()
        .get_key_value(name)
        .map(|(n, _)| n.as_str())
        .ok_or_else(|| internal!("組立てViewの定義がない").into())
}
fn input(
    b: &mut Builder<'_>,
    e: &Environment<'_>,
    name: &str,
    a: &Assembly,
    read: &super::assembly_plan::Read,
) -> Result<(NodeRef, Option<NodeRef>), ValidationFailure> {
    let d = &e.indexes.inputs.law().declarations()[name];
    let archsig_input::law::model::Signature::View { returns, body, .. } = &d.signature else {
        return Err(internal!("組立て入力がViewでない").into());
    };
    let source = b.push(
        NodeType::Expression(returns.erase()),
        "expression",
        Json::obj([
            ("kind", Json::str("source")),
            (
                "location",
                archsig_input::result::location_wire(&Location::Law {
                    span: e.indexes.inputs.law().exprs()[*body].span,
                }),
            ),
            ("parameters", Json::Arr(vec![])),
            (
                "bindings",
                Json::Arr(
                    a.bindings
                        .iter()
                        .map(|v| {
                            Json::obj([("name", Json::str(&v.name)), ("value", v.value.wire())])
                        })
                        .collect(),
                ),
            ),
        ]),
        a.bindings.iter().map(|v| v.value).chain(a.design).collect(),
        None,
    )?;
    let part = &mut b.parts[source.0 - b.base];
    part.support
        .make_owned()
        .extend(read.metadata.support.iter().cloned());
    part.support.make_owned().sort();
    part.support.make_owned().dedup();
    part.scope.merge(&read.metadata.scope);
    let value = read
        .value
        .as_ref()
        .map(|v| b.scalar(NodeType::Value(v.ty()), "binding", v.clone(), vec![source]))
        .transpose()?;
    Ok((source, value))
}
fn attach_facts(
    b: &mut Builder<'_>,
    e: &Environment<'_>,
    reading: &str,
    at: NodeRef,
    facts: &[Fact],
) -> Result<(), ValidationFailure> {
    let part = &mut b.parts[at.0 - b.base];
    for fact in facts {
        let subject = e.indexes.subject(&fact.snapshot, &fact.subject)?;
        let origin = if let Some(name) = &fact.field {
            let field = e
                .indexes
                .field(&e.state, &fact.snapshot, &fact.subject, name)?;
            match &field.slot {
                archsig_input::archmap::Slot::Known { origin, .. } => Some(origin.as_str()),
                _ => None,
            }
        } else {
            None
        };
        part.scope
            .merge(&e.indexes.scope(subject, reading, origin)?);
        part.support.make_owned().push(fact.clone());
    }
    part.support.make_owned().sort();
    part.support.make_owned().dedup();
    Ok(())
}

pub(super) type Actions = Vec<(usize, Action)>;
#[derive(Clone, Debug)]
pub(super) struct Action {
    model: std::sync::Arc<super::model_assembly::Model>,
    index: usize,
    restriction: bool,
}
impl Action {
    pub(super) fn map(&self) -> &crate::construction::maps::ConfigurationMap {
        if self.restriction {
            &self.model.restrictions[self.index]
        } else {
            self.model.inclusions[self.index].operation().map()
        }
    }
    pub(super) fn images(&self) -> &[Fact] {
        if self.restriction {
            self.model.restrictions[self.index].candidate().images()
        } else {
            self.model.inclusions[self.index].action().images()
        }
    }
}
impl PartialEq for Action {
    fn eq(&self, other: &Self) -> bool {
        self.images() == other.images()
    }
}
impl Eq for Action {}
fn map(
    b: &mut Builder<'_>,
    descriptor: Action,
    source: NodeRef,
    target: NodeRef,
    universe: NodeRef,
    proof: NodeRef,
    deferred: &mut Actions,
) -> Result<NodeRef, ValidationFailure> {
    let action = b.push(
        NodeType::Construction(T::AtomMap),
        "atom_map",
        Json::obj([("universe", universe.wire())]),
        vec![universe],
        None,
    )?;
    deferred.push((action.0 - b.base, descriptor));
    let candidate = b.push(
        NodeType::Construction(T::MapCandidate),
        "map_candidate",
        Json::obj([
            ("source", source.wire()),
            ("target", target.wire()),
            ("action", action.wire()),
        ]),
        vec![source, target, action, proof],
        None,
    )?;
    b.push(
        NodeType::Construction(T::ConfigurationMap),
        "configuration_map",
        Json::obj([("candidate", candidate.wire())]),
        vec![candidate, proof],
        None,
    )
}
pub(super) fn operations(
    g: &Graph,
    diagram: &super::internal_arrow_diagram::Diagram,
) -> Result<BTreeMap<Fact, NodeRef>, ValidationFailure> {
    diagram
        .rows
        .iter()
        .map(|row| {
            let Scalar::Subject {
                snapshot, subject, ..
            } = g.scalar(row.subject)?
            else {
                return Err(internal!("生成元の原始参照がない").into());
            };
            Ok((
                Fact::from(archsig_input::archmap::FactData {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: None,
                    atom: None,
                }),
                row.operation.ok_or(internal!("組立ての生成操作が未決"))?,
            ))
        })
        .collect()
}
pub(super) fn append(
    e: &Environment<'_>,
    plan: &Plan,
    r: &Request,
    b: &mut Builder<'_>,
    algebra: NodeRef,
    proof: NodeRef,
    c: &Control,
) -> Result<(NodeRef, NodeRef, Actions), ValidationFailure> {
    let a = plan
        .assembly
        .as_ref()
        .ok_or(internal!("組立ての計画がない"))?;
    let model = a
        .model
        .as_ref()
        .ok_or(internal!("組立ての成立済み構成がない"))?;
    let (_, fragments) = input(b, e, field(e, r, "head")?, a, &a.fragments)?;
    let (_, interfaces) = input(b, e, field(e, r, "along")?, a, &a.interfaces)?;
    let fragments = fragments.ok_or(internal!("担当Viewの値がない"))?;
    let interfaces = interfaces.ok_or(internal!("共有Viewの値がない"))?;
    let globals = operations(
        b.g,
        plan.arrows
            .as_ref()
            .ok_or(internal!("組立ての全生成操作がない"))?,
    )?;
    let mut inclusions = Vec::new();
    let mut deferred = Vec::new();
    let mut args = vec![
        fragments,
        interfaces,
        plan.architecture.reference,
        algebra,
        proof,
    ];
    let label = b.scalar(
        NodeType::Value(Type::Text),
        "binding",
        Scalar::Text("generator_transport".into()),
        vec![],
    )?;
    for (index, core) in model.inclusions.iter().enumerate() {
        c.checkpoint(Checkpoint::ConfigurationMap)?;
        let local = &a.locals[index];
        let inclusion = map(
            b,
            Action {
                model: model.clone(),
                index,
                restriction: false,
            },
            local.architecture.reference,
            plan.architecture.reference,
            plan.architecture.universe,
            proof,
            &mut deferred,
        )?;
        let restriction = map(
            b,
            Action {
                model: model.clone(),
                index,
                restriction: true,
            },
            a.restrictions[index].reference,
            local.architecture.reference,
            plan.architecture.universe,
            proof,
            &mut deferred,
        )?;
        let locals = operations(b.g, &local.arrows)?;
        let mut generators = Vec::new();
        args.extend([local.architecture.reference, inclusion, restriction]);
        for generator in core.generators() {
            c.checkpoint(Checkpoint::ConfigurationMap)?;
            let source = *locals
                .get(generator.source())
                .ok_or(internal!("包含元の操作がない"))?;
            let target = *globals
                .get(generator.target())
                .ok_or(internal!("包含先の操作がない"))?;
            let proposition = b.proposition(
                "constructible",
                vec![label, inclusion, source, target],
                vec![proof],
                Decision::Established,
            )?;
            generators.push(Json::obj([
                ("source", source.wire()),
                ("target", target.wire()),
                ("proposition", proposition.wire()),
            ]));
            args.extend([source, target, proposition]);
        }
        let mut wire = Json::obj([
            ("fragment", local.architecture.reference.wire()),
            ("map", inclusion.wire()),
            ("restriction", restriction.wire()),
            ("generators", Json::Arr(generators)),
        ]);
        if let Some(applied) = local.applied
            && let Json::Obj(fields) = &mut wire
        {
            fields.insert("applied".into(), applied.wire());
            args.push(applied);
        }
        inclusions.push(wire);
    }
    let mut wire = Json::obj([
        (
            "reading",
            Json::str(plan.architecture.witness.construction().reading()),
        ),
        ("fragments", fragments.wire()),
        ("interfaces", interfaces.wire()),
        ("object", plan.architecture.reference.wire()),
        ("algebra", algebra.wire()),
        ("inclusions", Json::Arr(inclusions)),
    ]);
    if let Some(design) = a.design
        && let Json::Obj(fields) = &mut wire
    {
        fields.insert("design".into(), design.wire());
        args.push(design);
    }
    let result = b.push(
        NodeType::Construction(T::ModelAssembly),
        "model_assembly",
        wire,
        args,
        None,
    )?;
    let label = b.scalar(
        NodeType::Value(Type::Text),
        "binding",
        Scalar::Text("model_assembly".into()),
        vec![],
    )?;
    let claim = b.proposition(
        "constructible",
        vec![label, result],
        vec![proof],
        Decision::Established,
    )?;
    Ok((result, claim, deferred))
}
pub(super) fn failed(
    e: &Environment<'_>,
    plan: &Plan,
    r: &Request,
    base: usize,
    g: &Graph,
) -> Result<(super::build_result::Parts, Answer), ValidationFailure> {
    let a = plan
        .assembly
        .as_ref()
        .ok_or(internal!("失敗した組立て計画がない"))?;
    let failure = a
        .failure
        .as_ref()
        .ok_or(internal!("組立ての不成立理由がない"))?;
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let (head, head_value) = input(&mut b, e, field(e, r, "head")?, a, &a.fragments)?;
    let (along, along_value) = input(&mut b, e, field(e, r, "along")?, a, &a.interfaces)?;
    let label = b.scalar(
        NodeType::Value(Type::Text),
        "binding",
        Scalar::Text("model_assembly".into()),
        vec![],
    )?;
    let (status, detail) = match failure {
        Failure::Rejected(d) => (Decision::Refuted, Some(&d.detail)),
        Failure::Unsupported(d) => (Decision::Undetermined, Some(&d.detail)),
        Failure::Missing(_) => (Decision::Undetermined, None),
    };
    let mut evidence = Vec::new();
    let mut dependencies = vec![head, along];
    if let Failure::Unsupported(unsupported) = failure
        && let Some(position) = &unsupported.position
    {
        let expression = b.field_source(
            e,
            position,
            unsupported
                .operand_types
                .first()
                .ok_or(internal!("未対応fieldの型がない"))?,
            &unsupported.location,
            plan.architecture.witness.construction().reading(),
            vec![head, along],
        )?;
        dependencies.push(expression);
    }
    if let Some(detail) = detail {
        let actual = b.scalar(
            NodeType::Value(Type::Text),
            "binding",
            Scalar::Text(detail.clone()),
            vec![head, along],
        )?;
        dependencies.push(actual);
        if status == Decision::Refuted {
            let Failure::Rejected(rejection) = failure else {
                unreachable!()
            };
            let (left, right) = if let Some((input, expected)) = a.rejected_design_origin {
                let expected = b.scalar(
                    NodeType::Value(Type::Text),
                    "binding",
                    Scalar::Text(expected.into()),
                    vec![head, along],
                )?;
                (expected, input)
            } else if let Some((left, right)) = &rejection.values {
                let reading = plan.architecture.witness.construction().reading();
                let has_repaired = rejection.repaired.iter().any(Option::is_some);
                let mut values = Vec::new();
                for (value, position) in [left, right].into_iter().zip(&rejection.repaired) {
                    let mut operands = vec![head, along];
                    if let Some(position) = position {
                        operands.push(
                            *a.repaired
                                .get(position)
                                .ok_or(internal!("修復済み反例の元対象がない"))?,
                        );
                    }
                    let reference = b.scalar(
                        NodeType::Value(value.ty()),
                        "binding",
                        value.clone(),
                        operands,
                    )?;
                    if !has_repaired || position.is_none() {
                        attach_facts(&mut b, e, reading, reference, &rejection.facts)?;
                    }
                    values.push(reference);
                }
                (values[0], values[1])
            } else {
                (head_value.unwrap_or(head), along_value.unwrap_or(along))
            };
            let mut operands = vec![left, right, actual];
            let mut data = Json::obj([
                ("bindings", Json::Arr(vec![])),
                ("paths", Json::Arr(vec![])),
                ("left", left.wire()),
                ("right", right.wire()),
                (
                    "facts",
                    Json::Arr(rejection.facts.iter().map(Fact::wire).collect()),
                ),
            ]);
            if r.arguments
                .iter()
                .any(|argument| argument.name.starts_with("design."))
                && let Json::Obj(fields) = &mut data
            {
                fields.insert("condition_detail".into(), Json::str(detail));
            }
            let mut repaired = Vec::new();
            for (side, position) in ["left", "right"].into_iter().zip(&rejection.repaired) {
                let Some(position) = position else {
                    continue;
                };
                let object = *a
                    .repaired
                    .get(position)
                    .ok_or(internal!("共有部反例の修復済み対象がない"))?;
                let subject = e.indexes.subject(&position.snapshot, &position.subject)?;
                let subject = b.scalar(
                    NodeType::Value(Type::Ref(subject.ty.to_string())),
                    "binding",
                    Scalar::Subject {
                        snapshot: position.snapshot.clone(),
                        subject: position.subject.clone(),
                        entity: subject.ty.to_string(),
                    },
                    vec![object],
                )?;
                operands.extend([object, subject]);
                dependencies.push(object);
                repaired.push(Json::obj([
                    ("side", Json::str(side)),
                    ("object", object.wire()),
                    (
                        "slot",
                        Json::obj([
                            ("subject", subject.wire()),
                            (
                                "field",
                                Json::str(
                                    position
                                        .field
                                        .as_ref()
                                        .ok_or(internal!("修復slotのfieldがない"))?
                                        .as_str(),
                                ),
                            ),
                        ]),
                    ),
                ]));
            }
            if !repaired.is_empty()
                && let Json::Obj(fields) = &mut data
            {
                fields.insert("repaired".into(), Json::Arr(repaired));
            }
            let counterexample = b.push(
                NodeType::Evidence,
                "evidence",
                Json::obj([("kind", Json::str("counterexample")), ("data", data)]),
                operands,
                None,
            )?;
            attach_facts(
                &mut b,
                e,
                plan.architecture.witness.construction().reading(),
                counterexample,
                &rejection.facts,
            )?;
            evidence.push(counterexample);
        }
    }
    dependencies.extend(evidence.iter().copied());
    let mut operands = vec![label, head, along];
    operands.extend_from_slice(&a.selections);
    let condition = if status == Decision::Refuted {
        let condition = b.proposition(
            "constructible",
            operands.clone(),
            dependencies.clone(),
            status,
        )?;
        let p = &mut b.parts[condition.0 - base];
        p.evidence = evidence.clone();
        p.judgment.as_mut().unwrap().evidence = evidence.clone();
        dependencies.push(condition);
        Some(condition)
    } else {
        None
    };
    let claim = b.proposition("constructible", operands, dependencies.clone(), status)?;
    let mut reasons = match failure {
        Failure::Missing(facts) => native::missing(r, facts.clone()),
        Failure::Rejected(_) => vec![Reason {
            kind: ReasonKind::ConditionFailed {
                condition: condition.ok_or(internal!("組立ての失敗条件がない"))?,
                construction: "model_assembly",
            },
            request: r.id.clone(),
            dependencies: vec![condition.ok_or(internal!("組立ての失敗条件がない"))?],
            missing: vec![],
            location: None,
        }],
        Failure::Unsupported(unsupported) => vec![Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: r.kind,
                operand_types: unsupported.operand_types.clone(),
                method: "finite_local_model_assembly".into(),
            },
            request: r.id.clone(),
            dependencies: dependencies.clone(),
            missing: vec![],
            location: Some(unsupported.location.clone()),
        }],
    };
    for reason in &mut reasons {
        if matches!(reason.kind, ReasonKind::Missing) {
            reason.dependencies = vec![head, along];
        }
    }
    let part = &mut b.parts[claim.0 - base];
    part.evidence = evidence.clone();
    part.arguments.extend(evidence.iter().copied());
    part.arguments.sort_by_key(|r| r.0);
    part.arguments.dedup();
    part.reasons = reasons.clone();
    let judgment = part.judgment.as_mut().unwrap();
    judgment.evidence = evidence.clone();
    judgment.reasons = reasons.clone();
    let scope = part.scope.clone();
    Ok((
        b.parts.into(),
        Answer {
            id: r.id.clone(),
            status,
            outputs: BTreeMap::from([("proposition".into(), claim)]),
            claim: Some(claim),
            evidence,
            reasons,
            scope,
        },
    ))
}
