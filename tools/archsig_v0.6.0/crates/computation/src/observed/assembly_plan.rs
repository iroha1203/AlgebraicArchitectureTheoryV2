//! 組立ての元View評価と構成済み対象を、既存のbuild計画へ渡す。
use super::{
    PreparedObserved,
    architecture_result::{self, Architecture},
    build_plan::{self, Plan},
    construction_result::{self as native, ArchitectureWitness, Witness},
    environment::{AnswerBinding, Environment, change_search, repair_problem::family},
    model_assembly::{self, Model, Preparation},
    request::{Request, Selector},
    result::*,
};
use archsig_common::control::{Checkpoint, Control};
use std::{collections::BTreeMap, sync::Arc};
#[derive(Debug)]
pub(super) struct Read {
    pub metadata: family::Read,
    pub value: Option<Scalar>,
    pub unsupported: Option<model_assembly::Unsupported>,
}
fn read(
    env: &Environment<'_>,
    name: &str,
    bindings: &[(String, Scalar)],
) -> Result<Read, ValidationFailure> {
    match family::read_with_value(env, name, bindings) {
        Ok((metadata, value)) => Ok(Read {
            metadata,
            value,
            unsupported: None,
        }),
        Err(ValidationFailure::UnsupportedExpression { location, feature }) => {
            let law = env.indexes.inputs.law();
            let operand_types = if let archsig_common::issue::Location::Law { span } = &location {
                law.program()
                    .expressions
                    .get(span)
                    .and_then(|id| law.expr_type(*id))
                    .cloned()
                    .into_iter()
                    .collect()
            } else {
                vec![]
            };
            let mut scope = Scope::default();
            scope
                .readings
                .insert(law.declarations()[name].reading.clone());
            Ok(Read {
                metadata: family::Read {
                    failed: false,
                    blocked: true,
                    missing: vec![],
                    support: vec![],
                    scope,
                },
                value: None,
                unsupported: Some(model_assembly::Unsupported {
                    detail: feature,
                    location,
                    operand_types,
                    position: None,
                }),
            })
        }
        Err(e) => Err(e),
    }
}
#[derive(Debug)]
pub(super) enum Failure {
    Missing(Vec<Fact>),
    Unsupported(model_assembly::Unsupported),
    Rejected(model_assembly::Rejection),
}
#[derive(Debug)]
pub(super) struct Fragment {
    pub architecture: Architecture,
    pub arrows: super::internal_arrow_diagram::Diagram,
}
#[derive(Debug)]
pub(super) struct Assembly {
    pub model: Option<Arc<Model>>,
    pub failure: Option<Failure>,
    pub fragments: Read,
    pub interfaces: Read,
    pub bindings: Vec<Binding>,
    pub locals: Vec<Fragment>,
    pub restrictions: Vec<Architecture>,
}
fn failure(e: crate::construction::ConstructionFailure) -> ValidationFailure {
    match e {
        crate::construction::ConstructionFailure::Stopped(s) => s.into(),
        e => e
            .internal_context(format!("組立てのnative対象: {e:?}"))
            .into(),
    }
}
fn fact(value: &Scalar) -> Result<Fact, ValidationFailure> {
    let Scalar::Subject {
        snapshot, subject, ..
    } = value
    else {
        return Err(internal!("組立ての型付き値が個体参照でない").into());
    };
    Ok(Fact::from(archsig_input::archmap::FactData {
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        field: None,
        atom: None,
    }))
}
fn interfaces(value: &Scalar, c: &Control) -> Result<Vec<(Fact, Fact)>, ValidationFailure> {
    let mut pending = vec![value];
    let mut pairs = Vec::new();
    while let Some(value) = pending.pop() {
        c.checkpoint(Checkpoint::ConfigurationMap)?;
        match value {
            Scalar::Unit => {}
            Scalar::Tuple(items) => pending.extend(items.iter().rev()),
            Scalar::List { items, .. } => {
                for pair in items {
                    let Scalar::Tuple(items) = pair else {
                        return Err(internal!("共有対応が型付きの対でない").into());
                    };
                    if items.len() != 2 {
                        return Err(internal!("共有対応のarityが違う").into());
                    }
                    pairs.push((fact(&items[0])?, fact(&items[1])?));
                }
            }
            _ => return Err(internal!("共有対応が型付きListまたはTupleでない").into()),
        }
    }
    Ok(pairs)
}
fn reference(
    e: &Environment<'_>,
    g: &mut Graph,
    s: &Selector,
) -> Result<Option<NodeRef>, ValidationFailure> {
    if matches!(s, Selector::Answer { .. }) {
        Ok(Some(match e.answer_binding(g, s, (0, 0))? {
            AnswerBinding::Reference(r) => r,
            AnswerBinding::Projection(n) => {
                e.validate(g, &n)?;
                g.push(n)?
            }
            AnswerBinding::Inapplicable(_) => {
                return Err(internal!("組立て入力の型付き射影が不適合").into());
            }
        }))
    } else {
        Ok(None)
    }
}
pub(super) fn prepare(
    p: &PreparedObserved,
    e: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Plan, ValidationFailure> {
    c.checkpoint(Checkpoint::ConfigurationMap)?;
    let head = r.declaration().ok_or(internal!("組立ての元Viewがない"))?;
    let declaration = &p.inputs().law().declarations()[head];
    let reading = &declaration.reading;
    let along = r
        .arguments
        .iter()
        .find(|a| a.name == "along")
        .ok_or(internal!("組立ての共有Viewがない"))?;
    let Selector::Declaration { name: along } = &along.value else {
        return Err(internal!("共有Viewの宣言参照がない").into());
    };
    let on = r
        .arguments
        .iter()
        .find(|a| a.name == "on")
        .ok_or(internal!("組立てのrootがない"))?;
    let target = fact(&change_search::selector(e, g, &on.value)?)?;
    let mut input_refs = Vec::new();
    let mut values = Vec::new();
    let mut refs = BTreeMap::new();
    if let Some(at) = reference(e, g, &on.value)? {
        input_refs.push(at);
    }
    for argument in &r.arguments {
        if let Some(name) = argument.name.strip_prefix("bind.") {
            c.checkpoint(Checkpoint::ConfigurationMap)?;
            if let Some(at) = reference(e, g, &argument.value)? {
                input_refs.push(at);
                refs.insert(name.to_owned(), at);
            }
            values.push((
                name.to_owned(),
                change_search::selector(e, g, &argument.value)?,
            ));
        }
    }
    let fragments = read(e, head, &values)?;
    let shared = read(e, along, &values)?;
    let mut missing = fragments.metadata.missing.clone();
    missing.extend(shared.metadata.missing.iter().cloned());
    missing.sort();
    missing.dedup();
    let preparation = if fragments.metadata.failed || shared.metadata.failed {
        model_assembly::rejected(
            "組立てViewの束縛または適用条件が成立しない",
            vec![target.clone()],
        )
    } else if !missing.is_empty() {
        Preparation::Missing(missing)
    } else if let Some(unsupported) = fragments
        .unsupported
        .as_ref()
        .or(shared.unsupported.as_ref())
    {
        Preparation::Unsupported(unsupported.clone())
    } else {
        let Some(Scalar::Set { items, .. }) = &fragments.value else {
            return Err(internal!("担当Viewの型付き集合がない").into());
        };
        let roots = items.iter().map(fact).collect::<Result<Vec<_>, _>>()?;
        let pairs = interfaces(
            shared
                .value
                .as_ref()
                .ok_or(internal!("共有Viewの型付き値がない"))?,
            c,
        )?;
        model_assembly::compile(&p.shared_inputs(), reading, &target, &roots, &pairs, c)?
    };
    let (model, failed) = match preparation {
        Preparation::Ready(model) => (Some(Arc::new(model)), None),
        Preparation::Missing(missing) => (None, Some(Failure::Missing(missing))),
        Preparation::Rejected(detail) => (None, Some(Failure::Rejected(detail))),
        Preparation::Unsupported(detail) => (None, Some(Failure::Unsupported(detail))),
    };
    let witness = if let Some(model) = &model {
        let mut support = model.support.clone();
        support.extend(fragments.metadata.support.iter().cloned());
        support.extend(shared.metadata.support.iter().cloned());
        ArchitectureWitness::from_assembled(
            p.shared_inputs(),
            r,
            model.construction.clone(),
            model.overrides.clone(),
            &support,
            c,
        )
        .map_err(failure)?
    } else {
        ArchitectureWitness::compute(p.shared_inputs(), r, reading, &target, c).map_err(failure)?
    };
    let mut bindings = Vec::new();
    for (name, value) in values {
        let at = if let Some(at) = refs.get(&name) {
            *at
        } else {
            let f = fact(&value)?;
            native::retain(
                g,
                native::subject_value(Witness::Architecture(witness.clone()), &f)?,
                vec![],
                vec![],
                None,
            )?
        };
        input_refs.push(at);
        bindings.push(Binding {
            name,
            ty: value.ty(),
            value: at,
        });
    }
    let architecture = architecture_result::architecture(g, witness.clone(), c)?;
    let mut locals = Vec::new();
    let mut restrictions = Vec::new();
    if let Some(model) = &model {
        for (index, local) in model.fragments.iter().enumerate() {
            c.checkpoint(Checkpoint::ConfigurationMap)?;
            let local =
                ArchitectureWitness::assembly_fragment(&witness, Arc::new(local.clone()), c)
                    .map_err(failure)?;
            let local = architecture_result::architecture(g, local, c)?;
            let objects =
                super::object_component_diagram::retain(g, p.shared_inputs(), local.reference, c)?
                    .ok_or(internal!("局所対象の対象族が完成しない"))?;
            let arrows = super::internal_arrow_diagram::retain(
                g,
                p.shared_inputs(),
                local.reference,
                &objects,
                local.universe,
                c,
            )?;
            locals.push(Fragment {
                architecture: local,
                arrows,
            });
            let restricted = model.restrictions[index]
                .candidate()
                .source_construction()
                .ok_or(internal!("再制限写像の元対象がない"))?;
            let restricted = ArchitectureWitness::from_assembled(
                p.shared_inputs(),
                r,
                restricted,
                model.overrides.clone(),
                &model.support,
                c,
            )
            .map_err(failure)?;
            restrictions.push(architecture_result::architecture(g, restricted, c)?);
        }
    }
    input_refs.extend(locals.iter().map(|a| a.architecture.reference));
    input_refs.extend(restrictions.iter().map(|a| a.reference));
    let assembly = Arc::new(Assembly {
        model,
        failure: failed,
        fragments,
        interfaces: shared,
        bindings,
        locals,
        restrictions,
    });
    let mut plan = if assembly.failure.is_none() {
        build_plan::prepare_architecture(e, g, p.shared_inputs(), architecture, c)?
    } else {
        build_plan::incomplete_architecture(e, g, architecture, c)?
    };
    plan.boundary = super::native_source::Boundary::capture(
        e,
        g,
        plan.architecture.reference,
        plan.boundary
            .inputs()
            .iter()
            .copied()
            .chain(input_refs)
            .collect(),
        c,
    )?;
    plan.assembly = Some(assembly);
    Ok(plan)
}
