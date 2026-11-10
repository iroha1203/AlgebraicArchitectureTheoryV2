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
pub(super) fn read(
    env: &Environment<'_>,
    name: &str,
    bindings: &[(String, Scalar)],
) -> Result<Read, ValidationFailure> {
    match family::read_with_value(env, name, bindings) {
        Ok((mut metadata, value)) => {
            // The read collector records positions; native support records actual atoms.
            for fact in &mut metadata.support {
                if fact.atom.is_none()
                    && let Some(name) = &fact.field
                {
                    let subject = env.indexes.subject(&fact.snapshot, &fact.subject)?;
                    let field = subject
                        .fields
                        .iter()
                        .find(|f| &f.name == name)
                        .ok_or(internal!("読取り位置のfieldがない"))?;
                    if let archsig_input::archmap::Slot::Known { atom, .. } = &field.slot {
                        fact.atom = Some(atom.clone());
                    }
                }
            }
            metadata.support.sort();
            metadata.support.dedup();
            Ok(Read {
                metadata,
                value,
                unsupported: None,
            })
        }
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
                    affects_layout: true,
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
/// A known foreign layout remains outside the assembly family when another View is pending.
pub(super) fn layout_snapshot(
    env: &Environment<'_>,
    reading: &str,
    target: &Fact,
    fragments: &Read,
    shared: &Read,
    control: &Control,
) -> Result<Option<model_assembly::Unsupported>, ValidationFailure> {
    let roots = match &fragments.value {
        Some(Scalar::Set { items, .. }) => items.iter().map(fact).collect::<Result<Vec<_>, _>>()?,
        _ => vec![],
    };
    let pairs = shared
        .value
        .as_ref()
        .map(|value| interfaces(value, control))
        .transpose()?
        .unwrap_or_default();
    model_assembly::layout_snapshot(&env.indexes, reading, target, &roots, &pairs, control)
}

#[derive(Debug)]
pub(super) enum Failure {
    Missing(Vec<Fact>),
    Unsupported(model_assembly::Unsupported),
    Rejected(model_assembly::Rejection),
}
#[derive(Debug)]
pub(super) struct Fragment {
    pub applied: Option<NodeRef>,
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
    pub repaired: BTreeMap<Fact, NodeRef>,
    pub selections: Vec<NodeRef>,
}
fn failure(e: crate::construction::ConstructionFailure) -> ValidationFailure {
    match e {
        crate::construction::ConstructionFailure::Stopped(s) => s.into(),
        e => e
            .internal_context(format!("組立てのnative対象: {e:?}"))
            .into(),
    }
}
pub(super) fn fact(value: &Scalar) -> Result<Fact, ValidationFailure> {
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
pub(super) fn interfaces(
    value: &Scalar,
    c: &Control,
) -> Result<Vec<(Fact, Fact)>, ValidationFailure> {
    let mut pending = vec![value];
    let mut pairs = Vec::new();
    while let Some(value) = pending.pop() {
        c.checkpoint(Checkpoint::ConfigurationMap)?;
        match value {
            Scalar::Unit => {}
            Scalar::Tuple(items) => pending.extend(items.iter().rev()),
            Scalar::List { items, .. } => {
                for pair in items {
                    c.checkpoint(Checkpoint::ConfigurationMap)?;
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
pub(super) fn reference(
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
    let mut applied = BTreeMap::new();
    let mut selected = BTreeMap::new();
    let mut repaired = BTreeMap::new();
    let mut selections = Vec::new();
    let mut rejected = None;
    for argument in &r.arguments {
        let Some(name) = argument.name.strip_prefix("local.") else {
            continue;
        };
        c.checkpoint(Checkpoint::ConfigurationMap)?;
        let root = fact(
            &values
                .iter()
                .find(|(binding, _)| binding == name)
                .ok_or(internal!("修復局所の元root束縛がない"))?
                .1,
        )?;
        let at = reference(e, g, &argument.value)?.ok_or(internal!("修復局所の元出力がない"))?;
        input_refs.push(at);
        selections.push(at);
        if root.snapshot != target.snapshot {
            rejected = Some(model_assembly::foreign_snapshot(
                &p.shared_inputs(),
                &root,
                "局所選択の束縛rootが別snapshotに属する",
            )?);
            break;
        }
        let node = g.get(at)?;
        let source = match &node.payload {
            Some(Payload::Construction(value)) => match (&value.witness, &value.data) {
                (Witness::Architecture(witness), native::ConstructionData::SharedRepair(data))
                    if data.request().kind == super::request::QuestionKind::Apply =>
                {
                    let (overrides, _) = value.retained_architecture_overrides(g, c)?;
                    Some((Arc::clone(witness), overrides))
                }
                _ => None,
            },
            _ => None,
        };
        let Some((source, overrides)) = source else {
            rejected = Some(model_assembly::rejected(
                "局所入力はapplyの実Architectureを要求する",
                vec![root],
            ));
            break;
        };
        let construction = source.construction();
        if construction.root().snapshot != target.snapshot {
            rejected = Some(model_assembly::foreign_snapshot(
                &p.shared_inputs(),
                construction.root(),
                "修復局所の元rootが別snapshotに属する",
            )?);
            break;
        }
        if construction.root() != &root
            || construction.reading() != reading
            || construction.transport().is_some()
            || applied.contains_key(&root)
        {
            rejected = Some(model_assembly::rejected(
                "修復局所の元root・snapshot・readingまたは選択が異なる",
                vec![root, construction.root().clone()],
            ));
            break;
        }
        for (position, value) in overrides.iter() {
            c.checkpoint(Checkpoint::ConfigurationMap)?;
            let mut subject = position.clone();
            subject.field = None;
            subject.atom = None;
            if !construction.local_domain().known().contains(&subject)
                || selected.insert(position.clone(), value.clone()).is_some()
            {
                return Err(internal!("修復済み局所の更新が対象域と違う").into());
            }
            repaired.insert(position.clone(), at);
        }
        applied.insert(root, (at, source, overrides));
    }
    let fragments = read(e, head, &values)?;
    let shared = read(e, along, &values)?;
    let mut missing = fragments.metadata.missing.clone();
    missing.extend(shared.metadata.missing.iter().cloned());
    missing.sort();
    missing.dedup();
    let roots = match &fragments.value {
        Some(Scalar::Set { items, .. }) => items.iter().map(fact).collect::<Result<Vec<_>, _>>()?,
        _ => vec![],
    };
    let pairs = shared
        .value
        .as_ref()
        .map(|value| interfaces(value, c))
        .transpose()?
        .unwrap_or_default();
    let layout_problem =
        model_assembly::layout_snapshot(&e.indexes, reading, &target, &roots, &pairs, c)?;
    let preparation = if let Some(problem) = layout_problem {
        Preparation::Unsupported(problem)
    } else if let Some(rejected) = rejected {
        rejected
    } else if fragments.metadata.failed || shared.metadata.failed {
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
        if fragments.value.is_none() || shared.value.is_none() {
            return Err(internal!("組立ての担当または共有Viewの値がない").into());
        }
        if let Some(root) = applied.keys().find(|root| !roots.contains(root)) {
            model_assembly::rejected("修復局所が担当Viewの選択域にない", vec![root.clone()])
        } else {
            model_assembly::compile_same_snapshot(
                &p.shared_inputs(),
                reading,
                &target,
                &roots,
                &pairs,
                &selected,
                c,
            )?
        }
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
            let source = applied.get(local.root());
            let local = ArchitectureWitness::assembly_fragment(
                &witness,
                local.clone(),
                source.map(|(_, source, overrides)| (source.as_ref(), Arc::clone(overrides))),
                c,
            )
            .map_err(failure)?;
            let local = architecture_result::architecture(g, local, c)?;
            let objects =
                super::object_component_diagram::retain(g, p.shared_inputs(), local.reference, c)?
                    .ok_or(internal!("局所対象の対象族が完成しない"))?;
            let arrows = super::internal_arrow_diagram::retain_constructed(
                g,
                p.shared_inputs(),
                local.reference,
                &objects,
                local.universe,
                model.inclusions[index].shared_source(),
                c,
            )?;
            locals.push(Fragment {
                applied: source.map(|(reference, _, _)| *reference),
                architecture: local,
                arrows,
            });
            let restricted = model.restrictions[index]
                .candidate()
                .source_construction()
                .ok_or(internal!("再制限写像の元対象がない"))?;
            let restricted = ArchitectureWitness::assembly_restriction(&witness, restricted, c)
                .map_err(failure)?;
            restrictions.push(architecture_result::restriction(
                g,
                restricted,
                &architecture,
                c,
            )?);
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
        repaired,
        selections,
    });
    let mut plan = if assembly.failure.is_none() {
        let core = assembly
            .model
            .as_ref()
            .and_then(|m| m.inclusions.first())
            .ok_or(internal!("組立ての共有操作族がない"))?
            .shared_target();
        build_plan::prepare_architecture_with_arrows(
            e,
            g,
            p.shared_inputs(),
            architecture,
            Some(core),
            c,
        )?
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
