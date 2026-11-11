//! 組立ての元View評価と構成済み対象を、既存のbuild計画へ渡す。
use super::{
    PreparedObserved,
    architecture_result::{self, Architecture},
    build_plan::{self, Plan},
    construction_result::{self as native, ArchitectureWitness, Witness},
    environment::{
        AnswerBinding, AssemblyCondition, CapturedDomain, Environment, change_search,
        repair_problem::family,
    },
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
    pub domains: Vec<(Quantifier, CapturedDomain)>,
    pub condition: Option<AssemblyCondition>,
    pub unsupported: Option<model_assembly::Unsupported>,
}
pub(super) fn read(
    env: &Environment<'_>,
    name: &str,
    bindings: &[(String, Scalar)],
    capture: bool,
    fixed_design: bool,
) -> Result<Read, ValidationFailure> {
    match env.with_assembly_domains(capture, fixed_design, || {
        family::read_with_value(env, name, bindings)
    }) {
        Ok((Ok((mut metadata, value)), trace)) => {
            metadata.scope.merge_quantifiers(&trace.term_scope);
            // The evaluator can determine a value for every completion, for
            // instance when a universal test has a known counterexample.
            if fixed_design && value.is_some() && !metadata.failed && !metadata.condition_pending {
                metadata.missing.clear();
                metadata.blocked = false;
            }
            // The read collector records positions; native support records actual atoms.
            let mut observed = Vec::with_capacity(metadata.support.len());
            for mut fact in std::mem::take(&mut metadata.support) {
                if env.has_primitive_override(&fact) {
                    continue;
                }
                if fact.atom.is_none()
                    && let Some(name) = &fact.field
                {
                    let subject = env.indexes.subject(&fact.snapshot, &fact.subject)?;
                    let field = subject
                        .fields
                        .iter()
                        .find(|f| &f.name == name)
                        .ok_or(internal!("読取り位置のfieldがない"))?;
                    match &field.slot {
                        archsig_input::archmap::Slot::Known { atom, .. } => {
                            fact.atom = Some(atom.clone());
                        }
                        archsig_input::archmap::Slot::Missing if fixed_design => continue,
                        archsig_input::archmap::Slot::Missing => {}
                    }
                }
                observed.push(fact);
            }
            metadata.support = observed;
            metadata
                .missing
                .retain(|fact| !env.has_primitive_override(fact));
            metadata.support.sort();
            metadata.support.dedup();
            Ok(Read {
                metadata,
                value,
                domains: trace.domains,
                condition: trace.condition,
                unsupported: None,
            })
        }
        Ok((Err(ValidationFailure::UnsupportedExpression { location, feature }), trace)) => {
            let law = env.indexes.inputs.law();
            let expression_type = if let archsig_common::issue::Location::Law { span } = &location {
                law.program()
                    .expressions
                    .get(span)
                    .and_then(|id| law.expr_type(*id))
                    .cloned()
            } else {
                None
            };
            let output_type = match &law.declarations()[name].signature {
                archsig_input::law::model::Signature::View { returns, .. } => returns.erase(),
                _ => return Err(internal!("未対応の組立て入力がViewでない").into()),
            };
            let operand_types = vec![expression_type.unwrap_or(output_type)];
            let mut scope = trace.scope;
            scope
                .readings
                .insert(law.declarations()[name].reading.clone());
            if fixed_design {
                for (descriptor, _) in &trace.domains {
                    scope.add_quantifier(descriptor.clone());
                }
            }
            Ok(Read {
                metadata: family::Read {
                    failed: false,
                    blocked: true,
                    condition_pending: false,
                    missing: vec![],
                    support: trace
                        .support
                        .into_iter()
                        .filter(|fact| !env.has_primitive_override(fact))
                        .collect(),
                    scope,
                },
                value: None,
                domains: trace.domains,
                condition: trace.condition,
                unsupported: Some(model_assembly::Unsupported {
                    affects_layout: true,
                    detail: feature,
                    location,
                    operand_types,
                    position: None,
                }),
            })
        }
        Ok((Err(error), _)) | Err(error) => Err(error),
    }
}
pub(super) fn fragment_roots(
    fragments: &Read,
    control: &Control,
) -> Result<Option<Vec<Fact>>, ValidationFailure> {
    match &fragments.value {
        Some(Scalar::Set { items, .. }) => items
            .iter()
            .map(|item| {
                control.checkpoint(Checkpoint::ConfigurationMap)?;
                fact(item)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Some),
        Some(_) => Err(internal!("担当Viewの型が集合でない").into()),
        None => Ok(None),
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
    pub applied: Option<NodeRef>,
    pub architecture: Architecture,
    pub arrows: super::internal_arrow_diagram::Diagram,
}
#[derive(Debug)]
pub(super) struct Assembly {
    pub checked_ownership: bool,
    pub model: Option<Arc<Model>>,
    pub failure: Option<Failure>,
    pub fragments: Read,
    pub interfaces: Read,
    pub bindings: Vec<Binding>,
    pub design: Option<NodeRef>,
    pub rejected_design_origin: Option<(NodeRef, &'static str)>,
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
    let mut design = None;
    let mut rejected_design_origin = None;
    let mut rejected_design = false;
    let mut rejected = None;
    for argument in &r.arguments {
        let (name, is_design) = if let Some(name) = argument.name.strip_prefix("local.") {
            (name, false)
        } else if let Some(name) = argument.name.strip_prefix("design.") {
            (name, true)
        } else {
            continue;
        };
        c.checkpoint(Checkpoint::ConfigurationMap)?;
        let root = fact(
            &values
                .iter()
                .find(|(binding, _)| binding == name)
                .ok_or(internal!("選択状態の元root束縛がない"))?
                .1,
        )?;
        let at = reference(e, g, &argument.value)?.ok_or(internal!("選択状態の元出力がない"))?;
        input_refs.push(at);
        selections.push(at);
        if !is_design && root.snapshot != target.snapshot {
            rejected_design = false;
            rejected_design_origin = None;
            rejected = Some(model_assembly::foreign_snapshot(
                &p.shared_inputs(),
                &root,
                "局所選択の束縛rootが別snapshotに属する",
            )?);
            break;
        }
        let node = g.get(at)?;
        let architecture = match &node.payload {
            Some(Payload::Construction(value)) => match &value.witness {
                Witness::Architecture(witness) => Some((witness, value)),
                _ => None,
            },
            _ => None,
        };
        if !is_design
            && let Some((witness, _)) = architecture
            && witness.construction().root().snapshot != target.snapshot
        {
            rejected_design = false;
            rejected_design_origin = None;
            rejected = Some(model_assembly::foreign_snapshot(
                &p.shared_inputs(),
                witness.construction().root(),
                "修復局所の元rootが別snapshotに属する",
            )?);
            break;
        }
        let Some((source, value)) = architecture.filter(|(_, value)| {
            matches!(&value.data, native::ConstructionData::SharedRepair(data)
                if data.request().kind == super::request::QuestionKind::Apply)
        }) else {
            if rejected.is_some() {
                continue;
            }
            rejected_design = is_design;
            let detail = if is_design {
                "設計選択にはapplyの実Architectureを要求する"
            } else {
                "局所入力はapplyの実Architectureを要求する"
            };
            rejected = Some(model_assembly::rejected(detail, vec![root]));
            if is_design {
                rejected_design_origin = Some((at, "apply.object"));
            }
            continue;
        };
        let construction = source.construction();
        // A later local input can still put the entire assembly outside this snapshot.
        if rejected.is_some() {
            continue;
        }
        if construction.root() != &root
            || (is_design && root.snapshot != target.snapshot)
            || construction.reading() != reading
            || construction.transport().is_some()
            || applied.contains_key(&root)
        {
            let selected_root = construction.root();
            rejected_design = is_design;
            let mut failure = model_assembly::rejected(
                "修復局所の元root・snapshot・readingまたは選択が異なる",
                vec![root.clone(), selected_root.clone()],
            );
            if is_design && let Preparation::Rejected(rejection) = &mut failure {
                let (detail, left, right) = if selected_root != &root {
                    let original_root = |fact: &Fact| -> Result<Scalar, ValidationFailure> {
                        let subject = e.indexes.subject(&fact.snapshot, &fact.subject)?;
                        Ok(Scalar::Subject {
                            snapshot: fact.snapshot.clone(),
                            subject: fact.subject.clone(),
                            entity: subject.ty.to_string(),
                        })
                    };
                    (
                        "設計選択の元rootが明示束縛と異なる",
                        original_root(&root)?,
                        original_root(selected_root)?,
                    )
                } else if root.snapshot != target.snapshot {
                    rejection.facts.push(target.clone());
                    (
                        "設計選択のsnapshotが組立て先と異なる",
                        Scalar::Text(target.snapshot.clone()),
                        Scalar::Text(root.snapshot.clone()),
                    )
                } else if construction.reading() != reading {
                    (
                        "設計選択のreadingが組立てのreadingと異なる",
                        Scalar::Text(reading.into()),
                        Scalar::Text(construction.reading().into()),
                    )
                } else {
                    rejection.detail = "設計選択は未輸送の固有rootを要求する".into();
                    rejected_design_origin = Some((at, "untransported apply.object"));
                    rejected = Some(failure);
                    continue;
                };
                rejection.facts.dedup();
                rejection.detail = detail.into();
                rejection.values = Some((left, right));
            }
            rejected = Some(failure);
            continue;
        }
        let (overrides, _) = value.retained_architecture_overrides(g, c)?;
        if is_design {
            design = Some((at, overrides));
            continue;
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
        applied.insert(root, (at, Arc::clone(source), overrides));
    }
    let selected_reading = design
        .as_ref()
        .map(|(_, overrides)| e.with_fixed_primitive_values(overrides, c))
        .transpose()?;
    let reader = selected_reading.as_ref().unwrap_or(e);
    let (fragments, shared) = if rejected_design {
        let unread = || Read {
            metadata: family::Read {
                failed: false,
                blocked: false,
                condition_pending: false,
                missing: vec![],
                support: vec![],
                scope: Scope::default(),
            },
            value: None,
            domains: vec![],
            condition: None,
            unsupported: None,
        };
        (unread(), unread())
    } else {
        let capture = design.is_some() || p.requests().reads_assembly_domains(&r.id);
        (
            read(reader, head, &values, capture, design.is_some())?,
            read(reader, along, &values, capture, design.is_some())?,
        )
    };
    let mut missing = fragments.metadata.missing.clone();
    missing.extend(shared.metadata.missing.iter().cloned());
    missing.sort();
    missing.dedup();
    let roots = fragment_roots(&fragments, c)?.unwrap_or_default();
    let pairs = shared
        .value
        .as_ref()
        .map(|value| interfaces(value, c))
        .transpose()?
        .unwrap_or_default();
    let layout_problem =
        model_assembly::layout_snapshot(&e.indexes, reading, &target, &roots, &pairs, c)?;
    let root_problem = if layout_problem.is_none() && fragments.value.is_some() {
        model_assembly::layout_root_condition(&e.indexes, &target, &roots, c)?
    } else {
        None
    };
    let mut checked_ownership = false;
    let preparation = if rejected_design {
        rejected.ok_or(internal!("設計選択の拒否理由がない"))?
    } else if let Some(problem) = layout_problem {
        Preparation::Unsupported(problem)
    } else if let Some(Preparation::Unsupported(problem)) = rejected.as_ref() {
        Preparation::Unsupported(problem.clone())
    } else if let Some(problem) = root_problem {
        Preparation::Rejected(problem)
    } else if let Some(rejected) = rejected {
        rejected
    } else if let Some(failure) = [
        (&fragments.metadata, fragments.condition.as_ref()),
        (&shared.metadata, shared.condition.as_ref()),
    ]
    .into_iter()
    .find_map(|(read, failure)| read.failed.then_some(failure).flatten())
    {
        let mut facts = failure.support.clone();
        for value in [&failure.values.0, &failure.values.1] {
            if matches!(value, Scalar::Subject { .. }) {
                facts.push(fact(value)?);
            }
        }
        facts.retain(|fact| !reader.has_primitive_override(fact) && !selected.contains_key(fact));
        facts.sort();
        facts.dedup();
        Preparation::Rejected(model_assembly::Rejection {
            affects_layout: true,
            detail: failure.detail.into(),
            facts,
            values: Some(failure.values.clone()),
            repaired: [None, None],
            location: Some(archsig_common::issue::Location::Law { span: failure.span }),
        })
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
            checked_ownership = true;
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
        checked_ownership,
        model,
        failure: failed,
        fragments,
        interfaces: shared,
        bindings,
        design: design.map(|(reference, _)| reference),
        rejected_design_origin,
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
