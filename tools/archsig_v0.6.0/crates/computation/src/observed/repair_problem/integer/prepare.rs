//! 現在の元式から不変な整数問題を生成する。
use super::*;
pub(in crate::observed::repair_problem) fn is_prepare(env: &Environment<'_>, r: &Request) -> bool {
    let Some(using) = r.arguments.iter().find(|a| a.name == "using") else {
        return false;
    };
    let Selector::Declaration { name } = &using.value else {
        return false;
    };
    let Some(declaration) = env.indexes.inputs.law().declarations().get(name) else {
        return false;
    };
    matches!(&declaration.signature,Signature::Change{params,..} if params.iter().skip(1).any(|p|p.ty==Type::Z))
}
pub(super) fn diagnostic(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    r: &Request,
    inputs: &[NodeRef],
    details: &crate::observed::environment::change_affine::Pending,
) -> Result<(NodeRef, Type, archsig_common::issue::Location), ValidationFailure> {
    let mut bindings = vec![];
    let (body, parameters, ty) = if let Some(body) = details.expression {
        for (name, scalar) in &details.bindings {
            bindings.push((name.clone(), change_result::value(b, scalar)?));
        }
        (
            body,
            details.parameters.clone(),
            details.coefficient_type.clone().unwrap_or(Type::Z),
        )
    } else {
        let declaration = &env.indexes.inputs.law().declarations()
            [r.declaration().ok_or(internal!("理由の宣言がない"))?];
        let (params, body, ty) = match &declaration.signature {
            Signature::Law { params, body, .. } => (params, *body, Type::Bool),
            Signature::View {
                params,
                body,
                returns,
            } => (params, *body, returns.clone()),
            _ => return Err(internal!("理由の宣言がLaw/Viewでない").into()),
        };
        for a in &r.arguments {
            if let Some(name) = a.name.strip_prefix("bind.") {
                let scalar = change_search::selector(env, b.g, &a.value)?;
                bindings.push((name.to_owned(), change_result::value(b, &scalar)?));
            }
        }
        let parameters = params
            .iter()
            .filter(|p| !bindings.iter().any(|(n, _)| *n == p.name))
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        (body, parameters, ty)
    };
    let expression = change_result::source_expression(b, env, body, &bindings, &parameters)?;
    let part = &mut b.parts[expression.0 - b.base];
    part.arguments.extend_from_slice(inputs);
    for at in inputs {
        part.scope.merge(&b.g.get(*at)?.scope);
    }
    Ok((
        expression,
        details.coefficient_type.clone().unwrap_or(ty),
        archsig_common::issue::Location::Law {
            span: env.indexes.inputs.law().exprs()[body].span,
        },
    ))
}
pub(super) fn pending(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    witness: Arc<ArchitectureWitness>,
    inputs: Vec<NodeRef>,
    details: crate::observed::environment::change_affine::Pending,
    unsupported: bool,
) -> Result<Source, ValidationFailure> {
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let (expression, ty, location) = diagnostic(&mut b, env, r, &inputs, &details)?;
    let claim = condition(&mut b, r, inputs.clone(), Decision::Undetermined)?;
    let mut a = answer(r, claim, Decision::Undetermined, BTreeMap::new(), &b);
    if !details.facts.is_empty() {
        a.reasons.push(Reason {
            kind: ReasonKind::Missing,
            request: r.id.clone(),
            dependencies: vec![expression],
            missing: details.facts,
            location: Some(location.clone()),
        });
    }
    if unsupported {
        a.reasons.push(Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: r.kind,
                operand_types: vec![ty],
                method: details
                    .unsupported
                    .unwrap_or("integer_affine_repair_relation")
                    .into(),
            },
            request: r.id.clone(),
            dependencies: vec![expression],
            missing: vec![],
            location: Some(location),
        });
    }
    Ok(wrap(b, a, r, witness, None, inputs))
}
pub(in crate::observed::repair_problem) fn prepare(
    p: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    use crate::observed::change_result::linear_result as display;
    use crate::observed::environment::repair_problem::integer::{self as compiler, Preparation};
    let _selected = env.enter_architecture(g)?;
    let mut architecture = architecture_result::build(p.shared_inputs(), env, g, r, c)?;
    if let Some(at) = env.state.architecture_ref() {
        architecture.reference = at;
    }
    let mut inputs = vec![architecture.reference];
    let internal_values = if let Some(a) = r.arguments.iter().find(|a| a.name == "internal") {
        let (at, values) = scalar_set(env, g, &a.value)?;
        inputs.push(at);
        values
    } else {
        vec![]
    };
    let mut bindings = BTreeMap::new();
    for a in &r.arguments {
        if let Some(name) = a.name.strip_prefix("bind.") {
            if matches!(a.value, Selector::Answer { .. }) {
                inputs.push(reference(env, g, &a.value)?);
            }
            bindings.insert(name.to_owned(), change_search::selector(env, g, &a.value)?);
        }
    }
    if !architecture.complete {
        let missing = architecture
            .reasons
            .iter()
            .flat_map(|r| r.missing.iter().cloned())
            .collect();
        return pending(
            env,
            g,
            r,
            architecture.witness,
            inputs,
            crate::observed::environment::change_affine::Pending {
                facts: missing,
                ..Default::default()
            },
            false,
        );
    }
    let mut reused = None;
    let fixed_values = env.fixed_values();
    for node in &g.nodes {
        tick(c)?;
        let Some(Payload::Construction(v)) = &node.payload else {
            continue;
        };
        let D::SharedRepair(d) = &v.data else {
            continue;
        };
        if d.index != 0 {
            continue;
        }
        let Some(old) = d.source.integer() else {
            continue;
        };
        if d.source.request.kind==QuestionKind::Prepare && d.source.request.declaration()==r.declaration()
            && old.shared.witness.construction().root()==architecture.witness.construction().root()
            && old.shared.witness.construction().reading()==architecture.witness.construction().reading()
            && old.shared.compiled.family.as_ref().map(|f| &f.view)==r.arguments.iter().find_map(|a| match (&*a.name,&a.value) {("inputs",Selector::Declaration{name})=>Some(name),_=>None})
            && fixed_equal(&old.shared.compiled.fixed,&fixed_values,c)?
            && bindings_equal(&old.shared.compiled.bindings,&bindings,c)?
            && r.arguments.iter().any(|a|a.name=="using" && matches!(&a.value,Selector::Declaration{name}if *name==old.shared.compiled.change)) {
            reused=Some(old.shared.clone());break;
        }
    }
    let compiled = if let Some(old) = &reused {
        old.compiled.clone()
    } else {
        match compiler::compile(env, g, &architecture.witness, r, c)? {
            Preparation::Ready(compiled) => compiled,
            Preparation::Rejected => {
                let base = g.nodes.len();
                let mut b = Builder {
                    g,
                    base,
                    parts: vec![],
                };
                let claim = condition(&mut b, r, inputs.clone(), Decision::Refuted)?;
                let mut a = answer(r, claim, Decision::Refuted, BTreeMap::new(), &b);
                fail(&mut a, "prepare");
                return Ok(wrap(b, a, r, architecture.witness, None, inputs));
            }
            Preparation::Pending {
                details,
                unsupported,
            } => {
                return pending(
                    env,
                    g,
                    r,
                    architecture.witness,
                    inputs,
                    *details,
                    unsupported,
                );
            }
        }
    };
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let subjects = compiled
        .subjects
        .iter()
        .map(|s| change_result::value(&mut b, s))
        .collect::<Result<Vec<_>, _>>()?;
    let internal = entity_mask(&compiled.subjects, &internal_values, c)?;
    if internal.is_none() {
        let claim = condition(&mut b, r, inputs.clone(), Decision::Refuted)?;
        let mut a = answer(r, claim, Decision::Refuted, BTreeMap::new(), &b);
        fail(&mut a, "prepare");
        return Ok(wrap(b, a, r, architecture.witness, None, inputs));
    }
    let internal = internal.ok_or(internal!("検査済み内部集合がない"))?;
    let requirements = change_result::requirements(&mut b, env, &compiled.requirements, c)?;
    let ring = b.push(
        NodeType::Construction(T::Ring),
        "ring",
        Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))]),
        vec![],
        None,
    )?;
    let parameter_module = display::module(
        &mut b,
        ring,
        compiled.linear.parameter_count,
        "free",
        vec![],
    )?;
    let parameters = display::domain(&mut b, parameter_module)?;
    let mut binding_refs = vec![];
    let mut binding_fields = vec![];
    for (name, value) in &compiled.bindings {
        let at = change_result::value(&mut b, value)?;
        binding_refs.push(at);
        binding_fields.push(Json::obj([("name", Json::str(name)), ("value", at.wire())]));
    }
    let mut slots = vec![];
    let mut slot_arguments = vec![architecture.reference];
    for fact in &compiled.linear.slots {
        tick(c)?;
        let subject = env.indexes.subject(&fact.snapshot, &fact.subject)?;
        let at = change_result::value(
            &mut b,
            &Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: subject.ty.to_string(),
            },
        )?;
        slot_arguments.push(at);
        slots.push(Json::obj([
            ("subject", at.wire()),
            (
                "field",
                Json::str(
                    fact.field
                        .as_deref()
                        .ok_or(internal!("整数更新fieldがない"))?,
                ),
            ),
        ]));
    }
    let state_space = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", architecture.reference.wire()),
            ("slots", Json::Arr(slots)),
            (
                "state_type",
                Type::Tuple(vec![Type::Z; compiled.linear.slots.len()]).wire(),
            ),
        ]),
        slot_arguments,
        None,
    )?;
    let states = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([("kind", Json::str("states")), ("space", state_space.wire())]),
        vec![state_space],
        None,
    )?;
    let action = b.push(
        NodeType::Construction(T::StateMap),
        "state_map",
        Json::obj([
            ("source", parameters.wire()),
            ("target", states.wire()),
            ("kind", Json::str("change")),
            ("base", architecture.reference.wire()),
            ("change", Json::str(&compiled.change)),
            ("instances", refs(&subjects)),
        ]),
        [
            vec![parameters, states, architecture.reference],
            subjects.clone(),
        ]
        .concat(),
        None,
    )?;
    let Signature::Change { params, guard, .. } =
        &env.indexes.inputs.law().declarations()[&compiled.change].signature
    else {
        unreachable!("検査済みchange")
    };
    let mut guards = vec![];
    if let Some(guard) = guard {
        let free = params[1..]
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        for subject in &subjects {
            guards.push(change_result::source_expression(
                &mut b,
                env,
                *guard,
                &[(params[0].name.clone(), *subject)],
                &free,
            )?);
        }
    }
    let instances = subjects
        .iter()
        .enumerate()
        .map(|(i, s)| {
            Json::obj([
                ("subject", s.wire()),
                (
                    "positions",
                    Json::Arr(
                        (i * (params.len() - 1)..(i + 1) * (params.len() - 1))
                            .map(|p| Json::Nat(p as u64))
                            .collect(),
                    ),
                ),
            ])
        })
        .collect();
    let domain = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("change")),
            ("base", architecture.reference.wire()),
            ("bindings", Json::Arr(binding_fields)),
            ("change", Json::str(&compiled.change)),
            ("parameters", parameters.wire()),
            ("states", state_space.wire()),
            ("action", action.wire()),
            ("instances", Json::Arr(instances)),
            ("guards", refs(&guards)),
            ("requirements", refs(&requirements)),
        ]),
        [
            vec![
                architecture.reference,
                parameters,
                states,
                state_space,
                action,
            ],
            subjects.clone(),
            requirements.clone(),
            guards,
            binding_refs,
        ]
        .concat(),
        None,
    )?;
    let internal_refs = subjects
        .iter()
        .zip(&internal)
        .filter_map(|(s, on)| on.then_some(*s))
        .collect::<Vec<_>>();
    let unit_refs = subjects
        .iter()
        .zip(&internal)
        .filter_map(|(s, on)| (!*on).then_some(*s))
        .collect::<Vec<_>>();
    let ty = compiled
        .subjects
        .first()
        .map(|s| s.ty())
        .unwrap_or_else(|| params[0].ty.clone());
    let internal_domain = super::domain(&mut b, &ty, &internal_refs)?;
    let units = super::domain(&mut b, &ty, &unit_refs)?;
    let mut problem_fields = vec![];
    let mut input_bindings = vec![];
    let input_domain = if let Some(family) = &compiled.family {
        let coordinates = display::module(&mut b, ring, family.fields.len(), "free", vec![])?;
        let mut binding_fields = vec![];
        let mut arguments = vec![architecture.reference, coordinates];
        for (name, value) in &family.bindings {
            let at = change_result::value(&mut b, value)?;
            arguments.push(at);
            input_bindings.push(at);
            binding_fields.push(Json::obj([("name", Json::str(name)), ("value", at.wire())]));
        }
        let fields = Json::Arr(family.fields.iter().map(Fact::wire).collect());
        let domain = b.push(
            NodeType::Domain,
            "domain",
            Json::obj([
                ("kind", Json::str("integer_input_completions")),
                ("base", architecture.reference.wire()),
                ("view", Json::str(&family.view)),
                ("bindings", Json::Arr(binding_fields.clone())),
                ("fields", fields.clone()),
                (
                    "value_type",
                    Type::Tuple(vec![Type::Z; family.fields.len()]).wire(),
                ),
                ("coordinates", coordinates.wire()),
            ]),
            arguments,
            None,
        )?;
        problem_fields.push((
            "inputs".to_owned(),
            Json::obj([
                ("view", Json::str(&family.view)),
                ("bindings", Json::Arr(binding_fields)),
                ("fields", fields),
                ("domain", domain.wire()),
            ]),
        ));
        Some(InputDomain {
            domain,
            coordinates,
        })
    } else {
        None
    };
    let problem = b.push(
        NodeType::Construction(T::RepairProblem),
        "repair_problem",
        Json::Obj(
            problem_fields
                .into_iter()
                .chain([
                    ("domain".into(), domain.wire()),
                    ("requirements".into(), refs(&requirements)),
                    ("internal".into(), internal_domain.wire()),
                    ("units".into(), units.wire()),
                ])
                .collect(),
        ),
        [
            vec![domain, internal_domain, units],
            requirements.clone(),
            inputs.clone(),
            input_bindings,
            input_domain.into_iter().map(|d| d.domain).collect(),
        ]
        .concat(),
        None,
    )?;
    let part = &mut b.parts[problem.0 - base];
    part.support = Support::sum(compiled.support.clone(), [part.support.clone()]);

    b.parts[problem.0 - base].scope.merge(&compiled.scope);
    let (projection, unit_rows) = if let Some(old) = reused.filter(|old| old.internal == internal) {
        (old.projection.clone(), old.unit_rows.clone())
    } else {
        let mut shared = vec![false; compiled.linear.slots.len()];
        for (i, writes) in compiled.linear.unit_writes.iter().enumerate() {
            if !internal[i] {
                for fact in writes {
                    let row = find(&compiled.linear.slots, fact, c)?
                        .ok_or(internal!("整数instanceの更新行がない"))?;
                    shared[row] = true;
                }
            }
        }
        let rows = shared
            .iter()
            .enumerate()
            .filter_map(|(i, on)| on.then_some(i))
            .collect::<Vec<_>>();
        let mut unit_rows = vec![];
        for writes in &compiled.linear.unit_writes {
            let mut unit = vec![];
            for fact in writes {
                for (row, index) in rows.iter().enumerate() {
                    tick(c)?;
                    if compiled.linear.slots[*index] == *fact {
                        unit.push(row);
                        break;
                    }
                }
            }
            unit_rows.push(unit);
        }
        let projection = compiled
            .linear
            .particular
            .as_ref()
            .map(|origin| {
                Projection::new(
                    &env.results.integer_factors,
                    origin,
                    &compiled.linear.kernel,
                    &compiled.linear.action,
                    &compiled.linear.offset,
                    rows,
                    c,
                )
                .map(Arc::new)
            })
            .transpose()?;
        (projection, unit_rows)
    };
    let claim = condition(&mut b, r, vec![problem], Decision::Established)?;
    let a = answer(
        r,
        claim,
        Decision::Established,
        BTreeMap::from([("problem".into(), problem)]),
        &b,
    );
    let root = architecture.witness.construction().root();
    let root_type = env
        .indexes
        .subject(&root.snapshot, &root.subject)?
        .ty
        .to_string();
    let shared = Arc::new(Shared {
        compiled,
        input_domain,
        projection,
        witness: architecture.witness.clone(),
        base: architecture.reference,
        domain,
        problem: Some(problem),
        subjects,
        requirements,
        internal,
        unit_rows,
        ring,
        parameter_module,
        action,
        root_type,
    });
    Ok(wrap(b, a, r, architecture.witness, Some(shared), inputs))
}
