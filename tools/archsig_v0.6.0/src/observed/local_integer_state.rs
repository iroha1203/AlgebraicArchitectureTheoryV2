//! 整数局所状態を既存の型付き加群・解集合として公開する。
use super::*;
use crate::observed::change_result::linear_result as wire;
pub(super) struct State {
    pub ambient: NodeRef,
    pub equation: NodeRef,
    pub equations: NodeRef,
    pub equation_domain: NodeRef,
    pub parameters: NodeRef,
    pub semantic: NodeRef,
    pub semantic_domain: NodeRef,
    pub action: NodeRef,
    pub comparison: NodeRef,
    pub coefficients: [NodeRef; 2],
}
pub(super) fn position(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    f: &Fact,
) -> Result<(Json, NodeRef), ValidationFailure> {
    let subject = env.subject(&f.snapshot, &f.subject)?;
    let r = change_result::value(
        b,
        &Scalar::Subject {
            snapshot: f.snapshot.clone(),
            subject: f.subject.clone(),
            entity: subject.ty.clone(),
        },
    )?;
    Ok((
        Json::obj([
            ("subject", r.wire()),
            (
                "field",
                Json::str(f.field.as_ref().ok_or("状態のfieldがない")?),
            ),
        ]),
        r,
    ))
}
pub(super) fn affine_map(
    b: &mut Builder<'_>,
    source: NodeRef,
    target: NodeRef,
    source_module: NodeRef,
    target_module: NodeRef,
    matrix: &Matrix,
    cols: usize,
    offset: &[Z],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let map = wire::map(b, source_module, target_module, matrix, cols, c)?;
    let offset = wire::vector(b, target_module, offset, c)?;
    b.push(
        NodeType::Construction(T::StateMap),
        "state_map",
        Json::obj([
            ("source", source.wire()),
            ("target", target.wire()),
            ("kind", Json::str("affine")),
            ("linear", map.wire()),
            ("offset", offset.wire()),
        ]),
        vec![source, target, map, offset],
        None,
        None,
    )
}
fn solutions(
    b: &mut Builder<'_>,
    ring: NodeRef,
    ambient: NodeRef,
    domain: NodeRef,
    matrix: &Matrix,
    cols: usize,
    rhs: &[Option<Z>],
    laws: &[NodeRef],
    equation: bool,
    c: &mut Control,
) -> Result<(NodeRef, NodeRef, NodeRef), ValidationFailure> {
    let known_rhs = rhs.iter().cloned().collect::<Option<Vec<_>>>();
    let homogeneous = vec![Z::zero(); matrix.len()];
    let fiber = integer_fiber::solve(
        matrix,
        cols,
        known_rhs.as_deref().unwrap_or(&homogeneous),
        c,
    )?;
    let (equations, certificate) = if let Some(rhs) = &known_rhs {
        let (map, proof) = wire::smith(b, ring, ambient, matrix, rhs, &fiber, laws, c)?;
        (map, Some(proof))
    } else {
        let target = wire::module(b, ring, matrix.len(), "free", laws.to_vec())?;
        (wire::map(b, ambient, target, matrix, cols, c)?, None)
    };
    let directions = wire::module(b, ring, cols - fiber.rank, "kernel", vec![equations])?;
    let mut args = vec![domain, equations, directions];
    args.extend_from_slice(laws);
    let representation = if let Some(certificate) = certificate {
        args.push(certificate);
        if let Some(p) = &fiber.particular {
            let particular = wire::vector(b, ambient, p, c)?;
            let embedding = wire::map(b, directions, ambient, &fiber.kernel, cols - fiber.rank, c)?;
            args.extend([particular, embedding]);
            Json::obj([
                ("kind", Json::str("affine")),
                ("particular", particular.wire()),
                ("directions", directions.wire()),
                ("embedding", embedding.wire()),
            ])
        } else {
            Json::obj([
                ("kind", Json::str("empty")),
                ("certificate", certificate.wire()),
            ])
        }
    } else {
        Json::obj([("kind", Json::str("symbolic"))])
    };
    let mut fields = BTreeMap::from([
        ("domain".into(), domain.wire()),
        ("representation".into(), representation),
    ]);
    if !equation {
        fields.insert("requirements".into(), refs(laws));
    }
    let solution = b.push(
        NodeType::Construction(if equation {
            T::EquationSolutionSet
        } else {
            T::SolutionSet
        }),
        if equation {
            "equation_solutions"
        } else {
            "solution_set"
        },
        Json::Obj(fields),
        args,
        None,
        None,
    )?;
    let values = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("solutions")),
            ("solutions", solution.wire()),
        ]),
        vec![solution],
        None,
        None,
    )?;
    Ok((solution, values, directions))
}
pub(super) fn build(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    ring: NodeRef,
    target: NodeRef,
    model: &Model,
    support: &geometry::Support,
    positions: &[usize],
    laws: &[NodeRef],
    semantic: &linear::Fiber,
    c: &mut Control,
) -> Result<State, ValidationFailure> {
    let selected = model
        .supports
        .iter()
        .enumerate()
        .filter(|(_, s)| support.contains(s))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    let requirements = selected.iter().map(|i| laws[*i]).collect::<Vec<_>>();
    let mut d = vec![];
    let mut rhs = vec![];
    for i in &selected {
        d.extend(model.laws[*i].0.iter().map(|row| {
            positions
                .iter()
                .map(|j| row[*j].clone())
                .collect::<Vec<_>>()
        }));
        rhs.extend(model.laws[*i].1.iter().cloned());
    }
    let mut variables = vec![];
    let mut fixed = vec![];
    let mut subjects = vec![];
    for slot in &support.positions {
        let (slot_value, subject) = position(env, b, slot)?;
        subjects.push(subject);
        if let Some(i) = model
            .action
            .slots
            .iter()
            .position(|f| f == slot)
            .filter(|i| positions.contains(i))
        {
            variables.push((
                i,
                Json::obj([
                    (
                        "position",
                        Json::obj([
                            ("kind", Json::str("observation")),
                            ("field", slot.wire()),
                            ("component", Json::Arr(vec![])),
                        ]),
                    ),
                    ("type", Type::Z.wire()),
                ]),
            ));
        } else {
            fixed.push(slot_value);
        }
    }
    variables.sort_by_key(|(i, _)| *i);
    let ambient = wire::module(b, ring, positions.len(), "free", vec![])?;
    let parameter_domain = wire::domain(b, ambient)?;
    let equations = b.push(
        NodeType::Construction(T::EquationSpace),
        "equation_space",
        Json::obj([
            ("base", target.wire()),
            (
                "variables",
                Json::Arr(variables.into_iter().map(|(_, v)| v).collect()),
            ),
            ("fixed", Json::Arr(fixed)),
            ("parameters", parameter_domain.wire()),
            ("requirements", refs(&requirements)),
        ]),
        [target, parameter_domain]
            .into_iter()
            .chain(requirements.iter().copied())
            .chain(subjects.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let (equation, equation_domain, eq_coeff) = solutions(
        b,
        ring,
        ambient,
        equations,
        &d,
        positions.len(),
        &rhs,
        &requirements,
        true,
        c,
    )?;
    let parameters = wire::module(b, ring, model.action.parameter_count, "free", vec![])?;
    let parameter_values = wire::domain(b, parameters)?;
    let action = linear::project(&model.action.action, positions);
    let offset = positions
        .iter()
        .map(|i| model.action.offset[*i].clone())
        .collect::<Vec<_>>();
    let action_ref = affine_map(
        b,
        parameter_values,
        parameter_domain,
        parameters,
        ambient,
        &action,
        model.action.parameter_count,
        &offset,
        c,
    )?;
    let mut state_slots = vec![];
    for i in positions {
        state_slots.push(position(env, b, &model.action.slots[*i])?.0);
    }
    let states = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", target.wire()),
            ("slots", Json::Arr(state_slots)),
            (
                "state_type",
                Type::Tuple(vec![Type::Z; positions.len()]).wire(),
            ),
        ]),
        std::iter::once(target).chain(subjects).collect(),
        None,
        None,
    )?;
    let mut instances = vec![];
    let mut instance_subjects = vec![];
    // 元changeのinstanceとparameter軸はModelが保持し、公開値は元座標へ戻す。
    for (subject, positions) in &model.instances {
        let r = change_result::value(b, subject)?;
        instance_subjects.push(r);
        instances.push(Json::obj([
            ("subject", r.wire()),
            (
                "positions",
                Json::Arr(positions.iter().map(|i| Json::Nat(*i as u64)).collect()),
            ),
        ]));
    }
    let bindings = model
        .bindings
        .iter()
        .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let declaration = &env.inputs.law().declarations[&model.change];
    let Signature::Change { params, guard, .. } = &declaration.signature else {
        return Err("change署名がない".into());
    };
    let mut guards = vec![];
    if let Some(guard) = guard {
        let residual = params
            .iter()
            .skip(1)
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        for subject in &instance_subjects {
            guards.push(change_result::source_expression(
                b,
                env,
                *guard,
                &[(params[0].name.clone(), *subject)],
                &residual,
            )?);
        }
    }
    let candidates = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("change")),
            ("change", Json::str(&model.change)),
            ("base", target.wire()),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|(n, r)| Json::obj([("name", Json::str(n)), ("value", r.wire())]))
                        .collect(),
                ),
            ),
            ("parameters", parameter_values.wire()),
            ("states", states.wire()),
            ("action", action_ref.wire()),
            ("instances", Json::Arr(instances)),
            ("guards", refs(&guards)),
            ("requirements", refs(&requirements)),
        ]),
        [target, parameter_values, states, action_ref]
            .into_iter()
            .chain(instance_subjects)
            .chain(guards)
            .chain(bindings.iter().map(|(_, r)| *r))
            .chain(requirements.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let mut da = integer_fiber::multiply(&d, &action, model.action.parameter_count, c)?;
    let shift = linear::apply(&d, &offset, c)?;
    let mut shifted = rhs
        .iter()
        .zip(shift)
        .map(|(x, y)| x.as_ref().map(|x| x - y))
        .collect::<Vec<_>>();
    parameter_guards(model, &mut da, &mut shifted);
    let (sem, solution_domain, _) = solutions(
        b,
        ring,
        parameters,
        candidates,
        &da,
        model.action.parameter_count,
        &shifted,
        &requirements,
        false,
        c,
    )?;
    let restricted_action = affine_map(
        b,
        solution_domain,
        parameter_domain,
        parameters,
        ambient,
        &action,
        model.action.parameter_count,
        &offset,
        c,
    )?;
    let semantic_domain = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("image")),
            ("map", restricted_action.wire()),
            ("source", sem.wire()),
        ]),
        vec![restricted_action, sem],
        None,
        None,
    )?;
    let sem_coeff = wire::module(b, ring, semantic.rank, "image", vec![restricted_action])?;
    let comparison = affine_map(
        b,
        semantic_domain,
        equation_domain,
        ambient,
        ambient,
        &linear::identity(positions.len()),
        positions.len(),
        &vec![Z::zero(); positions.len()],
        c,
    )?;
    Ok(State {
        ambient,
        equation,
        equations,
        equation_domain,
        parameters: parameter_values,
        semantic: sem,
        semantic_domain,
        action: restricted_action,
        comparison,
        coefficients: [eq_coeff, sem_coeff],
    })
}
