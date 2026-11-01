//! 整数局所状態を既存の型付き加群・解集合として公開する。
use super::*;
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
    pub actions: Vec<NodeRef>,
}
pub(super) fn position(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    f: &Fact,
) -> Result<(Json, NodeRef), ValidationFailure> {
    let subject = env.indexes.subject(&f.snapshot, &f.subject)?;
    let r = change_result::value(
        b,
        &Scalar::Subject {
            snapshot: f.snapshot.clone(),
            subject: f.subject.clone(),
            entity: subject.ty.to_string(),
        },
    )?;
    Ok((
        Json::obj([
            ("subject", r.wire()),
            (
                "field",
                Json::str(f.field.as_ref().ok_or(internal!("状態のfieldがない"))?),
            ),
        ]),
        r,
    ))
}
pub(in crate::observed::local_result) fn affine_map(
    b: &mut Builder<'_>,
    source: NodeRef,
    target: NodeRef,
    source_module: NodeRef,
    target_module: NodeRef,
    matrix: &Matrix,
    cols: usize,
    offset: &[Z],
    c: &Control,
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
pub(in crate::observed::local_result) fn solutions(
    b: &mut Builder<'_>,
    ring: NodeRef,
    ambient: NodeRef,
    domain: NodeRef,
    matrix: &Matrix,
    cols: usize,
    rhs: &[Option<Z>],
    laws: &[NodeRef],
    equation: bool,
    c: &Control,
) -> Result<(NodeRef, NodeRef, NodeRef, linear::Fiber), ValidationFailure> {
    let known_rhs = rhs.iter().cloned().collect::<Option<Vec<_>>>();
    let homogeneous = vec![Z::zero(); matrix.len()];
    let fiber = integer_fiber::solve(
        matrix,
        cols,
        known_rhs.as_deref().unwrap_or(&homogeneous),
        c,
    )?;
    let (equations, certificate) = if let Some(rhs) = &known_rhs {
        let (map, proof) = wire::certificate(b, ring, ambient, matrix, rhs, &fiber, laws, c)?;
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
    let local_fiber = linear::Fiber {
        origin: if known_rhs.is_some() { fiber.particular } else { None },
        known: known_rhs.is_some(), basis: fiber.kernel, rank: cols - fiber.rank,
    };
    Ok((solution, values, directions, local_fiber))
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
    reading: &linear::Reading,
    equation_state: &linear::Fiber,
    semantic: &linear::Fiber,
    c: &Control,
) -> Result<State, ValidationFailure> {
    let mut selected = vec![];
    for i in 0..model.supports.len() {
        if visible_law(model, support, reading, i, c)? {
            selected.push(i);
        }
    }
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
                    ("type", coefficient_type().wire()),
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
    let (equation, mut equation_domain, mut eq_coeff, _) = solutions(
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
                Type::Tuple(vec![coefficient_type(); positions.len()]).wire(),
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
    let declaration = &env.indexes.inputs.law().declarations()[&model.change];
    let Signature::Change { params, guard, .. } = &declaration.signature else {
        return Err(internal!("change署名がない").into());
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
    let (sem, solution_domain, parameter_kernel, parameter_fiber) = solutions(
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
    let projection: Matrix = reading
        .map
        .iter()
        .map(|row| positions.iter().map(|i| row[*i].clone()).collect())
        .collect();
    let (ambient, read_domain) = if projection == linear::identity(positions.len()) {
        (ambient, parameter_domain)
    } else {
        let read_module = wire::module(b, ring, reading.map.len(), "image", vec![equation])?;
        let read_domain = wire::domain(b, read_module)?;
        let quotient = affine_map(
            b,
            equation_domain,
            read_domain,
            ambient,
            read_module,
            &projection,
            positions.len(),
            &vec![Z::zero(); reading.map.len()],
            c,
        )?;
        equation_domain = b.push(
            NodeType::Domain,
            "domain",
            Json::obj([
                ("kind", Json::str("image")),
                ("map", quotient.wire()),
                ("source", equation.wire()),
            ]),
            vec![quotient, equation],
            None,
            None,
        )?;
        eq_coeff = wire::module(b, ring, equation_state.rank, "image", vec![quotient])?;
        (read_module, read_domain)
    };
    let read_action =
        integer_fiber::multiply(&projection, &action, model.action.parameter_count, c)?;
    let read_offset = linear::apply(&projection, &offset, c)?;
    let restricted_action = affine_map(
        b,
        solution_domain,
        read_domain,
        parameters,
        ambient,
        &read_action,
        model.action.parameter_count,
        &read_offset,
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
    let mut actions = vec![];
    if parameter_fiber.origin.is_some() {
        actions.push(fiber_action(b, ring, "lawful_fiber", solution_domain,
            semantic_domain, restricted_action, parameters, ambient,
            parameter_kernel, &parameter_fiber, &read_action, sem_coeff,
            semantic, sem, c)?);
    }
    let mut guard_matrix = vec![];
    let mut guard_rhs = vec![];
    parameter_guards(model, &mut guard_matrix, &mut guard_rhs);
    let same_fiber = guard_matrix == da && guard_rhs == shifted;
    let (allowed, allowed_domain, allowed_kernel, allowed_fiber) = if same_fiber {
        (sem, solution_domain, parameter_kernel, parameter_fiber.clone())
    } else {
        solutions(b, ring, parameters, candidates, &guard_matrix,
            model.action.parameter_count, &guard_rhs, &[], false, c)?
    };
    if allowed_fiber.origin.is_some() {
        let (allowed_image, allowed_map, allowed_states, effective) = if same_fiber {
            (semantic.clone(), restricted_action, semantic_domain, sem_coeff)
        } else {
            let image = linear::affine_image(&allowed_fiber, &read_action, &read_offset, c)?;
            let map = affine_map(b, allowed_domain, read_domain, parameters, ambient,
                &read_action, model.action.parameter_count, &read_offset, c)?;
            let states = b.push(NodeType::Domain, "domain", Json::obj([
                ("kind", Json::str("image")), ("map", map.wire()), ("source", allowed.wire()),
            ]), vec![map, allowed], None, None)?;
            let effective = wire::module(b, ring, image.rank, "image", vec![map])?;
            (image, map, states, effective)
        };
        actions.push(fiber_action(b, ring, "allowed", allowed_domain,
            allowed_states, allowed_map, parameters, ambient, allowed_kernel,
            &allowed_fiber, &read_action, effective, &allowed_image, allowed, c)?);
    }
    let comparison = affine_map(
        b,
        semantic_domain,
        equation_domain,
        ambient,
        ambient,
        &linear::identity(reading.map.len()),
        reading.map.len(),
        &vec![Z::zero(); reading.map.len()],
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
        actions,
    })
}

// 候補parameterの差の作用。元のchange自体の反復が群作用になるとは仮定しない。
fn fiber_action(
    b: &mut Builder<'_>, ring: NodeRef, stage: &str,
    parameters: NodeRef, states: NodeRef, map: NodeRef,
    parameter_module: NodeRef, ambient: NodeRef, kernel: NodeRef,
    fiber: &linear::Fiber, action: &Matrix, effective: NodeRef,
    image: &linear::Fiber, solutions: NodeRef, c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    let differences = integer_fiber::multiply(action, &fiber.basis, fiber.rank, c)?;
    let coordinates = linear::coordinates(&image.basis, image.rank, &differences, fiber.rank, c)?;
    let quotient = wire::map(b, kernel, effective, &coordinates, fiber.rank, c)?;
    let stabilizer_fiber = integer_fiber::solve(&coordinates, fiber.rank,
        &vec![Z::zero(); image.rank], c)?;
    let stabilizer = wire::module(b, ring, fiber.rank - stabilizer_fiber.rank,
        "kernel", vec![quotient])?;
    let stabilizer_inclusion = wire::map(b, stabilizer, kernel,
        &stabilizer_fiber.kernel, fiber.rank - stabilizer_fiber.rank, c)?;
    let parameter_inclusion = wire::map(b, kernel, parameter_module, &fiber.basis, fiber.rank, c)?;
    let effective_inclusion = wire::map(b, effective, ambient, &image.basis, image.rank, c)?;
    // image基底への座標射影が全射であることを、整数の各単位元の持上げで検査する。
    for j in 0..image.rank {
        let mut unit = vec![Z::zero(); image.rank]; unit[j] = Z::from(1);
        if integer_fiber::solve(&coordinates, fiber.rank, &unit, c)?.particular.is_none() {
            return Err(internal!("局所作用の有効像への商射影が全射でない").into());
        }
    }
    let inhabited = b.proposition("inhabited", vec![solutions], vec![], Decision::Established)?;
    let laws = b.proposition("action_laws", vec![map],
        vec![parameter_inclusion, effective_inclusion, stabilizer_inclusion, quotient],
        Decision::Established)?;
    let mut fields = BTreeMap::from([
        ("side".into(), Json::str("semantic")), ("stage".into(), Json::str(stage)),
        ("parameters".into(), parameters.wire()), ("states".into(), states.wire()),
        ("map".into(), map.wire()), ("stabilizer".into(), stabilizer.wire()),
        ("effective".into(), effective.wire()), ("quotient".into(), quotient.wire()),
        ("conditions".into(), refs(&[inhabited, laws])),
    ]);
    if stage == "lawful_fiber" { fields.insert("parameter_kernel".into(), kernel.wire()); }
    b.push(NodeType::Construction(T::Action), "action", Json::Obj(fields),
        vec![parameters, states, map, kernel, stabilizer, effective, quotient, inhabited, laws],
        None, None)
}
