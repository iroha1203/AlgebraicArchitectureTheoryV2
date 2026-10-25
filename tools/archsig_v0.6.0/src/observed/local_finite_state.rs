//! 有限状態の射影、matching family、各側の完全な局所fiber。
use super::*;
fn project(value: &Scalar, from: &[Fact], to: &[Fact]) -> Result<Scalar, ValidationFailure> {
    if matches!(value, Scalar::Unit) && from.is_empty() && to.is_empty() {
        return Ok(Scalar::Unit);
    }
    let Scalar::Tuple(values) = value else {
        return Err("有限状態がTupleでない".into());
    };
    if values.len() != from.len() {
        return Err("有限状態の座標数が違う".into());
    }
    Ok(Scalar::Tuple(
        to.iter()
            .map(|f| {
                from.iter()
                    .position(|x| x == f)
                    .map(|i| values[i].clone())
                    .ok_or_else(|| ValidationFailure::from("制限先の自由位置がない"))
            })
            .collect::<Result<Vec<_>, _>>()?,
    ))
}
fn values(state: &State, equation: bool) -> &[(Scalar, NodeRef)] {
    if equation {
        &state.equation_values
    } else {
        &state.semantic_values
    }
}
pub(super) fn restriction(
    from: &State,
    to: &State,
    equation: bool,
    c: &mut Control,
) -> Result<Vec<(NodeRef, NodeRef)>, ValidationFailure> {
    let mut pairs = vec![];
    for (value, r) in values(from, equation) {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let image = project(value, &from.free, &to.free)?;
        let target = values(to, equation)
            .iter()
            .find(|(v, _)| *v == image)
            .map(|(_, r)| *r)
            .ok_or("有限状態の制限が局所Lawを保たない")?;
        pairs.push((*r, target));
    }
    Ok(pairs)
}
pub(super) fn summary(
    states: &[State],
    supports: &[Support],
    patches: &[usize],
    base: usize,
    equation: bool,
    c: &mut Control,
) -> Result<FiniteSide, ValidationFailure> {
    let mut matching: Vec<Vec<Scalar>> = vec![vec![]];
    for &patch in patches {
        let mut next = vec![];
        for row in matching {
            for (value, _) in values(&states[patch], equation) {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                let mut compatible = true;
                for (j, previous) in row.iter().enumerate() {
                    let intersection = supports[patch].intersect(&supports[patches[j]]);
                    let overlap = supports
                        .iter()
                        .position(|s| *s == intersection)
                        .ok_or("matchingの重なりがない")?;
                    compatible &= project(value, &states[patch].free, &states[overlap].free)?
                        == project(previous, &states[patches[j]].free, &states[overlap].free)?;
                }
                if compatible {
                    let mut extended = row.clone();
                    extended.push(value.clone());
                    next.push(extended);
                }
            }
        }
        matching = next;
    }
    let matching = matching.into_iter().map(Scalar::Tuple).collect::<Vec<_>>();
    let mut restriction = vec![];
    for (value, r) in values(&states[base], equation) {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let image = Scalar::Tuple(
            patches
                .iter()
                .map(|p| project(value, &states[base].free, &states[*p].free))
                .collect::<Result<Vec<_>, _>>()?,
        );
        if !matching.contains(&image) {
            return Err("大域状態の制限がmatching familyでない".into());
        }
        restriction.push((*r, image));
    }
    let state = &states[base];
    Ok(FiniteSide {
        global: if equation {
            state.equation
        } else {
            state.semantic
        },
        domain: if equation {
            state.equation_domain
        } else {
            state.states
        },
        solution_domain: if equation {
            state.equations
        } else {
            state.semantic_solution_domain
        },
        values: values(state, equation).to_vec(),
        matching,
        restriction,
        matching_type: Type::Tuple(
            patches
                .iter()
                .map(|p| states[*p].state_type.clone())
                .collect(),
        ),
        all: if equation {
            state.equation_parameters
        } else {
            state.point
        },
        checked: if equation {
            state.equation_checked
        } else {
            state.semantic_checked
        },
        parameters: if equation {
            state
                .equation_values
                .iter()
                .map(|(_, r)| (*r, vec![*r]))
                .collect()
        } else {
            state.semantic_parameters.clone()
        },
    })
}
pub(super) fn bijective(summary: &FiniteSide, c: &mut Control) -> Result<bool, ValidationFailure> {
    let key = |value: &Scalar| Json::obj([
        ("type", value.ty().wire()), ("value", value.wire())
    ]).canonical();
    let mut counts = BTreeMap::<String, usize>::new();
    for (_, value) in &summary.restriction {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        *counts.entry(key(value)).or_default() += 1;
    }
    for value in &summary.matching {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        if counts.get(&key(value)) != Some(&1) {
            return Ok(false);
        }
    }
    c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
    Ok(true)
}

fn scalar_domain(
    b: &mut Builder<'_>,
    ty: &Type,
    values: &[Scalar],
    c: &mut Control,
) -> Result<(NodeRef, Vec<(Scalar, NodeRef)>), ValidationFailure> {
    let mut elements = vec![];
    for value in values {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        if !elements.iter().any(|(v, _)| v == value) {
            elements.push((value.clone(), change_result::value(b, value)?));
        }
    }
    let domain = domain(b, ty, &elements.iter().map(|(_, r)| *r).collect::<Vec<_>>())?;
    Ok((domain, elements))
}
#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    target: NodeRef,
    laws: &[NodeRef],
    selected: &[usize],
    support: &Support,
    model: &finite_model::Model,
    c: &mut Control,
) -> Result<State, ValidationFailure> {
    let indexes = model
        .slots
        .iter()
        .enumerate()
        .filter(|(_, s)| support.visible.contains(s))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    let free = indexes
        .iter()
        .map(|i| model.slots[*i].clone())
        .collect::<Vec<_>>();
    let ty = Type::Tuple(
        indexes
            .iter()
            .map(|i| model.slot_types[*i].clone())
            .collect(),
    );
    let mut projected = vec![];
    let mut equation_values = vec![];
    let holds = |i: usize| selected.iter().all(|law| model.truth[i][*law]);
    for (i, point) in model.points.iter().enumerate() {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let value = Scalar::Tuple(indexes.iter().map(|i| point[*i].clone()).collect());
        if holds(i) {
            equation_values.push(value.clone());
        }
        projected.push(value);
    }
    let (equation_parameters, _) = scalar_domain(b, &ty, &projected, c)?;
    let (equation_domain, equation_values) = scalar_domain(b, &ty, &equation_values, c)?;
    let mut all_parameters = vec![];
    let mut all_images = vec![];
    let mut solution_parameters = vec![];
    let mut solution_images = vec![];
    for (row, point) in model.candidates.rows.iter().zip(&model.candidate_points) {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let Some(point) = point else { continue };
        let parameters = Scalar::Tuple(row.parameters.clone());
        all_parameters.push(parameters.clone());
        all_images.push(projected[*point].clone());
        if holds(*point) {
            solution_parameters.push(parameters);
            solution_images.push(projected[*point].clone());
        }
    }
    let parameter_type = Type::Tuple(model.candidates.parameter_types.clone());
    let (point, parameter_values) = scalar_domain(b, &parameter_type, &all_parameters, c)?;
    let (image, image_values) = scalar_domain(b, &ty, &all_images, c)?;
    let pair_refs = all_parameters
        .iter()
        .zip(&all_images)
        .map(|(p, v)| {
            let p = parameter_values
                .iter()
                .find(|(x, _)| x == p)
                .map(|(_, r)| *r)
                .ok_or("候補parameterがない")?;
            let v = image_values
                .iter()
                .find(|(x, _)| x == v)
                .map(|(_, r)| *r)
                .ok_or("候補状態がない")?;
            Ok((p, v))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let action = state_map(b, point, image, &pair_refs)?;
    let mut slot_values = vec![];
    let mut variables = vec![];
    let mut fixed = vec![];
    let mut slot_subjects = vec![];
    for slot in &support.positions {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let subject = env.subject(&slot.snapshot, &slot.subject)?;
        let r = change_result::value(
            b,
            &Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: subject.ty.clone(),
            },
        )?;
        slot_subjects.push(r);
        let wire = Json::obj([
            ("subject", r.wire()),
            (
                "field",
                Json::str(slot.field.as_ref().ok_or("局所位置のfieldがない")?),
            ),
        ]);
        slot_values.push(wire.clone());
        if let Some(i) = model.slots.iter().position(|f| f == slot) {
            if !support.visible.contains(slot) { continue; }
            variables.push(Json::obj([
                (
                    "position",
                    Json::obj([
                        ("kind", Json::str("observation")),
                        ("field", slot.wire()),
                        ("component", Json::Arr(vec![])),
                    ]),
                ),
                ("type", model.slot_types[i].wire()),
            ]));
        } else {
            fixed.push(wire);
        }
    }
    let state_slots = support
        .positions
        .iter()
        .zip(&slot_values)
        .filter(|(f, _)| free.contains(f))
        .map(|(_, v)| v.clone())
        .collect();
    let space = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", target.wire()),
            ("slots", Json::Arr(state_slots)),
            ("state_type", ty.wire()),
        ]),
        std::iter::once(target)
            .chain(slot_subjects.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let declaration = &env.inputs.law().declarations[&model.change];
    let Signature::Change { params, guard, .. } = &declaration.signature else {
        return Err("局所changeの署名がない".into());
    };
    let mut subjects = vec![];
    let mut guards = vec![];
    let mut instances = vec![];
    for (i, subject) in model.candidates.subjects.iter().enumerate() {
        let r = change_result::value(b, subject)?;
        subjects.push(r);
        let width = params.len() - 1;
        instances.push(Json::obj([
            ("subject", r.wire()),
            (
                "positions",
                Json::Arr(
                    (i * width..(i + 1) * width)
                        .map(|p| Json::Nat(p as u64))
                        .collect(),
                ),
            ),
        ]));
        if let Some(guard) = guard {
            guards.push(change_result::source_expression(
                b,
                env,
                *guard,
                &[(params[0].name.clone(), r)],
                &params[1..]
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect::<Vec<_>>(),
            )?);
        }
    }
    let bindings = model
        .bindings
        .iter()
        .map(|(name, value)| Ok((name, change_result::value(b, value)?)))
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let candidates = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("change")),
            ("base", target.wire()),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|(name, r)| {
                            Json::obj([("name", Json::str(*name)), ("value", r.wire())])
                        })
                        .collect(),
                ),
            ),
            ("change", Json::str(&model.change)),
            ("parameters", point.wire()),
            ("states", space.wire()),
            ("action", action.wire()),
            ("instances", Json::Arr(instances)),
            ("guards", refs(&guards)),
            ("requirements", refs(laws)),
        ]),
        [target, point, space, action]
            .into_iter()
            .chain(subjects)
            .chain(bindings.iter().map(|(_, r)| *r))
            .chain(guards)
            .chain(laws.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let (solution_parameter_domain, solution_parameter_values) =
        scalar_domain(b, &parameter_type, &solution_parameters, c)?;
    let semantic = b.push(
        NodeType::Construction(T::SolutionSet),
        "solution_set",
        Json::obj([
            ("domain", candidates.wire()),
            ("requirements", refs(laws)),
            (
                "representation",
                Json::obj([
                    ("kind", Json::str("finite")),
                    (
                        "values",
                        refs(
                            &solution_parameter_values
                                .iter()
                                .map(|(_, r)| *r)
                                .collect::<Vec<_>>(),
                        ),
                    ),
                ]),
            ),
        ]),
        std::iter::once(candidates)
            .chain(laws.iter().copied())
            .chain(solution_parameter_values.iter().map(|(_, r)| *r))
            .collect(),
        None,
        None,
    )?;
    let (states, semantic_values) = scalar_domain(b, &ty, &solution_images, c)?;
    let mut semantic_parameters = vec![];
    let mut semantic_pairs = vec![];
    for (v, r) in &semantic_values {
        let parameters = solution_images
            .iter()
            .zip(&solution_parameters)
            .filter(|(image, _)| *image == v)
            .map(|(_, p)| {
                solution_parameter_values
                    .iter()
                    .find(|(v, _)| v == p)
                    .map(|(_, r)| *r)
                    .ok_or_else(|| ValidationFailure::from("局所解parameterがない"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        semantic_pairs.extend(parameters.iter().map(|p| (*p, *r)));
        semantic_parameters.push((*r, parameters));
    }
    let semantic_action = state_map(b, solution_parameter_domain, states, &semantic_pairs)?;
    let equations = b.push(
        NodeType::Construction(T::EquationSpace),
        "equation_space",
        Json::obj([
            ("base", target.wire()),
            ("variables", Json::Arr(variables)),
            ("fixed", Json::Arr(fixed)),
            ("parameters", equation_parameters.wire()),
            ("requirements", refs(laws)),
        ]),
        [target, equation_parameters]
            .into_iter()
            .chain(slot_subjects.iter().copied())
            .chain(laws.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let equation = b.push(
        NodeType::Construction(T::EquationSolutionSet),
        "equation_solutions",
        Json::obj([
            ("domain", equations.wire()),
            (
                "representation",
                Json::obj([
                    ("kind", Json::str("finite")),
                    (
                        "values",
                        refs(&equation_values.iter().map(|(_, r)| *r).collect::<Vec<_>>()),
                    ),
                ]),
            ),
        ]),
        std::iter::once(equations)
            .chain(equation_values.iter().map(|(_, r)| *r))
            .collect(),
        None,
        None,
    )?;
    let comparison_pairs = semantic_values
        .iter()
        .map(|(v, r)| {
            equation_values
                .iter()
                .find(|(w, _)| w == v)
                .map(|(_, s)| (*r, *s))
                .ok_or_else(|| ValidationFailure::from("許可作用の解が方程式解にない"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let identity = state_map(b, states, equation_domain, &comparison_pairs)?;
    Ok(State {
        point,
        semantic,
        equations,
        equation,
        states,
        identity,
        slots: Json::Arr(slot_values),
        subjects: slot_subjects,
        equation_domain,
        semantic_values,
        equation_values,
        free,
        semantic_action,
        semantic_solution_domain: candidates,
        semantic_parameters,
        state_type: ty,
        equation_parameters,
        semantic_checked: all_parameters.len(),
        equation_checked: projected
            .iter()
            .map(|v| v.wire().canonical())
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
    })
}
