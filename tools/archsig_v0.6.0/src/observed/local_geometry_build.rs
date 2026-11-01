pub(super) fn project(
    b: &mut Builder<'_>,
    mut expression: NodeRef,
    p: &Projection,
    free: &[Fact],
) -> Result<(NodeRef, NodeRef), ValidationFailure> {
    if let Some((subject, location)) = &p.field {
        let subject = change_result::value(b, subject)?;
        let ty = p.ty.clone();
        expression = b.push(
            NodeType::Expression(ty), "expression",
            Json::obj([
                ("kind", Json::str("source")),
                ("location", crate::result::location_wire(location)),
                ("parameters", Json::Arr(vec![])),
                ("bindings", Json::Arr(vec![Json::obj([
                    ("name", Json::str("subject")), ("value", subject.wire())
                ])])),
            ]), [expression,subject].into_iter().chain(p.arguments.iter().copied()).collect(), None, None,
        )?;
    } else {
    for position in &p.path {
        let NodeType::Expression(Type::Tuple(types)) = &b.parts[expression.0 - b.base].ty else {
            return Err("Tuple射影の入力型が積でない".into());
        };
        let ty = types
            .get(*position)
            .ok_or("Tuple射影の位置が範囲外")?
            .clone();
        expression = b.push(
            NodeType::Expression(ty),
            "expression",
            Json::obj([
                ("kind", Json::str("transform")),
                ("operation", Json::str("project")),
                ("operands", refs(&[expression])),
                ("position", Json::Nat(*position as u64)),
                ("parameters", Json::Arr(vec![])),
                ("bindings", Json::Arr(vec![])),
            ]),
            vec![expression],
            None,
            None,
        )?;
    }
    }
    let ty = p.ty.clone();
    let image = if p.support.visible.iter().any(|slot| free.contains(slot)) {
        if !matches!(ty, Type::Z | Type::Q) || p.support.visible.len() != 1 { return Err(unsupported("アフィン射影の積の像は未実装")); }
        b.push(NodeType::Domain, "domain", Json::obj([
            ("kind", Json::str("type")), ("type", ty.wire())
        ]), vec![], None, None)?
    } else {
        let actual = p.values.iter().map(|v| change_result::value(b, v)).collect::<Result<Vec<_>, _>>()?;
        domain(b, &ty, &actual)?
    };
    Ok((expression, image))
}
pub(super) struct Built {
    pub system: NodeRef,
    pub adequacy: NodeRef,
    pub point: NodeRef,
    pub semantic: NodeRef,
    pub equation: NodeRef,
    pub states: NodeRef,
    pub patch_count: usize,
    pub finite: Option<Finite>,
    pub integer: Option<integer::Diagram>,
}
struct State {
    reading: Option<integer::linear::Reading>,
    integer: Option<mixed_equation::State>,
    point: NodeRef,
    semantic: NodeRef,
    equations: NodeRef,
    equation: NodeRef,
    states: NodeRef,
    identity: NodeRef,
    slots: Json,
    subjects: Vec<NodeRef>,
    equation_domain: NodeRef,
    semantic_values: Vec<(Scalar, NodeRef)>,
    equation_values: Vec<(Scalar, NodeRef)>,
    free: Vec<Fact>,
    state_type: Type,
    equation_parameters: NodeRef,
    semantic_checked: usize,
    equation_checked: usize,
    semantic_action: NodeRef,
    semantic_solution_domain: NodeRef,
    semantic_parameters: Vec<(NodeRef, Vec<NodeRef>)>,
}

fn state(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    target: NodeRef,
    laws: &[NodeRef],
    positions: &[Fact],
    inhabited: bool,
    unit: NodeRef,
    c: &mut Control,
) -> Result<State, ValidationFailure> {
    let mut slot_values = vec![];
    let mut slot_subjects = vec![];
    for position in positions {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        let subject = env.indexes.subject(&position.snapshot, &position.subject)?;
        let reference = change_result::value(
            b,
            &Scalar::Subject {
                snapshot: position.snapshot.clone(),
                subject: position.subject.clone(),
                entity: subject.ty.to_string(),
            },
        )?;
        slot_subjects.push(reference);
        slot_values.push(Json::obj([
            ("subject", reference.wire()),
            (
                "field",
                Json::str(position.field.as_ref().ok_or("固定位置にfieldがない")?),
            ),
        ]));
    }
    let slots = Json::Arr(slot_values);

    let point = domain(b, &Type::Unit, &[unit])?;
    let elements = if inhabited { vec![unit] } else { vec![] };
    let states = domain(b, &Type::Unit, &elements)?;
    let action = state_map(b, point, point, &[(unit, unit)])?;
    let space = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", target.wire()),
            ("slots", Json::Arr(vec![])),
            ("state_type", Type::Unit.wire()),
        ]),
        vec![target],
        None,
        None,
    )?;
    let candidates = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("identity")),
            ("base", target.wire()),
            ("bindings", Json::Arr(vec![])),
            ("parameters", point.wire()),
            ("states", space.wire()),
            ("action", action.wire()),
            ("instances", Json::Arr(vec![])),
            ("guards", Json::Arr(vec![])),
            ("requirements", refs(laws)),
        ]),
        [target, point, space, action]
            .into_iter()
            .chain(laws.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let representation = Json::obj([("kind", Json::str("finite")), ("values", refs(&elements))]);
    let semantic = b.push(
        NodeType::Construction(T::SolutionSet),
        "solution_set",
        Json::obj([
            ("domain", candidates.wire()),
            ("requirements", refs(laws)),
            ("representation", representation.clone()),
        ]),
        [candidates, states]
            .into_iter()
            .chain(laws.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let equations = b.push(
        NodeType::Construction(T::EquationSpace),
        "equation_space",
        Json::obj([
            ("base", target.wire()),
            ("variables", Json::Arr(vec![])),
            ("fixed", slots.clone()),
            ("parameters", point.wire()),
            ("requirements", refs(laws)),
        ]),
        [target, point]
            .into_iter()
            .chain(laws.iter().copied())
            .chain(slot_subjects.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let equation = b.push(
        NodeType::Construction(T::EquationSolutionSet),
        "equation_solutions",
        Json::obj([
            ("domain", equations.wire()),
            ("representation", representation),
        ]),
        vec![equations, states],
        None,
        None,
    )?;

    let pairs = elements.iter().map(|r| (*r, *r)).collect::<Vec<_>>();
    let identity = state_map(b, states, states, &pairs)?;
    Ok(State {
        reading: None,
        integer: None,
        point,
        semantic,
        equations,
        equation,
        states,
        identity,
        slots,
        subjects: slot_subjects,
        equation_domain: states,
        semantic_values: elements.iter().map(|r| (Scalar::Unit, *r)).collect(),
        equation_values: elements.iter().map(|r| (Scalar::Unit, *r)).collect(),
        free: vec![],
        state_type: Type::Unit,
        equation_parameters: point,
        semantic_checked: 1,
        equation_checked: 1,
        semantic_action: identity,
        semantic_solution_domain: candidates,
        semantic_parameters: elements.iter().map(|r| (*r, vec![*r])).collect(),
    })
}
#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    target: NodeRef,
    laws: &[NodeRef],
    truth: &[bool],
    patches: &[Support],
    law_supports: &[Support],
    global: Support,
    readings: &[Json],
    read_supports: &[Support],
    reading_refs: &[NodeRef],
    projections: &[Projection],
    locals: &[Local],
    finite_model: Option<&finite_model::Model>,
    information: Option<&Information>,
    local_scope: &Scope,
    c: &mut Control,
) -> Result<Built, ValidationFailure> {
    let integer_ring = if finite_model.is_some_and(|m| m.affine_equations) {
        Some(b.push(NodeType::Construction(T::Ring), "ring",
            Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str(integer::coefficient_name()))]), vec![], None, None)?)
    } else { None };
    let mut supports = vec![global];
    let mut linear_reads = vec![information.map(|i| i.identity(c)).transpose()?];
    let mut patch_indices = vec![];
    for (p, patch) in patches.iter().enumerate() {
        let read = information.map(|i| i.patches[p].clone());
        let i = if let Some(i) = mixed_read::find(&supports, &linear_reads, patch, &read, c)? {
            i
        } else {
            supports.push(patch.clone());
            linear_reads.push(read);
            supports.len() - 1
        };
        if !patch_indices.contains(&i) {
            patch_indices.push(i);
        }
    }
    let unit = change_result::value(b, &Scalar::Unit)?;
    let mut projected = BTreeMap::new();
    let mut contexts = vec![];
    let mut states = vec![];
    let mut context_index = 0;
    while context_index < supports.len() {
        let support = &supports[context_index];
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        let mut selected = vec![];
        for (i, required) in law_supports.iter().enumerate() {
            if if let Some(info) = information {
                info.visible_law(support, linear_reads[context_index].as_ref().ok_or("アフィン読取りがない")?, required, i, c)?
            } else { support.contains(required) } { selected.push(i); }
        }
        let context_laws = selected.iter().map(|i| laws[*i]).collect::<Vec<_>>();
        let holds = selected.iter().all(|i| truth[*i]);
        let state = if let Some(model) = finite_model {
            finite_state::build(env, b, target, &context_laws, &selected, support, model, integer_ring, linear_reads[context_index].as_ref(), c)?
        } else {
            state(
                env,
                b,
                target,
                &context_laws,
                &support.positions,
                holds,
                unit,
                c,
            )?
        };
        let mut visible = vec![];
        for (i, rs) in read_supports.iter().enumerate() {
            if support.contains(rs) && mixed_read::contains(&linear_reads[context_index], &information.map(|x| x.reads[i].clone()), c)? { visible.push(i); }
        }
        let mut selected_locals = vec![];
        for (i, local) in locals.iter().enumerate() {
            if support.contains(&local.support) && mixed_read::contains(&linear_reads[context_index], &information.map(|x| x.patches[i].clone()), c)? { selected_locals.push(local); }
        }
        let mut dependencies = visible
            .iter()
            .flat_map(|i| reading_refs[2 * i..2 * i + 2].iter().copied())
            .chain(
                selected_locals
                    .iter()
                    .flat_map(|local| local.arguments.iter().copied()),
            )
            .collect::<Vec<_>>();
        let mut context_readings = visible
            .iter()
            .map(|i| readings[*i].clone())
            .collect::<Vec<_>>();
        let mut selected_projections: Vec<&Projection> = vec![];
        for (i, p) in projections.iter().enumerate() {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            if !support.contains(&p.support)
                || !mixed_read::contains(&linear_reads[context_index], &information.map(|x| x.reading(None, &p.support.visible, c)).transpose()?, c)?
                || visible
                    .iter()
                    .any(|j| read_supports[*j].contains(&p.support))
                || selected_projections
                    .iter()
                    .any(|q| q.support == p.support && q.values == p.values)
            {
                continue;
            }
            let (expression, image) = if let Some(pair) = projected.get(&i) {
                *pair
            } else {
                let pair = project(b, reading_refs[2 * p.read], p, information.map(|i| i.slots()).unwrap_or(&[]))?;
                projected.insert(i, pair);
                pair
            };
            context_readings.push(Json::obj([
                ("expression", expression.wire()),
                ("type", p.ty.clone().wire()),
                ("domain", image.wire()),
            ]));
            dependencies.extend([expression, image]);
            selected_projections.push(p);
        }
        let local_instances = selected_locals
            .iter()
            .flat_map(|local| local.instances.iter().cloned())
            .collect::<Vec<_>>();
        let context = b.push(
            NodeType::Construction(T::Context),
            "context",
            Json::obj([
                ("base", target.wire()),
                ("locals", Json::Arr(local_instances)),
                ("carrier", Json::Arr(support.carrier.clone())),
                ("dependencies", state.slots.clone()),
                ("readings", Json::Arr(context_readings)),
                ("law_coordinates", refs(&context_laws)),
            ]),
            std::iter::once(target)
                .chain(context_laws)
                .chain(dependencies)
                .chain(state.subjects.iter().copied())
                .collect(),
            None,
            None,
        )?;
        b.parts[context.0 - b.base].scope.merge(local_scope);
        contexts.push(context);
        states.push(state);
        // 完成したcontextを先に保持し、引戻し閉包を一つずつ拡張する。
        for j in 0..context_index {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            let intersection = supports[context_index].intersect(&supports[j]);
            let read = mixed_read::intersect(&linear_reads[context_index], &linear_reads[j], c)?;
            if mixed_read::find(&supports, &linear_reads, &intersection, &read, c)?.is_none() {
                supports.push(intersection);
                linear_reads.push(read);
            }
        }
        context_index += 1;
    }
    let mut arrows = BTreeMap::new();
    let mut maps = vec![];
    let mut restrictions = vec![];
    let mut restriction_refs = vec![];
    let mut coefficient_refs = vec![];
    let mut coefficient_values = vec![];
    let mut integer_coefficients = BTreeMap::new();
    let mut integer_projections = BTreeMap::new();
    for (v, small) in supports.iter().enumerate() {
        for (w, big) in supports.iter().enumerate() {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            if !big.contains(small) || !mixed_read::contains(&linear_reads[w], &linear_reads[v], c)? {
                continue;
            }
            let semantic_pairs = finite_state::restriction(&states[w], &states[v], false, c)?;
            let equation_pairs = finite_state::restriction(&states[w], &states[v], true, c)?;
            let restriction = if v == w && finite_model.is_none() {
                states[v].identity
            } else {
                state_map(b, states[w].states, states[v].states, &semantic_pairs)?
            };
            let equation_restriction = if integer_ring.is_some() {
                let (map, coefficient, matrix, projection) = mixed_equation::restriction(b, &states[w], &states[v], c)?;
                coefficient_refs.push(coefficient);
                integer_coefficients.insert((v,w),(matrix,vec![]));
                integer_projections.insert((v,w),projection);
                map
            } else if finite_model.is_some() {
                state_map(
                    b,
                    states[w].equation_domain,
                    states[v].equation_domain,
                    &equation_pairs,
                )?
            } else {
                restriction
            };
            let images = small
                .carrier
                .iter()
                .map(|value| {
                    big.carrier
                        .iter()
                        .position(|x| x == value)
                        .map(|i| Json::Nat(i as u64))
                        .ok_or_else(|| ValidationFailure::from("contextの包含像がない"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let arrow = b.push(
                NodeType::Construction(T::ContextMap),
                "context_map",
                Json::obj([
                    ("source", contexts[v].wire()),
                    ("target", contexts[w].wire()),
                    ("images", Json::Arr(images)),
                    (
                        "restrictions",
                        refs(&if restriction == equation_restriction {
                            vec![restriction]
                        } else {
                            vec![restriction, equation_restriction]
                        }),
                    ),
                ]),
                vec![contexts[v], contexts[w], restriction, equation_restriction],
                None,
                None,
            )?;
            arrows.insert((v, w), arrow);
            maps.push(arrow);
            if integer_ring.is_some() {
                let coefficient=*coefficient_refs.last().ok_or("アフィン係数の制限がない")?;
                coefficient_values.push(Json::obj([("side",Json::str("equation")),("arrow",arrow.wire()),("map",coefficient.wire())]));
            }
            restriction_refs.extend([restriction, equation_restriction]);
            for (side, restriction) in [
                ("equation", equation_restriction),
                ("semantic", restriction),
            ] {
                restrictions.push(Json::obj([
                    ("side", Json::str(side)),
                    ("arrow", arrow.wire()),
                    ("map", restriction.wire()),
                ]));
            }
        }
    }
    let mut overlaps = vec![];
    for &left in &patch_indices {
        for &right in &patch_indices {
            c.checkpoint(crate::control::Checkpoint::Localize)?;
            let intersection = supports[left].intersect(&supports[right]);
            let read = mixed_read::intersect(&linear_reads[left], &linear_reads[right], c)?;
            let i = mixed_read::find(&supports, &linear_reads, &intersection, &read, c)?.ok_or("交わりcontextがない")?;
            let lp = arrows[&(i, left)];
            let rp = arrows[&(i, right)];
            overlaps.push(b.push(
                NodeType::Construction(T::Overlap),
                "context",
                Json::obj([
                    ("left", contexts[left].wire()),
                    ("right", contexts[right].wire()),
                    ("context", contexts[i].wire()),
                    ("left_projection", lp.wire()),
                    ("right_projection", rp.wire()),
                ]),
                vec![contexts[left], contexts[right], contexts[i], lp, rp],
                None,
                None,
            )?);
        }
    }
    let adequate = supports[0].carrier.iter().all(|x| {
        patch_indices
            .iter()
            .any(|i| supports[*i].carrier.contains(x))
    }) && supports[0].positions.iter().all(|x| {
        patch_indices
            .iter()
            .any(|i| supports[*i].positions.contains(x))
    }) && if let Some(info) = information { info.adequate(patches, law_supports, c)? } else { law_supports.iter().all(|law| patches.iter().any(|patch| patch.contains(law))) };
    if !adequate {
        return Err("暗黙支持coverが全体を被覆しない".into());
    }
    let adequacy = b.proposition(
        "cover_adequate",
        contexts.clone(),
        vec![],
        Decision::Established,
    )?;
    let patch_refs = patch_indices
        .iter()
        .map(|i| contexts[*i])
        .collect::<Vec<_>>();
    let cover = b.push(
        NodeType::Construction(T::Cover),
        "cover",
        Json::obj([
            ("base", contexts[0].wire()),
            ("patches", refs(&patch_refs)),
            ("overlaps", refs(&overlaps)),
            ("adequacy", adequacy.wire()),
        ]),
        std::iter::once(contexts[0])
            .chain(patch_refs)
            .chain(overlaps)
            .chain([adequacy])
            .collect(),
        None,
        None,
    )?;
    let (topology, matching_checks) = topology(b, &supports, &contexts, &maps, cover, &arrows, &patch_indices)?;
    let mut intersections = vec![];
    for (i, a) in supports.iter().enumerate() {
        let mut row = vec![];
        for (j, z) in supports.iter().enumerate() {
            let read = mixed_read::intersect(&linear_reads[i], &linear_reads[j], c)?;
            row.push(mixed_read::find(&supports, &linear_reads, &a.intersect(z), &read, c)?.ok_or("交わりcontextがない")?);
        }
        intersections.push(row);
    }
    let mut integer = if integer_ring.is_some() {
        Some(mixed_equation::diagram(finite_model.ok_or("アフィン方程式のmodelがない")?, &states, &intersections, &contexts,
            &patch_indices,cover,laws,integer_coefficients,integer_projections,c)?)
    } else {None};
    let mut checks = vec![];
    let mut summaries = vec![];
    for (side, equation_side) in [("semantic", false), ("equation", true)] {
        let summary = if equation_side && integer.is_some() {None} else {
            Some(finite_state::summary(&states, &intersections, &patch_indices, 0, equation_side, c)?)
        };
        let cover_holds = if let Some(summary)=&summary {finite_state::bijective(summary,c)?} else {
            integer::linear::glues(integer.as_ref().ok_or("アフィン図式がない")?,&patch_indices,0,false,c)?
        };
        let mut topology_holds=true;
        for (w,sources) in &matching_checks {
            topology_holds &= if equation_side && integer.is_some() {
                integer::linear::glues(integer.as_ref().ok_or("アフィン図式がない")?,sources,*w,false,c)?
            } else {finite_state::bijective(&finite_state::summary(&states,&intersections,sources,*w,equation_side,c)?,c)?};
        }
        for (scope, object, holds) in [("cover",cover,cover_holds),("topology",topology,topology_holds)] {
            let proposition=b.proposition("sheaf_condition",std::iter::once(object)
                .chain(restriction_refs.iter().skip(usize::from(equation_side)).step_by(2).copied()).collect(),vec![],
                if holds {Decision::Established}else{Decision::Refuted})?;
            checks.push((proposition,Json::obj([("scope",Json::str(scope)),("side",Json::str(side)),("proposition",proposition.wire())])));
        }
        summaries.push(summary);
    }
    if let Some(diagram)=&mut integer {diagram.sheaf_conditions=checks.iter().map(|(r,_)|*r).collect();}
    let finite=if finite_model.is_some(){Some(Finite {
        semantic:summaries.remove(0).ok_or("有限意味状態がない")?,equation:summaries.remove(0),
    })}else{None};
    let mut fields = BTreeMap::from([
        ("base".into(), target.wire()),
        ("laws".into(), refs(laws)),
        ("contexts".into(), refs(&contexts)),
        ("maps".into(), refs(&maps)),
        ("cover".into(), cover.wire()),
        ("topology".into(), topology.wire()),
        (
            "semantic_states".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("parameters", s.semantic.wire()),
                            ("state_image", s.states.wire()),
                            ("action", s.semantic_action.wire()),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "equation_states".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("space", s.equations.wire()),
                            ("solutions", s.equation.wire()),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("restrictions".into(), Json::Arr(restrictions)),
        (
            "state_comparisons".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("map", s.identity.wire()),
                            ("conditions", Json::Arr(vec![])),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "sheaf_checks".into(),
            Json::Arr(checks.iter().map(|(_, v)| v.clone()).collect()),
        ),
    ]);
    for name in [
        "coefficients",
        "coefficient_restrictions",
        "actions",
        "presentations",
        "polynomial_inclusions",
        "residual_restrictions",
        "conditions",
    ] {
        fields.insert(name.into(), Json::Arr(vec![]));
    }
    if integer.is_some() {
        fields.insert("coefficients".into(),Json::Arr(contexts.iter().zip(&states).map(|(context,s)| {
            let state=s.integer.as_ref().ok_or("アフィン係数がない")?;
            Ok(Json::obj([("side",Json::str("equation")),("context",context.wire()),("module",state.coefficients.wire())]))
        }).collect::<Result<Vec<_>,ValidationFailure>>()?));
        fields.insert("coefficient_restrictions".into(),Json::Arr(coefficient_values));
    }
    if let Some(model) = finite_model {
        fields.insert("change".into(), Json::str(&model.change));
    }
    let system = b.push(
        NodeType::Construction(T::LocalSystem),
        "local_system",
        Json::Obj(fields),
        std::iter::once(target)
            .chain(contexts)
            .chain(maps)
            .chain([cover, topology])
            .chain(laws.iter().copied())
            .chain(states.iter().flat_map(|s| {
                [
                    s.semantic,
                    s.states,
                    s.equations,
                    s.equation,
                    s.identity,
                    s.semantic_action,
                    s.equation_domain,
                ]
            }))
            .chain(checks.iter().map(|(r, _)| *r))
            .chain(restriction_refs)
            .chain(coefficient_refs)
            .chain(states.iter().filter_map(|s|s.integer.as_ref().map(|x|x.coefficients)))
            .collect(),
        None,
        None,
    )?;
    Ok(Built {
        integer,
        finite,
        system,
        adequacy,
        point: states[0].point,
        semantic: states[0].semantic,
        equation: states[0].equation,
        states: states[0].states,
        patch_count: patch_indices.len(),
    })
}

pub(super) fn topology(
    b: &mut Builder<'_>, supports: &[Support], contexts: &[NodeRef], maps: &[NodeRef],
    cover: NodeRef, arrows: &BTreeMap<(usize, usize), NodeRef>, patch_indices: &[usize],
) -> Result<(NodeRef, Vec<(usize, Vec<usize>)>), ValidationFailure> {
    // 唯一の生成coverを各contextに引き戻すと、真の部分contextでは恒等射を含む。
    // 従って生成位相は各最大篩と、全体上のpatchで生成した篩(およびその上位篩)である。
    // 全体以外はすべてpatch以下なので、上位篩は生成篩自身と最大篩だけ。
    let mut sieves = vec![];
    let mut matching_checks = vec![];
    for w in 0..supports.len() {
        let sources = (0..supports.len())
            .filter(|v| arrows.contains_key(&(*v, w)))
            .collect::<Vec<_>>();
        matching_checks.push((w, sources.clone()));
        sieves.push(Json::obj([
            ("base", contexts[w].wire()),
            (
                "arrows",
                refs(&sources.iter().map(|v| arrows[&(*v, w)]).collect::<Vec<_>>()),
            ),
        ]));
    }
    if !patch_indices.contains(&0) {
        let sources = (0..supports.len())
            .filter(|v| {
                patch_indices
                    .iter()
                    .any(|p| arrows.contains_key(&(*v,*p)))
            })
            .collect::<Vec<_>>();
        matching_checks.push((0, sources.clone()));
        sieves.push(Json::obj([
            ("base", contexts[0].wire()),
            (
                "arrows",
                refs(&sources.iter().map(|v| arrows[&(*v, 0)]).collect::<Vec<_>>()),
            ),
        ]));
    }
    let topology = b.push(
        NodeType::Construction(T::Topology),
        "topology",
        Json::obj([
            ("contexts", refs(&contexts)),
            ("maps", refs(&maps)),
            ("generators", refs(&[cover])),
            ("covering_sieves", Json::Arr(sieves)),
        ]),
        contexts
            .iter()
            .chain(maps)
            .copied()
            .chain([cover])
            .collect(),
        None,
        None,
    )?;
    Ok((topology, matching_checks))
}
