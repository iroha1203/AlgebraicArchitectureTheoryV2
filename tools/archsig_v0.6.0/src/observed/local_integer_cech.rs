//! 順序付きpatch tupleから微分を構成し、整数核/像の商と局所差の類を求める。
use super::*;
use crate::observed::change_result::linear_result as wire;
use num_traits::One;
struct Level {
    tuples: Vec<Vec<usize>>,
    contexts: Vec<usize>,
    offsets: Vec<usize>,
    rank: usize,
}
fn level(diagram: &Diagram, states: &[linear::Fiber], tuples: Vec<Vec<usize>>) -> Level {
    let mut contexts = vec![];
    let mut offsets = vec![];
    let mut rank = 0;
    for tuple in &tuples {
        let mut context = tuple[0];
        for i in tuple.iter().skip(1) {
            context = diagram.intersections[context][*i];
        }
        contexts.push(context);
        offsets.push(rank);
        rank += states[context].rank;
    }
    Level {
        tuples,
        contexts,
        offsets,
        rank,
    }
}
fn differential(
    diagram: &Diagram,
    states: &[linear::Fiber],
    from: &Level,
    to: &Level,
    semantic: bool,
    c: &mut Control,
) -> Result<Matrix, ValidationFailure> {
    let mut d = vec![vec![Z::zero(); from.rank]; to.rank];
    for (i, tuple) in to.tuples.iter().enumerate() {
        for omitted in 0..tuple.len() {
            c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
            let face = tuple
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != omitted)
                .map(|(_, x)| *x)
                .collect::<Vec<_>>();
            let j = from
                .tuples
                .iter()
                .position(|t| *t == face)
                .ok_or("Čechの面がない")?;
            let pair = &diagram.restrictions[&(to.contexts[i], from.contexts[j])];
            let map = if semantic { &pair.1 } else { &pair.0 };
            for r in 0..states[to.contexts[i]].rank {
                for s in 0..states[from.contexts[j]].rank {
                    if omitted % 2 == 0 {
                        d[to.offsets[i] + r][from.offsets[j] + s] += &map[r][s];
                    } else {
                        d[to.offsets[i] + r][from.offsets[j] + s] -= &map[r][s];
                    }
                }
            }
        }
    }
    Ok(d)
}
pub(in crate::observed::local_result) fn diagnose(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    target: NodeRef,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    diagram: &Diagram,
    degree: u64,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let semantic = request.arguments.iter().any(|a| {
        a.name == "side" && matches!(&a.value,Selector::Enum { value } if value == "semantic")
    });
    if semantic && diagram.equation_only {
        return Err("有限意味状態を整数係数の診断へ渡せない".into());
    }
    let states = if semantic {
        &diagram.semantic
    } else {
        &diagram.equation
    };
    let mut levels = vec![level(
        diagram,
        states,
        diagram.patches.iter().map(|i| vec![*i]).collect(),
    )];
    for _ in 0..=degree {
        c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
        let mut tuples = vec![];
        for tuple in &levels.last().ok_or("Čechの次数がない")?.tuples {
            for patch in &diagram.patches {
                c.checkpoint(crate::observed::control::Checkpoint::Localize)?;
                let mut next = tuple.clone();
                next.push(*patch);
                tuples.push(next);
            }
        }
        levels.push(level(diagram, states, tuples));
    }
    let mut differentials = vec![];
    for i in 0..levels.len() - 1 {
        differentials.push(differential(
            diagram,
            states,
            &levels[i],
            &levels[i + 1],
            semantic,
            c,
        )?);
    }
    let degree_index =
        usize::try_from(degree).map_err(|_| unsupported("診断次数を内部indexに変換できない"))?;
    let zero = vec![vec![]; levels[degree_index].rank];
    let previous = if degree_index == 0 {
        &zero
    } else {
        &differentials[degree_index - 1]
    };
    let previous_rank = if degree_index == 0 {
        0
    } else {
        levels[degree_index - 1].rank
    };
    let cohomology = linear::cohomology(
        previous,
        previous_rank,
        &differentials[degree_index],
        levels[degree_index].rank,
        c,
    )?;
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let saved_witness = witness.clone();
    let result = (|| -> Result<Source, ValidationFailure> {
        let ring = b.push(
            NodeType::Construction(T::Ring),
            "ring",
            Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))]),
            vec![target],
            None,
            None,
        )?;
        let mut modules = vec![];
        let mut maps = vec![];
        for l in &levels {
            modules.push(wire::module(
                &mut b,
                ring,
                l.rank,
                "free",
                vec![diagram.cover],
            )?);
        }
        for (i, d) in differentials.iter().enumerate() {
            maps.push(wire::map(
                &mut b,
                modules[i],
                modules[i + 1],
                d,
                levels[i].rank,
                c,
            )?);
        }
        let complex = b.push(
            NodeType::Construction(T::Complex),
            "complex",
            Json::obj([
                ("modules", refs(&modules)),
                ("differentials", refs(&maps)),
                ("last_diagnosable_degree", Json::Nat(degree)),
                ("cover", diagram.cover.wire()),
                ("convention", Json::str("ordered")),
            ]),
            modules
                .iter()
                .chain(&maps)
                .copied()
                .chain([diagram.cover])
                .collect(),
            None,
            None,
        )?;
        let cycles = wire::module(
            &mut b,
            ring,
            cohomology.cycle_rank,
            "kernel",
            vec![maps[degree_index]],
        )?;
        let boundaries = wire::module(
            &mut b,
            ring,
            cohomology.boundary_rank,
            "image",
            if degree_index == 0 {
                vec![]
            } else {
                vec![maps[degree_index - 1]]
            },
        )?;
        let rank = cohomology.torsion.len() + cohomology.free_rank;
        let mut relations = vec![];
        let mut relation_refs = vec![];
        for (i, divisor) in cohomology.torsion.iter().enumerate() {
            let mut row = vec![];
            for j in 0..rank {
                row.push(change_result::value(
                    &mut b,
                    &Scalar::Z(if i == j { divisor.clone() } else { Z::zero() }),
                )?);
            }
            relations.push(refs(&row));
            relation_refs.extend(row);
        }
        let module = b.push(
            NodeType::Construction(T::Module),
            "module",
            Json::obj([
                ("ring", ring.wire()),
                (
                    "generators",
                    Json::Arr(
                        (0..rank)
                            .map(|i| {
                                Json::obj([
                                    ("type", Type::Text.wire()),
                                    ("value", Json::str(format!("e{i}"))),
                                ])
                            })
                            .collect(),
                    ),
                ),
                ("relations", Json::Arr(relations)),
                ("free_rank", Json::Nat(cohomology.free_rank as u64)),
                (
                    "torsion",
                    Json::Arr(
                        cohomology
                            .torsion
                            .iter()
                            .map(|x| Json::str(x.to_string()))
                            .collect(),
                    ),
                ),
                (
                    "construction",
                    Json::obj([
                        ("name", Json::str("quotient")),
                        ("arguments", refs(&[cycles, boundaries])),
                    ]),
                ),
            ]),
            [ring, cycles, boundaries]
                .into_iter()
                .chain(relation_refs)
                .collect(),
            None,
            None,
        )?;
        let inclusion = wire::map(
            &mut b,
            cycles,
            modules[degree_index],
            &cohomology.cycles,
            cohomology.cycle_rank,
            c,
        )?;
        let projection = wire::map(
            &mut b,
            cycles,
            module,
            &cohomology.projection,
            cohomology.cycle_rank,
            c,
        )?;
        let space = b.push(
            NodeType::Construction(T::Cohomology),
            "cohomology",
            Json::obj([
                ("complex", complex.wire()),
                ("degree", Json::Nat(degree)),
                ("cycles", cycles.wire()),
                ("boundaries", boundaries.wire()),
                ("module", module.wire()),
                ("inclusion", inclusion.wire()),
                ("projection", projection.wire()),
            ]),
            vec![complex, cycles, boundaries, module, inclusion, projection],
            None,
            None,
        )?;
        let mut local_sections = vec![];
        let mut class = None;
        let mut claim = None;
        let mut evidence = vec![];
        let mut status = if degree == 1 {
            Decision::Undetermined
        } else {
            Decision::Established
        };
        if degree == 1 && diagram.patches.iter().all(|i| states[*i].origin.is_some()) {
            for i in &diagram.patches {
                let ambient = wire::module(
                    &mut b,
                    ring,
                    diagram.readings[*i].map.len(),
                    "free",
                    vec![diagram.contexts[*i]],
                )?;
                local_sections.push(wire::vector(
                    &mut b,
                    ambient,
                    states[*i].origin.as_ref().ok_or("局所特解がない")?,
                    c,
                )?);
            }
            let mut cocycle = vec![Z::zero(); levels[1].rank];
            for (i, tuple) in levels[1].tuples.iter().enumerate() {
                let context = levels[1].contexts[i];
                let left = states[tuple[0]].origin.as_ref().ok_or("局所特解がない")?;
                let right = states[tuple[1]].origin.as_ref().ok_or("局所特解がない")?;
                let left =
                    linear::apply(&diagram.state_restrictions[&(context, tuple[0])], left, c)?;
                let right =
                    linear::apply(&diagram.state_restrictions[&(context, tuple[1])], right, c)?;
                let delta = right.iter().zip(&left).map(|(r, l)| vec![r - l]).collect();
                let coordinates = linear::coordinates(
                    &states[context].basis,
                    states[context].rank,
                    &delta,
                    1,
                    c,
                )?;
                for (j, row) in coordinates.iter().enumerate() {
                    cocycle[levels[1].offsets[i] + j] = row[0].clone();
                }
            }
            if linear::apply(&differentials[1], &cocycle, c)?
                .iter()
                .any(|v| !v.is_zero())
            {
                return Err("局所差がcocycleでない".into());
            }
            let cycle_coordinates = linear::coordinates(
                &cohomology.cycles,
                cohomology.cycle_rank,
                &cocycle.iter().map(|x| vec![x.clone()]).collect(),
                1,
                c,
            )?
            .into_iter()
            .map(|v| v[0].clone())
            .collect::<Vec<_>>();
            let mut values = linear::apply(&cohomology.projection, &cycle_coordinates, c)?;
            for (v, m) in values.iter_mut().zip(&cohomology.torsion) {
                *v = ((&*v % m) + m) % m;
            }
            let representative = wire::vector(&mut b, modules[1], &cocycle, c)?;
            let coordinates = wire::vector(&mut b, module, &values, c)?;
            let r = b.push(
                NodeType::Construction(T::Class),
                "class",
                Json::obj([
                    ("cohomology", space.wire()),
                    ("representative", representative.wire()),
                    ("coordinates", coordinates.wire()),
                ]),
                vec![space, representative, coordinates],
                None,
                None,
            )?;
            class = Some(r);
            let correction = integer_fiber::solve(&differentials[0], levels[0].rank, &cocycle, c)?;
            let (_, certificate) = wire::smith(
                &mut b,
                ring,
                modules[0],
                &differentials[0],
                &cocycle,
                &correction,
                &[complex, space, r],
                c,
            )?;
            evidence.push(certificate);
            let zero = values.iter().all(Z::is_zero);
            if zero != correction.particular.is_some() {
                return Err("商座標とcoboundary判定が一致しない".into());
            }
            status = if zero {
                Decision::Established
            } else {
                Decision::Refuted
            };
            if let Some(row) = correction.obstruction {
                let annihilator = wire::vector(&mut b, modules[1], &correction.left[row], c)?;
                let pairing = change_result::value(
                    &mut b,
                    &Scalar::Z(correction.transformed_rhs[row].clone()),
                )?;
                let mut data = BTreeMap::from([
                    ("map".into(), maps[0].wire()),
                    ("rhs".into(), representative.wire()),
                    ("annihilator".into(), annihilator.wire()),
                    ("pairing".into(), pairing.wire()),
                ]);
                if row < correction.rank && correction.diagonal[row][row] > Z::one() {
                    data.insert(
                        "modulus".into(),
                        Json::str(correction.diagonal[row][row].to_string()),
                    );
                }
                evidence.push(b.push(
                    NodeType::Evidence,
                    "evidence",
                    Json::obj([
                        ("kind", Json::str("linear_inconsistent")),
                        ("data", Json::Obj(data)),
                    ]),
                    vec![maps[0], representative, annihilator, pairing],
                    None,
                    None,
                )?);
            }
            if let Some(correction) = &correction.particular
                && linear::glues(diagram, &diagram.patches, 0, semantic, c)?
            {
                evidence.push(gluing(
                    env, &mut b, ring, modules[0], correction, diagram, states, &levels[0],
                    &witness, c,
                )?);
            }
            let proposition = b.proposition("class_zero", vec![r], evidence.clone(), status)?;
            b.parts[proposition.0 - base]
                .judgment
                .as_mut()
                .ok_or("類の判断がない")?
                .evidence = evidence.clone();
            claim = Some(proposition);
        }
        let mut conditions = diagram.sheaf_conditions.clone();
        let mut reasons = if diagram.missing.is_empty() {
            vec![]
        } else {
            vec![Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![target],
                missing: diagram.missing.clone(),
                location: None,
            }]
        };
        for i in &diagram.patches {
            let condition = b.proposition(
                "inhabited",
                vec![diagram.solutions[*i][usize::from(semantic)]],
                vec![],
                if !states[*i].known {
                    Decision::Undetermined
                } else if states[*i].origin.is_some() {
                    Decision::Established
                } else {
                    Decision::Refuted
                },
            )?;
            if degree == 1 && states[*i].known && states[*i].origin.is_none() {
                reasons.push(Reason {
                    kind: ReasonKind::ConditionFailed {
                        condition,
                        construction: "diagnostic",
                    },
                    request: request.id.clone(),
                    dependencies: vec![condition],
                    missing: vec![],
                    location: None,
                });
            }
            conditions.push(condition);
        }
        let mut fields = BTreeMap::from([
            ("kind".into(), Json::str("affine_cech")),
            (
                "side".into(),
                Json::str(if semantic { "semantic" } else { "equation" }),
            ),
            ("system".into(), target.wire()),
            ("degree".into(), Json::Nat(degree)),
            ("complex".into(), complex.wire()),
            ("space".into(), space.wire()),
            ("local_sections".into(), refs(&local_sections)),
            ("conditions".into(), refs(&conditions)),
        ]);
        if let Some(r) = class {
            fields.insert("class".into(), r.wire());
        }
        let diagnostic = b.push(
            NodeType::Construction(T::Diagnostic),
            "diagnostic",
            Json::Obj(fields),
            [target, complex, space]
                .into_iter()
                .chain(class)
                .chain(local_sections)
                .chain(conditions)
                .collect(),
            None,
            None,
        )?;
        b.parts[diagnostic.0 - base].reasons = reasons.clone();
        let mut outputs =
            BTreeMap::from([("diagnostic".into(), diagnostic), ("space".into(), space)]);
        if let Some(r) = class {
            outputs.insert("class".into(), r);
        }
        if let Some(r) = claim {
            outputs.insert("proposition".into(), r);
        }
        let answer = Answer {
            id: request.id.clone(),
            status,
            outputs,
            claim,
            evidence,
            reasons,
            scope: b.parts[diagnostic.0 - base].scope.clone(),
        };
        Ok(Source {
            base,
            parts: std::mem::take(&mut b.parts),
            scope_domains: vec![],
            answer,
            request: request.clone(),
            witness,
            system: None,
        })
    })();
    retain_partial(result, b, request, saved_witness)
}

fn gluing(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    ring: NodeRef,
    correction_module: NodeRef,
    correction: &[Z],
    diagram: &Diagram,
    states: &[linear::Fiber],
    level: &Level,
    witness: &ArchitectureWitness,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut equations = vec![];
    let mut rhs = vec![];
    let mut local = vec![];
    for (j, i) in diagram.patches.iter().enumerate() {
        let adjustment = linear::apply(
            &states[*i].basis,
            &correction[level.offsets[j]..level.offsets[j] + states[*i].rank],
            c,
        )?;
        let values = states[*i]
            .origin
            .as_ref()
            .ok_or("補正の局所特解がない")?
            .iter()
            .zip(adjustment)
            .map(|(x, y)| x - y)
            .collect::<Vec<_>>();
        equations.extend(diagram.readings[*i].map.iter().cloned());
        rhs.extend(values.iter().cloned());
        let ambient = wire::module(b, ring, values.len(), "free", vec![diagram.contexts[*i]])?;
        local.push(wire::vector(b, ambient, &values, c)?);
    }
    let global_values = integer_fiber::solve(&equations, diagram.slots.len(), &rhs, c)?
        .particular
        .ok_or("補正した局所族の大域持上げがない")?;
    let origin = states[0]
        .origin
        .as_ref()
        .ok_or("貼り合わせ先の大域fiberが空")?;
    let delta = global_values
        .iter()
        .zip(origin)
        .map(|(x, y)| vec![x - y])
        .collect();
    linear::coordinates(&states[0].basis, states[0].rank, &delta, 1, c)?;
    let ambient = wire::module(
        b,
        ring,
        global_values.len(),
        "free",
        vec![diagram.contexts[0]],
    )?;
    let global = wire::vector(b, ambient, &global_values, c)?;
    let mut assignments = diagram
        .assignments
        .iter()
        .cloned()
        .collect::<BTreeMap<_, _>>();
    for (i, v) in diagram.free[0].iter().zip(&global_values) {
        assignments.insert(diagram.slots[*i].clone(), Scalar::Z(v.clone()));
    }
    let mut evaluated = Environment::try_primitive_valuation(
        env.inputs,
        &assignments.into_iter().collect::<Vec<_>>(),
        c,
    )?
    .ok_or("貼り合わせ証人の元代入が不適合")?;
    evaluated.select_local_object(witness, c)?;
    let mut rechecks = vec![];
    for ((name, bindings), law) in diagram.requirements.iter().zip(&diagram.law_refs) {
        let (row, missing, _) =
            evaluated.local_point(&env.inputs.law().declarations[name], bindings)?;
        let holds = row.application == Some(false)
            || (row.application == Some(true)
                && !row.condition_pending
                && !row.condition_failed
                && (row.guard == Some(false)
                    || (row.guard == Some(true) && row.predicate == Some(true))));
        if !missing.is_empty() || !row.application_missing.is_empty() || !holds {
            return Err("貼り合わせ証人が元Lawの再検査を満たさない".into());
        }
        let check = b.proposition("law_holds", vec![*law], vec![], Decision::Established)?;
        b.parts[check.0 - b.base].arguments.push(global);
        rechecks.push(check);
    }
    let correction = wire::vector(b, correction_module, correction, c)?;
    b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str("gluing")),
            (
                "data",
                Json::obj([
                    ("local", refs(&local)),
                    ("correction", correction.wire()),
                    ("global", global.wire()),
                    ("rechecks", refs(&rechecks)),
                ]),
            ),
        ]),
        local
            .into_iter()
            .chain([correction, global])
            .chain(rechecks)
            .collect(),
        None,
        None,
    )
}
