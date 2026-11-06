//! 元入力からの共有問題生成と、既存有限解集合への接続。
use super::*;

pub(super) fn prepare(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    let _selected = env.enter_architecture(g)?;
    let mut architecture = architecture_result::build(prepared.shared_inputs(), env, g, r, c)?;
    if let Some(old) = env.state.architecture_ref() {
        architecture.reference = old;
    }
    let mut inputs = vec![architecture.reference];
    let internal = if let Some(a) = r.arguments.iter().find(|a| a.name == "internal") {
        let (at, values) = scalar_set(env, g, &a.value)?;
        inputs.push(at);
        values
    } else {
        vec![]
    };
    let mut binding_values = BTreeMap::new();
    for a in &r.arguments {
        if let Some(name) = a.name.strip_prefix("bind.") {
            if matches!(a.value, Selector::Answer { .. }) {
                inputs.push(reference(env, g, &a.value)?);
            }
            binding_values.insert(name.to_owned(), change_search::selector(env, g, &a.value)?);
        }
    }
    let fixed = env.fixed_values();
    let mut reused = None;
    if architecture.complete {
        for n in &g.nodes {
            tick(c)?;
            let Some(Payload::Construction(v)) = &n.payload else {
                continue;
            };
            let D::SharedRepair(d) = &v.data else {
                continue;
            };
            if d.source.request.kind != QuestionKind::Prepare
                || d.source.request.declaration() != r.declaration()
            {
                continue;
            }
            let Some(s) = &d.source.shared else {
                continue;
            };
            if s.witness.construction().root() == architecture.witness.construction().root()
                && s.witness.construction().reading()
                    == architecture.witness.construction().reading()
                && s.compiled.fixed == fixed
                && s.compiled
                    .bindings
                    .iter()
                    .cloned()
                    .collect::<BTreeMap<_, _>>()
                    == binding_values
                && r.arguments.iter().any(|a| {
                    a.name == "using"
                        && matches!(&a.value,Selector::Declaration {name}if *name==s.change)
                })
            {
                reused = Some(s.compiled.clone());
                break;
            }
        }
    }
    let compilation = if let Some(compiled) = reused {
        Compilation::Ready(compiled)
    } else if architecture.complete {
        crate::observed::environment::repair_problem::compile(env, g, &architecture.witness, r, c)?
    } else {
        Compilation::Pending(
            architecture
                .reasons
                .iter()
                .flat_map(|r| r.missing.iter().cloned())
                .collect(),
        )
    };
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let compiled = match compilation {
        Compilation::Pending(missing) => {
            let claim = condition(&mut b, r, inputs.clone(), Decision::Undetermined)?;
            let mut a = answer(r, claim, Decision::Undetermined, BTreeMap::new(), &b);
            a.reasons.push(Reason {
                kind: if missing.is_empty() {
                    ReasonKind::UnsupportedAlgorithm {
                        question: r.kind,
                        operand_types: vec![Type::Bool],
                        method: "finite_repair_relation".into(),
                    }
                } else {
                    ReasonKind::Missing
                },
                request: r.id.clone(),
                dependencies: vec![architecture.reference],
                missing,
                location: None,
            });
            return Ok(Source {
                base,
                parts: b.parts,
                answer: a,
                request: r.clone(),
                witness: architecture.witness,
                shared: None,
                range: None,
                ranges: BTreeMap::new(),
                chosen: None,
                inputs,
                context: g.active,
            });
        }
        Compilation::Ready(compiled) => compiled,
    };
    let origin = Witness::Architecture(architecture.witness.clone());
    let change = r
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "using" {
                if let Selector::Declaration { name } = &a.value {
                    Some(name.clone())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .ok_or(internal!("修復問題のchangeがない"))?;
    let Signature::Change { params, guard, .. } =
        &origin.inputs().law().declarations()[&change].signature
    else {
        unreachable!()
    };
    let subjects = compiled
        .subjects
        .iter()
        .map(|v| change_result::value(&mut b, v))
        .collect::<Result<Vec<_>, _>>()?;
    let valid_internal = internal.iter().all(|v| compiled.subjects.contains(v));
    if !valid_internal {
        let claim = condition(&mut b, r, inputs.clone(), Decision::Refuted)?;
        let mut a = answer(r, claim, Decision::Refuted, BTreeMap::new(), &b);
        fail(&mut a, "prepare");
        return Ok(Source {
            base,
            parts: b.parts,
            answer: a,
            request: r.clone(),
            witness: architecture.witness,
            shared: None,
            range: None,
            ranges: BTreeMap::new(),
            chosen: None,
            inputs,
            context: g.active,
        });
    }
    let internal = compiled
        .subjects
        .iter()
        .map(|v| internal.contains(v))
        .collect::<Vec<_>>();
    let requirements = change_result::requirements(&mut b, env, &compiled.requirements, c)?;
    let mut binding_refs = vec![];
    let mut bindings = vec![];
    for (name, value) in &compiled.bindings {
        let at = change_result::value(&mut b, value)?;
        binding_refs.push(at);
        bindings.push(Json::obj([("name", Json::str(name)), ("value", at.wire())]));
    }
    let mut factors = vec![];
    for ty in &compiled.parameter_types {
        tick(c)?;
        factors.push(b.push(
            NodeType::Domain,
            "domain",
            Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
            vec![],
            None,
        )?);
    }
    let parameters = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([("kind", Json::str("product")), ("factors", refs(&factors))]),
        factors,
        None,
    )?;
    let mut slots = vec![];
    let mut state_types = vec![];
    for o in &compiled.outputs {
        slots.push(Json::obj([
            ("subject", subjects[o.subject].wire()),
            (
                "field",
                Json::str(
                    o.fact
                        .field
                        .as_deref()
                        .ok_or(internal!("更新fieldがない"))?,
                ),
            ),
        ]));
        state_types.push(compiled.domains[o.column][0].ty());
    }
    let state_space = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", architecture.reference.wire()),
            ("slots", Json::Arr(slots)),
            ("state_type", Type::Tuple(state_types).wire()),
        ]),
        std::iter::once(architecture.reference)
            .chain(subjects.iter().copied())
            .collect(),
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
            ("change", Json::str(&change)),
            ("instances", refs(&subjects)),
        ]),
        [
            vec![parameters, states, architecture.reference],
            subjects.clone(),
        ]
        .concat(),
        None,
    )?;
    let mut guards = vec![];
    if let Some(guard) = guard {
        let ps = params[1..]
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        for subject in &subjects {
            guards.push(change_result::source_expression(
                &mut b,
                env,
                *guard,
                &[(params[0].name.clone(), *subject)],
                &ps,
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
    let d = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("change")),
            ("base", architecture.reference.wire()),
            ("bindings", Json::Arr(bindings)),
            ("change", Json::str(&change)),
            ("parameters", parameters.wire()),
            ("states", state_space.wire()),
            ("action", action.wire()),
            ("instances", Json::Arr(instances)),
            ("guards", refs(&guards)),
            ("requirements", refs(&requirements)),
        ]),
        [
            vec![architecture.reference, parameters, state_space, action],
            subjects.clone(),
            requirements.clone(),
            guards,
            binding_refs,
        ]
        .concat(),
        None,
    )?;
    let in_refs = subjects
        .iter()
        .zip(&internal)
        .filter_map(|(r, on)| on.then_some(*r))
        .collect::<Vec<_>>();
    let unit_refs = subjects
        .iter()
        .zip(&internal)
        .filter_map(|(r, on)| (!on).then_some(*r))
        .collect::<Vec<_>>();
    let inside = domain(&mut b, &params[0].ty.erase(), &in_refs)?;
    let units = domain(&mut b, &params[0].ty.erase(), &unit_refs)?;
    let problem = b.push(
        NodeType::Construction(T::RepairProblem),
        "repair_problem",
        Json::obj([
            ("domain", d.wire()),
            ("requirements", refs(&requirements)),
            ("internal", inside.wire()),
            ("units", units.wire()),
        ]),
        [vec![d, inside, units], requirements.clone(), inputs.clone()].concat(),
        None,
    )?;
    b.parts[problem.0 - base].scope.merge(&compiled.scope);
    b.parts[problem.0 - base]
        .support
        .extend(compiled.support.iter().cloned());
    b.parts[problem.0 - base].support.sort();
    b.parts[problem.0 - base].support.dedup();
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
        witness: architecture.witness.clone(),
        base: architecture.reference,
        domain: d,
        problem: Some(problem),
        legacy_set: None,
        subjects,
        requirements,
        internal,
        change,
        root_type,
    });
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness: architecture.witness,
        shared: Some(shared),
        range: None,
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context: g.active,
    })
}
// 従来の完全な有限SolutionSetも同じ元座標で選択する。元producerの環境と検査を使う。
pub(super) fn legacy(
    env: &Environment<'_>,
    g: &Graph,
    set: NodeRef,
    c: &Control,
) -> Result<Arc<Shared>, ValidationFailure> {
    let input = change_result::candidate_input(env, g, set, c)?;
    if input.search.linear.is_some() || input.search.rational.is_some() {
        return Err(ValidationFailure::UnsupportedExpression {
            location: archsig_common::issue::Location::Law { span: (0, 0) },
            feature: "candidate requires a complete finite SolutionSet".into(),
        });
    }
    let origin = Witness::Architecture(input.witness.clone());
    let request = origin.request();
    let compiled = env.with_request_context(g, request, || {
        let _a = env.enter_architecture(g)?;
        crate::observed::environment::repair_problem::compile(env, g, &input.witness, request, c)
    })?;
    let Compilation::Ready(compiled) = compiled else {
        return Err(ValidationFailure::UnsupportedExpression {
            location: archsig_common::issue::Location::Law { span: (0, 0) },
            feature: "finite candidate reconstruction requires a known baseline".into(),
        });
    };
    let Some(Payload::Construction(v)) = &g.get(set)?.payload else {
        return Err(internal!("元解集合がnativeでない").into());
    };
    let (domain, _) = v
        .project(&[ProjectionStep::Field("domain".into())])
        .ok_or(internal!("元候補域がない"))?;
    let Some(Payload::Construction(d)) = &g.get(domain)?.payload else {
        return Err(internal!("元候補域がnativeでない").into());
    };
    let wire = d.wire();
    let Some(Json::Arr(rows)) = fields(&wire).and_then(|f| f.get("instances")) else {
        return Err(internal!("元change instanceがない").into());
    };
    let mut subjects = vec![];
    for scalar in &compiled.subjects {
        let mut selected = None;
        for row in rows {
            let Some(subject) = fields(row).and_then(|f| f.get("subject")) else {
                continue;
            };
            for r in d.arguments() {
                if r.wire() == *subject && g.scalar(r).ok() == Some(scalar) {
                    selected = Some(r);
                    break;
                }
            }
        }
        subjects.push(selected.ok_or(internal!("元change instanceの参照がない"))?);
    }
    let set_wire = v.wire();
    let mut requirements = vec![];
    if let Some(Json::Arr(rows)) = fields(&set_wire).and_then(|f| f.get("requirements")) {
        for value in rows {
            requirements.push(
                v.arguments()
                    .into_iter()
                    .find(|r| r.wire() == *value)
                    .ok_or(internal!("元Law instanceの参照がない"))?,
            );
        }
    }
    let change = request
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "using" {
                if let Selector::Declaration { name } = &a.value {
                    Some(name.clone())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .ok_or(internal!("元changeがない"))?;
    let root = input.witness.construction().root();
    let root_type = env
        .indexes
        .subject(&root.snapshot, &root.subject)?
        .ty
        .to_string();
    let internal = vec![false; subjects.len()];
    Ok(Arc::new(Shared {
        compiled,
        witness: input.witness,
        base: input.architecture,
        domain,
        problem: None,
        legacy_set: Some(set),
        subjects,
        requirements,
        internal,
        change,
        root_type,
    }))
}
