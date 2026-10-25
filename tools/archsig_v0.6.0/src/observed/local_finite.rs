//! 有限changeを持つ支持局所系の公開構成と両側のmatching診断。
use super::*;
#[allow(clippy::too_many_arguments)]
pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    target: NodeRef,
    original: &ConstructionValue,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let assignments = match &original.data {
        D::Change(d) => d.overrides(g)?,
        D::Quotient(d) => d.overrides(g)?,
        _ => vec![],
    }
    .into_iter()
    .map(|(f, _, v)| (f, v))
    .collect::<Vec<_>>();
    let mut fixed = Environment::try_primitive_valuation(env.inputs, &assignments, c)?
        .ok_or("有限局所系の元Architectureが不適合")?;
    fixed.select_local_object(&witness, c)?;
    let (model, missing) = finite_model::analyze(env, &fixed, g, &witness, request, c)?;
    let Some(model) = model else {
        let using = request
            .arguments
            .iter()
            .find_map(|a| match (&*a.name, &a.value) {
                ("using", Selector::Declaration { name }) => Some(name),
                _ => None,
            })
            .ok_or("欠測した局所change名がない")?;
        let declaration = &env.inputs.law().declarations[using];
        let Signature::Change { params, body, .. } = &declaration.signature else {
            return Err("局所changeの署名がない".into());
        };
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let expression = change_result::source_expression(
            &mut b,
            env,
            *body,
            &[],
            &params
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect::<Vec<_>>(),
        )?;
        b.parts[expression.0 - base].arguments.push(target);
        b.parts[expression.0 - base]
            .scope
            .merge(&g.get(target)?.scope);
        let scope = b.parts[expression.0 - base].scope.clone();
        let reason = Reason {
            kind: ReasonKind::Missing,
            request: request.id.clone(),
            dependencies: vec![expression],
            missing,
            location: Some(Location::Law {
                span: declaration.span,
            }),
        };
        b.parts[expression.0 - base].reasons.push(reason.clone());
        return Ok(Source {
            base,
            parts: b.parts,
            scope_domains: vec![],
            request: request.clone(),
            witness,
            system: None,
            answer: Answer {
                id: request.id.clone(),
                status: Decision::Undetermined,
                outputs: BTreeMap::new(),
                claim: None,
                evidence: vec![],
                scope,
                reasons: vec![reason],
            },
        });
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut laws = vec![];
    let mut expressions = vec![];
    let mut scope_domains = vec![];
    let mut quantifiers = vec![];
    let mut reasons = vec![];
    let mut local_scope = Scope::default();
    let result = (|| -> Result<(Option<geometry::Built>, Vec<Fact>), ValidationFailure> {
        if model.requirements.is_empty() {
            let declaration = &env.inputs.law().declarations[&model.change];
            let Signature::Change { params, body, .. } = &declaration.signature else {
                return Err("局所changeの署名がない".into());
            };
            let expression = change_result::source_expression(
                &mut b, env, *body, &[],
                &params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect::<Vec<_>>(),
            )?;
            b.parts[expression.0 - base].arguments.push(target);
            b.parts[expression.0 - base].scope.merge(&g.get(target)?.scope);
            expressions.push(expression);
        }
        for (name, parameter, values) in &model.universal {
            c.checkpoint(super::super::control::Checkpoint::Localize)?;
            let items = values.iter().map(|v| change_result::value(&mut b, v)).collect::<Result<Vec<_>, _>>()?;
            let reference = domain(&mut b, &parameter.ty.erase(), &items)?;
            scope_domains.push((reference, parameter.ty.erase()));
            quantifiers.push((name, Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: parameter.name.clone(),
                ty: parameter.ty.erase(),
                domain: Some(reference),
                occurrence: parameter.span,
                context: Some(env.current_context(g)),
            }));
        }
        for (name, bindings) in &model.requirements {
            c.checkpoint(super::super::control::Checkpoint::Localize)?;
            let law = &env.inputs.law().declarations[name];
            let Signature::Law {
                role, body, guard, ..
            } = law.signature
            else {
                return Err("有限局所Lawの署名がない".into());
            };
            let bindings = bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let expression = change_result::source_expression(&mut b, env, body, &bindings, &[])?;
            b.parts[expression.0 - base].scope.merge(&model.scope);
            for (_, quantifier) in quantifiers.iter().filter(|(law, _)| *law == name) {
                b.parts[expression.0 - base].arguments.extend(quantifier.domain);
                b.parts[expression.0 - base].scope.quantifiers.push(quantifier.clone());
            }
            expressions.push(expression);
            let guard = guard
                .map(|id| change_result::source_expression(&mut b, env, id, &bindings, &[]))
                .transpose()?;
            let mut fields = BTreeMap::from([
                ("name".into(), Json::str(name)),
                (
                    "role".into(),
                    Json::str(if role == crate::law::ast::Role::Required {
                        "required"
                    } else {
                        "optional"
                    }),
                ),
                (
                    "occurrence".into(),
                    crate::result::location_wire(&Location::Law { span: law.span }),
                ),
                (
                    "bindings".into(),
                    Json::Arr(
                        bindings
                            .iter()
                            .map(|(n, r)| Json::obj([("name", Json::str(n)), ("value", r.wire())]))
                            .collect(),
                    ),
                ),
                ("body".into(), expression.wire()),
            ]);
            if let Some(guard) = guard {
                fields.insert("guard".into(), guard.wire());
            }
            laws.push(
                b.push(
                    NodeType::LawInstance,
                    "law_instance",
                    Json::Obj(fields),
                    std::iter::once(expression)
                        .chain(guard)
                        .chain(bindings.iter().map(|(_, r)| *r))
                        .collect(),
                    None,
                    None,
                )?,
            );
        }
        if !model.missing.is_empty() {
            return Err(unsupported("有限局所系に欠測がある"));
        }
        let mut readings = vec![];
        let mut read_refs = vec![];
        let mut read_supports = vec![];
        let locals = env.inputs.law().declarations.values().filter(|d|
            d.reading == witness.construction().reading() && matches!(d.signature, Signature::Local { .. })
        ).collect::<Vec<_>>();
        let mut information = if model.integer_equations && !locals.is_empty() { Some(geometry::Information::new(&fixed, &model)?) } else { None };
        let mut patches = vec![];
        let mut local_instances = vec![];
        let mut projections = vec![];
        if locals.is_empty() && model.integer_equations {
            patches=model.law_supports.clone();
            for slot in &model.slots {
                if patches.iter().any(|p|p.positions.contains(slot)){continue;}
                let subject=fixed.subject(&slot.snapshot,&slot.subject)?;
                let value=Scalar::Subject{snapshot:slot.snapshot.clone(),subject:slot.subject.clone(),entity:subject.ty.clone()};
                patches.push(geometry::Support{carrier:vec![Json::obj([("type",value.ty().wire()),("value",value.wire())])],positions:vec![slot.clone()],visible:vec![slot.clone()]});
            }
            for support in &patches {
                let read=super::super::environment::local_read::materialize_positions(&fixed,&mut b,request,support,&model.slots,witness.construction().reading(),c)?;
                local_scope.merge(&read.scope);
                reasons.extend(read.reasons);
                readings.extend(read.readings);
                read_refs.extend(read.read_refs);
                read_supports.extend(read.read_supports);
            }
            if !reasons.is_empty(){return Ok((None,vec![]));}
        } else if locals.is_empty() {
        for read in &model.readings {
            c.checkpoint(super::super::control::Checkpoint::Localize)?;
            let bindings = read
                .bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let expression =
                change_result::source_expression(&mut b, env, read.expression, &bindings, &[])?;
            let ty = read.values.first().ok_or("有限読取りの値域が空")?.ty();
            let values = read
                .values
                .iter()
                .map(|v| change_result::value(&mut b, v))
                .collect::<Result<Vec<_>, _>>()?;
            let image = domain(&mut b, &ty, &values)?;
            readings.push(Json::obj([
                ("expression", expression.wire()),
                ("type", ty.wire()),
                ("domain", image.wire()),
            ]));
            read_refs.extend([expression, image]);
            read_supports.push(read.support.clone());
        }
        patches = model.law_supports.clone();
        for (position, slot) in model.slots.iter().enumerate() {
            if patches.iter().any(|p| p.positions.contains(slot)) {
                continue;
            }
            let subject = env.subject(&slot.snapshot, &slot.subject)?;
            let value = Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: subject.ty.clone(),
            };
            let support = geometry::Support {
                carrier: vec![Json::obj([
                    ("type", value.ty().wire()),
                    ("value", value.wire()),
                ])],
                positions: vec![slot.clone()],
                visible: vec![slot.clone()],
            };
            let subject_ref = change_result::value(&mut b, &value)?;
            let declaration = &env.inputs.definitions().declarations[&subject.ty];
            let (parameters, fields) = declaration.signature.record_fields().ok_or("singletonの原始recordがない")?;
            let field_name = slot.field.as_ref().ok_or("singletonのfieldがない")?;
            let field = parameters.iter().chain(fields).find(|field| {
                format!("{}.{}", subject.ty, field.name) == *field_name
            }).ok_or("singletonの原始field宣言がない")?;
            let ty = model.slot_types[position].clone();
            // 未出現の候補位置は、原始field宣言の読取りをsingleton座標とする。
            let expression = b.push(
                NodeType::Expression(ty.clone()),
                "expression",
                Json::obj([
                    ("kind", Json::str("source")),
                    ("location", crate::result::location_wire(&field.location)),
                    ("parameters", Json::Arr(vec![])),
                    ("bindings", Json::Arr(vec![Json::obj([
                        ("name", Json::str("subject")), ("value", subject_ref.wire())
                    ])])),
                ]),
                vec![subject_ref], None, None,
            )?;
            let mut image_values = vec![];
            for point in &model.points {
                c.checkpoint(super::super::control::Checkpoint::Localize)?;
                if !image_values.contains(&point[position]) {
                    image_values.push(point[position].clone());
                }
            }
            let items = image_values.iter().map(|v| change_result::value(&mut b,v)).collect::<Result<Vec<_>,_>>()?;
            let image = domain(&mut b, &ty, &items)?;
            readings.push(Json::obj([
                ("expression", expression.wire()), ("type", ty.wire()), ("domain", image.wire())
            ]));
            read_refs.extend([expression, image]);
            read_supports.push(support.clone());
            patches.push(support);
        }
        } else {
            let mut states = vec![];
            for point in &model.points {
                c.checkpoint(super::super::control::Checkpoint::Localize)?;
                let mut assignments = fixed.fixed_values().into_iter().collect::<BTreeMap<_, _>>();
                assignments.extend(model.slots.iter().cloned().zip(point.iter().cloned()));
                let mut state = Environment::try_primitive_valuation(env.inputs, &assignments.into_iter().collect::<Vec<_>>(), c)?
                    .ok_or_else(|| unsupported("明示localの自由状態が不適合"))?;
                state.select_local_object(&witness, c)?;
                states.push(state);
            }
            for declaration in &locals {
                let contexts = if model.integer_equations {
                    super::super::environment::local_read::materialize_with_free(
                        &fixed, &mut b, declaration, request, &expressions, &states,
                        &model.slots, Some(target), c,
                    )?
                } else {
                    super::super::environment::local_read::materialize(
                        &fixed, &mut b, declaration, request, &expressions, &states, c,
                    )?
                };
                for explicit in contexts {
                    local_scope.merge(&explicit.scope);
                    let stopped = explicit.reasons.iter().any(|r| matches!(r.kind, ReasonKind::Stop(_)));
                    reasons.extend(explicit.reasons);
                    if stopped { return Ok((None, vec![])); }
                    if explicit.locals.is_empty() { continue; }
                    if let Some(info) = &mut information {
                        info.patches.push(info.reading(explicit.information.as_ref(), &explicit.visible, c)?);
                        for (j, support) in explicit.read_supports.iter().enumerate() {
                            info.reads.push(info.reading(explicit.read_information.get(j).and_then(Option::as_ref), &support.visible, c)?);
                        }
                    }
                    let support = geometry::Support { carrier: explicit.carrier, positions: explicit.positions, visible: explicit.visible };
                    projections.extend(explicit.projections.into_iter().map(|mut p| { p.read += readings.len(); p }));
                    readings.extend(explicit.readings);
                    read_supports.extend(explicit.read_supports);
                    read_refs.extend(explicit.read_refs);
                    patches.push(support.clone());
                    local_instances.push(geometry::Local { support, instances: explicit.locals, arguments: explicit.arguments });
                }
            }
            let adequate = if let Some(info) = &information { info.adequate(&patches, &model.law_supports, c)? } else {
                model.law_supports.iter().all(|law| patches.iter().any(|patch| patch.contains(law)))
                    && model.slots.iter().all(|slot| patches.iter().any(|patch| patch.visible.contains(slot)))
            };
            if reasons.is_empty() && !adequate {
                reasons.push(Reason { kind: ReasonKind::VisibilityInsufficient {
                    locals: locals.iter().map(|d| d.name.clone()).collect(), coordinates: expressions.clone(),
                }, request: request.id.clone(), dependencies: expressions.clone(), missing: vec![], location: None });
            }
            if !reasons.is_empty() { return Ok((None, vec![])); }
        }
        let mut global = geometry::Support {
            carrier: vec![],
            positions: vec![],
            visible: vec![],
        };
        for support in &patches {
            global.carrier.extend(support.carrier.iter().cloned());
            global.positions.extend(support.positions.iter().cloned());
            global.visible.extend(support.visible.iter().cloned());
        }
        global.carrier.sort_by_key(Json::canonical);
        global.carrier.dedup();
        global.positions.sort();
        global.positions.dedup();
        global.visible.sort();
        global.visible.dedup();
        let positions = global.positions.clone();
        let built = geometry::build(
            &fixed,
            &mut b,
            target,
            &laws,
            &vec![true; laws.len()],
            &patches,
            &model.law_supports,
            global,
            &readings,
            &read_supports,
            &read_refs,
            &projections,
            &local_instances,
            Some(&model),
            information.as_ref(),
            &{ let mut scope = model.scope.clone(); scope.merge(&local_scope); scope },
            c,
        )?;
        Ok((Some(built), positions))
    })();
    let (built, fixed_positions) = match result {
        Ok((Some(built), positions)) => (built, positions),
        Ok((None, _)) => {
            let scope = b.parts.iter().fold(local_scope, |mut scope, part| { scope.merge(&part.scope); scope });
            return Ok(Source { base, parts: b.parts, scope_domains, request: request.clone(), witness, system: None,
                answer: Answer { id: request.id.clone(), status: Decision::Undetermined, outputs: BTreeMap::new(), claim: None,
                    evidence: vec![], reasons, scope } });
        }
        Err(error) => {
            if b.parts.is_empty() {
                return Err(error);
            }
            let (kind, location) = match error {
                ValidationFailure::Stop(stop) => (ReasonKind::Stop(stop), None),
                _ if !model.missing.is_empty() => (ReasonKind::Missing, None),
                ValidationFailure::UnsupportedExpression { location, .. } => (
                    ReasonKind::UnsupportedAlgorithm {
                        question: QuestionKind::Localize,
                        operand_types: b.parts.iter().filter_map(|p| match &p.ty {
                            NodeType::Expression(ty) => Some(ty.clone()), _ => None,
                        }).collect(),
                        method: "finite_local_system".into(),
                    }, Some(location),
                ),
                other => return Err(other),
            };
            let reason = Reason {
                kind,
                request: request.id.clone(),
                dependencies: expressions
                    .first()
                    .copied()
                    .or(Some(NodeRef(base)))
                    .into_iter()
                    .chain(
                        b.parts
                            .iter()
                            .enumerate()
                            .filter(|(_, p)| {
                                matches!(
                                    p.ty,
                                    NodeType::Construction(
                                        T::Context
                                            | T::ContextMap
                                            | T::Overlap
                                            | T::Cover
                                            | T::Topology
                                    )
                                )
                            })
                            .map(|(i, _)| NodeRef(base + i)),
                    )
                    .collect(),
                missing: model.missing.clone(),
                location,
            };
            reasons.push(reason);
            let mut scope = model.scope.clone();
            scope.merge(&local_scope);
            let scope = b.parts.iter().fold(scope, |mut scope, part| {
                scope.merge(&part.scope);
                scope
            });
            return Ok(Source {
                base,
                parts: b.parts,
                scope_domains,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons,
                    scope,
                },
                request: request.clone(),
                witness,
                system: None,
            });
        }
    };
    let label = change_result::value(&mut b, &Scalar::Text("local_system".into()))?;
    let proposition = b.proposition(
        "constructible",
        std::iter::once(label)
            .chain(b.parts[built.system.0 - base].arguments.iter().copied())
            .collect(),
        vec![built.adequacy],
        Decision::Established,
    )?;
    let answer = Answer {
        id: request.id.clone(),
        status: Decision::Established,
        outputs: BTreeMap::from([
            ("system".into(), built.system),
            ("proposition".into(), proposition),
        ]),
        claim: Some(proposition),
        evidence: vec![],
        reasons: vec![],
        scope: b.parts[proposition.0 - base].scope.clone(),
    };
    let expression = *expressions.first().ok_or("有限局所構成の原式がない")?;
    let inhabited = built
        .finite
        .as_ref()
        .is_some_and(|f| !f.semantic.values.is_empty());
    Ok(Source {
        base,
        parts: b.parts,
        scope_domains,
        answer,
        request: request.clone(),
        witness,
        system: Some(System {
            parameters: built.point,
            laws,
            expression: Some(expression),
            semantic: built.semantic,
            equation: built.equation,
            domain: built.states,
            inhabited,
            patch_count: built.patch_count,
            finite: built.finite,
            integer: built.integer,
            rational: None,
            fixed_positions,
        }),
    })
}
#[allow(clippy::too_many_arguments)]
pub(super) fn diagnose(
    g: &Graph,
    request: &Request,
    target: NodeRef,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    finite: &geometry::Finite,
    laws: &[NodeRef],
    degree: u64,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let side = request
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("side", Selector::Enum { value }) => Some(value.as_str()),
            _ => None,
        })
        .ok_or("有限診断のsideがない")?;
    let selected = if side == "equation" {
        finite.equation.as_ref().ok_or("有限の方程式状態がない")?
    } else {
        &finite.semantic
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut matching_values = vec![];
    for value in &selected.matching {
        c.checkpoint(super::super::control::Checkpoint::Localize)?;
        matching_values.push((value, change_result::value(&mut b, value)?));
    }
    let matching = domain(
        &mut b,
        &selected.matching_type,
        &matching_values.iter().map(|(_, r)| *r).collect::<Vec<_>>(),
    )?;
    let pairs = selected
        .restriction
        .iter()
        .map(|(r, v)| {
            matching_values
                .iter()
                .find(|(w, _)| *w == v)
                .map(|(_, s)| (*r, *s))
                .ok_or_else(|| ValidationFailure::from("matching像がない"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let restriction = state_map(&mut b, selected.domain, matching, &pairs)?;
    let mut fibers = vec![];
    let mut fiber_refs = vec![];
    for (value, r) in matching_values {
        c.checkpoint(super::super::control::Checkpoint::Localize)?;
        let states = selected
            .restriction
            .iter()
            .filter(|(_, v)| v == value)
            .map(|(r, _)| *r)
            .collect::<Vec<_>>();
        let parameters = selected
            .parameters
            .iter()
            .filter(|(s, _)| states.contains(s))
            .flat_map(|(_, p)| p.iter().copied())
            .collect::<Vec<_>>();
        let mut fields = BTreeMap::from([
            ("domain".into(), selected.solution_domain.wire()),
            (
                "representation".into(),
                Json::obj([("kind", Json::str("finite")), ("values", refs(&parameters))]),
            ),
        ]);
        if side == "semantic" {
            fields.insert("requirements".into(), refs(laws));
        }
        let fiber = b.push(
            NodeType::Construction(if side == "semantic" {
                T::SolutionSet
            } else {
                T::EquationSolutionSet
            }),
            if side == "semantic" {
                "solution_set"
            } else {
                "equation_solutions"
            },
            Json::Obj(fields),
            [selected.solution_domain, restriction, r]
                .into_iter()
                .chain(parameters)
                .chain(laws.iter().copied())
                .collect(),
            None,
            None,
        )?;
        fiber_refs.push(fiber);
        fibers.push(Json::obj([
            ("matching", r.wire()),
            ("preimage", fiber.wire()),
        ]));
    }
    let diagnostic = b.push(
        NodeType::Construction(T::Diagnostic),
        "diagnostic",
        Json::obj([
            ("kind", Json::str("finite_matching")),
            ("side", Json::str(side)),
            ("system", target.wire()),
            ("degree", Json::Nat(degree)),
            ("matching", matching.wire()),
            ("global", selected.global.wire()),
            ("restriction", restriction.wire()),
            ("fibers", Json::Arr(fibers)),
            ("conditions", Json::Arr(vec![])),
        ]),
        std::iter::once(target)
            .chain([matching, selected.global, restriction])
            .chain(fiber_refs)
            .collect(),
        None,
        None,
    )?;
    let status = if degree == 0 || !selected.values.is_empty() {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let mut outputs = BTreeMap::from([("diagnostic".into(), diagnostic)]);
    let mut evidence = vec![];
    let claim = if degree == 1 {
        if selected.values.is_empty() {
            evidence.push(
                b.push(
                    NodeType::Evidence,
                    "evidence",
                    Json::obj([
                        ("kind", Json::str("finite_exhaustion")),
                        (
                            "data",
                            Json::obj([
                                ("domain", selected.all.wire()),
                                ("checked", Json::Nat(selected.checked as u64)),
                                ("instances", refs(laws)),
                            ]),
                        ),
                    ]),
                    std::iter::once(selected.all)
                        .chain(laws.iter().copied())
                        .collect(),
                    None,
                    None,
                )?,
            );
        }
        let proposition = b.proposition(
            "inhabited",
            vec![selected.global],
            std::iter::once(diagnostic)
                .chain(evidence.iter().copied())
                .collect(),
            status,
        )?;
        b.parts[proposition.0 - base]
            .judgment
            .as_mut()
            .ok_or("診断の判断がない")?
            .evidence = evidence.clone();
        outputs.insert("proposition".into(), proposition);
        Some(proposition)
    } else {
        None
    };
    let answer = Answer {
        id: request.id.clone(),
        status,
        outputs,
        claim,
        evidence,
        reasons: vec![],
        scope: b.parts[diagnostic.0 - base].scope.clone(),
    };
    Ok(Source {
        base,
        parts: b.parts,
        scope_domains: vec![],
        answer,
        request: request.clone(),
        witness,
        system: None,
    })
}
