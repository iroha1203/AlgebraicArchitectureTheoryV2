#[allow(clippy::too_many_arguments)]
pub(super) fn compute_model(env: &Environment<'_>, g: &Graph, request: &Request, target: NodeRef,
    base: usize, witness: Arc<ArchitectureWitness>, fixed: Environment<'_>, model: finite_model::Model,
    c: &Control) -> Result<Source,ValidationFailure> {
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
            let declaration = &env.indexes.inputs.law().declarations()[&model.change];
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
            c.checkpoint(archsig_common::control::Checkpoint::Localize)?;
            let reference = if let Some(values) = values {
                let items = values.iter().map(|v| change_result::value(&mut b, v)).collect::<Result<Vec<_>, _>>()?;
                let reference = domain(&mut b, &parameter.ty.erase(), &items)?;
                scope_domains.push((reference, parameter.ty.erase()));
                Some(reference)
            } else { None };
            quantifiers.push((name, Quantifier {
                kind: archsig_input::law::ast::QuantKind::Forall,
                name: parameter.name.clone(),
                ty: parameter.ty.erase(),
                domain: reference,
                occurrence: parameter.span,
                context: Some(env.current_context(g)),
            }));
        }
        for (name, bindings) in &model.requirements {
            c.checkpoint(archsig_common::control::Checkpoint::Localize)?;
            let law = &env.indexes.inputs.law().declarations()[name];
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
            let parameters = model.universal.iter().filter(|(law,_,values)| law == name && values.is_none())
                .map(|(_,p,_)| (p.name.clone(),p.ty.clone())).collect::<Vec<_>>();
            let expression = change_result::source_expression(&mut b, env, body, &bindings, &parameters)?;
            b.parts[expression.0 - base].scope.merge(&model.scope);
            for (_, quantifier) in quantifiers.iter().filter(|(law, _)| *law == name) {
                b.parts[expression.0 - base].arguments.extend(quantifier.domain);
                b.parts[expression.0 - base].scope.quantifiers.push(quantifier.clone());
            }
            expressions.push(expression);
            let guard = guard
                .map(|id| change_result::source_expression(&mut b, env, id, &bindings, &parameters))
                .transpose()?;
            let mut fields = BTreeMap::from([
                ("name".into(), Json::str(name)),
                (
                    "role".into(),
                    Json::str(if role == archsig_input::law::ast::Role::Required {
                        "required"
                    } else {
                        "optional"
                    }),
                ),
                (
                    "occurrence".into(),
                    archsig_input::result::location_wire(&Location::Law { span: law.span }),
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
        let locals = env.indexes.inputs.law().declarations().values().filter(|d|
            d.reading == witness.construction().reading() && matches!(d.signature, Signature::Local { .. })
        ).collect::<Vec<_>>();
        let mut information = if model.affine_equations && !locals.is_empty() { Some(geometry::Information::new(&fixed, &model)?) } else { None };
        let mut patches = vec![];
        let mut local_instances = vec![];
        let mut projections = vec![];
        if locals.is_empty() && model.affine_equations {
            patches=model.law_supports.clone();
            for slot in &model.slots {
                if patches.iter().any(|p|p.positions.contains(slot)){continue;}
                let subject=fixed.indexes.subject(&slot.snapshot,&slot.subject)?;
                let value=Scalar::Subject{snapshot:slot.snapshot.clone(),subject:slot.subject.clone(),entity:subject.ty.to_string()};
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
            c.checkpoint(archsig_common::control::Checkpoint::Localize)?;
            let bindings = read
                .bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let expression =
                change_result::source_expression(&mut b, env, read.expression, &bindings,
                    &read.parameters.iter().map(|p| (p.name.clone(), p.ty.clone())).collect::<Vec<_>>())?;
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
            let subject = env.indexes.subject(&slot.snapshot, &slot.subject)?;
            let value = Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: subject.ty.to_string(),
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
            let declaration = &env.indexes.inputs.definitions().declarations()[subject.ty.as_str()];
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
                    ("location", archsig_input::result::location_wire(&field.location)),
                    ("parameters", Json::Arr(vec![])),
                    ("bindings", Json::Arr(vec![Json::obj([
                        ("name", Json::str("subject")), ("value", subject_ref.wire())
                    ])])),
                ]),
                vec![subject_ref], None, None,
            )?;
            let mut image_values = vec![];
            for point in &model.points {
                c.checkpoint(archsig_common::control::Checkpoint::Localize)?;
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
                c.checkpoint(archsig_common::control::Checkpoint::Localize)?;
                let mut assignments = fixed.fixed_values().into_iter().collect::<BTreeMap<_, _>>();
                assignments.extend(model.slots.iter().cloned().zip(point.iter().cloned()));
                let mut state = Environment::try_primitive_valuation(env.indexes.inputs, &assignments.into_iter().collect::<Vec<_>>(), c)?
                    .ok_or_else(|| unsupported("明示localの自由状態が不適合"))?;
                state.select_local_object(&witness, c)?;
                states.push(state);
            }
            for declaration in &locals {
                let contexts = if model.affine_equations {
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
    let diagrams = split_diagram(built.integer);
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
            integer: diagrams.0,
            rational: diagrams.1,
            fixed_positions,
        }),
    })
}
