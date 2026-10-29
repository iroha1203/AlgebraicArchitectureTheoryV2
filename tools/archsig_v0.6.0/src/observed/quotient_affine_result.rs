//! Z/Q Viewの実アフィン像。終域を周囲の格子全体に置き換えない。
use super::*;
use crate::observed::{
    change_result::field_linear_result as scalar_wire,
    change_result::{linear_result as linear, CandidateInput},
    environment::quotient_affine,
    environment::quotient_affine::coefficients,
    numeric,
};

pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    input: CandidateInput,
    reference: NodeRef,
    request: &Request,
    base: usize,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let image = quotient_affine::compute(env, g, &input, request, c)?;
    let ty = &image.ty;
    let declaration =
        &env.inputs.law().declarations[request.declaration().ok_or("アフィン商のViewがない")?];
    let Signature::View { body, .. } = &declaration.signature else {
        return Err("アフィン商のView署名が違う".into());
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let bindings = image
        .bindings
        .iter()
        .map(|(name, value)| {
            let selector = &request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{name}"))
                .ok_or("アフィン商の束縛がない")?
                .value;
            let r = if matches!(selector, Selector::Answer { .. }) {
                match env.answer_binding(g, selector, (0, 0))? {
                    AnswerBinding::Reference(r) => r,
                    AnswerBinding::Projection(node) => g
                        .nodes
                        .iter()
                        .position(|n| *n == node)
                        .map(NodeRef)
                        .ok_or("アフィン商の公開束縛が保持されていない")?,
                    AnswerBinding::Inapplicable(_) => {
                        return Err(ValidationFailure::from("アフィン商の束縛射影が不適合"));
                    }
                }
            } else {
                change_result::value(&mut b, value)?
            };
            Ok((name.clone(), r))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let expression = change_result::source_expression(&mut b, env, *body, &bindings, &[])?;
    let part = &mut b.parts[expression.0 - base];
    part.arguments.push(reference);
    part.arguments.sort_by_key(|r| r.0);
    part.arguments.dedup();
    part.scope.merge(&g.get(reference)?.scope);
    part.scope.merge(&image.scope);
    part.scope.readings.insert(declaration.reading.clone());
    let law_expression = if let Some(law) = &image.law {
        let declaration = &env.inputs.law().declarations[&law.name];
        let Signature::Law { body, params, .. } = &declaration.signature else {
            return Err("アフィン商のLaw署名がない".into());
        };
        let bindings = bindings
            .iter()
            .filter(|(name, _)| law.bindings.iter().any(|(n, _)| n == name))
            .cloned()
            .collect::<Vec<_>>();
        let parameters = params
            .iter()
            .filter(|p| !bindings.iter().any(|(name, _)| name == &p.name))
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        let r = change_result::source_expression(
            &mut b,
            env,
            law.pending_expression.unwrap_or(*body),
            &bindings,
            &parameters,
        )?;
        let part = &mut b.parts[r.0 - base];
        part.arguments.push(reference);
        part.arguments.sort_by_key(|r| r.0);
        part.arguments.dedup();
        part.scope.merge(&image.scope);
        part.scope.merge(&g.get(reference)?.scope);
        part.scope.readings.insert(declaration.reading.clone());
        Some(r)
    } else {
        None
    };
    if !image.missing.is_empty() {
        let reason = Reason {
            kind: ReasonKind::Missing,
            request: request.id.clone(),
            dependencies: std::iter::once(expression).chain(law_expression).collect(),
            missing: image.missing,
            location: Some(Location::Law {
                span: declaration.span,
            }),
        };
        b.parts[expression.0 - base].reasons.push(reason.clone());
        let scope = b.parts[expression.0 - base].scope.clone();
        return Ok(Source {
            base,
            parts: b.parts,
            answer: Answer {
                id: request.id.clone(),
                status: Decision::Undetermined,
                outputs: BTreeMap::new(),
                claim: None,
                evidence: vec![],
                reasons: vec![reason],
                scope,
            },
            request: request.clone(),
            witness: input.witness,
            domain_type: input.domain_type,
        });
    }
    let source = b.push(
        NodeType::Domain,
        "domain",
        match &input.domain_type {
            ProjectionType::CandidateSpace(_) => Json::obj([
                ("kind", Json::str("candidates")),
                ("space", reference.wire()),
            ]),
            ProjectionType::SolutionSet(_) => Json::obj([
                ("kind", Json::str("solutions")),
                ("solutions", reference.wire()),
            ]),
            _ => return Err("アフィン商の元domain型が違う".into()),
        },
        vec![reference, expression],
        None,
        None,
    )?;
    let mut descent = None;
    let mut evidence = vec![];
    let mut evaluations = vec![];
    let (classes, projection, representation) = if image.empty {
        let parameter_type = Type::Tuple(vec![ty.clone(); image.parameter_count]);
        let classes = domain(
            &mut b,
            &Type::Set(Box::new(parameter_type)),
            &[],
            &[reference, expression],
        )?;
        let projection = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", source.wire()),
                ("target", classes.wire()),
                ("kind", Json::str("finite")),
                ("pairs", Json::Arr(vec![])),
            ]),
            vec![source, classes],
            None,
            None,
        )?;
        if let Some(law) = &image.law {
            let target = domain(
                &mut b,
                &law_result::family_type(
                    env,
                    &law.name,
                    &Type::Tuple(vec![law.value_type.clone(); 2]),
                )?,
                &[],
                &[reference, law_expression.ok_or("アフィン商のLaw式がない")?],
            )?;
            descent = Some(b.push(
                NodeType::Construction(T::StateMap),
                "state_map",
                Json::obj([
                    ("source", classes.wire()),
                    ("target", target.wire()),
                    ("kind", Json::str("finite")),
                    ("pairs", Json::Arr(vec![])),
                ]),
                vec![classes, target],
                None,
                None,
            )?);
        }
        (
            classes,
            projection,
            Json::obj([("kind", Json::str("finite")), ("fibers", Json::Arr(vec![]))]),
        )
    } else {
        let n = image.dimensions;
        let ring = b.push(
            NodeType::Construction(T::Ring),
            "ring",
            Json::obj([("kind", Json::str("scalar")), ("scalar", ty.wire())]),
            vec![],
            None,
            None,
        )?;
        let original = linear::module(&mut b, ring, image.origin.len(), "free", vec![reference])?;
        let parameters = linear::module(&mut b, ring, n, "free", vec![reference])?;
        // 元Assignmentへの復元は、解集合またはguardで選んだ同じ表示を使う。
        let embedding = scalar_wire::map(&mut b, parameters, original, &image.embedding, n, c)?;
        let origin = scalar_wire::vector(&mut b, original, &image.origin, c)?;
        let ambient = linear::module(&mut b, ring, image.matrix.len(), "free", vec![expression])?;
        let map = scalar_wire::map(&mut b, parameters, ambient, &image.matrix, n, c)?;
        let offset = scalar_wire::vector(&mut b, ambient, &image.offset, c)?;
        let fiber = coefficients::fiber(ty, &image.matrix, n, c)?;
        let actual_image = linear::module(&mut b, ring, fiber.rank, "image", vec![map])?;
        let kernel = linear::module(&mut b, ring, n - fiber.rank, "kernel", vec![map])?;
        let basis = &fiber.image;
        let image_generators = (0..fiber.rank)
            .map(|j| {
                let column = basis.iter().map(|row| row[j].clone()).collect::<Vec<_>>();
                let generator = coefficients::view_value(&image.view_type, &column, c)?;
                Ok(Json::obj([
                    ("type", image.view_type.wire()),
                    ("value", generator.wire()),
                ]))
            })
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let kernel_generators = (0..n - fiber.rank)
            .map(|j| {
                let value = Scalar::Tuple(fiber.kernel.iter().map(|row| row[j].clone()).collect());
                Json::obj([("type", value.ty().wire()), ("value", value.wire())])
            })
            .collect();
        for (r, generators) in [
            (actual_image, image_generators),
            (kernel, kernel_generators),
        ] {
            let Json::Obj(wire) = &mut b.parts[r.0 - base].wire else {
                return Err("アフィン商の加群がrecordでない".into());
            };
            wire.insert("generators".into(), Json::Arr(generators));
        }
        let inclusion =
            scalar_wire::map(&mut b, kernel, parameters, &fiber.kernel, n - fiber.rank, c)?;
        let image_basis = basis.iter().map(|row| row[..fiber.rank].to_vec()).collect();
        let image_inclusion =
            scalar_wire::map(&mut b, actual_image, ambient, &image_basis, fiber.rank, c)?;
        let ambient_domain = linear::domain(&mut b, ambient)?;
        let view = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", source.wire()),
                ("target", ambient_domain.wire()),
                ("kind", Json::str("affine")),
                ("linear", map.wire()),
                ("offset", offset.wire()),
            ]),
            vec![source, ambient_domain, map, offset, embedding, origin],
            None,
            None,
        )?;
        let classes = b.push(
            NodeType::Domain,
            "domain",
            Json::obj([
                ("kind", Json::str("image")),
                ("map", view.wire()),
                ("source", reference.wire()),
            ]),
            vec![view, reference],
            None,
            None,
        )?;
        let projection = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", source.wire()),
                ("target", classes.wire()),
                ("kind", Json::str("affine")),
                ("linear", map.wire()),
                ("offset", offset.wire()),
            ]),
            vec![
                source,
                classes,
                map,
                offset,
                embedding,
                origin,
                inclusion,
                image_inclusion,
            ],
            None,
            None,
        )?;
        if image.law.is_some() {
            (descent, evidence, evaluations) = law_descent(
                &mut b,
                env,
                &input,
                &image,
                reference,
                request,
                law_expression.ok_or("アフィン商のLaw式がない")?,
                ring,
                actual_image,
                classes,
                &fiber,
                c,
            )?;
        }
        (
            classes,
            projection,
            Json::obj([
                ("kind", Json::str("affine")),
                ("image", actual_image.wire()),
                ("kernel", kernel.wire()),
                ("map", map.wire()),
                ("offset", offset.wire()),
            ]),
        )
    };
    let mut args = (base..base + b.parts.len())
        .map(NodeRef)
        .collect::<Vec<_>>();
    args.push(reference);
    let quotient = b.push(
        NodeType::Construction(T::Quotient),
        "quotient",
        Json::obj([
            ("domain", reference.wire()),
            (
                "view",
                Json::str(request.declaration().ok_or("アフィン商のViewがない")?),
            ),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|(name, value)| {
                            Json::obj([("name", Json::str(name)), ("value", value.wire())])
                        })
                        .collect(),
                ),
            ),
            ("classes", classes.wire()),
            ("projection", projection.wire()),
            ("representation", representation),
            ("evaluations", refs(&evaluations)),
        ]),
        args,
        None,
        None,
    )?;
    let mut status = Decision::Established;
    let mut outputs = BTreeMap::from([("quotient".into(), quotient)]);
    let mut claim = None;
    if let Some(law) = &image.law {
        let Json::Obj(wire) = &mut b.parts[quotient.0 - base].wire else {
            return Err("アフィン商のrecordがない".into());
        };
        wire.insert("law".into(), Json::str(&law.name));
        if let Some(descent) = descent {
            wire.insert("descent".into(), descent.wire());
        }
        if !evidence.is_empty() {
            status = Decision::Refuted;
        }
        let proposition = b.proposition("sufficient", vec![quotient], evidence.clone(), status)?;
        let part = &mut b.parts[proposition.0 - base];
        part.evidence = evidence.clone();
        part.judgment
            .as_mut()
            .ok_or("アフィン商の十分性判断がない")?
            .evidence = evidence.clone();
        outputs.insert("proposition".into(), proposition);
        claim = Some(proposition);
    }
    let scope = b.parts[quotient.0 - base].scope.clone();
    Ok(Source {
        base,
        parts: b.parts,
        answer: Answer {
            id: request.id.clone(),
            status,
            outputs,
            claim,
            evidence,
            reasons: vec![],
            scope,
        },
        request: request.clone(),
        witness: input.witness,
        domain_type: input.domain_type,
    })
}

fn law_descent(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    input: &CandidateInput,
    image: &quotient_affine::Image,
    reference: NodeRef,
    request: &Request,
    expression: NodeRef,
    ring: NodeRef,
    actual_image: NodeRef,
    classes: NodeRef,
    fiber: &coefficients::Fiber,
    c: &mut Control,
) -> Result<(Option<NodeRef>, Vec<NodeRef>, Vec<NodeRef>), ValidationFailure> {
    let ty = &image.ty;
    let law = image.law.as_ref().ok_or("アフィン商のLawがない")?;
    let free = image.dimensions - fiber.rank;
    let differences = coefficients::multiply(ty, &law.matrix, &fiber.kernel, free, c)?;
    let zero = numeric::zero(ty, c)?;
    let mut separating = None;
    for instance in &law.instances {
        if instance.guard.never() {
            continue;
        }
        let origin = match &instance.guard {
            quotient_affine::Guard::Affine(domain) => {
                let guard_differences =
                    coefficients::multiply(ty, &domain.equations, &fiber.kernel, free, c)?;
                let origin = domain
                    .particular
                    .as_ref()
                    .ok_or("商の非空guardの解がない")?;
                if let Some(j) =
                    (0..free).find(|j| guard_differences.iter().any(|row| row[*j] != zero))
                {
                    separating = Some((origin.clone(), j));
                    break;
                }
                origin.clone()
            }
            quotient_affine::Guard::Fixed(_) => vec![zero.clone(); image.dimensions],
        };
        if let Some(j) = (0..free).find(|j| {
            differences[instance.rows.clone()]
                .iter()
                .any(|row| row[*j] != zero)
        }) {
            separating = Some((origin, j));
            break;
        }
    }
    if let Some((origin, j)) = separating {
        let other = origin
            .iter()
            .zip(&fiber.kernel)
            .map(|(x, row)| numeric::binary(crate::law::ast::BinOp::Add, x, &row[j], c))
            .collect::<Result<Vec<_>, _>>()?;
        let points = [origin, other];
        let mut candidates = vec![];
        let mut values = vec![];
        let mut views = vec![];
        let mut evaluations = vec![];
        let mut checked_views = vec![];
        let mut checked_families = vec![];
        for point in &points {
            let row = quotient_affine::point(env, input, image, point, request, c)?;
            candidates.push(change_result::value(b, &row.parameters)?);
            views.push(change_result::value(b, &row.image)?);
            let (family, checked) = law_result::row(
                b,
                env,
                input,
                &row,
                &law.name,
                &Type::Tuple(vec![law.value_type.clone(); 2]),
                expression,
            )?;
            values.push(change_result::value(b, &family)?);
            checked_views.push(row.image);
            checked_families.push(family);
            evaluations.extend(checked);
        }
        if checked_views[0] != checked_views[1] || checked_families[0] == checked_families[1] {
            return Err("商の通常評価で反例対を確認できない".into());
        }
        let evidence = b.push(
            NodeType::Evidence,
            "evidence",
            Json::obj([
                ("kind", Json::str("separating_pair")),
                (
                    "data",
                    Json::obj([
                        ("domain", reference.wire()),
                        ("first", candidates[0].wire()),
                        ("second", candidates[1].wire()),
                        ("view_values", refs(&views)),
                        ("law_values", refs(&values)),
                    ]),
                ),
            ]),
            std::iter::once(reference)
                .chain(candidates)
                .chain(views)
                .chain(values)
                .chain(evaluations.iter().copied())
                .collect(),
            None,
            None,
        )?;
        return Ok((None, vec![evidence], evaluations));
    }
    if law
        .instances
        .iter()
        .any(|instance| matches!(instance.guard, quotient_affine::Guard::Affine(_)))
    {
        // Use actual image coordinates, with Option-valued families as a
        // typed Domain rather than a numeric module.
        let family_type = law_result::family_type(
            env,
            &law.name,
            &Type::Tuple(vec![law.value_type.clone(); 2]),
        )?;
        let target = b.push(
            NodeType::Domain,
            "domain",
            Json::obj([("kind", Json::str("type")), ("type", family_type.wire())]),
            vec![expression],
            None,
            None,
        )?;
        let mut arguments = vec![classes, target, actual_image, expression];
        let mut instances = vec![];
        let affine_component = |b: &mut Builder<'_>,
                                rows: &[Vec<Scalar>],
                                offset: &[Scalar],
                                arguments: &mut Vec<NodeRef>,
                                c: &mut Control| {
            let target = linear::module(b, ring, rows.len(), "free", vec![])?;
            let transformed = coefficients::multiply(&image.ty, rows, &fiber.lifts, fiber.rank, c)?;
            let map = scalar_wire::map(b, actual_image, target, &transformed, fiber.rank, c)?;
            let offset = scalar_wire::vector(b, target, offset, c)?;
            arguments.extend([map, offset]);
            Ok::<_, ValidationFailure>(Json::obj([
                ("linear", map.wire()),
                ("offset", offset.wire()),
            ]))
        };
        for instance in &law.instances {
            c.checkpoint(crate::observed::control::Checkpoint::Quotient)?;
            c.checkpoint(crate::observed::control::Checkpoint::QuotientGuardedInstance)?;
            let key = Scalar::Tuple(
                instance
                    .bindings
                    .iter()
                    .map(|(_, value)| value.clone())
                    .collect(),
            );
            let key = change_result::value(b, &key)?;
            arguments.push(key);
            let guard = match &instance.guard {
                quotient_affine::Guard::Fixed(value) => Json::Bool(*value),
                quotient_affine::Guard::Affine(domain) => {
                    let offset = domain
                        .rhs
                        .iter()
                        .map(|rhs| {
                            numeric::binary(
                                crate::law::ast::BinOp::Sub,
                                &numeric::zero(&image.ty, c)?,
                                rhs,
                                c,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    affine_component(b, &domain.equations, &offset, &mut arguments, c)?
                }
            };
            let mut row = BTreeMap::from([("key".into(), key.wire()), ("guard".into(), guard)]);
            if !instance.guard.never() {
                let values = affine_component(
                    b,
                    &law.matrix[instance.rows.clone()],
                    &law.offset[instance.rows.clone()],
                    &mut arguments,
                    c,
                )?;
                row.insert("values".into(), values);
            }
            instances.push(Json::Obj(row));
        }
        let map = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", classes.wire()),
                ("target", target.wire()),
                ("kind", Json::str("guarded_affine")),
                ("coordinates", actual_image.wire()),
                ("value_type", law.value_type.wire()),
                ("instances", Json::Arr(instances)),
            ]),
            arguments,
            None,
            None,
        )?;
        return Ok((Some(map), vec![], vec![]));
    }
    // 固定したinstance keyの左右値を座標とする係数加群。成立Boolや残差には縮めない。
    let mut arguments = vec![expression];
    // 不適用のinstanceも族の固定成分であり、キーを落として空族へ変えない。
    if law.instances.iter().any(|i| i.guard.never()) {
        let Signature::Law { params, .. } = &env.inputs.law().declarations[&law.name].signature
        else {
            return Err("商のLaw署名がない".into());
        };
        let key_type = Type::Tuple(params.iter().map(|p| p.ty.erase()).collect());
        let mut items = law
            .instances
            .iter()
            .map(|instance| {
                Scalar::Tuple(vec![
                    Scalar::Tuple(instance.bindings.iter().map(|(_, v)| v.clone()).collect()),
                    Scalar::Bool(!instance.guard.never()),
                ])
            })
            .collect::<Vec<_>>();
        items.sort_by_key(|v| v.wire().canonical());
        items.dedup();
        let pattern = Scalar::Set {
            element: Type::Tuple(vec![key_type, Type::Bool]),
            items,
        };
        arguments.push(change_result::value(b, &pattern)?);
    }
    let applicability = arguments.get(1).copied();
    let family = linear::module(b, ring, law.matrix.len(), "free", arguments)?;
    let mut labels = coefficients::coordinate_names(&law.value_type, "lhs", c)?;
    labels.extend(coefficients::coordinate_names(&law.value_type, "rhs", c)?);
    let mut generators = vec![];
    for instance in law.instances.iter().filter(|i| !i.guard.never()) {
        let key = Scalar::Tuple(
            instance
                .bindings
                .iter()
                .map(|(_, value)| value.clone())
                .collect(),
        );
        for side in &labels {
            let label = Scalar::Tuple(vec![key.clone(), Scalar::Text(side.clone())]);
            generators.push(Json::obj([
                ("type", label.ty().wire()),
                ("value", label.wire()),
            ]));
        }
    }
    let Json::Obj(wire) = &mut b.parts[family.0 - b.base].wire else {
        return Err("アフィン商の評価族加群がrecordでない".into());
    };
    wire.insert("generators".into(), Json::Arr(generators));
    if let Some(pattern) = applicability {
        wire.insert("applicability".into(), pattern.wire());
    }
    let transformed = coefficients::multiply(ty, &law.matrix, &fiber.lifts, fiber.rank, c)?;
    let matrix = transformed
        .iter()
        .map(|row| row[..fiber.rank].to_vec())
        .collect();
    let linear = scalar_wire::map(b, actual_image, family, &matrix, fiber.rank, c)?;
    let offset = scalar_wire::vector(b, family, &law.offset, c)?;
    let target = linear::domain(b, family)?;
    let descent = b.push(
        NodeType::Construction(T::StateMap),
        "state_map",
        Json::obj([
            ("source", classes.wire()),
            ("target", target.wire()),
            ("kind", Json::str("affine")),
            ("linear", linear.wire()),
            ("offset", offset.wire()),
        ]),
        vec![classes, target, linear, offset, expression],
        None,
        None,
    )?;
    Ok((Some(descent), vec![], vec![]))
}
