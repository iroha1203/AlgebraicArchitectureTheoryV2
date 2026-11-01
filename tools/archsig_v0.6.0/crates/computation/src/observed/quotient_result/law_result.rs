//! 同じ候補環境の通常評価と、instance keyを含む型付き評価族。
use super::*;
use crate::observed::environment::quotient_evaluation::{LawRow, Row};

fn bindings_wire(bindings: &[(String, NodeRef)]) -> Json {
    Json::Arr(
        bindings
            .iter()
            .map(|(name, value)| Json::obj([("name", Json::str(name)), ("value", value.wire())]))
            .collect(),
    )
}
fn evaluation(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    expression: usize,
    bindings: &[(String, NodeRef)],
    architecture: NodeRef,
    value: Option<&Scalar>,
    residual: Option<&Scalar>,
    children: &[NodeRef],
    applicable: bool,
) -> Result<NodeRef, ValidationFailure> {
    let source = change_result::source_expression(b, env, expression, bindings, &[])?;
    let ty = env
        .indexes
        .inputs
        .law()
        .expr_type(expression)
        .ok_or("商のLaw式型がない")?
        .clone();
    let mut arguments = vec![source, architecture];
    arguments.extend(children);
    let mut part = BTreeMap::from([
        (
            "location".into(),
            archsig_input::result::location_wire(&Location::Law {
                span: env.indexes.inputs.law().exprs()[expression].span,
            }),
        ),
        ("children".into(), refs(children)),
    ]);
    let mut wire = BTreeMap::from([
        ("expression".into(), source.wire()),
        ("bindings".into(), bindings_wire(bindings)),
        ("environment".into(), architecture.wire()),
        (
            "applicability".into(),
            Json::str(if applicable {
                "applicable"
            } else {
                "not_applicable"
            }),
        ),
    ]);
    if let Some(residual) = residual {
        let residual = b.push(
            NodeType::Value(residual.ty()),
            "evaluation",
            residual.wire(),
            children.to_vec(),
            Some(residual.clone()),
            None,
        )?;
        part.insert("residual".into(), residual.wire());
        arguments.push(residual);
    }
    if let Some(value) = value {
        let value = change_result::value(b, value)?;
        arguments.push(value);
        part.insert("value".into(), value.wire());
        wire.insert("value".into(), value.wire());
    }
    wire.insert("parts".into(), Json::Arr(vec![Json::Obj(part)]));
    b.push(
        NodeType::Evaluation(ty),
        "evaluation",
        Json::Obj(wire),
        arguments,
        None,
        None,
    )
}
pub(super) fn family_type(
    env: &Environment<'_>,
    name: &str,
    ty: &Type,
) -> Result<Type, ValidationFailure> {
    let Signature::Law { params, .. } = &env.indexes.inputs.law().declarations()[name].signature
    else {
        return Err("Lawがない".into());
    };
    Ok(Type::Set(Box::new(Type::Tuple(vec![
        Type::Tuple(params.iter().map(|p| p.ty.erase()).collect()),
        Type::Option(Box::new(ty.clone())),
    ]))))
}
pub(super) fn row(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    input: &change_result::CandidateInput,
    candidate: &Row,
    name: &str,
    ty: &Type,
    dependency: NodeRef,
) -> Result<(Scalar, Vec<NodeRef>), ValidationFailure> {
    let Some(Payload::Construction(original)) = &b.g.get(input.architecture)?.payload else {
        return Err("商の元Architectureがない".into());
    };
    let Json::Obj(wire) = &original.wire() else {
        return Err("商の元Architectureのrecordがない".into());
    };
    let mut wire = wire.clone();
    let mut arguments = original.arguments();
    arguments.extend([input.architecture, dependency]);
    let mut overrides = vec![];
    for (fact, scalar) in &candidate.assignments {
        let subject = env.indexes.subject(&fact.snapshot, &fact.subject)?;
        let subject = change_result::value(
            b,
            &Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: subject.ty.to_string(),
            },
        )?;
        let value = change_result::value(b, scalar)?;
        arguments.extend([subject, value]);
        overrides.push(Json::obj([
            (
                "slot",
                Json::obj([
                    ("subject", subject.wire()),
                    (
                        "field",
                        Json::str(fact.field.as_deref().ok_or("商の更新fieldがない")?),
                    ),
                ]),
            ),
            ("value", value.wire()),
        ]));
    }
    wire.insert("overrides".into(), Json::Arr(overrides));
    let architecture = b.push(
        NodeType::Construction(T::Architecture),
        "architecture",
        Json::Obj(wire),
        arguments,
        None,
        None,
    )?;
    let Signature::Law { body, guard, .. } =
        &env.indexes.inputs.law().declarations()[name].signature
    else {
        return Err("Lawがない".into());
    };
    let mut evaluations = vec![];
    let mut items = vec![];
    for LawRow {
        bindings,
        guard: applicable,
        values,
        scope,
        evaluations: captured,
        body_evaluation,
        guard_evaluation,
    } in &candidate.laws
    {
        let bindings = bindings
            .iter()
            .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let mut nodes = Vec::<NodeRef>::new();
        for captured in captured {
            let children = captured
                .children
                .iter()
                .map(|i| nodes.get(*i).copied().ok_or("通常評価の子が先行していない"))
                .collect::<Result<Vec<_>, _>>()?;
            let local = captured
                .bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let node = evaluation(
                b,
                env,
                captured.expression,
                &local,
                architecture,
                captured.value.as_ref(),
                captured.residual.as_ref(),
                &children,
                true,
            )?;
            b.parts[node.0 - b.base].scope.merge(&captured.scope);
            nodes.push(node);
        }
        let guard_evaluation = guard_evaluation
            .map(|i| nodes.get(i).copied().ok_or("通常guard評価がない"))
            .transpose()?;
        let guard_value = if guard.is_some() {
            Some(change_result::value(b, &Scalar::Bool(*applicable))?)
        } else {
            None
        };
        let evaluated = if *applicable {
            let index = body_evaluation.ok_or("通常Law body評価がない")?;
            *nodes.get(index).ok_or("通常Law body評価の位置が違う")?
        } else {
            evaluation(
                b,
                env,
                *body,
                &bindings,
                architecture,
                None,
                None,
                &[],
                false,
            )?
        };
        if let (Some(guard), Some(guard_evaluation)) = (guard, guard_evaluation) {
            let guard_value = guard_value.ok_or("商のguard値がない")?;
            let part = &mut b.parts[evaluated.0 - b.base];
            part.arguments.extend([guard_evaluation, guard_value]);
            part.arguments.sort_by_key(|r| r.0);
            part.arguments.dedup();
            let Json::Obj(wire) = &mut part.wire else {
                unreachable!()
            };
            let Some(Json::Arr(parts)) = wire.get_mut("parts") else {
                unreachable!()
            };
            parts.insert(
                0,
                Json::obj([
                    (
                        "location",
                        archsig_input::result::location_wire(&Location::Law {
                            span: env.indexes.inputs.law().exprs()[*guard].span,
                        }),
                    ),
                    ("value", guard_value.wire()),
                    ("children", refs(&[guard_evaluation])),
                ]),
            );
        }
        b.parts[evaluated.0 - b.base].scope.merge(scope);
        evaluations.push(evaluated);
        let key = Scalar::Tuple(
            bindings
                .iter()
                .map(|(_, r)| {
                    b.parts[r.0 - b.base]
                        .scalar
                        .clone()
                        .ok_or("Law束縛値がない")
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        items.push(Scalar::Tuple(vec![
            key,
            Scalar::Option {
                element: ty.clone(),
                value: values.as_ref().map(|value| Box::new(value.clone())),
            },
        ]));
    }
    items.sort_by_key(|v| v.wire().canonical());
    items.dedup();
    let Type::Set(element) = &family_type(env, name, ty)? else {
        unreachable!()
    };
    Ok((
        Scalar::Set {
            element: (**element).clone(),
            items,
        },
        evaluations,
    ))
}
