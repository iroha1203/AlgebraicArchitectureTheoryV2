//! 同じ候補環境の等式評価と、instance keyを含む型付き評価族。
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
    children: &[NodeRef],
    applicable: bool,
) -> Result<NodeRef, ValidationFailure> {
    let source = change_result::source_expression(b, env, expression, bindings, &[])?;
    let ty = env
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
            crate::result::location_wire(&Location::Law {
                span: env.inputs.law().exprs[expression].span,
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
    let Signature::Law { params, .. } = &env.inputs.law().declarations[name].signature else {
        return Err("Lawがない".into());
    };
    Ok(Type::Set(Box::new(Type::Tuple(vec![
        Type::Tuple(params.iter().map(|p| p.ty.erase()).collect()),
        Type::Option(Box::new(Type::Tuple(vec![ty.clone(), ty.clone()]))),
    ]))))
}
pub(super) fn row(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    input: &change_result::CandidateInput,
    candidate: &Row,
    name: &str,
    ty: &Type,
    lhs: usize,
    rhs: usize,
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
        let subject = env.subject(&fact.snapshot, &fact.subject)?;
        let subject = change_result::value(
            b,
            &Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: subject.ty.clone(),
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
    let Signature::Law { body, guard, .. } = &env.inputs.law().declarations[name].signature else {
        return Err("Lawがない".into());
    };
    let mut evaluations = vec![];
    let mut items = vec![];
    for LawRow {
        bindings,
        guard: applicable,
        values,
        scope,
    } in &candidate.laws
    {
        let bindings = bindings
            .iter()
            .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let mut children = vec![];
        let guard_evaluation = guard
            .map(|guard| {
                evaluation(
                    b,
                    env,
                    guard,
                    &bindings,
                    architecture,
                    Some(&Scalar::Bool(*applicable)),
                    &[],
                    true,
                )
            })
            .transpose()?;
        let result = if let Some((left, right)) = values {
            children.push(evaluation(
                b,
                env,
                lhs,
                &bindings,
                architecture,
                Some(left),
                &[],
                true,
            )?);
            children.push(evaluation(
                b,
                env,
                rhs,
                &bindings,
                architecture,
                Some(right),
                &[],
                true,
            )?);
            Some(Scalar::Bool(left == right))
        } else {
            None
        };
        let guard_value = if guard.is_some() {
            Some(change_result::value(b, &Scalar::Bool(*applicable))?)
        } else {
            None
        };
        let evaluated = evaluation(
            b,
            env,
            *body,
            &bindings,
            architecture,
            result.as_ref(),
            &children,
            *applicable,
        )?;
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
                        crate::result::location_wire(&Location::Law {
                            span: env.inputs.law().exprs[*guard].span,
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
                element: Type::Tuple(vec![ty.clone(), ty.clone()]),
                value: values
                    .as_ref()
                    .map(|(a, b)| Box::new(Scalar::Tuple(vec![a.clone(), b.clone()]))),
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
