//! Z/Q coordinates stay symbolic while the other argument domains are exhausted.
use super::*;
use archsig_input::law::model::Declaration;

pub(super) fn compare(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    declarations: [&Declaration; 2],
    maps: &[LocalParameter],
    expressions: [usize; 2],
    ty: &Type,
    values: NodeRef,
    origins: &[NodeRef],
    request: &Request,
    c: &Control,
) -> Result<field::Comparison, ValidationFailure> {
    let mut out = field::Comparison {
        values,
        status: Decision::Established,
        arguments: vec![],
        reasons: vec![],
        evidence: vec![],
        support: vec![],
        scope: Scope::default(),
    };
    let mut params = vec![];
    for declaration in declarations {
        let Signature::Local { params: p, .. } = &declaration.signature else {
            return Err("numeric transport requires local".into());
        };
        params.push(p);
    }
    for row in parameter_rows(maps, c)? {
        let mut bindings = [vec![], vec![]];
        for side in 0..2 {
            for ((p, map), index) in params[side].iter().zip(maps).zip(&row) {
                tick(c)?;
                if !matches!(map, LocalParameter::Numeric { .. }) {
                    bindings[side].push((p.name.clone(), map.binding(*index, side)?));
                }
            }
        }
        let result = super::super::super::environment::local_read::affine_transport(
            env,
            declarations,
            [&bindings[0], &bindings[1]],
            expressions,
            ty,
        )?;
        out.status = merge_status(out.status, result.status);
        out.support.extend(result.support.iter().cloned());
        out.scope.merge(&result.scope);
        if result.status == Decision::Undetermined {
            out.reasons.push(Reason {
                kind: if result.missing.is_empty() {
                    ReasonKind::UnsupportedAlgorithm {
                        question: request.kind,
                        operand_types: params[0]
                            .iter()
                            .map(|p| p.ty.clone())
                            .chain(std::iter::once(ty.clone()))
                            .collect(),
                        method: if *ty == Type::Z {
                            "local_integer_guard_fiber"
                        } else {
                            "local_rational_guard_fiber"
                        }
                        .into(),
                    }
                } else {
                    ReasonKind::Missing
                },
                request: request.id.clone(),
                dependencies: origins.to_vec(),
                missing: result.missing,
                location: Some(archsig_common::issue::Location::Law {
                    span: declarations[0].span,
                }),
            });
        }
        if let Some(point) = result.point {
            // Re-evaluate the original expressions at the reconstructed source tuple.
            let mut actual = [vec![], vec![]];
            for side in 0..2 {
                for ((p, map), (index, v)) in
                    params[side].iter().zip(maps).zip(row.iter().zip(&point))
                {
                    actual[side].push((
                        p.name.clone(),
                        if matches!(map, LocalParameter::Numeric { .. }) {
                            v.clone()
                        } else {
                            map.binding(*index, side)?
                        },
                    ));
                }
            }
            let mut guards = [true, true];
            for side in 0..2 {
                if let Signature::Local {
                    guard: Some(id), ..
                } = &declarations[side].signature
                {
                    let (value, _, _, _) =
                        super::super::super::environment::local_read::guard_value(
                            env,
                            *id,
                            &actual[side],
                            &declarations[side].reading,
                        )?;
                    guards[side] = value.ok_or("numeric guard witness is not determined")?;
                }
            }
            if !guards[0] {
                return Err("numeric witness lies outside source guard".into());
            }
            let mut outputs = vec![];
            if !guards[1] {
                outputs.extend([Scalar::Bool(true), Scalar::Bool(false)]);
            } else {
                let ids = expressions;
                for side in 0..2 {
                    let (v, _, _, _) = super::super::super::environment::local_read::read_value(
                        env,
                        ids[side],
                        &actual[side],
                        &declarations[side].reading,
                    )?;
                    outputs.push(v.ok_or("numeric read witness is not determined")?);
                }
                if outputs[0] == outputs[1] {
                    return Err("numeric read witness does not refute equality".into());
                }
            }
            let mut arguments = origins.to_vec();
            let mut wire_bindings = vec![];
            for (p, v) in params[0].iter().zip(point) {
                let value = super::super::super::change_result::value(b, &v)?;
                arguments.push(value);
                wire_bindings.push(Json::obj([
                    ("name", Json::str(&p.name)),
                    ("type", p.ty.wire()),
                    ("value", value.wire()),
                ]));
            }
            let left = super::super::super::change_result::value(b, &outputs[0])?;
            let right = super::super::super::change_result::value(b, &outputs[1])?;
            arguments.extend([left, right]);
            let evidence = b.push(
                NodeType::Evidence,
                "evidence",
                Json::obj([
                    ("kind", Json::str("counterexample")),
                    (
                        "data",
                        Json::obj([
                            ("bindings", Json::Arr(wire_bindings)),
                            ("paths", Json::Arr(vec![])),
                            ("left", left.wire()),
                            ("right", right.wire()),
                            (
                                "facts",
                                Json::Arr(result.support.iter().map(Fact::wire).collect()),
                            ),
                        ]),
                    ),
                ]),
                arguments,
                None,
                None,
            )?;
            out.evidence.push(evidence);
            out.arguments.push(evidence);
            break;
        }
    }
    Ok(out)
}
