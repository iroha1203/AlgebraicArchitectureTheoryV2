//! 全引数と戻り値の実像を、同じEvaluator・値移送で比較する。
use super::*;
use crate::law::model::Declaration;

pub(super) struct Comparison {
    pub values: NodeRef,
    pub status: Decision,
    pub arguments: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
    pub evidence: Vec<NodeRef>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
/// 引数の全組を列挙し、source適用域上で値写像とreadの可換性を比較する。
pub(super) fn compare_expression(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    declarations: [&Declaration; 2],
    correspondence: &construction::DeclarationCorrespondence,
    maps: &[LocalParameter],
    read_map: Option<&ReadValueMap>,
    direct: Option<(usize, &[String; 2])>,
    applicable: Option<&[Vec<usize>]>,
    expressions: [usize; 2],
    origins: [NodeRef; 2],
    dependencies: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Comparison, ValidationFailure> {
    let Signature::Local {
        params: source_params,
        ..
    } = &declarations[0].signature
    else {
        return Err("local readの元宣言がない".into());
    };
    let Signature::Local {
        params: target_params,
        ..
    } = &declarations[1].signature
    else {
        return Err("local readの先宣言がない".into());
    };
    let ty = inputs
        .law()
        .expr_type(expressions[0])
        .ok_or("local readの元型がない")?
        .erase();
    let values = if let Some(map) = read_map {
        map.values()
    } else {
        if !super::super::super::environment::local_read::value_type_supported(
            &ty,
            inputs.law(),
            c,
        )? || inputs.law().expr_type(expressions[1]).map(|ty| ty.erase()) != Some(ty.clone())
        {
            return Err("local readの型が同じ恒等移送の適用域にない".into());
        }
        let identities =
            super::super::super::value_transport::identity_declarations(&ty, inputs.law(), c)?
                .ok_or("local readの恒等値写像がない")?;
        value_map(b, [&ty, &ty], &[], &identities, dependencies)?
    };
    let mut result = Comparison {
        values,
        status: Decision::Established,
        arguments: vec![],
        reasons: vec![],
        evidence: vec![],
        support: vec![],
        scope: Scope::default(),
    };
    let identity_values = if direct.is_some() {
        match read_map {
            Some(map) => map.is_identity(c)?,
            None => true,
        }
    } else {
        false
    };
    let direct = direct
        .and_then(|(position, names)| maps[position].reference().map(|map| (position, names, map)));
    let all_rows;
    let rows = if let Some(rows) = applicable {
        rows
    } else {
        // 一つの参照引数だけに依存する直接fieldは、他の非空引数との
        // 直積で同じ比較を繰り返さない。guardがある場合は実適用行を使う。
        all_rows = if maps.iter().any(|map| map.len() == 0) {
            vec![]
        } else if let Some((position, _, map)) = direct {
            (0..map.subjects.len())
                .map(|i| {
                    let mut row = vec![0; maps.len()];
                    row[position] = i;
                    row
                })
                .collect()
        } else {
            parameter_rows(maps, c)?
        };
        &all_rows
    };
    for row in rows {
        tick(c)?;
        if let Some((position, names, map)) = direct {
            // 同じslotへの恒等値写像は、欠測を補完せず全補完で可換と分かる。
            if identity_values
                && map.source == map.target
                && names[0] == names[1]
                && map.transport.source()[row[position]] == map.transport.images()[row[position]]
            {
                continue;
            }
        }
        let mut values = vec![];
        let mut missing = vec![];
        let mut facts = vec![];
        for side in 0..2 {
            let params = if side == 0 {
                source_params
            } else {
                target_params
            };
            let mut bindings = vec![];
            for ((param, map), &index) in params.iter().zip(maps).zip(row) {
                tick(c)?;
                bindings.push((param.name.clone(), map.binding(index, side)));
            }
            let (value, support, scope, absent) =
                super::super::super::environment::local_read::read_value(
                    env,
                    expressions[side],
                    &bindings,
                    &declarations[side].reading,
                )?;
            facts.extend(support.iter().cloned());
            result.support.extend(support);
            result.scope.merge(&scope);
            missing.extend(absent);
            values.push(value);
        }
        let [Some(left), Some(right)] = values.as_slice() else {
            result.status = merge_status(result.status, Decision::Undetermined);
            missing.sort();
            missing.dedup();
            result.reasons.push(Reason {
                kind: if missing.is_empty() {
                    ReasonKind::UnsupportedAlgorithm {
                        question: request.kind,
                        operand_types: vec![ty.clone()],
                        method: match ty {
                            Type::Bool => "local_boolean_read_transport",
                            Type::Q => "local_rational_read_transport",
                            Type::Z => "local_integer_read_transport",
                            _ => "local_finite_read_transport",
                        }
                        .into(),
                    }
                } else {
                    ReasonKind::Missing
                },
                request: request.id.clone(),
                dependencies: origins.to_vec(),
                missing,
                location: Some(crate::issue::Location::Law {
                    span: inputs.law().exprs[expressions[0]].span,
                }),
            });
            continue;
        };
        let image;
        let moved = match read_map {
            Some(ReadValueMap::Finite(transport, _)) => {
                image = transport.forward_scalar(left, c).map_err(failure)?;
                &image
            }
            Some(ReadValueMap::Structural(_, _)) => {
                image = super::super::super::value_transport::candidate_image(
                    inputs,
                    correspondence,
                    &declarations[0].name,
                    left,
                    c,
                )
                .map_err(failure)?;
                &image
            }
            None => left,
        };
        let equal = super::super::super::value_equality::equal(moved, right, inputs.law(), c)?
            .ok_or("local read等値の算法は未実装")?;
        if !equal {
            let left = super::super::super::change_result::value(b, left)?;
            let right = super::super::super::change_result::value(b, right)?;
            facts.sort();
            facts.dedup();
            let evidence = counterexample(b, source_params, maps, row, left, right, &facts)?;
            result.status = Decision::Refuted;
            result.arguments.push(evidence);
            result.evidence.push(evidence);
            break;
        }
    }
    Ok(result)
}
