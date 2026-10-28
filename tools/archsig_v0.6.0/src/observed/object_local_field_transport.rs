//! 原始値・参照field値を、全引数と戻り値の実像で比較する。
use super::*;
use crate::{archmap::Slot, construction::FactPointer, law::model::Declaration};

pub(super) struct Comparison {
    pub values: NodeRef,
    pub status: Decision,
    pub arguments: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
    pub evidence: Vec<NodeRef>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
fn read_scalar(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    fact: &FactPointer,
    field: &str,
    ty: &Type,
    reading: &str,
    dependencies: &[NodeRef],
    c: &mut Control,
) -> Result<(Option<NodeRef>, Fact, Scope), ValidationFailure> {
    tick(c)?;
    let owner = env.subject(&fact.snapshot, &fact.subject)?;
    let slot = env.field(&fact.snapshot, &fact.subject, field)?;
    if slot.ty.erase() != *ty {
        return Err("local readのfield型が元式と違う".into());
    }
    let mut position = Fact {
        snapshot: fact.snapshot.clone(),
        subject: fact.subject.clone(),
        field: Some(field.into()),
        atom: None,
    };
    if let Some((reference, value)) = env.architecture_value(&position) {
        if value.ty() != *ty {
            return Err("local readの修復値の型が違う".into());
        }
        return Ok((Some(reference), position, env.architecture_scope()));
    }
    let scope = env.scope(
        owner,
        reading,
        match &slot.slot {
            Slot::Known { origin, .. } => Some(origin),
            Slot::Missing => None,
        },
    )?;
    let Slot::Known { atom, value, .. } = &slot.slot else {
        return Ok((None, position, scope));
    };
    let scalar = super::super::super::environment::scalar_from(value, ty, env.inputs.law(), c)?
        .ok_or("local field値の型付き読取りが未対応")?;
    position.atom = Some(atom.clone());
    let reference = b.push(
        NodeType::Value(ty.clone()),
        "binding",
        scalar.wire(),
        dependencies.to_vec(),
        Some(scalar),
        None,
    )?;
    let part = &mut b.parts[reference.0 - b.base];
    part.support.push(position.clone());
    part.support.sort();
    part.support.dedup();
    part.scope.merge(&scope);
    Ok((Some(reference), position, scope))
}
pub(super) fn compare(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    declarations: [&Declaration; 2],
    correspondence: &construction::DeclarationCorrespondence,
    maps: &[LocalParameter],
    applicable: Option<&[Vec<usize>]>,
    position: usize,
    names: &[String; 2],
    expressions: [usize; 2],
    origins: [NodeRef; 2],
    dependencies: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Comparison, ValidationFailure> {
    let types = [
        inputs
            .law()
            .expr_type(expressions[0])
            .ok_or("local fieldの元型がない")?
            .erase(),
        inputs
            .law()
            .expr_type(expressions[1])
            .ok_or("local fieldの先型がない")?
            .erase(),
    ];
    let reference = if let (Type::Ref(source), Type::Ref(target)) = (&types[0], &types[1]) {
        // mapsは同じ宣言対応・入力・依存から構成した型全域の写像。
        // 引数位置は保持したまま、戻り値と同じ参照型の写像だけを共有する。
        Some(
            if let Some(map) = maps
                .iter()
                .filter_map(LocalParameter::reference)
                .find(|map| &map.source == source && &map.target == target)
            {
                map.clone()
            } else {
                reference_map(b, inputs, correspondence, source, target, dependencies, c)?
            },
        )
    } else {
        None
    };
    let values = if let Some(map) = &reference {
        map.values
    } else {
        if types[0] != types[1] {
            return Err("異型local fieldの移送は未実装".into());
        }
        let identity = super::super::super::value_transport::identity_declarations(
            &types[0],
            inputs.law(),
            c,
        )?
        .ok_or("参照を含むlocal field値の移送は未実装")?;
        value_map(b, [&types[0], &types[1]], &[], &identity, dependencies)?
    };
    let identity_values = if let Some(map) = &reference {
        let mut identity = map.source == map.target;
        for (source, target) in map.transport.source().iter().zip(map.transport.images()) {
            tick(c)?;
            identity &= source == target;
        }
        identity
    } else {
        true
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
    // 引数の直積が空なら全ての句は空域上で可換。標本を作らない。
    if maps.iter().any(|map| map.len() == 0) {
        return Ok(result);
    }
    // このreadは一つの参照引数だけに依存する。残りの非空域との直積では
    // 同じ比較が繰り返されるため、依存する引数の全域を一度ずつ検査する。
    let map = maps[position]
        .reference()
        .ok_or("local field parameter is not a reference")?;
    let fields = [
        format!("{}.{}", map.source, names[0]),
        format!("{}.{}", map.target, names[1]),
    ];
    let rows;
    let rows = if let Some(rows) = applicable {
        rows
    } else {
        rows = (0..map.subjects.len())
            .map(|i| {
                let mut row = vec![0; maps.len()];
                row[position] = i;
                row
            })
            .collect::<Vec<_>>();
        &rows
    };
    for row in rows {
        let source = &map.transport.source()[row[position]];
        let target = &map.transport.images()[row[position]];
        tick(c)?;
        // 恒等移送の同じ元slotは全補完で同じ値。参照値には実写像を適用する。
        if identity_values && source == target && fields[0] == fields[1] {
            continue;
        }
        let (left, lf, ls) = read_scalar(
            b,
            env,
            source,
            &fields[0],
            &types[0],
            &declarations[0].reading,
            dependencies,
            c,
        )?;
        let (right, rf, rs) = read_scalar(
            b,
            env,
            target,
            &fields[1],
            &types[1],
            &declarations[1].reading,
            dependencies,
            c,
        )?;
        result.support.extend([lf.clone(), rf.clone()]);
        result.scope.merge(&ls);
        result.scope.merge(&rs);
        result.arguments.extend(left);
        result.arguments.extend(right);
        if left.is_none() || right.is_none() {
            result.status = merge_status(result.status, Decision::Undetermined);
            let mut missing = vec![];
            if left.is_none() {
                missing.push(lf);
            }
            if right.is_none() {
                missing.push(rf);
            }
            result.reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: origins.to_vec(),
                missing,
                location: Some(crate::issue::Location::Law {
                    span: inputs.law().exprs[expressions[0]].span,
                }),
            });
            continue;
        }
        let left = left.ok_or("local field左値がない")?;
        let right = right.ok_or("local field右値がない")?;
        let scalar = |r: NodeRef| -> Result<&Scalar, ValidationFailure> {
            if r.0 < b.base {
                b.g.scalar(r).map_err(Into::into)
            } else {
                b.parts[r.0 - b.base]
                    .scalar
                    .as_ref()
                    .ok_or_else(|| "local field値がScalarでない".into())
            }
        };
        let image;
        let left_value = if let Some(map) = &reference {
            let Scalar::Subject {
                snapshot, subject, ..
            } = scalar(left)?
            else {
                return Err("local参照field値が参照でない".into());
            };
            let mut mapped = None;
            for (source, target) in map.transport.source().iter().zip(map.transport.images()) {
                tick(c)?;
                if &source.snapshot == snapshot && &source.subject == subject {
                    mapped = Some(Scalar::Subject {
                        snapshot: target.snapshot.clone(),
                        subject: target.subject.clone(),
                        entity: map.target.clone(),
                    });
                    break;
                }
            }
            image = mapped.ok_or("local参照field値が元参照域にない")?;
            &image
        } else {
            scalar(left)?
        };
        let equal = super::super::super::value_equality::equal(
            left_value,
            scalar(right)?,
            inputs.law(),
            c,
        )?
        .ok_or("local field等値の算法は未実装")?;
        if !equal {
            result.status = Decision::Refuted;
            let Signature::Local { params, .. } = &declarations[0].signature else {
                return Err("local元宣言がない".into());
            };
            let evidence = counterexample(b, params, maps, row, left, right, &[lf, rf])?;
            result.arguments.push(evidence);
            result.evidence.push(evidence);
            break;
        }
    }
    Ok(result)
}

/// 引数の全組を列挙し、source適用域上で値写像とreadの可換性を比較する。
pub(super) fn compare_expression(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    declarations: [&Declaration; 2],
    maps: &[LocalParameter],
    value_parameter: Option<usize>,
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
    let values = if let Some(position) = value_parameter {
        maps[position].values()
    } else {
        if !super::super::super::environment::local_read::value_type_supported(&ty, inputs.law(), c)?
            || inputs.law().expr_type(expressions[1]).map(|ty| ty.erase()) != Some(ty.clone())
        {
            return Err("local readの型が同じ恒等移送の適用域にない".into());
        }
        let identities = super::super::super::value_transport::identity_declarations(&ty, inputs.law(), c)?
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
    let all_rows;
    let rows = if let Some(rows) = applicable {
        rows
    } else {
        all_rows = parameter_rows(maps, c)?;
        &all_rows
    };
    for row in rows {
        tick(c)?;
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
        let moved = if let Some(position) = value_parameter {
            let map = &maps[position];
            let mut found = None;
            for index in 0..map.len() {
                tick(c)?;
                if super::super::super::value_equality::equal(
                    left, &map.binding(index, 0), inputs.law(), c,
                )? == Some(true) {
                    found = Some(map.binding(index, 1));
                    break;
                }
            }
            image = found.ok_or("local read値が確認済み全域にない")?;
            &image
        } else {
            left
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
