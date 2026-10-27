//! changeの候補域と同時更新を、実引数の対応に沿って検査する。
use super::*;
use crate::observed::{
    change_result,
    environment::{change_affine, change_evaluation},
    integer_fiber,
};
use num_bigint::BigInt as Z;
use num_traits::Zero;
use std::collections::BTreeSet;

fn unsupported(
    inputs: &super::super::super::input::CheckedInputs,
    id: usize,
    message: &str,
) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: crate::issue::Location::Law {
            span: inputs.law().exprs[id].span,
        },
        feature: message.into(),
    }
}
struct Updates {
    base: usize,
    fields: Vec<String>,
    plain: Option<Vec<(String, usize)>>,
}
fn updates(
    env: &Environment<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    declaration: &crate::law::model::Declaration,
    mut id: usize,
    c: &mut Control,
) -> Result<Updates, ValidationFailure> {
    while let ExprKind::Group(inner) = inputs.law().exprs[id].kind {
        tick(c)?;
        id = inner;
    }
    if let ExprKind::With { base, updates } = &inputs.law().exprs[id].kind {
        return Ok(Updates {
            base: *base,
            fields: updates.iter().map(|(name, _)| name.name.clone()).collect(),
            plain: Some(
                updates
                    .iter()
                    .map(|(name, id)| (name.name.clone(), *id))
                    .collect(),
            ),
        });
    }
    let (base, fields) = change_evaluation::update_shape(env, declaration)?;
    Ok(Updates {
        base,
        fields,
        plain: None,
    })
}
fn update_expression(
    b: &mut Builder<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    updates: &Updates,
    body: Option<NodeRef>,
    field: &str,
    entity: &str,
    ty: &Type,
    params: &[Param],
    dependencies: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    if let Some(plain) = &updates.plain {
        let id = plain
            .iter()
            .find(|(name, _)| name == field)
            .ok_or("元更新句がない")?
            .1;
        return expression(b, inputs, id, params, dependencies);
    }
    let source = body.ok_or("change全体の元式がない")?;
    b.push(
        NodeType::Expression(ty.clone()),
        "expression",
        Json::obj([
            ("kind", Json::str("change_update")),
            ("source", source.wire()),
            ("field", Json::str(format!("{entity}.{field}"))),
            (
                "parameters",
                Json::Arr(
                    params
                        .iter()
                        .map(|p| Json::obj([("name", Json::str(&p.name)), ("type", p.ty.wire())]))
                        .collect(),
                ),
            ),
            ("bindings", Json::Arr(vec![])),
        ]),
        vec![source],
        None,
        None,
    )
}
fn guard_expression(
    b: &mut Builder<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    guard: Option<usize>,
    base: usize,
    params: &[Param],
    dependencies: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    if let Some(id) = guard {
        return expression(b, inputs, id, params, dependencies);
    }
    // 省略guardのtrueは、必ず束縛される第1参照の自己等値で表す。
    let base = expression(b, inputs, base, params, dependencies)?;
    b.push(
        NodeType::Expression(Type::Bool),
        "expression",
        Json::obj([
            ("kind", Json::str("transform")),
            ("operation", Json::str("equal")),
            ("operands", Json::Arr(vec![base.wire(), base.wire()])),
            (
                "parameters",
                Json::Arr(
                    params
                        .iter()
                        .map(|p| Json::obj([("name", Json::str(&p.name)), ("type", p.ty.wire())]))
                        .collect(),
                ),
            ),
            ("bindings", Json::Arr(vec![])),
        ]),
        vec![base],
        None,
        None,
    )
}
fn example(
    b: &mut Builder<'_>,
    params: &[Param],
    bindings: &[(String, Scalar)],
    left: Scalar,
    right: Scalar,
    facts: &[Fact],
) -> Result<NodeRef, ValidationFailure> {
    let left = change_result::value(b, &left)?;
    let right = change_result::value(b, &right)?;
    let mut args = vec![left, right];
    let mut bound = vec![];
    for (p, (name, value)) in params.iter().zip(bindings) {
        let value = change_result::value(b, value)?;
        args.push(value);
        bound.push(Json::obj([
            ("name", Json::str(name)),
            ("type", p.ty.wire()),
            ("value", value.wire()),
        ]));
    }
    b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str("counterexample")),
            (
                "data",
                Json::obj([
                    ("bindings", Json::Arr(bound)),
                    ("paths", Json::Arr(vec![])),
                    ("left", left.wire()),
                    ("right", right.wire()),
                    ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                ]),
            ),
        ]),
        args,
        None,
        None,
    )
}
fn pending(
    check: &mut field::Comparison,
    missing: Vec<Fact>,
    request: &Request,
    origins: &[NodeRef],
    span: (usize, usize),
) {
    check.status = merge_status(check.status, Decision::Undetermined);
    check.reasons.push(Reason {
        kind: if missing.is_empty() {
            ReasonKind::UnsupportedAlgorithm {
                question: request.kind,
                operand_types: vec![],
                method: "change_transport".into(),
            }
        } else {
            ReasonKind::Missing
        },
        request: request.id.clone(),
        dependencies: origins.to_vec(),
        missing,
        location: Some(crate::issue::Location::Law { span }),
    });
}
fn update_value<'a>(
    values: &'a [(Fact, Scalar)],
    name: &str,
) -> Result<&'a (Fact, Scalar), ValidationFailure> {
    values
        .iter()
        .find(|(f, _)| {
            f.field
                .as_ref()
                .is_some_and(|field| field.rsplit('.').next() == Some(name))
        })
        .ok_or_else(|| ValidationFailure::from("change移送の名前付き更新先がない"))
}
fn point(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    declarations: [&crate::law::model::Declaration; 2],
    params: [&[Param]; 2],
    guards: [Option<usize>; 2],
    subjects: [Scalar; 2],
    values: &[Scalar],
    names: &[[String; 2]],
    checks: &mut [field::Comparison],
    origins: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let bindings = [0, 1].map(|side| {
        std::iter::once((params[side][0].name.clone(), subjects[side].clone()))
            .chain(
                params[side][1..]
                    .iter()
                    .zip(values)
                    .map(|(p, v)| (p.name.clone(), v.clone())),
            )
            .collect::<Vec<_>>()
    });
    let mut truth = [Some(true); 2];
    let mut facts = vec![];
    let mut scope = Scope::default();
    let mut missing = vec![];
    for side in 0..2 {
        if let Some(id) = guards[side] {
            let (v, support, reading, absent) =
                super::super::super::environment::local_read::guard_value(
                    env,
                    id,
                    &bindings[side],
                    &declarations[side].reading,
                )?;
            truth[side] = v;
            facts.extend(support);
            scope.merge(&reading);
            missing.extend(absent);
        }
    }
    for check in checks.iter_mut() {
        check.support.extend(facts.iter().cloned());
        check.scope.merge(&scope);
    }
    if truth.iter().any(Option::is_none) {
        missing.sort();
        missing.dedup();
        pending(
            &mut checks[0],
            missing,
            request,
            origins,
            declarations[0].span,
        );
        return Ok(());
    }
    if truth[0] != truth[1] {
        let evidence = example(
            b,
            params[0],
            &bindings[0],
            Scalar::Bool(truth[0].ok_or("元guard値がない")?),
            Scalar::Bool(truth[1].ok_or("先guard値がない")?),
            &facts,
        )?;
        checks[0].status = Decision::Refuted;
        checks[0].evidence.push(evidence);
        checks[0].arguments.push(evidence);
        return Ok(());
    }
    if truth[0] == Some(false) {
        return Ok(());
    }
    let left = change_evaluation::evaluate(env, declarations[0], &bindings[0])?;
    let right = change_evaluation::evaluate(env, declarations[1], &bindings[1])?;
    for check in checks.iter_mut() {
        check
            .support
            .extend(left.support.iter().chain(&right.support).cloned());
        check.scope.merge(&left.scope);
        check.scope.merge(&right.scope);
    }
    if matches!(
        left.state,
        change_evaluation::State::ConditionFailed | change_evaluation::State::Excluded
    ) || matches!(
        right.state,
        change_evaluation::State::ConditionFailed | change_evaluation::State::Excluded
    ) {
        for check in &mut checks[1..] {
            pending(check, vec![], request, origins, declarations[0].span);
        }
        return Ok(());
    }
    for (i, name) in names.iter().enumerate() {
        tick(c)?;
        let (Ok((lf, lv)), Ok((rf, rv))) = (
            update_value(&left.values, &name[0]),
            update_value(&right.values, &name[1]),
        ) else {
            let mut missing = left.missing.clone();
            missing.extend(right.missing.iter().cloned());
            missing.sort();
            missing.dedup();
            pending(
                &mut checks[i + 1],
                missing,
                request,
                origins,
                declarations[0].span,
            );
            continue;
        };
        let equal = super::super::super::value_equality::equal(lv, rv, env.inputs.law(), c)?;
        if equal.is_none() {
            pending(
                &mut checks[i + 1],
                vec![],
                request,
                origins,
                declarations[0].span,
            );
            continue;
        }
        if equal == Some(false) {
            let evidence = example(
                b,
                params[0],
                &bindings[0],
                lv.clone(),
                rv.clone(),
                &[lf.clone(), rf.clone()],
            )?;
            checks[i + 1].status = Decision::Refuted;
            checks[i + 1].evidence.push(evidence);
            checks[i + 1].arguments.push(evidence);
        }
    }
    Ok(())
}
// originと整数核の全基底で線形式を確認する。反例点の選択であり標本検査ではない。
fn violation(
    fiber: &integer_fiber::Fiber,
    row: &[Z],
    rhs: &Z,
    c: &mut Control,
) -> Result<Option<Vec<Z>>, ValidationFailure> {
    let Some(origin) = &fiber.particular else {
        return Ok(None);
    };
    if row.len() != origin.len() {
        return Err("change移送の整数parameter次元が違う".into());
    }
    let dot = |point: &[Z]| row.iter().zip(point).map(|(a, b)| a * b).sum::<Z>();
    if dot(origin) != *rhs {
        return Ok(Some(origin.clone()));
    }
    let cols = fiber.kernel.first().map_or(0, Vec::len);
    for j in 0..cols {
        tick(c)?;
        let direction = fiber
            .kernel
            .iter()
            .map(|r| r[j].clone())
            .collect::<Vec<_>>();
        if !dot(&direction).is_zero() {
            return Ok(Some(
                origin.iter().zip(direction).map(|(a, b)| a + b).collect(),
            ));
        }
    }
    Ok(None)
}
pub(super) fn outside(
    left: &change_affine::Guard,
    right: &change_affine::Guard,
    c: &mut Control,
) -> Result<Option<Vec<Z>>, ValidationFailure> {
    if left.fiber.particular.is_none() {
        return Ok(None);
    }
    if right.fiber.particular.is_none() {
        return Ok(left.fiber.particular.clone());
    }
    for (row, rhs) in right.equations.iter().zip(&right.rhs) {
        if let Some(point) = violation(&left.fiber, row, rhs, c)? {
            return Ok(Some(point));
        }
    }
    Ok(None)
}

pub(super) fn retain(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    inputs: &super::super::super::input::CheckedInputs,
    correspondence: &construction::DeclarationCorrespondence,
    candidate: &construction::DeclarationCandidate,
    dependencies: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let pair = candidate.pair().ok_or("changeの対応署名がない")?;
    let declarations = [
        &inputs.law().declarations[pair.source()],
        &inputs.law().declarations[pair.target()],
    ];
    let mut params = vec![];
    let mut guards = vec![];
    let mut bodies = vec![];
    let mut items = vec![];
    for d in declarations {
        let Signature::Change {
            params: ps,
            guard,
            body,
        } = &d.signature
        else {
            return Err("change移送の元宣言が違う".into());
        };
        params.push(ps.as_slice());
        guards.push(*guard);
        bodies.push(*body);
    }
    for (side, declaration) in declarations.iter().enumerate() {
        match updates(env, inputs, declaration, bodies[side], c) {
            Ok(item) => items.push(item),
            Err(ValidationFailure::UnsupportedExpression { location, feature }) => {
                let mut origins = vec![];
                for index in 0..2 {
                    origins.push(expression(
                        b,
                        inputs,
                        bodies[index],
                        params[index],
                        dependencies,
                    )?);
                }
                return Ok(Output {
                    transports: vec![],
                    status: Decision::Undetermined,
                    reasons: vec![Reason {
                        kind: ReasonKind::UnsupportedAlgorithm {
                            question: request.kind,
                            operand_types: vec![],
                            method: feature,
                        },
                        request: request.id.clone(),
                        dependencies: origins,
                        missing: vec![],
                        location: Some(location),
                    }],
                    evidence: vec![],
                });
            }
            Err(error) => return Err(error),
        }
    }
    if params[0].is_empty() || params[0].len() != params[1].len() {
        return Err("change移送の引数数が違う".into());
    }
    let (Type::Ref(st), Type::Ref(tt)) = (&params[0][0].ty.erase(), &params[1][0].ty.erase())
    else {
        return Err("change第1引数が参照でない".into());
    };
    let reference = reference_map(b, inputs, correspondence, st, tt, dependencies, c)?;
    let mut names = vec![];
    for name in &items[0].fields {
        let moved = correspondence
            .field_target(inputs, &format!("{st}.{name}"), c)
            .map_err(failure)?
            .ok_or_else(|| unsupported(inputs, bodies[0], "missing field correspondence for the change update target"))?;
        let target = moved
            .strip_prefix(&format!("{tt}."))
            .ok_or("change更新先の型対応が違う")?
            .to_owned();
        names.push([name.clone(), target]);
    }
    let mut expected = names.iter().map(|n| n[1].clone()).collect::<Vec<_>>();
    expected.sort();
    let mut actual = items[1].fields.clone();
    actual.sort();
    if expected != actual {
        return Err(unsupported(
            inputs,
            bodies[0],
            "change transport with noncorresponding update target sets is not implemented",
        ));
    }
    let mut identity = vec![];
    for (s, t) in params[0][1..].iter().zip(&params[1][1..]) {
        if s.ty != t.ty {
            return Err(unsupported(
                inputs,
                bodies[0],
                "transport of change value parameters with different types is not implemented",
            ));
        }
        identity.extend(
            super::super::super::value_transport::identity_declarations(&s.ty, inputs.law(), c)?
                .ok_or("change値parameterの写像が未対応")?,
        );
    }
    identity.extend(correspondence.types().iter().cloned());
    identity.sort();
    identity.dedup();
    let types = [0, 1].map(|side| Type::Tuple(params[side].iter().map(|p| p.ty.erase()).collect()));
    let arguments = value_map(
        b,
        [&types[0], &types[1]],
        &reference.subjects,
        &identity,
        dependencies,
    )?;
    let mut expressions = vec![[
        guard_expression(b, inputs, guards[0], items[0].base, params[0], dependencies)?,
        guard_expression(b, inputs, guards[1], items[1].base, params[1], dependencies)?,
    ]];
    let mut body_sources = [None, None];
    for side in 0..2 {
        if items[side].plain.is_none() {
            body_sources[side] = Some(expression(
                b,
                inputs,
                bodies[side],
                params[side],
                dependencies,
            )?);
        }
    }
    let mut update_types = vec![];
    for name in &names {
        let mut types = vec![];
        let mut origins = vec![];
        for (side, entity) in [st, tt].into_iter().enumerate() {
            let ty = inputs
                .definitions()
                .declarations
                .get(entity)
                .and_then(|d| d.signature.field(&name[side]))
                .ok_or("change更新fieldの宣言型がない")?
                .ty
                .erase();
            origins.push(update_expression(
                b,
                inputs,
                &items[side],
                body_sources[side],
                &name[side],
                entity,
                &ty,
                params[side],
                dependencies,
            )?);
            types.push(ty);
        }
        expressions.push([origins[0], origins[1]]);
        update_types.push(types);
    }
    let mut checks = vec![];
    for (i, origins) in expressions.iter().enumerate() {
        let (ty, target_ty) = if i == 0 {
            (Type::Bool, Type::Bool)
        } else {
            (
                update_types[i - 1][0].clone(),
                update_types[i - 1][1].clone(),
            )
        };
        if ty != target_ty {
            return Err(unsupported(
                inputs,
                bodies[0],
                "transport of change update values with different types is not implemented",
            ));
        }
        let identity =
            super::super::super::value_transport::identity_declarations(&ty, inputs.law(), c)?
                .ok_or("change更新値写像が未対応")?;
        let values = value_map(b, [&ty, &target_ty], &[], &identity, dependencies)?;
        checks.push(field::Comparison {
            values,
            status: Decision::Established,
            arguments: origins.to_vec(),
            reasons: vec![],
            evidence: vec![],
            support: vec![],
            scope: Scope::default(),
        });
    }
    // changeの第1binderは元対象内のinstance。固定外部参照を更新対象へ追加しない。
    let map = correspondence.operation().map().candidate();
    let instances = reference
        .transport
        .source()
        .iter()
        .enumerate()
        .filter(|(_, fact)| map.source_configuration().family().contains(fact))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    let targets = reference
        .transport
        .target()
        .iter()
        .filter(|fact| map.target_configuration().family().contains(fact))
        .cloned()
        .collect::<BTreeSet<_>>();
    let images = instances
        .iter()
        .map(|&i| reference.transport.images()[i].clone())
        .collect::<BTreeSet<_>>();
    // 独立なinstanceのparameter直積を運べる場合だけ組み立てる。合流や未到達域を既定値で埋めない。
    let instance_bijection = images.len() == instances.len() && images == targets;
    let first_values = instances
        .iter()
        .map(|&i| reference.subjects[i].0)
        .collect::<Vec<_>>();
    let first_domain = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("finite")),
            ("type", params[0][0].ty.erase().wire()),
            (
                "elements",
                Json::Arr(first_values.iter().map(|r| r.wire()).collect()),
            ),
        ]),
        first_values,
        None,
        None,
    )?;
    b.parts[first_domain.0 - b.base].domain_type = Some(params[0][0].ty.erase());
    if !instance_bijection {
        for check in &mut checks {
            pending(
                check,
                vec![],
                request,
                &expressions[0],
                declarations[0].span,
            );
        }
    }
    let ps = [params[0], params[1]];
    let gs = [guards[0], guards[1]];
    let affine = !params[0][1..].is_empty() && params[0][1..].iter().all(|p| p.ty == Type::Z);
    let finite = if affine {
        None
    } else {
        Some(env.finite_values(
            &Type::Tuple(params[0][1..].iter().map(|p| p.ty.clone()).collect()),
            &mut |_, _| {},
        )?)
    };
    for &instance in instances.iter().filter(|_| instance_bijection) {
        let source = &reference.transport.source()[instance];
        let target = &reference.transport.images()[instance];
        tick(c)?;
        let subjects = [
            Scalar::Subject {
                snapshot: source.snapshot.clone(),
                subject: source.subject.clone(),
                entity: st.clone(),
            },
            Scalar::Subject {
                snapshot: target.snapshot.clone(),
                subject: target.subject.clone(),
                entity: tt.clone(),
            },
        ];
        if let Some(domain) = &finite {
            for tuple in &domain.values {
                let Scalar::Tuple(values) = tuple else {
                    return Err("change値域がTupleでない".into());
                };
                point(
                    env,
                    b,
                    declarations,
                    ps,
                    gs,
                    subjects.clone(),
                    values,
                    &names,
                    &mut checks,
                    &expressions[0],
                    request,
                    c,
                )?;
            }
        } else {
            let mut domains = vec![];
            for side in 0..2 {
                let mut metadata = change_affine::Pending::default();
                let result = change_affine::guard_domain(
                    env,
                    declarations[side],
                    &subjects[side],
                    &mut metadata,
                );
                for check in &mut checks {
                    check.support.extend(metadata.support.iter().cloned());
                    check.scope.merge(&metadata.scope);
                }
                match result {
                    Ok(domain) => domains.push(domain),
                    Err(ValidationFailure::UnsupportedExpression { .. }) => {
                        metadata.facts.sort();
                        metadata.facts.dedup();
                        pending(
                            &mut checks[0],
                            metadata.facts,
                            request,
                            &expressions[0],
                            declarations[side].span,
                        );
                        break;
                    }
                    Err(error) => return Err(error),
                }
            }
            if domains.len() != 2 {
                continue;
            }
            if let Some(witness) =
                outside(&domains[0], &domains[1], c)?.or(outside(&domains[1], &domains[0], c)?)
            {
                let values = witness.into_iter().map(Scalar::Z).collect::<Vec<_>>();
                point(
                    env,
                    b,
                    declarations,
                    ps,
                    gs,
                    subjects.clone(),
                    &values,
                    &names,
                    &mut checks,
                    &expressions[0],
                    request,
                    c,
                )?;
                continue;
            }
            if domains[0].fiber.particular.is_none() {
                continue;
            }
            for (index, name) in names.iter().enumerate() {
                let mut forms = vec![];
                for side in 0..2 {
                    let mut metadata = change_affine::Pending::default();
                    let result = change_affine::compute_update(
                        env,
                        declarations[side],
                        &subjects[side],
                        &name[side],
                        &mut metadata,
                    );
                    checks[index + 1].support.extend(metadata.support);
                    checks[index + 1].scope.merge(&metadata.scope);
                    match result {
                        Ok(form) => forms.push(form),
                        Err(ValidationFailure::UnsupportedExpression { .. }) => {
                            metadata.facts.sort();
                            metadata.facts.dedup();
                            pending(
                                &mut checks[index + 1],
                                metadata.facts,
                                request,
                                &expressions[index + 1],
                                declarations[side].span,
                            );
                            break;
                        }
                        Err(error) => return Err(error),
                    }
                }
                if forms.len() != 2 {
                    continue;
                }
                let ((left_row, left_offset), (right_row, right_offset)) = (&forms[0], &forms[1]);
                let row = left_row
                    .iter()
                    .zip(right_row)
                    .map(|(a, b)| a - b)
                    .collect::<Vec<_>>();
                let rhs = right_offset - left_offset;
                if let Some(witness) = violation(&domains[0].fiber, &row, &rhs, c)? {
                    let values = witness.into_iter().map(Scalar::Z).collect::<Vec<_>>();
                    point(
                        env,
                        b,
                        declarations,
                        ps,
                        gs,
                        subjects.clone(),
                        &values,
                        &names,
                        &mut checks,
                        &expressions[0],
                        request,
                        c,
                    )?;
                }
            }
        }
    }
    let guard_status = checks[0].status;
    let guard_reasons = checks[0].reasons.clone();
    let guard_evidence = checks[0].evidence.clone();
    let mut out = Output {
        transports: vec![],
        status: Decision::Established,
        reasons: vec![],
        evidence: vec![],
    };
    let mut clauses = vec![];
    let mut all = dependencies.to_vec();
    all.extend([arguments, first_domain]);
    for (index, (origins, mut check)) in expressions.into_iter().zip(checks).enumerate() {
        if index > 0 {
            check.status = merge_status(check.status, guard_status);
            check.reasons.extend(guard_reasons.iter().cloned());
            check.evidence.extend(guard_evidence.iter().copied());
            check.arguments.extend(guard_evidence.iter().copied());
        }
        check.arguments.push(first_domain);
        let commutes = b.proposition(
            "declaration_transport",
            vec![origins[0], origins[1], arguments, check.values],
            check.arguments,
            check.status,
        )?;
        let part = &mut b.parts[commutes.0 - b.base];
        part.support = check.support;
        part.support.sort();
        part.support.dedup();
        part.scope.merge(&check.scope);
        part.scope.assignments = true;
        let quantifiers = params[0]
            .iter()
            .enumerate()
            .map(|(index, p)| Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: p.name.clone(),
                ty: p.ty.clone(),
                domain: if index == 0 { Some(first_domain) } else { None },
                occurrence: p.span,
                context: None,
            })
            .collect::<Vec<_>>();
        part.scope.quantifiers.extend(quantifiers.iter().cloned());
        if let Json::Obj(wire) = &mut part.wire {
            wire.insert(
                "quantifiers".into(),
                Json::Arr(quantifiers.iter().map(Quantifier::wire).collect()),
            );
        }
        sort_reasons(&mut check.reasons);
        part.reasons = check.reasons.clone();
        part.evidence = check.evidence.clone();
        if let Some(judgment) = &mut part.judgment {
            judgment.reasons = part.reasons.clone();
            judgment.evidence = part.evidence.clone();
        }
        out.status = merge_status(out.status, check.status);
        out.reasons.extend(check.reasons);
        out.evidence.extend(check.evidence);
        all.extend([origins[0], origins[1], check.values, commutes]);
        clauses.push(Json::obj([
            ("source", origins[0].wire()),
            ("target", origins[1].wire()),
            ("arguments", arguments.wire()),
            ("values", check.values.wire()),
            ("commutes", commutes.wire()),
        ]));
    }
    out.transports.push(
        b.push(
            NodeType::Construction(T::DeclarationTransport),
            "declaration_transport",
            Json::obj([
                ("kind", Json::str("change")),
                ("source", Json::str(&declarations[0].name)),
                ("target", Json::str(&declarations[1].name)),
                (
                    "parameters",
                    Json::Arr(
                        pair.parameters()
                            .iter()
                            .map(|(a, z)| Json::Arr(vec![Json::str(a), Json::str(z)]))
                            .collect(),
                    ),
                ),
                ("clauses", Json::Arr(clauses)),
            ]),
            all,
            None,
            None,
        )?,
    );
    Ok(out)
}
