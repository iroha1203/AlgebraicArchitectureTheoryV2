//! 明示localの各instanceが公開する直接読取り。依存と読取り権限を分ける。
use super::*;
use crate::observed::{build_result::Builder, change_result, local_result};
use crate::{
    canonical::Json,
    law::model::{Declaration, Signature},
};

pub(in crate::observed) struct Context {
    pub locals: Vec<Json>,
    pub carrier: Vec<Json>,
    pub positions: Vec<Fact>,
    pub visible: Vec<Fact>,
    pub read_supports: Vec<local_result::geometry::Support>,
    pub read_refs: Vec<NodeRef>,
    pub projections: Vec<local_result::geometry::Projection>,
    pub readings: Vec<Json>,
    pub arguments: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
    pub scope: Scope,
    pub information: Option<(Vec<Fact>, crate::observed::field_fiber::Matrix)>,
    pub read_information: Vec<Option<(Vec<Fact>, crate::observed::field_fiber::Matrix)>>,
}
fn unsupported(span: (usize, usize), feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span },
        feature: feature.into(),
    }
}
fn known(value: Scalar) -> SourceValue {
    SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        scope: Scope::default(),
        known_value: Some(value),
        affine: None,
        support: vec![],
        scalar_scope: Some(Scope::default()),
    }
}
fn subject_carrier(
    value: &Scalar,
    carrier: &mut Vec<Json>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match value {
            Scalar::Subject { .. } => carrier.push(Json::obj([
                ("type", value.ty().wire()),
                ("value", value.wire()),
            ])),
            Scalar::Tuple(items) => pending.extend(items.iter().rev()),
            _ => {}
        }
    }
    Ok(())
}

fn positions(facts: &[Fact]) -> impl Iterator<Item = Fact> + '_ {
    facts.iter().filter(|f| f.field.is_some()).map(|f| Fact {
        atom: None,
        ..f.clone()
    })
}
fn evaluate_read(
    env: &Environment<'_>,
    id: usize,
    variables: &BTreeMap<String, SourceValue>,
    scope: &Scope,
    reading: &str,
) -> Result<(SourceValue, Vec<Fact>, Vec<Fact>), ValidationFailure> {
    let outer_missing = env.missing_slot_reads.replace(Some(BTreeSet::new()));
    let outer_reads = env.primitive_reads.replace(Some(BTreeSet::new()));
    let value = env.scoped_ast(id, variables, scope, reading);
    let reads = env
        .primitive_reads
        .replace(outer_reads)
        .ok_or("localの読取り収集がない")?;
    let missing = env
        .missing_slot_reads
        .replace(outer_missing)
        .ok_or("localの欠測収集がない")?;
    if let Some(outer) = env.primitive_reads.borrow_mut().as_mut() {
        outer.extend(reads.iter().cloned());
    }
    if let Some(outer) = env.missing_slot_reads.borrow_mut().as_mut() {
        outer.extend(missing.iter().cloned());
    }
    Ok((
        value?,
        reads.into_iter().collect(),
        missing
            .into_iter()
            .filter(|f| {
                !env.primitive_valuation
                    .as_ref()
                    .is_some_and(|v| v.contains_key(f))
            })
            .collect(),
    ))
}
// 値/guardに必要な欠測を収集する。局所幾何の全読取り位置の収集とは区別する。
fn evaluate_value(
    env: &Environment<'_>, id: usize, variables: &BTreeMap<String, SourceValue>,
    scope: &Scope, reading: &str,
) -> Result<(SourceValue, Vec<Fact>, Vec<Fact>), ValidationFailure> {
    let outer = env.value_read.replace(true);
    let result = evaluate_read(env, id, variables, scope, reading);
    env.value_read.set(outer);
    result
}

/// local移送でも、直接読取りと同じEvaluator・適合条件でguardを確認する。
pub(in crate::observed) fn guard_value(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
) -> Result<(Option<bool>, Vec<Fact>, Scope, Vec<Fact>), ValidationFailure> {
    let variables = bindings
        .iter()
        .map(|(name, value)| (name.clone(), known(value.clone())))
        .collect();
    let mut scope = Scope::default();
    scope.readings.insert(reading.into());
    let (value, _, missing) = evaluate_value(env, id, &variables, &scope, reading)?;
    if value.condition_failed {
        return Err(unsupported(
            env.inputs.law().exprs[id].span,
            "local guardの式の適合条件が不成立",
        ));
    }
    let result = if value.condition_pending {
        None
    } else {
        match value.known_value.as_ref() {
            Some(Scalar::Bool(value)) => Some(*value),
            None => None,
            _ => return Err("local guardがBoolでない".into()),
        }
    };
    // 評価cacheの有無に依存しない、型付き結果の支持を保持する。
    let mut support = value.support.clone();
    support.sort();
    support.dedup();
    Ok((result, support, value.scope, missing))
}

/// 既存値演算と恒等写像を持つ、参照を含まない型。
pub(in crate::observed) fn value_type_supported(
    ty: &Type,
    law: &crate::law::CheckedLaw,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    Ok(super::super::data::supported(ty, law, c)?
        && super::super::value_transport::identity_declarations(ty, law, &mut c.clone())?.is_some())
}

/// 全参照作用とscalar恒等写像をTuple/List/Set/Optionへ延長できる型。
/// Map等は実値の検査だけで全域性を代用しない。
pub(in crate::observed) fn reference_value_type_supported(
    ty: &Type,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    let mut pending = vec![ty];
    let mut reference = false;
    while let Some(ty) = pending.pop() {
        c.clone().checkpoint(Checkpoint::ObjectViewTransport)?;
        match ty {
            Type::Ref(_) => reference = true,
            Type::Tuple(items) => pending.extend(items),
            Type::Option(item) | Type::List(item) | Type::Set(item) => pending.push(item),
            Type::Unit | Type::Bool | Type::Fp(_) | Type::Z | Type::Q | Type::Text => {}
            _ => return Ok(false),
        }
    }
    Ok(reference)
}

/// 引数を束縛したlocal readを、通常Evaluatorで評価する。
pub(in crate::observed) fn read_value(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
) -> Result<(Option<Scalar>, Vec<Fact>, Scope, Vec<Fact>), ValidationFailure> {
    let ty = env
        .inputs
        .law()
        .expr_type(id)
        .ok_or("local readの型がない")?
        .erase();
    if !value_type_supported(&ty, env.inputs.law(), &env.control)?
        && !super::super::finite::supported(&ty, env.inputs.law(), &env.control)?
        && !reference_value_type_supported(&ty, &env.control)?
    {
        return Err("local readの値型は既存の評価域外".into());
    }
    let variables = bindings
        .iter()
        .map(|(name, value)| (name.clone(), known(value.clone())))
        .collect();
    let mut scope = Scope::default();
    scope.readings.insert(reading.into());
    let (value, _, missing) = evaluate_value(env, id, &variables, &scope, reading)?;
    if value.condition_failed {
        return Err(unsupported(
            env.inputs.law().exprs[id].span,
            "local readの式の適合条件が不成立",
        ));
    }
    let result = if value.condition_pending {
        None
    } else {
        value.known_value
    };
    if result.as_ref().is_some_and(|value| value.ty() != ty) {
        return Err("local readの評価値の型が元式と違う".into());
    }
    let mut support = value.support;
    support.sort();
    support.dedup();
    Ok((result, support, value.scope, missing))
}

/// 暗黙contextの公開読取りを、その式が実際に参照する位置へ制限する。
pub(in crate::observed) fn implicit_support(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
    c: &mut Control,
) -> Result<(Vec<Json>, Vec<Fact>), ValidationFailure> {
    implicit_support_with_parameters(env, id, bindings, &[], reading, c)
}
pub(in crate::observed) fn implicit_support_with_parameters(
    env: &Environment<'_>, id: usize, bindings: &[(String, Scalar)],
    parameters: &[crate::law::model::Param], reading: &str, c: &mut Control,
) -> Result<(Vec<Json>, Vec<Fact>), ValidationFailure> {
    let (mut variables, _) = change_affine::law_variables(env, parameters, &[])?;
    variables.extend(bindings
        .iter()
        .map(|(n, v)| (n.clone(), known(v.clone()))));
    let (value, reads, missing) = evaluate_read(env, id, &variables, &Scope::default(), reading)?;
    if !missing.is_empty() {
        return Err("確定した暗黙読取りに欠測がある".into());
    }
    let mut carrier = vec![];
    for (_, value) in bindings {
        subject_carrier(value, &mut carrier, c)?;
    }
    if let Some(value) = value.known_value {
        subject_carrier(&value, &mut carrier, c)?;
    }
    for fact in &reads {
        let subject = env.subject(&fact.snapshot, &fact.subject)?;
        subject_carrier(
            &Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: subject.ty.clone(),
            },
            &mut carrier,
            c,
        )?;
    }
    carrier.sort_by_key(Json::canonical);
    carrier.dedup();
    let mut dependencies = positions(&reads).collect::<Vec<_>>();
    dependencies.sort();
    dependencies.dedup();
    Ok((carrier, dependencies))
}
pub(in crate::observed) fn read_bindings(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    c: &mut Control,
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let mut names = BTreeSet::new();
    let mut pending = vec![id];
    while let Some(id) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(child)
            | ExprKind::Field { base: child, .. }
            | ExprKind::Unary { operand: child, .. } => pending.push(*child),
            ExprKind::Binary { lhs, rhs, .. } => pending.extend([*lhs, *rhs]),
            ExprKind::If { cond, then_branch, else_branch } => {
                pending.extend([*cond, *then_branch, *else_branch]);
            }
            ExprKind::Tuple(items) => pending.extend(items),
            ExprKind::Dotted(parts) => {
                if let Some(first) = parts.first() {
                    names.insert(first.name.as_str());
                }
            }
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => {}
            _ => return Ok(bindings.to_vec()),
        }
    }
    Ok(bindings
        .iter()
        .filter(|(name, _)| names.contains(name.as_str()))
        .cloned()
        .collect())
}
// Tuple全体を読めない交差でだけ使う成分。公開ノードは必要になるまで作らない。
fn projections(
    env: &Environment<'_>,
    id: usize,
    value: &Scalar,
    read: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
    out: &mut Vec<local_result::geometry::Projection>,
    affine_state: bool,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![(id, value, vec![])];
    while let Some((id, value, path)) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match (&env.inputs.law().exprs[id].kind, value) {
            (ExprKind::Group(child), _) => pending.push((*child, value, path)),
            (ExprKind::Tuple(items), Scalar::Tuple(values)) => {
                for (i, (child, value)) in items.iter().zip(values).enumerate().rev() {
                    let mut child_path = path.clone();
                    child_path.push(i);
                    pending.push((*child, value, child_path));
                }
            }
            _ if field_path(env, id)?.is_some_and(|(_, fields)| fields.len() > 1) => {
                let slots = visible_slots(env, id, bindings, reading)?;
                let slot = slots.first().ok_or("参照経路の末端slotがない")?;
                let owner = env.subject(&slot.snapshot, &slot.subject)?;
                let subject = Scalar::Subject {
                    snapshot: slot.snapshot.clone(),
                    subject: slot.subject.clone(),
                    entity: owner.ty.clone(),
                };
                let declaration = &env.inputs.definitions().declarations[&owner.ty];
                let (params, fields) = declaration
                    .signature
                    .record_fields()
                    .ok_or("末端fieldのrecordがない")?;
                let field = params
                    .iter()
                    .chain(fields)
                    .find(|f| slot.field.as_ref() == Some(&format!("{}.{}", owner.ty, f.name)))
                    .ok_or("末端fieldの宣言がない")?;
                let mut carrier = vec![];
                subject_carrier(value, &mut carrier, c)?;
                out.push(local_result::geometry::Projection {
                    read,
                    path,
                    arguments: vec![],
                    field: Some((subject, field.location.clone())),
                    values: vec![value.clone()],
                    ty: value.ty(),
                    support: local_result::geometry::Support {
                        carrier,
                        positions: slots.clone(),
                        visible: slots,
                    },
                });
            }
            _ if affine_state && field_path(env, id)?.is_none() => {}
            _ if !path.is_empty() => {
                // 成分を読むための束縛だけを残す。他成分の参照は射影の支持ではない。
                let used = read_bindings(env, id, bindings, c)?;
                let (carrier, positions) = implicit_support(env, id, &used, reading, c)?;
                out.push(local_result::geometry::Projection {
                    read,
                    path,
                    arguments: vec![],
                    field: None,
                    values: vec![value.clone()],
                    ty: value.ty(),
                    support: local_result::geometry::Support {
                        carrier,
                        positions,
                        visible: visible_slots(env, id, &used, reading)?,
                    },
                });
            }
            _ => {}
        }
    }
    Ok(())
}
fn field_path<'a>(env: &'a Environment<'_>, mut id: usize) -> Result<Option<(&'a str, Vec<&'a str>)>, ValidationFailure> {
    let mut fields = vec![];
    loop {
        env.control.clone().checkpoint(Checkpoint::Localize)?;
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(child) => id = *child,
            ExprKind::Field { base, name } => {
                fields.push(name.name.as_str());
                id = *base;
            }
            ExprKind::Dotted(parts) if !parts.is_empty() => {
                fields.extend(parts[1..].iter().rev().map(|p| p.name.as_str()));
                fields.reverse();
                return Ok(Some((parts[0].name.as_str(), fields)));
            }
            _ => return Ok(None),
        }
    }
}
fn visible_slots(
    env: &Environment<'_>,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
) -> Result<Vec<Fact>, ValidationFailure> {
    let mut visible = vec![];
    let mut pending = vec![id];
    while let Some(id) = pending.pop() {
        env.control.clone().checkpoint(Checkpoint::Localize)?;
        let expr = &env.inputs.law().exprs[id];
        match &expr.kind {
            ExprKind::Group(child) => { pending.push(*child); continue; }
            ExprKind::Tuple(items) => { pending.extend(items.iter().rev()); continue; }
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => continue,
            _ => {}
        }
        let (variable, fields) = field_path(env, id)?
            .ok_or_else(|| unsupported(expr.span, "明示localの複合読取りの因子分解は未実装"))?;
        let (_, root) = bindings.iter().find(|(n, _)| n == variable)
            .ok_or_else(|| unsupported(expr.span, "明示localの読取り元が束縛でない"))?;
        let Some((last, prefix)) = fields.split_last() else { continue; };
        let mut owner = known(root.clone());
        for field in prefix {
            env.control.clone().checkpoint(Checkpoint::Localize)?;
            owner = env.scoped_field(owner, field, &Scope::default(), reading, expr.span)?;
        }
        let Some(Scalar::Subject { snapshot, subject, entity }) = &owner.known_value else {
            return Err(unsupported(expr.span, "明示localのfield読取り元が確定した参照でない"));
        };
        visible.push(Fact { snapshot: snapshot.clone(), subject: subject.clone(), field: Some(format!("{entity}.{last}")), atom: None });
    }
    visible.sort();
    visible.dedup();
    Ok(visible)
}
/// 固定状態の参照経路では、中間参照を値座標の公開要件へ混ぜない。
/// let/helper等の一般因子分解はここで推測せず、従来の支持検査へ戻す。
pub(in crate::observed) fn fixed_chain_visibility(
    env: &Environment<'_>, roots: &[usize], bindings: &[(String, Scalar)],
    parameters: &[crate::law::model::Param], reading: &str,
    c: &mut Control,
) -> Result<Option<(Vec<Json>, Vec<Fact>)>, ValidationFailure> {
    state_visibility_inner(env, roots, bindings, parameters, reading, c, true)
}
pub(in crate::observed) fn state_visibility(
    env: &Environment<'_>, roots: &[usize], bindings: &[(String, Scalar)], reading: &str,
    c: &mut Control,
) -> Result<Option<(Vec<Json>, Vec<Fact>)>, ValidationFailure> {
    state_visibility_inner(env, roots, bindings, &[], reading, c, false)
}
pub(in crate::observed) fn state_visibility_with_parameters(
    env: &Environment<'_>, roots: &[usize], bindings: &[(String, Scalar)],
    parameters: &[crate::law::model::Param], reading: &str, c: &mut Control,
) -> Result<Option<(Vec<Json>, Vec<Fact>)>, ValidationFailure> {
    state_visibility_inner(env, roots, bindings, parameters, reading, c, false)
}
fn state_visibility_inner(
    env: &Environment<'_>,
    roots: &[usize],
    bindings: &[(String, Scalar)],
    parameters: &[crate::law::model::Param],
    reading: &str,
    c: &mut Control,
    require_chain: bool,
) -> Result<Option<(Vec<Json>, Vec<Fact>)>, ValidationFailure> {
    let mut carrier = vec![];
    for (_, value) in bindings {
        subject_carrier(value, &mut carrier, c)?;
    }
    let (mut variables, _) = change_affine::law_variables(env, parameters, &[])?;
    variables.extend(bindings
        .iter()
        .map(|(n, v)| (n.clone(), known(v.clone()))));
    let mut pending = roots
        .iter()
        .map(|id| (*id, variables.clone()))
        .collect::<Vec<_>>();
    let mut visible = vec![];
    let mut chain = false;
    while let Some((id, variables)) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match &env.inputs.law().exprs[id].kind {
            ExprKind::Group(child) | ExprKind::Unary { operand: child, .. } => {
                pending.push((*child, variables))
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                pending.push((*lhs, variables.clone()));
                pending.push((*rhs, variables));
            }
            ExprKind::Tuple(items) => {
                pending.extend(items.iter().map(|id| (*id, variables.clone())))
            }
            ExprKind::Let { name, value, body } if !require_chain => {
                let value_result =
                    env.scoped_ast(*value, &variables, &Scope::default(), reading)?;
                if value_result.condition_failed || value_result.condition_pending {
                    return Ok(None);
                }
                let reference_alias =
                    matches!(value_result.known_value, Some(Scalar::Subject { .. }));
                let mut inner = variables.clone();
                inner.insert(name.name.clone(), value_result);
                // 中間参照の別名は公開値座標にしない。利用先の末端fieldを読む。
                if !reference_alias {
                    pending.push((*value, variables));
                }
                pending.push((*body, inner));
            }
            ExprKind::Call { args, .. } if !require_chain && env.builtin(id)? == Some("rat") => {
                pending.extend(args.iter().map(|id| (*id, variables.clone())));
            }
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Unit => {}
            ExprKind::Index { .. } if !require_chain => {
                // 束縛済み値の射影は固定係数。観測fieldの射影を自由座標から消さない。
                let value = env.scoped_ast(id, &variables, &Scope::default(), reading)?;
                if value.condition_failed || value.condition_pending
                    || value.support.iter().any(|f| f.field.is_some()) {
                    return Ok(None);
                }
                let Some(value) = value.known_value else { return Ok(None); };
                subject_carrier(&value, &mut carrier, c)?;
            }
            ExprKind::Dotted(_) | ExprKind::Field { .. } => {
                let Some((name, fields)) = field_path(env, id)? else {
                    let ExprKind::Field { base, name } = &env.inputs.law().exprs[id].kind else {
                        return Ok(None);
                    };
                    let owner = env.scoped_ast(*base, &variables, &Scope::default(), reading)?;
                    if owner.condition_failed || owner.condition_pending
                        || owner.support.iter().any(|f| f.field.is_some()) {
                        return Ok(None);
                    }
                    let Some(Scalar::Subject { snapshot, subject, entity }) = &owner.known_value else {
                        return Ok(None);
                    };
                    visible.push(Fact { snapshot: snapshot.clone(), subject: subject.clone(),
                        field: Some(format!("{entity}.{}",name.name)), atom: None });
                    subject_carrier(owner.known_value.as_ref().ok_or("局所読取り元がない")?, &mut carrier, c)?;
                    let value = env.scoped_ast(id, &variables, &Scope::default(), reading)?;
                    if value.condition_failed || value.condition_pending { return Ok(None); }
                    if let Some(value) = value.known_value { subject_carrier(&value,&mut carrier,c)?; }
                    chain = true;
                    continue;
                };
                if !variables.contains_key(name) {
                    return Ok(None);
                }
                chain |= fields.len() > 1;
                if !fields.is_empty() {
                    let bound = variables
                        .iter()
                        .filter_map(|(n, v)| v.known_value.clone().map(|v| (n.clone(), v)))
                        .collect::<Vec<_>>();
                    visible.extend(visible_slots(env, id, &bound, reading)?);
                }
                let value = env.scoped_ast(id, &variables, &Scope::default(), reading)?;
                if value.condition_failed || value.condition_pending {
                    return Ok(None);
                }
                if let Some(value) = value.known_value {
                    subject_carrier(&value, &mut carrier, c)?;
                }
            }
            _ => return Ok(None),
        }
    }
    carrier.sort_by_key(Json::canonical);
    carrier.dedup();
    visible.sort();
    visible.dedup();
    Ok((chain || !require_chain).then_some((carrier, visible)))
}
fn reason(
    context: &mut Context,
    request: &Request,
    kind: ReasonKind,
    missing: Vec<Fact>,
    span: (usize, usize),
    dependencies: Vec<NodeRef>,
) {
    context.reasons.push(Reason {
        kind,
        request: request.id.clone(),
        dependencies,
        missing,
        location: Some(Location::Law { span }),
    });
}
pub(in crate::observed) fn materialize(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    declaration: &Declaration,
    request: &Request,
    coordinates: &[NodeRef],
    states: &[Environment<'_>],
    c: &mut Control,
) -> Result<Vec<Context>, ValidationFailure> {
    materialize_with_free(env, b, declaration, request, coordinates, states, &[], None, c)
}
pub(in crate::observed) fn materialize_with_free(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    declaration: &Declaration,
    request: &Request,
    coordinates: &[NodeRef],
    states: &[Environment<'_>],
    free: &[Fact],
    target: Option<NodeRef>,
    c: &mut Control,
) -> Result<Vec<Context>, ValidationFailure> {
    let Signature::Local { params, .. } = &declaration.signature else {
        return Err("local署名がない".into());
    };
    let mut assignments = vec![vec![]];
    let mut missing = vec![];
    for p in params {
        let values = change_search::domain(env, &p.ty, p.span, &mut missing)?;
        let Some(values) = values else {
            if missing.is_empty() {
                return Err(unsupported(declaration.span, "localのparameter域が未確定"));
            }
            return Ok(vec![Context {
                locals: vec![],
                carrier: vec![],
                positions: vec![],
                visible: vec![],
                read_supports: vec![],
                read_refs: vec![],
                projections: vec![],
                readings: vec![],
                arguments: vec![],
                reasons: vec![Reason {
                    kind: ReasonKind::Missing,
                    request: request.id.clone(),
                    dependencies: coordinates.to_vec(),
                    missing,
                    location: Some(Location::Law {
                        span: declaration.span,
                    }),
                }],
                scope: Scope::default(),
                information: None,
                read_information: vec![],
            }]);
        };
        let mut next = vec![];
        for binding in assignments {
            for value in &values {
                c.checkpoint(Checkpoint::Localize)?;
                let mut instance = binding.clone();
                instance.push((p.name.clone(), value.clone()));
                next.push(instance);
            }
        }
        assignments = next;
    }
    let mut contexts = vec![];
    for bindings in &assignments {
        let context = materialize_instance(
            env,
            b,
            declaration,
            request,
            bindings,
            coordinates,
            states,
            free,
            target,
            c,
        )?;
        let stopped = context
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Stop(_)));
        contexts.push(context);
        if stopped {
            break;
        }
    }
    Ok(contexts)
}
// 読取りの係数型を入力定義から得る。異なる型の自由座標を同じ加群へ混ぜない。
fn free_coefficient(env: &Environment<'_>, slots: &[Fact]) -> Result<Type, ValidationFailure> {
    let mut coefficient = None;
    for slot in slots {
        env.tick()?;
        let ty = env
            .field(
                &slot.snapshot,
                &slot.subject,
                slot.field.as_ref().ok_or("自由位置にfieldがない")?,
            )?
            .ty
            .erase();
        if !matches!(ty, Type::Z | Type::Q)
            || coefficient.as_ref().is_some_and(|prior| prior != &ty)
        {
            return Err("局所読取りの自由座標の係数型が混在する".into());
        }
        coefficient = Some(ty);
    }
    coefficient.ok_or_else(|| "局所読取りの自由座標がない".into())
}
pub(in crate::observed) fn read_kernel(
    ty: &Type,
    matrix: &crate::observed::field_fiber::Matrix,
    cols: usize,
    c: &Control,
) -> Result<crate::observed::field_fiber::Matrix, ValidationFailure> {
    if *ty == Type::Z {
        let integer = matrix
            .iter()
            .map(|row| {
                row.iter()
                    .map(|v| match v {
                        Scalar::Z(v) => Ok(v.clone()),
                        _ => Err(ValidationFailure::from("整数読取りの係数がZでない")),
                    })
                    .collect()
            })
            .collect::<Result<crate::observed::integer_fiber::Matrix, _>>()?;
        let result = crate::observed::integer_fiber::solve(
            &integer,
            cols,
            &vec![0.into(); matrix.len()],
            c,
        )?;
        Ok(result
            .kernel
            .into_iter()
            .map(|row| row.into_iter().map(Scalar::Z).collect())
            .collect())
    } else {
        Ok(crate::observed::field_fiber::solve(
            ty,
            matrix,
            cols,
            &vec![crate::observed::numeric::zero(ty, c)?; matrix.len()],
            c,
        )?
        .kernel)
    }
}
// 元の式を自由状態上で評価し、重複・倍率・定数部を含む係数型上の像を保持する。
fn affine_read_image(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    target: NodeRef,
    expression: NodeRef,
    id: usize,
    bindings: &[(String, Scalar)],
    reading: &str,
    free: &[Fact],
    visible: &[Fact],
    read_type: &Type,
    c: &mut Control,
) -> Result<(NodeRef, Vec<Fact>, crate::observed::field_fiber::Matrix), ValidationFailure> {
    use crate::observed::{
        change_result::linear_result as wire, construction_result::ConstructionType as CT,
    };
    use crate::observed::{numeric, change_result::field_linear_result as scalar_wire};
    let slots = visible
        .iter()
        .filter(|f| free.contains(f))
        .cloned()
        .collect::<Vec<_>>();
    let coefficient = free_coefficient(env, &slots)?;
    let assignments = env.fixed_values();
    let mut arbitrary = Environment::with_primitive_valuation(env.inputs, &assignments, c)?;
    arbitrary.object = env.object_domain();
    for slot in free {
        arbitrary
            .affine_valuation
            .insert(slot.clone(), crate::observed::affine::Form::typed_state(&env.field(&slot.snapshot, &slot.subject, slot.field.as_ref().ok_or("自由位置にfieldがない")?)?.ty.erase(), slot, c)?);
    }
    let variables = bindings
        .iter()
        .map(|(n, v)| (n.clone(), known(v.clone())))
        .collect();
    let mut pending = vec![(id, read_type)];
    let mut matrix = vec![];
    let mut offset = vec![];
    while let Some((id, value)) = pending.pop() {
        c.checkpoint(Checkpoint::Localize)?;
        match (&env.inputs.law().exprs[id].kind, value) {
            (ExprKind::Group(inner), _) => pending.push((*inner, value)),
            (ExprKind::Tuple(ids), Type::Tuple(values)) if ids.len() == values.len() => {
                pending.extend(ids.iter().zip(values).rev().map(|(i, v)| (*i, v)))
            }
            (_, Type::Z | Type::Q) if value == &coefficient => {
                let evaluated = arbitrary.scoped_ast(id, &variables, &Scope::default(), reading)?;
                let form = evaluated.affine.ok_or_else(|| {
                    unsupported(
                        env.inputs.law().exprs[id].span,
                        "局所読取りが係数型上のアフィン式でない",
                    )
                })?;
                let coordinates = if coefficient == Type::Z {
                    form.state_coordinates(&slots, c)?.map(|(v,row)| (v.map(Scalar::Z),row.into_iter().map(Scalar::Z).collect()))
                } else {
                    form.rational_state_coordinates(&slots,c)?
                };
                let (constant, row) = coordinates.ok_or_else(|| {
                    unsupported(
                        env.inputs.law().exprs[id].span,
                        "局所読取りの係数が未確定",
                    )
                })?;
                matrix.push(row);
                offset.push(constant.ok_or_else(|| {
                    unsupported(env.inputs.law().exprs[id].span, "局所読取りの定数部が欠測")
                })?);
            }
            _ => {
                return Err(unsupported(
                    env.inputs.law().exprs[id].span,
                    "局所読取り像の係数型が混在する",
                ));
            }
        }
    }
    let ring = b.push(
        NodeType::Construction(CT::Ring),
        "ring",
        Json::obj([("kind", Json::str("scalar")), ("scalar", coefficient.wire())]),
        vec![],
        None,
        None,
    )?;
    let source_module = wire::module(b, ring, slots.len(), "free", vec![expression])?;
    let parameters = wire::domain(b, source_module)?;
    let variables = slots
        .iter()
        .map(|f| {
            Json::obj([
                (
                    "position",
                    Json::obj([
                        ("kind", Json::str("observation")),
                        ("field", f.wire()),
                        ("component", Json::Arr(vec![])),
                    ]),
                ),
                ("type", coefficient.wire()),
            ])
        })
        .collect();
    let mut fixed = vec![];
    let mut fixed_refs = vec![];
    for slot in visible.iter().filter(|f| !slots.contains(f)) {
        let owner = env.subject(&slot.snapshot, &slot.subject)?;
        let subject = change_result::value(
            b,
            &Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: owner.ty.clone(),
            },
        )?;
        fixed_refs.push(subject);
        fixed.push(Json::obj([
            ("subject", subject.wire()),
            (
                "field",
                Json::str(slot.field.as_ref().ok_or("読取り位置のfieldがない")?),
            ),
        ]));
    }
    let space = b.push(
        NodeType::Construction(CT::EquationSpace),
        "equation_space",
        Json::obj([
            ("base", target.wire()),
            ("variables", Json::Arr(variables)),
            ("fixed", Json::Arr(fixed)),
            ("parameters", parameters.wire()),
            ("requirements", Json::Arr(vec![])),
        ]),
        [target, parameters, expression]
            .into_iter()
            .chain(fixed_refs)
            .collect(),
        None,
        None,
    )?;
    let origin = scalar_wire::vector(b, source_module, &vec![numeric::zero(&coefficient,c)?; slots.len()], c)?;
    let zero=numeric::zero(&coefficient,c)?;
    let one=numeric::literal("1",&coefficient,c)?;
    let identity = (0..slots.len())
        .map(|i| {
            (0..slots.len())
                .map(|j| if i==j {one.clone()} else {zero.clone()})
                .collect()
        })
        .collect();
    let embedding = scalar_wire::map(b, source_module, source_module, &identity, slots.len(), c)?;
    let solutions = b.push(
        NodeType::Construction(CT::EquationSolutionSet),
        "equation_solutions",
        Json::obj([
            ("domain", space.wire()),
            (
                "representation",
                Json::obj([
                    ("kind", Json::str("affine")),
                    ("particular", origin.wire()),
                    ("directions", source_module.wire()),
                    ("embedding", embedding.wire()),
                ]),
            ),
        ]),
        vec![space, origin, source_module, embedding],
        None,
        None,
    )?;
    let source = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("solutions")),
            ("solutions", solutions.wire()),
        ]),
        vec![solutions],
        None,
        None,
    )?;
    let target_domain = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([("kind", Json::str("type")), ("type", read_type.wire())]),
        vec![],
        None,
        None,
    )?;
    let target_module = wire::module(b, ring, offset.len(), "free", vec![expression])?;
    let linear = scalar_wire::map(b, source_module, target_module, &matrix, slots.len(), c)?;
    let offset = scalar_wire::vector(b, target_module, &offset, c)?;
    let map = b.push(
        NodeType::Construction(CT::StateMap),
        "state_map",
        Json::obj([
            ("source", source.wire()),
            ("target", target_domain.wire()),
            ("kind", Json::str("affine")),
            ("linear", linear.wire()),
            ("offset", offset.wire()),
        ]),
        vec![source, target_domain, linear, offset],
        None,
        None,
    )?;
    let image = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("image")),
            ("map", map.wire()),
            ("source", solutions.wire()),
        ]),
        vec![map, solutions],
        None,
        None,
    )?;
    Ok((image, slots, matrix))
}

/// local省略時は支持の各原始位置をそのまま読む。
pub(in crate::observed) fn materialize_positions(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    request: &Request,
    support: &local_result::geometry::Support,
    free: &[Fact],
    reading: &str,
    c: &mut Control,
) -> Result<Context, ValidationFailure> {
    let mut out = Context {
        locals: vec![],
        carrier: support.carrier.clone(),
        positions: support.positions.clone(),
        visible: support.positions.clone(),
        read_supports: vec![],
        read_refs: vec![],
        projections: vec![],
        readings: vec![],
        arguments: vec![],
        reasons: vec![],
        scope: Scope::default(),
        information: None,
        read_information: vec![],
    };
    for slot in &support.positions {
        c.checkpoint(Checkpoint::Localize)?;
        let owner = env.subject(&slot.snapshot, &slot.subject)?;
        let subject = Scalar::Subject {
            snapshot: slot.snapshot.clone(),
            subject: slot.subject.clone(),
            entity: owner.ty.clone(),
        };
        let name = slot.field.as_ref().ok_or("暗黙読取りのfieldがない")?;
        let declaration = &env.inputs.definitions().declarations[&owner.ty];
        let (params, fields) = declaration
            .signature
            .record_fields()
            .ok_or("暗黙読取りのrecordがない")?;
        let field = params
            .iter()
            .chain(fields)
            .find(|f| name == &format!("{}.{}", owner.ty, f.name))
            .ok_or("暗黙読取りのfield宣言がない")?;
        let subject_ref = change_result::value(b, &subject)?;
        let ty = env.field(&slot.snapshot, &slot.subject, name)?.ty.erase();
        let expression = b.push(
            NodeType::Expression(ty.clone()),
            "expression",
            Json::obj([
                ("kind", Json::str("source")),
                ("location", crate::result::location_wire(&field.location)),
                ("parameters", Json::Arr(vec![])),
                (
                    "bindings",
                    Json::Arr(vec![Json::obj([
                        ("name", Json::str("subject")),
                        ("value", subject_ref.wire()),
                    ])]),
                ),
            ]),
            vec![subject_ref],
            None,
            None,
        )?;
        out.arguments.push(expression);
        let read = env.scoped_field(
            known(subject.clone()),
            &field.name,
            &Scope::default(),
            reading,
            (0, 0),
        )?;
        out.scope.merge(&read.scope);
        b.parts[expression.0 - b.base].scope.merge(&read.scope);
        let image = if free.contains(slot) {
            b.push(
                NodeType::Domain,
                "domain",
                Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
                vec![],
                None,
                None,
            )?
        } else if let Some(value) = read.known_value {
            let value = change_result::value(b, &value)?;
            local_result::domain(b, &ty, &[value])?
        } else {
            out.reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![expression],
                missing: vec![slot.clone()],
                location: Some(field.location.clone()),
            });
            continue;
        };
        out.arguments.push(image);
        out.read_refs.extend([expression, image]);
        out.readings.push(Json::obj([
            ("expression", expression.wire()),
            ("type", ty.wire()),
            ("domain", image.wire()),
        ]));
        let carrier = vec![Json::obj([
            ("type", subject.ty().wire()),
            ("value", subject.wire()),
        ])];
        out.read_supports.push(local_result::geometry::Support {
            carrier,
            positions: vec![slot.clone()],
            visible: vec![slot.clone()],
        });
    }
    Ok(out)
}
fn materialize_instance(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    declaration: &Declaration,
    request: &Request,
    bindings: &[(String, Scalar)],
    coordinates: &[NodeRef],
    states: &[Environment<'_>],
    free: &[Fact],
    target: Option<NodeRef>,
    c: &mut Control,
) -> Result<Context, ValidationFailure> {
    let Signature::Local {
        params,
        guard,
        reads,
    } = &declaration.signature
    else {
        return Err("局所読取りの元宣言がlocalでない".into());
    };
    let mut out = Context {
        locals: vec![],
        carrier: vec![],
        positions: vec![],
        visible: vec![],
        read_supports: vec![],
        read_refs: vec![],
        projections: vec![],
        readings: vec![],
        arguments: vec![],
        reasons: vec![],
        scope: Scope::default(),
        information: None,
        read_information: vec![],
    };
    let mut checks = owned_call::Checks::default();
    let result = (|| -> Result<(), ValidationFailure> {
        let mut absent = vec![];
        let mut owner_values = BTreeMap::new();
        for (p, (_, v)) in params.iter().zip(bindings) {
            env.owned_call_value_check(
                &p.ty,
                &super::super::term::affine::Value::Known(v.clone()),
                &owner_values,
                &declaration.reading,
                declaration.span,
                &mut checks,
            )?;
            owner_values.insert(p.name.as_str(), Some(v));
        }
        for state in states {
            c.checkpoint(Checkpoint::Localize)?;
            let mut varying = owned_call::Checks::default();
            let mut owners = BTreeMap::new();
            for (p, (_, v)) in params.iter().zip(bindings) {
                state.owned_call_value_check(
                    &p.ty,
                    &super::super::term::affine::Value::Known(v.clone()),
                    &owners,
                    &declaration.reading,
                    declaration.span,
                    &mut varying,
                )?;
                owners.insert(p.name.as_str(), Some(v));
            }
            if varying.failure.is_some() != checks.failure.is_some()
                || varying.blocked != checks.blocked
                || varying.missing != checks.missing
            {
                return Err(unsupported(
                    declaration.span,
                    "自由状態で所属が変わるlocalは未実装",
                ));
            }
            out.scope.merge(&varying.scope);
        }
        out.scope.merge(&checks.scope);
        out.positions.extend(positions(&checks.support));
        if checks.failure.is_some() {
            return Ok(());
        }
        absent.extend(checks.missing.iter().cloned());
        if checks.blocked || !absent.is_empty() {
            if absent.is_empty() {
                return Err(unsupported(declaration.span, "localの所属条件が未確定"));
            }
            reason(
                &mut out,
                request,
                ReasonKind::Missing,
                absent,
                declaration.span,
                coordinates.to_vec(),
            );
            return Ok(());
        }
        let variables = bindings
            .iter()
            .map(|(n, v)| (n.clone(), known(v.clone())))
            .collect();
        let node_bindings = bindings
            .iter()
            .map(|(n, v)| Ok((n.clone(), change_result::value(b, v)?)))
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        for (_, v) in bindings {
            subject_carrier(v, &mut out.carrier, c)?;
        }
        out.arguments.extend(node_bindings.iter().map(|(_, r)| *r));
        let mut scope = Scope::default();
        scope.readings.insert(declaration.reading.clone());
        if let Some(id) = guard {
            let expression = change_result::source_expression(b, env, *id, &node_bindings, &[])?;
            let (value, dependencies, absent) =
                evaluate_read(env, *id, &variables, &scope, &declaration.reading)?;
            b.parts[expression.0 - b.base].scope.merge(&value.scope);
            out.scope.merge(&value.scope);
            out.positions.extend(dependencies);
            out.arguments.push(expression);
            if !free.is_empty() && absent.is_empty() {
                let assignments = env.fixed_values();
                let mut arbitrary =
                    Environment::with_primitive_valuation(env.inputs, &assignments, c)?;
                arbitrary.object = env.object_domain();
                for slot in free {
                    arbitrary
                        .affine_valuation
                        .insert(slot.clone(), crate::observed::affine::Form::typed_state(&env.field(&slot.snapshot, &slot.subject, slot.field.as_ref().ok_or("自由位置にfieldがない")?)?.ty.erase(), slot, c)?);
                }
                let (all, _, _) =
                    evaluate_read(&arbitrary, *id, &variables, &scope, &declaration.reading)?;
                if all.known_value != value.known_value || all.known_value.is_none() {
                    return Err(unsupported(
                        declaration.span,
                        "自由状態でlocal guardの適用が変わる",
                    ));
                }
            }
            let mut guard_missing = absent.clone();
            let consistent = (|| -> Result<(), ValidationFailure> {
                for state in states {
                    c.checkpoint(Checkpoint::Localize)?;
                    let (other, _, other_absent) =
                        evaluate_read(state, *id, &variables, &scope, &declaration.reading)?;
                    guard_missing.extend(other_absent.iter().cloned());
                    if other.known_value != value.known_value
                        || other.condition_failed != value.condition_failed
                        || other.condition_pending != value.condition_pending
                        || other_absent != absent
                    {
                        return Err(unsupported(
                            declaration.span,
                            "自由状態で適用条件が変わるlocalは未実装",
                        ));
                    }
                }
                Ok(())
            })();
            if let Err(error) = consistent {
                if !guard_missing.is_empty() {
                    guard_missing.sort();
                    guard_missing.dedup();
                    reason(
                        &mut out,
                        request,
                        ReasonKind::Missing,
                        guard_missing,
                        declaration.span,
                        vec![expression],
                    );
                }
                return Err(error);
            }
            if value.condition_failed {
                return Err(unsupported(
                    declaration.span,
                    "local guardの式の適用条件が不成立",
                ));
            }
            if value.condition_pending || value.known_value.is_none() {
                if absent.is_empty() {
                    return Err(unsupported(declaration.span, "local guardが未確定"));
                }
                reason(
                    &mut out,
                    request,
                    ReasonKind::Missing,
                    absent,
                    declaration.span,
                    vec![expression],
                );
                return Ok(());
            }
            if value.known_value == Some(Scalar::Bool(false)) {
                return Ok(());
            }
            if value.known_value != Some(Scalar::Bool(true)) {
                return Err("local guardがBoolでない".into());
            }
        }
        let states = if states.is_empty() {
            vec![env]
        } else {
            states.iter().collect()
        };
        let mut information: Vec<(Vec<Fact>, crate::observed::field_fiber::Matrix)> = vec![];
        for id in reads {
            c.checkpoint(Checkpoint::Localize)?;
            let expression = change_result::source_expression(b, env, *id, &node_bindings, &[])?;
            out.arguments.push(expression);
            let mut values = vec![];
            let mut carrier = vec![];
            let mut dependencies = vec![];
            let mut visible = vec![];
            let mut missing_reason: Option<usize> = None;
            let mut projected = vec![];
            for state in &states {
                c.checkpoint(Checkpoint::Localize)?;
                let (read, positions, mut missing) =
                    evaluate_read(state, *id, &variables, &scope, &declaration.reading)?;
                b.parts[expression.0 - b.base].scope.merge(&read.scope);
                out.scope.merge(&read.scope);
                dependencies.extend(positions);
                let state_visible = if !free.is_empty() {
                    state_visibility(state, &[*id], bindings, &declaration.reading, c)?
                        .ok_or_else(|| unsupported(declaration.span, "整数読取りの支持を構成できない"))?.1
                } else if read.known_value.is_some() && !read.condition_pending {
                    visible_slots(state, *id, bindings, &declaration.reading)?
                } else {
                    visible.clone()
                };
                visible = state_visible;
                missing.retain(|f| !free.contains(f));
                if !missing.is_empty() {
                    let index = if let Some(index) = missing_reason {
                        index
                    } else {
                        let index = out.reasons.len();
                        reason(
                            &mut out,
                            request,
                            ReasonKind::Missing,
                            vec![],
                            declaration.span,
                            vec![expression],
                        );
                        missing_reason = Some(index);
                        index
                    };
                    out.reasons[index].missing.extend(missing);
                    out.reasons[index].missing.sort();
                    out.reasons[index].missing.dedup();
                }
                if read.condition_failed {
                    return Err(unsupported(
                        declaration.span,
                        "local読取りの式の適用条件が不成立",
                    ));
                }
                if read.condition_pending || read.known_value.is_none() {
                    if visible.iter().any(|slot| free.contains(slot)) && missing_reason.is_none() {
                        continue;
                    }
                    if missing_reason.is_none() {
                        return Err(unsupported(declaration.span, "localの読取り値が未確定"));
                    }
                    continue;
                }
                let value = read.known_value.ok_or("localの確定値がない")?;
                subject_carrier(&value, &mut carrier, c)?;
                projections(
                    state,
                    *id,
                    &value,
                    out.readings.len(),
                    bindings,
                    &declaration.reading,
                    &mut projected,
                    !free.is_empty(),
                    c,
                )?;
                if !values.contains(&value) {
                    values.push(value);
                }
            }
            out.positions.extend(dependencies.iter().cloned());
            out.visible.extend(visible.iter().cloned());
            if missing_reason.is_some() {
                continue;
            }
            let NodeType::Expression(ty) = &b.parts[expression.0 - b.base].ty else {
                return Err("local読取りの型が式でない".into());
            };
            let ty = ty.clone();
            let information_before = information.len();
            let image = if visible.iter().any(|slot| free.contains(slot)) {
                if matches!(ty, Type::Z | Type::Q) && visible.len() == 1 && field_path(env, *id)?.is_some() {
                    information.push((visible.clone(), vec![vec![crate::observed::numeric::literal("1", &ty, c)?]]));
                    b.push(
                        NodeType::Domain,
                        "domain",
                        Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
                        vec![],
                        None,
                        None,
                    )?
                } else {
                    let (image, slots, matrix) = affine_read_image(
                        env,
                        b,
                        target.ok_or("整数読取りの基底がない")?,
                        expression,
                        *id,
                        bindings,
                        &declaration.reading,
                        free,
                        &visible,
                        &ty,
                        c,
                    )?;
                    information.push((slots, matrix));
                    image
                }
            } else {
                let actual = values
                    .iter()
                    .map(|v| change_result::value(b, v))
                    .collect::<Result<Vec<_>, _>>()?;
                local_result::domain(b, &ty, &actual)?
            };
            for projection in projected {
                if let Some(existing) = out
                    .projections
                    .iter_mut()
                    .find(|p| p.read == projection.read && p.path == projection.path)
                {
                    existing.support.carrier.extend(projection.support.carrier);
                    existing
                        .support
                        .positions
                        .extend(projection.support.positions);
                    existing.support.visible.extend(projection.support.visible);
                    for value in projection.values {
                        if !existing.values.contains(&value) {
                            existing.values.push(value);
                        }
                    }
                } else {
                    out.projections.push(projection);
                }
            }
            out.read_information
                .push(if information.len() > information_before {
                    information.last().cloned()
                } else {
                    None
                });
            out.readings.push(Json::obj([
                ("expression", expression.wire()),
                ("type", ty.wire()),
                ("domain", image.wire()),
            ]));
            out.arguments.push(image);
            out.read_refs.extend([expression, image]);
            out.carrier.extend(carrier.iter().cloned());
            for (_, v) in &read_bindings(env, *id, bindings, c)? {
                subject_carrier(v, &mut carrier, c)?;
            }
            carrier.sort_by_key(Json::canonical);
            carrier.dedup();
            let mut dependencies = positions(&dependencies).collect::<Vec<_>>();
            dependencies.sort();
            dependencies.dedup();
            visible.sort();
            visible.dedup();
            out.read_supports.push(local_result::geometry::Support {
                carrier,
                positions: dependencies,
                visible,
            });
        }
        if !information.is_empty() {
            let mut slots = information
                .iter()
                .flat_map(|(slots, _)| slots.iter().cloned())
                .collect::<Vec<_>>();
            slots.sort();
            slots.dedup();
            let coefficient = free_coefficient(env, &slots)?;
            let zero = crate::observed::numeric::zero(&coefficient,c)?;
            let mut matrix = vec![];
            for (local, rows) in &information {
                for row in rows {
                    c.checkpoint(Checkpoint::Localize)?;
                    let mut expanded = vec![zero.clone(); slots.len()];
                    for (slot, value) in local.iter().zip(row) {
                        expanded[slots
                            .iter()
                            .position(|f| f == slot)
                            .ok_or("読取りの自由位置がない")?] = value.clone();
                    }
                    matrix.push(expanded);
                }
            }
            let kernel = read_kernel(&coefficient, &matrix, slots.len(), c)?;
            out.information = Some((slots.clone(), matrix));
            // 全readから復元できた原始座標を、重なりの読取りとして保持する。
            for (i, slot) in slots.iter().enumerate() {
                if kernel[i].iter().any(|x| x != &zero) {
                    continue;
                }
                if out
                    .projections
                    .iter()
                    .any(|p| p.support.visible.as_slice() == std::slice::from_ref(slot))
                {
                    continue;
                }
                let owner = env.subject(&slot.snapshot, &slot.subject)?;
                let subject = Scalar::Subject {
                    snapshot: slot.snapshot.clone(),
                    subject: slot.subject.clone(),
                    entity: owner.ty.clone(),
                };
                let name = slot.field.as_ref().ok_or("復元するfieldがない")?;
                let definition = &env.inputs.definitions().declarations[&owner.ty];
                let (params, fields) = definition
                    .signature
                    .record_fields()
                    .ok_or("復元するrecordがない")?;
                let field = params
                    .iter()
                    .chain(fields)
                    .find(|f| name == &format!("{}.{}", owner.ty, f.name))
                    .ok_or("復元するfield宣言がない")?;
                let value = env
                    .scoped_field(
                        known(subject.clone()),
                        &field.name,
                        &scope,
                        &declaration.reading,
                        declaration.span,
                    )?
                    .known_value;
                out.projections.push(local_result::geometry::Projection {
                    read: 0,
                    path: vec![],
                    arguments: out.read_refs.clone(),
                    field: Some((subject, field.location.clone())),
                    values: value.into_iter().collect(),
                    ty: env.field(&slot.snapshot, &slot.subject, name)?.ty.erase(),
                    support: local_result::geometry::Support {
                        carrier: vec![],
                        positions: vec![slot.clone()],
                        visible: vec![slot.clone()],
                    },
                });
            }
        }
        for projection in &mut out.projections {
            projection.support.carrier.sort_by_key(Json::canonical);
            projection.support.carrier.dedup();
            projection.support.positions.sort();
            projection.support.positions.dedup();
            projection.support.visible.sort();
            projection.support.visible.dedup();
        }
        out.carrier.sort_by_key(Json::canonical);
        out.carrier.dedup();
        out.positions.sort();
        out.positions.dedup();
        out.positions = positions(&out.positions).collect();
        out.positions.sort();
        out.positions.dedup();
        out.visible.sort();
        out.visible.dedup();
        out.locals.push(Json::obj([
            ("declaration", Json::str(&declaration.name)),
            (
                "bindings",
                Json::Arr(
                    node_bindings
                        .iter()
                        .map(|(n, r)| Json::obj([("name", Json::str(n)), ("value", r.wire())]))
                        .collect(),
                ),
            ),
        ]));
        Ok(())
    })();
    if let Err(error) = result {
        out.scope.merge(&checks.scope);
        out.positions.extend(positions(&checks.support));
        if checks.failure.is_none() && !checks.missing.is_empty() {
            reason(
                &mut out,
                request,
                ReasonKind::Missing,
                checks.missing,
                declaration.span,
                coordinates.to_vec(),
            );
        }
        let (kind, location) = match error {
            ValidationFailure::Stop(stop) => (ReasonKind::Stop(stop), None),
            ValidationFailure::UnsupportedExpression { location, .. } => {
                let mut types = vec![];
                for r in &out.arguments {
                    if let Some(part) = r.0.checked_sub(b.base).and_then(|i| b.parts.get(i)) {
                        if let NodeType::Expression(ty) = &part.ty {
                            if !types.contains(ty) {
                                types.push(ty.clone());
                            }
                        }
                    }
                }
                (
                    ReasonKind::UnsupportedAlgorithm {
                        question: QuestionKind::Localize,
                        operand_types: types,
                        method: "local_reading".into(),
                    },
                    Some(location),
                )
            }
            other => return Err(other),
        };
        out.reasons.push(Reason {
            kind,
            request: request.id.clone(),
            dependencies: coordinates.iter().chain(&out.arguments).copied().collect(),
            missing: vec![],
            location,
        });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{
        control::{Limits, Usage},
        input::check_inputs,
        request::resolve_native_for_test,
    };
    #[allow(dead_code)]
    mod fixture {
        use crate as archsig;
        include!("../../tests/common/architecture_environment.rs");
    }
    fn quiet() -> Control {
        Control::new(Limits::default(), |_| Usage::default())
    }
    #[test]
    fn local_owner_missing_survives_the_first_free_state_stop() {
        let map = fixture::remove_atom("p-owner");
        let inputs = check_inputs(
            fixture::input("local here(a:System,s:State[a]) reads s.free;", Some(&map)),
            &mut quiet(),
        )
        .unwrap();
        let requests = resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["c=check(Reservations.roots,x=@v/A)"],
            &mut quiet(),
        )
        .unwrap();
        let env = Environment::with_requests(&inputs, requests.requests(), &mut quiet()).unwrap();
        let declaration = &inputs.law().declarations["Reservations.here"];
        let bindings = vec![
            (
                "a".into(),
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "A".into(),
                    entity: "Reservations.System".into(),
                },
            ),
            (
                "s".into(),
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "p".into(),
                    entity: "Reservations.State".into(),
                },
            ),
        ];
        for mode in 0..3 {
            let state =
                Environment::with_requests(&inputs, requests.requests(), &mut quiet()).unwrap();
            let graph = Graph::new(&quiet());
            let mut b = Builder {
                g: &graph,
                base: 0,
                parts: vec![],
            };
            let mut c = Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |point| {
                    if point != Checkpoint::Localize {
                        return Usage::default();
                    }
                    match mode {
                        0 => Usage {
                            elapsed_ms: 2,
                            ..Usage::default()
                        },
                        1 => Usage {
                            memory_mib: 2,
                            ..Usage::default()
                        },
                        _ => Usage {
                            signal: Some(crate::result::Signal::Term),
                            ..Usage::default()
                        },
                    }
                },
            );
            let context = materialize_instance(
                &env,
                &mut b,
                declaration,
                &requests.requests()[0],
                &bindings,
                &[],
                &[state],
                &[],
                None,
                &mut c,
            )
            .unwrap();
            assert!(
                context
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Stop(_)))
            );
            assert!(context.reasons.iter().any(|r| r.missing.iter().any(
                |f| f.subject == "p" && f.field.as_deref() == Some("Reservations.State.owner")
            )));
        }
    }
}
