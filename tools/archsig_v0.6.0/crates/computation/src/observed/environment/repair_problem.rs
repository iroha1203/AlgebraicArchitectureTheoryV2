//! 元の型・更新式・Lawを有限の共有関係へ接続する。
use super::*;
use crate::observed::{construction_result::ArchitectureWitness, repair_problem::finite};
use archsig_input::law::{
    ast::{QuantDomain, QuantSplit},
    model::Signature,
};
use std::collections::BTreeSet;
pub(in crate::observed) mod family;
pub(in crate::observed) mod integer;
mod law_factors;
pub(in crate::observed) mod reuse;

#[cfg(test)]
thread_local! {static GENERATIONS:std::cell::Cell<usize>=const {std::cell::Cell::new(0)};}
#[cfg(test)]
pub(in crate::observed) fn generations() -> usize {
    GENERATIONS.with(std::cell::Cell::get)
}
#[derive(Clone, Debug)]
pub(in crate::observed) struct Output {
    pub fact: Fact,
    pub subject: usize,
    pub column: usize,
    // 旧SolutionSetの全更新からの復元では、上書き前値が未観測でもよい。
    pub baseline: Option<usize>,
}
#[derive(Debug)]
pub(in crate::observed) struct Compiled {
    pub subjects: Vec<Scalar>,
    pub parameter_types: Vec<Type>,
    pub domains: Vec<std::sync::Arc<Vec<Scalar>>>,
    pub parameter_count: usize,
    pub outputs: Vec<Output>,
    pub requirements: Vec<(String, Vec<(String, Scalar)>)>,
    pub bindings: Vec<(String, Scalar)>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub fixed: Vec<(Fact, Scalar)>,
    pub relations: std::sync::Arc<finite::Problem>,
}
pub(in crate::observed) enum Compilation {
    Ready(std::sync::Arc<Compiled>),
    Pending(Vec<Fact>),
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::PrimitiveValuation)?;
    Ok(())
}
fn unsupported(span: (usize, usize), feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span },
        feature: feature.into(),
    }
}
/// 原式の自由parameterの保守的な依存。viewの引数は全て保持する。
fn dependencies(
    env: &Environment<'_>,
    expression: usize,
    names: &BTreeMap<String, BTreeSet<usize>>,
) -> Result<BTreeSet<usize>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let mut result = BTreeSet::new();
        let mut add = |id| -> Result<(), ValidationFailure> {
            result.extend(dependencies(env, id, names)?);
            Ok(())
        };
        match &env.indexes.inputs.law().exprs()[expression].kind {
            ExprKind::Dotted(parts) => {
                if let Some(values) = names.get(&parts[0].name) {
                    result.extend(values);
                }
            }
            ExprKind::Let { name, value, body } => {
                let values = dependencies(env, *value, names)?;
                let mut nested = names.clone();
                nested.insert(name.name.clone(), values.clone());
                result.extend(values);
                result.extend(dependencies(env, *body, &nested)?);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                add(*cond)?;
                add(*then_branch)?;
                add(*else_branch)?;
            }
            ExprKind::Match { scrutinee, arms } => {
                add(*scrutinee)?;
                for a in arms {
                    add(a.body)?;
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                add(*lhs)?;
                add(*rhs)?;
            }
            ExprKind::Unary { operand, .. } => add(*operand)?,
            ExprKind::Field { base, .. }
            | ExprKind::Index { base, .. }
            | ExprKind::Group(base)
            | ExprKind::Some(base) => add(*base)?,
            ExprKind::Call { callee, args } => {
                add(*callee)?;
                for a in args {
                    add(*a)?;
                }
            }
            ExprKind::With { base, updates } => {
                add(*base)?;
                for (_, v) in updates {
                    add(*v)?;
                }
            }
            ExprKind::Tuple(items)
            | ExprKind::ListLit { items, .. }
            | ExprKind::SetLit { items, .. } => {
                for i in items {
                    add(*i)?;
                }
            }
            ExprKind::Comprehension {
                elem,
                domain,
                filter,
                ..
            } => {
                add(*domain)?;
                add(*elem)?;
                if let Some(f) = filter {
                    add(*f)?;
                }
            }
            ExprKind::Fn { body, .. } => add(*body)?,
            ExprKind::Family { owner, .. } => add(*owner)?,
            ExprKind::Quant { split, .. } => {
                let pairs: Vec<_> = match split {
                    QuantSplit::Fixed { domain, body } => vec![(domain, *body)],
                    QuantSplit::Candidates(xs) => xs.iter().map(|(d, b)| (d, *b)).collect(),
                };
                for (domain, body) in pairs {
                    if let QuantDomain::In(i) = domain {
                        add(*i)?;
                    }
                    add(body)?;
                }
            }
            ExprKind::ThenOp
            | ExprKind::Int(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Unit
            | ExprKind::None(_) => {}
        }
        Ok(result)
    })
}
fn field_dependencies(
    env: &Environment<'_>,
    expression: usize,
    field: &str,
    names: &BTreeMap<String, BTreeSet<usize>>,
) -> Result<BTreeSet<usize>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        match &env.indexes.inputs.law().exprs()[expression].kind {
            ExprKind::Group(i) => field_dependencies(env, *i, field, names),
            ExprKind::Let { name, value, body } => {
                let mut values = dependencies(env, *value, names)?;
                let mut nested = names.clone();
                nested.insert(name.name.clone(), values.clone());
                values.extend(field_dependencies(env, *body, field, &nested)?);
                Ok(values)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let mut values = dependencies(env, *cond, names)?;
                values.extend(field_dependencies(env, *then_branch, field, names)?);
                values.extend(field_dependencies(env, *else_branch, field, names)?);
                Ok(values)
            }
            ExprKind::With { updates, .. } => match updates.iter().find(|(f, _)| f.name == field) {
                Some((_, value)) => dependencies(env, *value, names),
                None => Ok(BTreeSet::new()),
            },
            _ => Err(internal!("更新関係の元bodyがwithでない").into()),
        }
    })
}
fn rows(
    columns: &[usize],
    domains: &[impl std::borrow::Borrow<Vec<Scalar>>],
    c: &Control,
    mut visit: impl FnMut(&[usize]) -> Result<(), ValidationFailure>,
) -> Result<(), ValidationFailure> {
    rows_while(columns, domains, c, |point| {
        visit(point)?;
        Ok(true)
    })?;
    Ok(())
}
fn rows_while(
    columns: &[usize],
    domains: &[impl std::borrow::Borrow<Vec<Scalar>>],
    c: &Control,
    mut visit: impl FnMut(&[usize]) -> Result<bool, ValidationFailure>,
) -> Result<bool, ValidationFailure> {
    if domains.iter().any(|d| d.borrow().is_empty()) {
        return Ok(true);
    }
    let mut point = vec![0; columns.len()];
    loop {
        tick(c)?;
        if !visit(&point)? {
            return Ok(false);
        }
        let mut at = point.len();
        loop {
            if at == 0 {
                return Ok(true);
            }
            at -= 1;
            point[at] += 1;
            if point[at] < domains[columns[at]].borrow().len() {
                break;
            }
            point[at] = 0;
        }
    }
}

fn holds(row: &finite_law_valuations::FiniteLawRow) -> Option<bool> {
    if row.application == Some(false) {
        Some(true)
    } else if row.application.is_none() || row.condition_pending {
        None
    } else if row.condition_failed {
        Some(false)
    } else {
        match (row.guard, row.predicate) {
            (Some(false), _) | (Some(true), Some(true)) => Some(true),
            (Some(true), Some(false)) => Some(false),
            _ => None,
        }
    }
}
pub(in crate::observed) fn same_slot(a: &Fact, b: &Fact) -> bool {
    a.snapshot == b.snapshot && a.subject == b.subject && a.field == b.field
}

/// 同じ原始位置に対する合法な有限入力。rowsは各field値域の添字を持つ。
pub(in crate::observed) struct InputSpace {
    pub fields: Vec<Fact>,
    pub domains: Vec<Vec<Scalar>>,
    pub rows: Vec<Vec<usize>>,
}
fn with_input<R>(
    fixed: &Environment<'_>,
    inputs: Option<&InputSpace>,
    parameters: usize,
    columns: &[usize],
    point: &[usize],
    evaluate: impl FnOnce(&Environment<'_>) -> Result<R, ValidationFailure>,
) -> Result<Option<R>, ValidationFailure> {
    let Some(inputs) = inputs else {
        return evaluate(fixed).map(Some);
    };
    let mut selected = None;
    for row in &inputs.rows {
        fixed.tick()?;
        if row.iter().enumerate().all(|(i, v)| {
            columns
                .iter()
                .position(|c| *c == parameters + i)
                .is_none_or(|j| point[j] == *v)
        }) {
            selected = Some(row);
            break;
        }
    }
    let Some(row) = selected else {
        return Ok(None);
    };
    let mut values = fixed.fixed_values().into_iter().collect::<BTreeMap<_, _>>();
    for ((fact, domain), index) in inputs.fields.iter().zip(&inputs.domains).zip(row) {
        values.insert(fact.clone(), domain[*index].clone());
    }
    let env = fixed
        .primitive_dependency_probe_from(&values.into_iter().collect::<Vec<_>>(), &fixed.control)?;
    evaluate(&env).map(Some)
}
fn input_dependencies(
    inputs: Option<&InputSpace>,
    parameters: usize,
    support: &[Fact],
    columns: &mut BTreeSet<usize>,
) {
    if let Some(inputs) = inputs {
        for fact in support {
            if let Some(i) = inputs.fields.iter().position(|f| same_slot(f, fact)) {
                columns.insert(parameters + i);
            }
        }
    }
}
pub(in crate::observed) fn compile(
    original: &Environment<'_>,
    graph: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    c: &Control,
) -> Result<Compilation, ValidationFailure> {
    compile_inputs(original, graph, witness, request, c, None)
}
pub(in crate::observed) fn compile_inputs(
    original: &Environment<'_>,
    graph: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    c: &Control,
    inputs: Option<&InputSpace>,
) -> Result<Compilation, ValidationFailure> {
    #[cfg(test)]
    GENERATIONS.with(|n| n.set(n.get() + 1));
    let fixed = original
        .try_object_primitive_valuation_from(&original.fixed_values(), witness, c)?
        .ok_or(internal!("有限修復の基準代入が不適合"))?;
    let selected = change_search::selection(original, &fixed, graph, witness, request, &[], c)?;
    let Some(mut subjects) = selected.subjects else {
        return Ok(Compilation::Pending(selected.missing));
    };
    subjects.sort_by_key(|s| match s {
        Scalar::Subject {
            snapshot, subject, ..
        } => (snapshot.clone(), subject.clone()),
        _ => unreachable!("選択済みentity"),
    });
    let name = request
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "using" {
                if let Selector::Declaration { name } = &a.value {
                    Some(name)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .ok_or(internal!("有限修復のchangeがない"))?;
    let change = &fixed.indexes.inputs.law().declarations()[name];
    let Signature::Change {
        params,
        guard,
        body,
    } = &change.signature
    else {
        return Err(internal!("有限修復のchange署名が違う").into());
    };
    let mut domains = vec![];
    let mut parameter_types = vec![];
    for _ in &subjects {
        for p in params.iter().skip(1) {
            tick(c)?;
            if !crate::observed::finite::completion_supported(&p.ty, fixed.indexes.inputs.law(), c)?
            {
                return Err(unsupported(
                    p.span,
                    "finite repair parameters require finite value types",
                ));
            }
            let values = crate::observed::finite::values(
                &p.ty,
                fixed.indexes.inputs.law(),
                c,
                &mut |_| Err(internal!("値parameterに参照域がある").into()),
                &mut |_| {},
            )?;
            domains.push(values.values);
            parameter_types.push(p.ty.clone());
        }
    }
    let parameter_count = domains.len();
    let width = params.len() - 1;
    let mut relations = vec![];
    if let Some(inputs) = inputs {
        domains.extend(inputs.domains.iter().cloned());
        relations.push(finite::Relation {
            columns: (parameter_count..domains.len()).collect(),
            rows: inputs.rows.clone().into(),
        });
    }
    let mut outputs = vec![];
    let mut support = BTreeSet::new();
    let mut missing = BTreeSet::new();
    let mut pending = false;
    let fields = change_evaluation::update_fields(&fixed, change)?;
    let mut scope = Scope::default();
    let mut base_scope = Scope::default();
    base_scope.readings.insert(change.reading.clone());
    for (subject_index, subject) in subjects.iter().enumerate() {
        let mut names = BTreeMap::new();
        for (i, p) in params.iter().skip(1).enumerate() {
            names.insert(p.name.clone(), BTreeSet::from([subject_index * width + i]));
        }
        let bindings_for = |columns: &[usize], point: &[usize], domains: &[Vec<Scalar>]| {
            let mut bindings = vec![(params[0].name.clone(), subject.clone())];
            for (i, p) in params.iter().skip(1).enumerate() {
                let column = subject_index * width + i;
                let index = columns
                    .iter()
                    .position(|v| *v == column)
                    .map_or(0, |i| point[i]);
                bindings.push((p.name.clone(), domains[column][index].clone()));
            }
            bindings
        };
        let guard_relation = relations.len();
        if let Some(guard) = guard {
            let mut columns = dependencies(&fixed, *guard, &names)?
                .into_iter()
                .collect::<Vec<_>>();
            loop {
                let mut discovered = BTreeSet::from_iter(columns.iter().copied());
                let mut allowed = vec![];
                let mut pass_pending = false;
                let mut pass_missing = BTreeSet::new();
                let mut pass_support = BTreeSet::new();
                let mut pass_scope = Scope::default();
                rows(&columns, &domains, c, |point| {
                    let Some(update) =
                        with_input(&fixed, inputs, parameter_count, &columns, point, |env| {
                            change_evaluation::relation_guard(
                                env,
                                change,
                                &bindings_for(&columns, point, &domains),
                            )
                        })?
                    else {
                        return Ok(());
                    };
                    input_dependencies(inputs, parameter_count, &update.support, &mut discovered);
                    pass_pending |= update.state == change_evaluation::State::Undetermined;
                    pass_scope.merge(&update.scope);
                    pass_support.extend(update.support);
                    pass_missing.extend(update.missing);
                    if update.state == change_evaluation::State::Ready {
                        allowed.push(point.to_vec());
                    }
                    Ok(())
                })?;
                let next = discovered.into_iter().collect::<Vec<_>>();
                if next == columns {
                    pending |= pass_pending;
                    scope.merge(&pass_scope);
                    support.extend(pass_support);
                    missing.extend(pass_missing);
                    relations.push(finite::Relation {
                        columns,
                        rows: allowed.into(),
                    });
                    break;
                }
                columns = next;
            }
        }
        for field in &fields {
            let Scalar::Subject {
                snapshot,
                subject: subject_id,
                entity,
            } = subject
            else {
                unreachable!("選択済みentity")
            };
            let field_name = fixed.input_name(&format!("{entity}.{field}"))?;
            let fact = Fact::from(archsig_input::archmap::FactData {
                snapshot: snapshot.clone(),
                subject: subject_id.clone(),
                field: Some(field_name.clone()),
                atom: None,
            });
            let base = fixed.scoped_field(
                change_evaluation::known(subject.clone()),
                &field_name,
                &base_scope,
                &change.reading,
                change.span,
            )?;
            scope.merge(&base.scope);
            support.extend(base.support.iter().cloned());
            let base_value = base.known_value;
            let input_domain = inputs.and_then(|inputs| {
                inputs
                    .fields
                    .iter()
                    .position(|f| same_slot(f, &fact))
                    .map(|i| &inputs.domains[i])
            });
            if base_value.is_none()
                && input_domain.is_none()
                && request.kind == crate::observed::request::QuestionKind::Prepare
            {
                missing.insert(fact);
                continue;
            }
            if base.condition_failed || base.condition_pending {
                return Err(unsupported(
                    change.span,
                    "finite repair baseline field is not constructible",
                ));
            }
            let baseline = base_value.as_ref().map(|_| 0);
            let initial_values = base_value
                .into_iter()
                .chain(input_domain.into_iter().flat_map(|v| v.iter().cloned()))
                .collect::<Vec<_>>();
            let mut columns = field_dependencies(&fixed, *body, field, &names)?
                .into_iter()
                .collect::<Vec<_>>();
            loop {
                let mut discovered = BTreeSet::from_iter(columns.iter().copied());
                let mut values = initial_values.clone();
                let mut allowed = vec![];
                let mut pass_pending = false;
                let mut pass_missing = BTreeSet::new();
                let mut pass_support = BTreeSet::new();
                let mut pass_scope = Scope::default();
                rows(&columns, &domains, c, |point| {
                    if guard.is_some() {
                        let relation = &relations[guard_relation];
                        let mut admissible = false;
                        for row in relation.rows.iter() {
                            tick(c)?;
                            if relation.columns.iter().zip(row).all(|(column, value)| {
                                columns
                                    .iter()
                                    .position(|v| v == column)
                                    .is_none_or(|i| point[i] == *value)
                            }) {
                                admissible = true;
                                break;
                            }
                        }
                        if !admissible {
                            return Ok(());
                        }
                    }
                    let Some(update) =
                        with_input(&fixed, inputs, parameter_count, &columns, point, |env| {
                            change_evaluation::relation_field(
                                env,
                                change,
                                &bindings_for(&columns, point, &domains),
                                field,
                            )
                        })?
                    else {
                        return Ok(());
                    };
                    input_dependencies(inputs, parameter_count, &update.support, &mut discovered);
                    pass_pending |= update.state == change_evaluation::State::Undetermined;
                    pass_scope.merge(&update.scope);
                    pass_support.extend(update.support);
                    pass_missing.extend(update.missing);
                    if update.state == change_evaluation::State::Ready {
                        let value = update
                            .values
                            .into_iter()
                            .find(|(f, _)| same_slot(f, &fact))
                            .map(|(_, v)| v)
                            .ok_or(internal!("更新関係の値がない"))?;
                        let index = values.iter().position(|v| *v == value).unwrap_or_else(|| {
                            values.push(value);
                            values.len() - 1
                        });
                        let mut row = point.to_vec();
                        row.push(index);
                        allowed.push(row);
                    }
                    Ok(())
                })?;
                let next = discovered.into_iter().collect::<Vec<_>>();
                if next == columns {
                    pending |= pass_pending;
                    scope.merge(&pass_scope);
                    support.extend(pass_support);
                    missing.extend(pass_missing);
                    let column = domains.len();
                    columns.push(column);
                    relations.push(finite::Relation {
                        columns,
                        rows: allowed.into(),
                    });
                    outputs.push(Output {
                        fact,
                        subject: subject_index,
                        column,
                        baseline,
                    });
                    domains.push(values);
                    break;
                }
                columns = next;
            }
        }
    }
    if pending || !missing.is_empty() {
        return Ok(Compilation::Pending(missing.into_iter().collect()));
    }
    let sizes = domains.iter().map(Vec::len).collect::<Vec<_>>();
    let updates = finite::Problem::new(sizes.clone(), relations, c)?;
    let domains = domains
        .into_iter()
        .map(std::sync::Arc::new)
        .collect::<Vec<_>>();
    let mut cached = reuse::Builder::begin(
        &fixed,
        witness,
        name,
        &subjects,
        &selected.requirements,
        reuse::Basis {
            domains: &domains,
            parameters: parameter_count,
            outputs: &outputs,
            inputs,
        },
        c,
    )?;
    let prior = cached
        .as_ref()
        .map(|frame| frame.prior(&fixed, c))
        .transpose()?
        .flatten();
    let mut relations = vec![];
    let mut unresolved = vec![];
    let mut law_axes = outputs.clone();
    if let Some(inputs) = inputs {
        for (i, fact) in inputs.fields.iter().enumerate() {
            if !outputs.iter().any(|o| same_slot(&o.fact, fact)) {
                law_axes.push(Output {
                    fact: fact.clone(),
                    subject: 0,
                    column: parameter_count + i,
                    baseline: None,
                });
            }
        }
    }

    for (name, bindings) in &selected.requirements {
        let law = &fixed.indexes.inputs.law().declarations()[name];
        let factors = law_factors::collect(&fixed, law, bindings, &law_axes, &domains, &updates)?;
        support.extend(factors.support);
        scope.merge(&factors.scope);
        for factor in factors.items {
            let mut signature = cached
                .as_mut()
                .map(|frame| frame.signature(name, &factor, c))
                .transpose()?
                .flatten();
            if let (Some(frame), Some(signature)) = (&mut cached, &signature)
                && let Some((relation, facts, saved_scope)) =
                    frame.reuse(&fixed, prior.as_deref(), signature, &updates, c)?
            {
                relations.push(relation);
                support.extend(facts);
                scope.merge(&saved_scope);
                continue;
            }
            reuse::generated();
            let mut columns: Vec<usize> = vec![];
            loop {
                let mut discovered = BTreeSet::from_iter(columns.iter().copied());
                let mut allowed = vec![];
                let mut pass_unknown = vec![];
                let mut pass_skipped = false;
                let mut pass_support = BTreeSet::new();
                let mut pass_scope = Scope::default();
                rows(&columns, &domains, c, |point| {
                    let mut pins = vec![None; domains.len()];
                    for (column, value) in columns.iter().zip(point) {
                        pins[*column] = Some(*value);
                    }
                    let Some(witness) = updates.witness(&pins, c)? else {
                        pass_skipped = true;
                        return Ok(());
                    };
                    let mut values = fixed.fixed_values().into_iter().collect::<BTreeMap<_, _>>();
                    for output in &law_axes {
                        let index = witness[output.column];
                        values.insert(output.fact.clone(), domains[output.column][index].clone());
                    }
                    let updated = fixed.primitive_dependency_probe_from(
                        &values.into_iter().collect::<Vec<_>>(),
                        c,
                    )?;
                    let outer = updated
                        .state
                        .missing_slot_reads
                        .scoped(Some(BTreeSet::new()));
                    let row = finite_law_valuations::evaluate_change_factor(
                        &updated,
                        law,
                        bindings,
                        finite_law_valuations::FactorBody {
                            original_context: factor.original_context,
                            expression: factor.expression,
                            reading: &factor.reading,
                            bindings: &factor.bindings,
                            conditions: &factor.conditions,
                        },
                    )?;
                    pass_scope.merge(&row.scope);
                    let absent = outer
                        .restore()
                        .ok_or(internal!("有限関係のLaw不足収集がない"))?;
                    for fact in &row.support {
                        if let Some(o) = law_axes.iter().find(|o| same_slot(&o.fact, fact)) {
                            discovered.insert(o.column);
                        } else {
                            pass_support.insert(fact.clone());
                        }
                    }
                    match holds(&row) {
                        Some(true) => allowed.push(point.to_vec()),
                        Some(false) => {}
                        None => {
                            // 未決行はまだ可能な行として結合し、他の条件で
                            // 到達不能と分かった欠測を要求しない。
                            allowed.push(point.to_vec());
                            pass_unknown.push((point.to_vec(), absent));
                        }
                    }
                    Ok(())
                })?;
                let next = discovered.into_iter().collect::<Vec<_>>();
                if next == columns {
                    // 依存が閉じる前の仮の基準値は、観測要求へ昇格しない。
                    let complete = pass_unknown.is_empty();
                    if !complete {
                        unresolved.push((columns.clone(), pass_unknown));
                    }
                    let relation = finite::Relation {
                        columns,
                        rows: allowed.into(),
                    };
                    if complete
                        && !pass_skipped
                        && let (Some(frame), Some(signature)) = (&mut cached, signature.take())
                    {
                        frame.remember(
                            &fixed,
                            signature,
                            &relation,
                            &pass_support,
                            &pass_scope,
                            c,
                        )?;
                    }
                    support.extend(pass_support);
                    scope.merge(&pass_scope);
                    relations.push(relation);
                    break;
                }
                columns = next;
            }
        }
    }
    // 関係の座標に束縛した仮代入と量化は外部の観測条件ではない。
    // 外側の固定条件は元Architectureの参照から継承する。
    scope.assignments = false;
    scope.quantifiers.clear();
    let mut combined = updates.into_relations();
    combined.extend(relations);
    let relations = finite::Problem::new(sizes, combined, c)?;
    for (columns, rows) in unresolved {
        for (point, absent) in rows {
            tick(c)?;
            let mut pins = vec![None; domains.len()];
            for (column, value) in columns.iter().zip(point) {
                pins[*column] = Some(value);
            }
            if relations.exists(&pins, c)? {
                pending = true;
                missing.extend(absent);
            }
        }
    }
    if let Some(frame) = cached {
        frame.finish(&fixed, c)?;
    }
    if pending || !missing.is_empty() {
        return Ok(Compilation::Pending(missing.into_iter().collect()));
    }
    Ok(Compilation::Ready(std::sync::Arc::new(Compiled {
        subjects,
        parameter_types,
        parameter_count,
        domains,
        outputs,
        requirements: selected.requirements,
        bindings: selected.bindings,
        support: support.into_iter().collect(),
        scope,
        fixed: fixed.fixed_values(),
        relations: std::sync::Arc::new(relations),
    })))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    #[allow(dead_code)]
    mod fixture {
        include!("../../../../../tests/common/primitive_valuation_data.rs");
    }
    fn map() -> String {
        fixture::MAP.replace(r#""atoms":["#,r#""atoms":[{"id":"fq","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"model"},"#)
    }
    fn compile_body(map: &str, body: &str) -> Compilation {
        compile_body_inputs(map, body, None)
    }
    fn compile_body_inputs(map: &str, body: &str, input_space: Option<&InputSpace>) -> Compilation {
        let inputs = fixture::with_body(map, body);
        let c = archsig_common::control::quiet();
        let req = crate::observed::request::resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["s=prepare(Selected.valid,using=Selected.choose,on=@v/root)"],
            &c,
        )
        .unwrap();
        let request = &req.requests()[0];
        let root = Fact::from(archsig_input::archmap::FactData {
            snapshot: "v".into(),
            subject: "root".into(),
            field: None,
            atom: None,
        });
        let witness =
            ArchitectureWitness::compute(inputs.clone(), request, "Selected", &root, &c).unwrap();
        let env = Environment::new(&inputs, &c).unwrap();
        compile_inputs(&env, &Graph::new(&c), &witness, request, &c, input_space).unwrap()
    }
    #[test]
    fn original_evaluator_compiles_update_and_law_relations_without_erasing_unused_parameters() {
        let Compilation::Ready(p) = compile_body(
            &map(),
            "change choose(c:Part,p:Bool,q:Bool)=c with {flag=p};law required valid(c:Part):c.flag;",
        ) else {
            panic!("既知有限入力")
        };
        assert_eq!(p.parameter_count, 4);
        assert_eq!(p.relations.variables(), 6);
        let c = archsig_common::control::quiet();
        let pins = vec![None; 6];
        let first = p
            .relations
            .candidate(&pins, BigUint::from(0_u32), &c)
            .unwrap()
            .unwrap();
        let last = p
            .relations
            .candidate(&pins, BigUint::from(3_u32), &c)
            .unwrap()
            .unwrap();
        assert_eq!(&first[..4], &[1, 0, 1, 0]);
        assert_eq!(&last[..4], &[1, 1, 1, 1]);
        assert!(
            p.relations
                .candidate(&pins, BigUint::from(4_u32), &c)
                .unwrap()
                .is_none()
        );
        for o in &p.outputs {
            assert_eq!(p.domains[o.column][first[o.column]], Scalar::Bool(true));
        }
        let mut fixed = pins;
        let q = p.outputs.iter().find(|o| o.fact.subject == "q").unwrap();
        fixed[q.column] = q.baseline;
        assert!(!p.relations.exists(&fixed, &c).unwrap());
    }
    #[test]
    fn dependency_discovery_revisits_branches_and_keeps_cross_instance_laws() {
        let map=map().replace(r#""field":"Pattern.Part.flag","value":true"#,r#""field":"Pattern.Part.flag","value":false"#)
            .replace(r#""field":"Pattern.Part.link","value":["v","p"]"#,r#""field":"Pattern.Part.link","value":["v","q"]"#)
            .replace(r#""atoms":["#,r#""atoms":[{"id":"lq","subject":"q","field":"Pattern.Part.link","value":["v","q"],"origin":"model"},"#);
        let Compilation::Ready(p) = compile_body(
            &map,
            "change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):if c.flag then c.link.flag else true;",
        ) else {
            panic!("既知有限入力")
        };
        let c = archsig_common::control::quiet();
        let pins = vec![None; p.relations.variables()];
        let actual = (0_u32..3)
            .map(|i| {
                p.relations
                    .candidate(&pins, BigUint::from(i), &c)
                    .unwrap()
                    .unwrap()[..2]
                    .to_vec()
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, vec![vec![0, 0], vec![0, 1], vec![1, 1]]);
        assert!(
            p.relations
                .candidate(&pins, BigUint::from(3_u32), &c)
                .unwrap()
                .is_none()
        );
    }
    #[test]
    fn unresolved_baseline_keeps_the_original_missing_slot() {
        let Compilation::Pending(missing) = compile_body(
            fixture::MAP,
            "change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):c.flag;",
        ) else {
            panic!("欠測の基準値")
        };
        assert!(missing.iter().any(|f| f.snapshot == "v"
            && f.subject == "q"
            && f.field.as_deref() == Some("Pattern.Part.flag")));
    }
    #[test]
    fn input_coordinates_share_one_compilation_and_separate_existence_from_uniform_repair() {
        let c = archsig_common::control::quiet();
        let input = InputSpace {
            fields: vec![Fact::from(archsig_input::archmap::FactData {
                snapshot: "v".into(),
                subject: "q".into(),
                field: Some("Pattern.Part.flag".into()),
                atom: None,
            })],
            domains: vec![vec![Scalar::Bool(false), Scalar::Bool(true)]],
            rows: vec![vec![0], vec![1]],
        };
        let before = generations();
        let Compilation::Ready(p) = compile_body_inputs(
            fixture::MAP,
            "change choose(c:Part,p:Bool)=c with {flag=if p then c.flag else not c.flag};law required valid(c:Part):c.flag;",
            Some(&input),
        ) else {
            panic!("有限入力軸");
        };
        assert_eq!(generations() - before, 1);
        assert_eq!(p.parameter_count, 2);
        assert_eq!(p.relations.variables(), 5);
        let mut first = vec![None; 5];
        first[2] = Some(0);
        let mut second = first.clone();
        second[2] = Some(1);
        let left = p.relations.cofactor(&first, &c).unwrap();
        let right = p.relations.cofactor(&second, &c).unwrap();
        assert_eq!(left.witness(&[None; 4], &c).unwrap().unwrap()[..2], [1, 0]);
        assert_eq!(right.witness(&[None; 4], &c).unwrap().unwrap()[..2], [1, 1]);
        assert!(
            left.relations()
                .iter()
                .zip(right.relations())
                .any(|(a, b)| std::sync::Arc::ptr_eq(&a.rows, &b.rows))
        );
        let (common, _) = finite::Problem::join(&[&left, &right], 2, &c).unwrap();
        assert!(!common.exists(&vec![None; common.variables()], &c).unwrap());
    }
}
