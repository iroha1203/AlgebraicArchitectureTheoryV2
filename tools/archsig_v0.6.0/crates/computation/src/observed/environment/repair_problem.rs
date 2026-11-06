//! 元の型・更新式・Lawを有限の共有関係へ接続する。
use super::*;
use crate::observed::{construction_result::ArchitectureWitness, repair_problem::finite};
use archsig_input::law::{
    ast::{QuantDomain, QuantSplit},
    model::Signature,
};
use std::collections::BTreeSet;
mod law_factors;

#[cfg(test)]
thread_local! {static GENERATIONS:std::cell::Cell<usize>=const {std::cell::Cell::new(0)};}
#[cfg(test)]
pub(in crate::observed) fn generations() -> usize {
    GENERATIONS.with(std::cell::Cell::get)
}
#[derive(Debug)]
pub(in crate::observed) struct Output {
    pub fact: Fact,
    pub subject: usize,
    pub column: usize,
    pub baseline: usize,
}
#[derive(Debug)]
pub(in crate::observed) struct Compiled {
    pub subjects: Vec<Scalar>,
    pub parameter_types: Vec<Type>,
    pub domains: Vec<Vec<Scalar>>,
    pub parameter_count: usize,
    pub outputs: Vec<Output>,
    pub requirements: Vec<(String, Vec<(String, Scalar)>)>,
    pub bindings: Vec<(String, Scalar)>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub fixed: Vec<(Fact, Scalar)>,
    pub relations: finite::Problem,
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
            ExprKind::SetComp {
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
    domains: &[Vec<Scalar>],
    c: &Control,
    mut visit: impl FnMut(&[usize]) -> Result<(), ValidationFailure>,
) -> Result<(), ValidationFailure> {
    if domains.iter().any(Vec::is_empty) {
        return Ok(());
    }
    let mut point = vec![0; columns.len()];
    loop {
        tick(c)?;
        visit(&point)?;
        let mut at = point.len();
        loop {
            if at == 0 {
                return Ok(());
            }
            at -= 1;
            point[at] += 1;
            if point[at] < domains[columns[at]].len() {
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
fn same_slot(a: &Fact, b: &Fact) -> bool {
    a.snapshot == b.snapshot && a.subject == b.subject && a.field == b.field
}

pub(in crate::observed) fn compile(
    original: &Environment<'_>,
    graph: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    c: &Control,
) -> Result<Compilation, ValidationFailure> {
    #[cfg(test)]
    GENERATIONS.with(|n| n.set(n.get() + 1));
    let mut fixed = original
        .try_primitive_valuation_from(&original.fixed_values(), c)?
        .ok_or(internal!("有限修復の基準代入が不適合"))?;
    fixed.select_local_object(witness, c)?;
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
            let columns = dependencies(&fixed, *guard, &names)?
                .into_iter()
                .collect::<Vec<_>>();
            let mut allowed = vec![];
            rows(&columns, &domains, c, |point| {
                let update = change_evaluation::relation_guard(
                    &fixed,
                    change,
                    &bindings_for(&columns, point, &domains),
                )?;
                pending |= update.state == change_evaluation::State::Undetermined;
                scope.merge(&update.scope);
                support.extend(update.support);
                missing.extend(update.missing);
                if update.state == change_evaluation::State::Ready {
                    allowed.push(point.to_vec());
                }
                Ok(())
            })?;
            relations.push(finite::Relation {
                columns,
                rows: allowed,
            });
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
            let Some(base_value) = base.known_value else {
                missing.insert(fact);
                continue;
            };
            if base.condition_failed || base.condition_pending {
                return Err(unsupported(
                    change.span,
                    "finite repair baseline field is not constructible",
                ));
            }
            let columns = field_dependencies(&fixed, *body, field, &names)?
                .into_iter()
                .collect::<Vec<_>>();
            let mut values = vec![base_value];
            let mut allowed = vec![];
            rows(&columns, &domains, c, |point| {
                // guardの許容行へ延長できない局所割当ては更新式を読まない。
                // 別因子のguardを再評価せず、その共通parameter上の射影を使う。
                if guard.is_some() {
                    let relation = &relations[guard_relation];
                    let mut admissible = false;
                    for row in &relation.rows {
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
                let update = change_evaluation::relation_field(
                    &fixed,
                    change,
                    &bindings_for(&columns, point, &domains),
                    field,
                )?;
                pending |= update.state == change_evaluation::State::Undetermined;
                scope.merge(&update.scope);
                support.extend(update.support);
                missing.extend(update.missing);
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
            let column = domains.len();
            let mut relation_columns = columns;
            relation_columns.push(column);
            relations.push(finite::Relation {
                columns: relation_columns,
                rows: allowed,
            });
            outputs.push(Output {
                fact,
                subject: subject_index,
                column,
                baseline: 0,
            });
            domains.push(values);
        }
    }
    if pending || !missing.is_empty() {
        return Ok(Compilation::Pending(missing.into_iter().collect()));
    }
    let sizes = domains.iter().map(Vec::len).collect::<Vec<_>>();
    let updates = finite::Problem::new(sizes.clone(), relations, c)?;
    let mut relations = vec![];
    let mut unresolved = vec![];
    for (name, bindings) in &selected.requirements {
        let law = &fixed.indexes.inputs.law().declarations()[name];
        let factors = law_factors::collect(&fixed, law, bindings, &outputs, &domains, &updates)?;
        support.extend(factors.support);
        scope.merge(&factors.scope);
        for factor in factors.items {
            let mut columns: Vec<usize> = vec![];
            loop {
                let mut discovered = BTreeSet::from_iter(columns.iter().copied());
                let mut allowed = vec![];
                let mut pass_unknown = vec![];
                let mut pass_support = BTreeSet::new();
                let mut pass_scope = Scope::default();
                rows(&columns, &domains, c, |point| {
                    let mut pins = vec![None; domains.len()];
                    for (column, value) in columns.iter().zip(point) {
                        pins[*column] = Some(*value);
                    }
                    if !updates.exists(&pins, c)? {
                        return Ok(());
                    }
                    let mut values = fixed.fixed_values().into_iter().collect::<BTreeMap<_, _>>();
                    for output in &outputs {
                        let index = columns
                            .iter()
                            .position(|v| *v == output.column)
                            .map_or(0, |i| point[i]);
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
                        if let Some(o) = outputs.iter().find(|o| same_slot(&o.fact, fact)) {
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
                    if !pass_unknown.is_empty() {
                        unresolved.push((columns.clone(), pass_unknown));
                    }
                    support.extend(pass_support);
                    scope.merge(&pass_scope);
                    relations.push(finite::Relation {
                        columns,
                        rows: allowed,
                    });
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
        relations,
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
        let inputs = fixture::with_body(map, body);
        let c = archsig_common::control::quiet();
        let req = crate::observed::request::resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["s=solve(Selected.valid,using=Selected.choose,on=@v/root)"],
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
        compile(&env, &Graph::new(&c), &witness, request, &c).unwrap()
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
        fixed[q.column] = Some(q.baseline);
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
}
