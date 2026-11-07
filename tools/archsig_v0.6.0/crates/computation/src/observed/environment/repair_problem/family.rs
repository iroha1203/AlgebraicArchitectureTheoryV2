//! 入力viewの有限補完を、一度生成した局所関係の制限へ対応させる。
use super::*;
use std::sync::Arc;

#[derive(Debug)]
pub(in crate::observed) struct Variant {
    pub outputs: Vec<Output>,
    pub relations: Arc<finite::Problem>,
}
#[derive(Debug)]
pub(in crate::observed) struct Family {
    pub view: String,
    pub bindings: Vec<(String, Scalar)>,
    pub fields: Vec<Fact>,
    pub domains: Vec<Arc<Vec<Scalar>>>,
    pub points: Vec<Vec<usize>>,
    pub variants: Vec<Variant>,
    pub maps: Vec<Vec<usize>>,
}
pub(in crate::observed) enum Preparation {
    Ready(Arc<Compiled>, Arc<Family>),
    Pending(Vec<Fact>),
    Rejected,
}
#[derive(Debug)]
pub(in crate::observed) struct Read {
    pub failed: bool,
    pub blocked: bool,
    pub missing: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
pub(in crate::observed) fn read(
    env: &Environment<'_>,
    name: &str,
    bindings: &[(String, Scalar)],
) -> Result<Read, ValidationFailure> {
    read_with_value(env, name, bindings).map(|(read, _)| read)
}
pub(in crate::observed) fn read_with_value(
    env: &Environment<'_>,
    name: &str,
    bindings: &[(String, Scalar)],
) -> Result<(Read, Option<Scalar>), ValidationFailure> {
    let declaration = &env.indexes.inputs.law().declarations()[name];
    let Signature::View { params, body, .. } = &declaration.signature else {
        return Err(internal!("原始読取りの元がviewでない").into());
    };
    let collector = env.state.missing_slot_reads.scoped(Some(BTreeSet::new()));
    let primitive = env.state.primitive_reads.scoped(Some(BTreeSet::new()));
    let positions = env.state.unresolved_read_positions.scoped(Some(false));
    let mut checked = BTreeMap::new();
    let mut checks = owned_call::Checks::default();
    let mut vars = BTreeMap::new();
    for parameter in params {
        let value = &bindings
            .iter()
            .find(|(n, _)| *n == parameter.name)
            .ok_or(internal!("原始読取りの束縛がない"))?
            .1;
        env.owned_call_value_check(
            &parameter.ty,
            &crate::observed::term::affine::Value::Known(value.clone()),
            &checked,
            &declaration.reading,
            parameter.span,
            &mut checks,
        )?;
        checked.insert(parameter.name.as_str(), Some(value));
        vars.insert(
            parameter.name.clone(),
            change_evaluation::known(value.clone()),
        );
    }
    let mut scope = checks.scope;
    scope.readings.insert(declaration.reading.clone());
    let value = if checks.failure.is_none() && !checks.blocked {
        Some(env.scoped_ast(*body, &vars, &scope, &declaration.reading)?)
    } else {
        None
    };
    let missing = collector
        .restore()
        .ok_or(internal!("入力viewの欠測収集がない"))?;
    let reads = primitive
        .restore()
        .ok_or(internal!("入力viewの原始読取り収集がない"))?;
    let unresolved = positions
        .restore()
        .ok_or(internal!("入力viewの読取り位置収集がない"))?;
    let mut support = checks.support;
    support.extend(reads);
    let mut failed = checks.failure.is_some();
    let mut blocked = checks.blocked || unresolved;
    let mut known = None;
    if let Some(value) = value {
        support.extend(value.support.iter().cloned());
        scope.merge(&value.scope);
        failed |= value.condition_failed;
        blocked |= value.condition_pending;
        if !failed && value.known_value.is_none() && missing.is_empty() {
            return Err(unsupported(
                declaration.span,
                "observation view has an unresolved computation",
            ));
        }
        known = value.known_value;
    }
    if blocked && missing.is_empty() {
        return Err(unsupported(
            declaration.span,
            "observation view requires valid primitive reads",
        ));
    }
    Ok((
        Read {
            failed,
            blocked,
            missing: missing.into_iter().collect(),
            support: support
                .into_iter()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            scope,
        },
        known,
    ))
}
impl Family {
    pub fn values(&self, index: usize) -> Vec<(Fact, Scalar)> {
        self.fields
            .iter()
            .cloned()
            .zip(
                self.points[index]
                    .iter()
                    .enumerate()
                    .map(|(i, p)| self.domains[i][*p].clone()),
            )
            .collect()
    }
    pub fn environment<'a>(
        &self,
        env: &Environment<'a>,
        index: usize,
    ) -> Result<Environment<'a>, ValidationFailure> {
        let values = env
            .fixed_values()
            .into_iter()
            .chain(self.values(index))
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .collect::<Vec<_>>();
        env.primitive_dependency_probe_from(&values, &env.control)
    }
}
pub(in crate::observed) fn prepare(
    original: &Environment<'_>,
    g: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    c: &Control,
) -> Result<Preparation, ValidationFailure> {
    let name = request
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("inputs", Selector::Declaration { name }) => Some(name.clone()),
            _ => None,
        })
        .ok_or(internal!("有限入力viewがない"))?;
    let mut bindings = vec![];
    let Signature::View { params, .. } =
        &original.indexes.inputs.law().declarations()[&name].signature
    else {
        return Err(internal!("有限入力がviewでない").into());
    };
    for parameter in params {
        let argument = request
            .arguments
            .iter()
            .find(|a| a.name == format!("bind.{}", parameter.name))
            .ok_or(internal!("入力viewの元束縛がない"))?;
        bindings.push((
            parameter.name.clone(),
            change_search::selector(original, g, &argument.value)?,
        ));
    }
    let mut fixed = original
        .try_primitive_valuation_from(&original.fixed_values(), c)?
        .ok_or(internal!("入力族の基準が不適合"))?;
    fixed.select_local_object(witness, c)?;
    let first = read(&fixed, &name, &bindings)?;
    if first.failed {
        return Ok(Preparation::Rejected);
    }
    if first
        .missing
        .iter()
        .any(|f| f.field.as_ref().is_some_and(|f| f.is_owner()))
    {
        return Ok(Preparation::Pending(first.missing));
    }
    let mut fields = first.missing;
    let mut support = first.support.into_iter().collect::<BTreeSet<_>>();
    let mut scope = first.scope;
    let (space, points) = loop {
        tick(c)?;
        for fact in &fields {
            let field = fixed.indexes.field(
                &fixed.state,
                &fact.snapshot,
                &fact.subject,
                fact.field
                    .as_deref()
                    .ok_or(internal!("入力位置のfieldがない"))?,
            )?;
            if !fixed.completion_type_supported(&field.ty)? {
                return Err(unsupported(
                    original.indexes.inputs.law().declarations()[&name].span,
                    "input view requires finite primitive completions",
                ));
            }
        }
        let enumeration = if fields.is_empty() {
            None
        } else {
            Some(fixed.completion_assignments(&fields, &mut |_, _| {})?)
        };
        let mut domains = vec![vec![]; fields.len()];
        let mut points = vec![];
        let mut additional = BTreeSet::new();
        if let Some(enumeration) = enumeration {
            scope.merge(&enumeration.scope);
            support.extend(enumeration.support);
            for mut value in enumeration.values {
                tick(c)?;
                let values = if fields.len() == 1 {
                    vec![value]
                } else {
                    let Scalar::Tuple(values) = &mut value else {
                        return Err(internal!("入力補完の積が違う").into());
                    };
                    std::mem::take(values)
                };
                let mut point = vec![];
                for (domain, value) in domains.iter_mut().zip(values) {
                    let at = domain.iter().position(|v| *v == value).unwrap_or_else(|| {
                        domain.push(value);
                        domain.len() - 1
                    });
                    point.push(at);
                }
                let assignment = fields
                    .iter()
                    .cloned()
                    .zip(
                        point
                            .iter()
                            .enumerate()
                            .map(|(i, p)| domains[i][*p].clone()),
                    )
                    .collect::<Vec<_>>();
                let values = fixed
                    .fixed_values()
                    .into_iter()
                    .chain(assignment)
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                let updated = fixed.primitive_dependency_probe_from(&values, c)?;
                let probe = read(&updated, &name, &bindings)?;
                if probe.failed {
                    return Ok(Preparation::Rejected);
                }
                if probe
                    .missing
                    .iter()
                    .any(|f| f.field.as_ref().is_some_and(|f| f.is_owner()))
                {
                    return Ok(Preparation::Pending(probe.missing));
                }
                additional.extend(
                    probe
                        .missing
                        .into_iter()
                        .filter(|f| !fields.iter().any(|old| same_slot(old, f))),
                );
                support.extend(probe.support);
                scope.merge(&probe.scope);
                points.push(point);
            }
        } else {
            points.push(vec![]);
        }
        points.sort();
        points.dedup();
        if points.is_empty() {
            return Ok(Preparation::Rejected);
        }
        if additional.is_empty() {
            break (
                InputSpace {
                    fields: fields.clone(),
                    domains,
                    rows: points.clone(),
                },
                points,
            );
        }
        fields.extend(additional);
        fields.sort();
        fields.dedup();
    };
    let compiled = match compile_inputs(&fixed, g, witness, request, c, Some(&space))? {
        Compilation::Ready(compiled) => compiled,
        Compilation::Pending(missing) => return Ok(Preparation::Pending(missing)),
    };
    let mut compiled = Arc::try_unwrap(compiled)
        .map_err(|_| internal!("入力関係の生成結果が既に共有されている"))?;
    let parameters = compiled.parameter_count;
    let count = space.fields.len();
    let mut variants = vec![];
    let mut pool = BTreeSet::new();
    for point in &points {
        tick(c)?;
        let mut pins = vec![None; compiled.domains.len()];
        for (i, v) in point.iter().enumerate() {
            pins[parameters + i] = Some(*v);
        }
        let mut relation = compiled.relations.cofactor(&pins, c)?;
        relation.share_rows(&mut pool, c)?;
        let mut outputs = compiled.outputs.clone();
        for output in &mut outputs {
            if output.baseline.is_none() {
                let i = space
                    .fields
                    .iter()
                    .position(|f| same_slot(f, &output.fact))
                    .ok_or(internal!("基準値の入力座標がない"))?;
                output.baseline = Some(
                    compiled.domains[output.column]
                        .iter()
                        .position(|v| *v == space.domains[i][point[i]])
                        .ok_or(internal!("入力基準値が更新先の域にない"))?,
                );
            }
            output.column -= count;
        }
        variants.push(Variant {
            outputs,
            relations: Arc::new(relation),
        });
    }
    let (relation, maps) = finite::Problem::join(
        &variants
            .iter()
            .map(|v| v.relations.as_ref())
            .collect::<Vec<_>>(),
        parameters,
        c,
    )?;
    let mut domains = compiled.domains[..parameters].to_vec();
    for _ in &variants {
        domains.extend(compiled.domains[parameters + count..].iter().cloned());
    }
    compiled.outputs = variants[0]
        .outputs
        .iter()
        .cloned()
        .map(|mut o| {
            o.column = maps[0][o.column];
            o
        })
        .collect();
    compiled.domains = domains;
    compiled.relations = Arc::new(relation);
    compiled.fixed = original.fixed_values();
    compiled.support.extend(support);
    compiled.support.sort();
    compiled.support.dedup();
    compiled.scope.merge(&scope);
    compiled.scope.completions = !fields.is_empty();
    let family = Family {
        view: name,
        bindings,
        fields,
        domains: space.domains.into_iter().map(Arc::new).collect(),
        points,
        variants,
        maps,
    };
    Ok(Preparation::Ready(Arc::new(compiled), Arc::new(family)))
}
