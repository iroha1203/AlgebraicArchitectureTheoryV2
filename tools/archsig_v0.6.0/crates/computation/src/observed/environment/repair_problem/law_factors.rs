//! 固定した有限域の全称・合取を元の束縛に対応する小因子へ分ける。
use super::*;
use archsig_input::law::ast::QuantKind;
use archsig_input::law::model::Declaration;

pub(super) struct Factor {
    pub expression: usize,
    pub original_context: bool,
    pub reading: String,
    pub bindings: Vec<(String, Scalar)>,
    pub conditions: Vec<finite_law_valuations::FactorCondition>,
}
pub(super) struct Factors {
    pub items: Vec<Factor>,
    pub support: BTreeSet<Fact>,
    pub scope: Scope,
}
struct Collector<'a, 'i> {
    env: &'a Environment<'i>,
    outputs: &'a [Output],
    domains: &'a [std::sync::Arc<Vec<Scalar>>],
    updates: &'a finite::Problem,
    conditions: Vec<finite_law_valuations::FactorCondition>,
    factors: Factors,
    active: BTreeSet<String>,
}
impl Collector<'_, '_> {
    fn invariant(
        &self,
        id: usize,
        bindings: &BTreeMap<String, Scalar>,
        reading: &str,
    ) -> Result<Option<SourceValue>, ValidationFailure> {
        let vars = bindings
            .iter()
            .map(|(n, v)| (n.clone(), change_evaluation::known(v.clone())))
            .collect();
        let mut scope = Scope::default();
        scope.readings.insert(reading.to_owned());
        let value = match self.env.scoped_ast(id, &vars, &scope, reading) {
            Err(ValidationFailure::UnsupportedExpression { .. }) => return Ok(None),
            result => result?,
        };
        if value.condition_failed
            || value.condition_pending
            || value.known_value.is_none()
            || value
                .support
                .iter()
                .any(|f| self.outputs.iter().any(|o| same_slot(&o.fact, f)))
        {
            return Ok(None);
        }
        Ok(Some(value))
    }
    fn retain(&mut self, value: &SourceValue) {
        self.factors.support.extend(value.support.iter().cloned());
        self.factors.scope.merge(&value.scope);
    }
    fn emit(&mut self, expression: usize, reading: &str, bindings: &BTreeMap<String, Scalar>) {
        self.factors.items.push(Factor {
            expression,
            original_context: false,
            reading: reading.into(),
            bindings: bindings
                .iter()
                .map(|(n, v)| (n.clone(), v.clone()))
                .collect(),
            conditions: self.conditions.clone(),
        });
    }
    fn total_condition(
        &self,
        id: usize,
        bindings: &BTreeMap<String, Scalar>,
        reading: &str,
    ) -> Result<bool, ValidationFailure> {
        let mut columns = vec![];
        loop {
            let mut discovered = BTreeSet::from_iter(columns.iter().copied());
            let mut total = true;
            rows(&columns, self.domains, &self.env.control, |point| {
                let mut pins = vec![None; self.domains.len()];
                for (column, value) in columns.iter().zip(point) {
                    pins[*column] = Some(*value);
                }
                let Some(witness) = self.updates.witness(&pins, &self.env.control)? else {
                    return Ok(());
                };
                let mut fixed = self
                    .env
                    .fixed_values()
                    .into_iter()
                    .collect::<BTreeMap<_, _>>();
                for output in self.outputs {
                    let index = witness[output.column];
                    fixed.insert(
                        output.fact.clone(),
                        self.domains[output.column][index].clone(),
                    );
                }
                let updated = self.env.primitive_dependency_probe_from(
                    &fixed.into_iter().collect::<Vec<_>>(),
                    &self.env.control,
                )?;
                let vars = bindings
                    .iter()
                    .map(|(n, v)| (n.clone(), change_evaluation::known(v.clone())))
                    .collect();
                let mut scope = Scope::default();
                scope.readings.insert(reading.into());
                let value = match updated.scoped_ast(id, &vars, &scope, reading) {
                    Err(ValidationFailure::UnsupportedExpression { .. }) => {
                        total = false;
                        return Ok(());
                    }
                    result => result?,
                };
                for fact in &value.support {
                    if let Some(output) = self.outputs.iter().find(|o| same_slot(fact, &o.fact)) {
                        discovered.insert(output.column);
                    }
                }
                total &= !value.condition_failed
                    && !value.condition_pending
                    && matches!(value.known_value, Some(Scalar::Bool(_)));
                Ok(())
            })?;
            let next = discovered.into_iter().collect::<Vec<_>>();
            if next == columns {
                return Ok(total);
            }
            columns = next;
        }
    }
    fn collect(
        &mut self,
        id: usize,
        reading: &str,
        bindings: &BTreeMap<String, Scalar>,
    ) -> Result<(), ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.collect_inner(id, reading, bindings)
        })
    }
    fn collect_inner(
        &mut self,
        id: usize,
        reading: &str,
        bindings: &BTreeMap<String, Scalar>,
    ) -> Result<(), ValidationFailure> {
        self.env.tick()?;
        let kind = self.env.indexes.inputs.law().exprs()[id].kind.clone();
        match kind {
            ExprKind::Group(inner) => return self.collect(inner, reading, bindings),
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                self.collect(lhs, reading, bindings)?;
                return self.collect(rhs, reading, bindings);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                if let Some(value) = self.invariant(cond, bindings, reading)?
                    && let Some(Scalar::Bool(test)) = &value.known_value
                {
                    let selected = if *test { then_branch } else { else_branch };
                    self.retain(&value);
                    return self.collect(selected, reading, bindings);
                }
                if self.total_condition(cond, bindings, reading)? {
                    let mut condition = finite_law_valuations::FactorCondition {
                        expression: cond,
                        reading: reading.into(),
                        bindings: bindings
                            .iter()
                            .map(|(n, v)| (n.clone(), v.clone()))
                            .collect(),
                        positive: true,
                    };
                    self.conditions.push(condition.clone());
                    self.collect(then_branch, reading, bindings)?;
                    self.conditions.pop();
                    condition.positive = false;
                    self.conditions.push(condition);
                    self.collect(else_branch, reading, bindings)?;
                    self.conditions.pop();
                    return Ok(());
                }
            }
            ExprKind::Let { name, value, body } => {
                if let Some(value) = self.invariant(value, bindings, reading)? {
                    let mut nested = bindings.clone();
                    nested.insert(
                        name.name,
                        value.known_value.as_ref().expect("既知の不変値").clone(),
                    );
                    self.retain(&value);
                    return self.collect(body, reading, &nested);
                }
            }
            ExprKind::Quant {
                kind: QuantKind::Forall,
                ..
            } => {
                let spec = match crate::observed::quantifier::spec(
                    self.env.indexes.inputs.law(),
                    id,
                    &self.env.control,
                ) {
                    Err(ValidationFailure::UnsupportedExpression { .. }) => {
                        self.emit(id, reading, bindings);
                        return Ok(());
                    }
                    result => result?,
                };
                let values = if let Some(domain) = spec.domain {
                    match self.invariant(domain, bindings, reading)? {
                        Some(value) => {
                            let values = match value.known_value.as_ref() {
                                Some(Scalar::Set { items, .. } | Scalar::List { items, .. }) => {
                                    items.clone()
                                }
                                _ => return Err(internal!("固定量化域がList/Setでない").into()),
                            };
                            self.retain(&value);
                            Some(values)
                        }
                        None => None,
                    }
                } else if !spec.owners.is_empty()
                    || self
                        .outputs
                        .iter()
                        .any(|o| o.fact.field.as_ref().is_some_and(|f| f.is_owner()))
                {
                    None
                } else {
                    let mut missing = vec![];
                    let values = change_search::domain(
                        self.env,
                        &spec.domain_type,
                        spec.span,
                        &mut missing,
                    )?;
                    if missing.is_empty() { values } else { None }
                };
                if let Some(values) = values {
                    // 空域でも外側Lawのguard・適用条件を省略しない。
                    if !values.is_empty() {
                        for value in values {
                            self.env.tick()?;
                            let mut nested = bindings.clone();
                            nested.insert(spec.name.to_owned(), value);
                            self.collect(spec.body, reading, &nested)?;
                        }
                        return Ok(());
                    }
                }
            }
            ExprKind::Call { callee, args } => {
                if let ExprKind::Dotted(parts) = &self.env.indexes.inputs.law().exprs()[callee].kind
                    && !bindings.contains_key(&parts[0].name)
                {
                    let raw = parts
                        .iter()
                        .map(|p| p.name.as_str())
                        .collect::<Vec<_>>()
                        .join(".");
                    let name = if parts.len() == 1 {
                        format!("{reading}.{raw}")
                    } else {
                        raw
                    };
                    if !self.active.contains(&name)
                        && let Some(view) = self.env.indexes.inputs.law().declarations().get(&name)
                        && let Signature::View { params, body, .. } = &view.signature
                    {
                        let mut actual = vec![];
                        for arg in &args {
                            let Some(value) = self.invariant(*arg, bindings, reading)? else {
                                self.emit(id, reading, bindings);
                                return Ok(());
                            };
                            actual.push(value);
                        }
                        if params.len() != actual.len() {
                            self.emit(id, reading, bindings);
                            return Ok(());
                        }
                        let mut checks = owned_call::Checks::default();
                        let mut checked = BTreeMap::new();
                        for (parameter, value) in params.iter().zip(&actual) {
                            let scalar = value.known_value.as_ref().expect("既知のview引数");
                            self.env.owned_call_value_check(
                                &parameter.ty,
                                &crate::observed::term::affine::Value::Known(scalar.clone()),
                                &checked,
                                &view.reading,
                                parameter.span,
                                &mut checks,
                            )?;
                            checked.insert(parameter.name.as_str(), Some(scalar));
                        }
                        if !checks.blocked
                            && checks.failure.is_none()
                            && !checks
                                .support
                                .iter()
                                .any(|f| self.outputs.iter().any(|o| same_slot(&o.fact, f)))
                        {
                            let mut nested = BTreeMap::new();
                            for (parameter, value) in params.iter().zip(&actual) {
                                nested.insert(
                                    parameter.name.clone(),
                                    value.known_value.as_ref().expect("既知のview引数").clone(),
                                );
                                self.retain(value);
                            }
                            self.factors.support.extend(checks.support);
                            self.factors.scope.merge(&checks.scope);
                            self.active.insert(name.clone());
                            self.collect(*body, &view.reading, &nested)?;
                            self.active.remove(&name);
                            return Ok(());
                        }
                    }
                }
            }
            _ => {}
        }
        self.emit(id, reading, bindings);
        Ok(())
    }
}
pub(super) fn collect(
    env: &Environment<'_>,
    law: &Declaration,
    bindings: &[(String, Scalar)],
    outputs: &[Output],
    domains: &[std::sync::Arc<Vec<Scalar>>],
    updates: &finite::Problem,
) -> Result<Factors, ValidationFailure> {
    let Signature::Law { params, body, .. } = &law.signature else {
        return Err(internal!("部品化する元Lawがない").into());
    };
    let mut collector = Collector {
        env,
        outputs,
        domains,
        updates,
        conditions: vec![],
        factors: Factors {
            items: vec![],
            support: BTreeSet::new(),
            scope: Scope::default(),
        },
        active: BTreeSet::new(),
    };
    let bindings = bindings.iter().cloned().collect::<BTreeMap<_, _>>();
    if params.iter().any(|p| !bindings.contains_key(&p.name)) {
        collector.emit(*body, &law.reading, &bindings);
        collector
            .factors
            .items
            .last_mut()
            .expect("元式の因子")
            .original_context = true;
    } else {
        collector.collect(*body, &law.reading, &bindings)?;
    }
    Ok(collector.factors)
}
