//! 元readingのrelation instanceと、語を保った全域作用の検査。
use super::*;
use crate::law::model::{Declaration, Param, Signature};
use crate::{
    input::InputSources,
    observed::{affine, path_value::PathValue},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum RelationState {
    OutsideDomain,
    Inactive,
    Established,
    Refuted,
    ConditionFailed,
    Pending,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum RelationDifference {
    Endpoints { left: Scalar, right: Scalar },
    Action { fact: Fact, left: Fact, right: Fact },
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct RelationInstance {
    pub declaration: String,
    pub bindings: Vec<(String, Scalar)>,
    // bindingsに具体値を置かず、元binderのまま全称評価した数値軸。
    pub numeric_parameters: Vec<Param>,
    // 元の数値parameter座標の適用域。guardと語はこの全解上で評価する。
    pub numeric_domain: Option<change_affine::NumericGuard>,
    pub guard: Option<bool>,
    // guard自身の適合条件を、左右の語の成立状態から区別する。
    pub guard_checked: bool,
    pub left: Option<Scalar>,
    pub right: Option<Scalar>,
    pub left_checked: bool,
    pub right_checked: bool,
    pub state: RelationState,
    pub difference: Option<RelationDifference>,
    pub missing: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct OutsideFiniteRelation {
    pub declaration: String,
    pub parameter: String,
    pub ty: Type,
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct PendingRelationDomain {
    pub declaration: String,
    pub parameter: String,
    pub bindings: Vec<(String, Scalar)>,
    pub missing: Vec<Fact>,
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct RelationInstances {
    sources: InputSources,
    reading: String,
    pub declarations: Vec<Declaration>,
    pub instances: Vec<RelationInstance>,
    pub outside_finite: Vec<OutsideFiniteRelation>,
    pub pending_domains: Vec<PendingRelationDomain>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    enumeration_complete: bool,
    numeric_families: bool,
}
pub(in crate::observed) struct RelationInstancesFailure {
    pub cause: ValidationFailure,
    pub partial: Box<RelationInstances>,
}
impl std::fmt::Debug for RelationInstancesFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RelationInstancesFailure")
            .field("cause", &self.cause)
            .field("completed_rows", &self.partial.instances.len())
            .finish()
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone().checkpoint(Checkpoint::FiniteIteration)?;
    Ok(())
}
impl RelationInstances {
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn enumeration_complete(&self) -> bool {
        self.enumeration_complete
    }
    // 未決・反証を除外した族を完成した提示として使わせない。
    pub fn conditions_verified(&self) -> bool {
        self.enumeration_complete
            && self.outside_finite.is_empty()
            && self.pending_domains.is_empty()
            && self.instances.iter().all(|r| {
                matches!(
                    r.state,
                    RelationState::OutsideDomain
                        | RelationState::Inactive
                        | RelationState::Established
                )
            })
    }
    pub fn established(&self) -> impl Iterator<Item = &RelationInstance> {
        self.instances
            .iter()
            .filter(|r| r.state == RelationState::Established)
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        c: &mut Control,
    ) -> Result<(), RelationInstancesFailure> {
        if &self.sources != inputs.sources() {
            return Err(RelationInstancesFailure {
                cause: "relation表の元三入力が違う".into(),
                partial: Box::new(self.clone()),
            });
        }
        let expected = instances(inputs, &self.reading, c, self.numeric_families)?;
        tick(c).map_err(|cause| RelationInstancesFailure {
            cause,
            partial: Box::new(expected.clone()),
        })?;
        if self != &expected {
            return Err(RelationInstancesFailure {
                cause: "relation表が元宣言・全束縛・作用検査と違う".into(),
                partial: Box::new(expected),
            });
        }
        Ok(())
    }
}
fn known(
    e: &Environment<'_>,
    value: Scalar,
    reading: &str,
) -> Result<SourceValue, ValidationFailure> {
    let mut scope = Scope::default();
    scope.readings.insert(reading.into());
    let mut support = vec![];
    let mut pending = vec![&value];
    while let Some(part) = pending.pop() {
        e.tick()?;
        match part {
            Scalar::Subject {
                snapshot,
                subject,
                entity,
            } => {
                let actual = e.indexes.subject(snapshot, subject)?;
                if actual.ty != *entity {
                    return Err("relationの参照束縛と原始型が違う".into());
                }
                scope.merge(&e.indexes.scope(actual, reading, None)?);
                support.extend(e.subject_support(part)?);
            }
            Scalar::Tuple(items)
            | Scalar::List { items, .. }
            | Scalar::Set { items, .. }
            | Scalar::Data { args: items, .. } => pending.extend(items),
            Scalar::Map { pairs, .. } => {
                for (a, b) in pairs {
                    e.tick()?;
                    pending.extend([a, b]);
                }
            }
            Scalar::Option { value: Some(v), .. } => pending.push(v),
            _ => {}
        }
    }
    support.sort();
    support.dedup();
    Ok(SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        scalar_scope: Some(scope.clone()),
        scope,
        known_value: Some(value),
        affine: None,
        support,
    })
}
fn difference(
    a: &PathValue,
    b: &PathValue,
    c: &Control,
) -> Result<Option<RelationDifference>, ValidationFailure> {
    a.check(c)?;
    b.check(c)?;
    for (left, right) in [(a.object(), b.object()), (a.target(), b.target())] {
        tick(c)?;
        if left != right {
            return Ok(Some(RelationDifference::Endpoints { left, right }));
        }
    }
    let Some(step) = a.step.as_ref().or(b.step.as_ref()) else {
        return Ok(None);
    };
    if let (Some(a), Some(b)) = (&a.step, &b.step) {
        if a.carrier != b.carrier {
            return Err("relationの共通Uが違う".into());
        }
    }
    for (index, fact) in step.carrier.iter().enumerate() {
        tick(c)?;
        let left = match &a.step {
            Some(s) => s.images.get(index).ok_or("左relation像がない")?,
            None => fact,
        };
        let right = match &b.step {
            Some(s) => s.images.get(index).ok_or("右relation像がない")?,
            None => fact,
        };
        if left != right {
            return Ok(Some(RelationDifference::Action {
                fact: fact.clone(),
                left: left.clone(),
                right: right.clone(),
            }));
        }
    }
    tick(c)?;
    Ok(None)
}
fn restrict_variables(
    e: &Environment<'_>,
    variables: &mut BTreeMap<String, SourceValue>,
    axes: &[affine::Parameter],
    domain: &change_affine::NumericGuard,
    params: &[Param],
) -> Result<(), ValidationFailure> {
    let particular = domain
        .particular
        .as_ref()
        .ok_or("空の数値域にrelationを適用できない")?;
    let width = domain.kernel.first().map_or(0, Vec::len);
    if particular.len() != axes.len()
        || domain.kernel.len() != axes.len()
        || width > axes.len()
        || domain.kernel.iter().any(|row| row.len() != width)
        || axes.iter().any(|axis| axis.kind != axes[0].kind)
    {
        return Err("relation適用域の元parameter座標が違う".into());
    }
    for (index, axis) in axes.iter().enumerate() {
        e.tick()?;
        let mut form =
            affine::constant(&particular[index], &e.control)?.ok_or("数値特解の式がない")?;
        for (coefficient, free) in domain.kernel[index].iter().zip(axes) {
            e.tick()?;
            let coefficient = affine::constant(coefficient, &e.control)?;
            let parameter = affine::parameter(&particular[index].ty(), free, &e.control)?;
            let term = affine::binary(
                BinOp::Mul,
                coefficient.as_ref(),
                parameter.as_ref(),
                &e.control,
            )?;
            form = affine::binary(BinOp::Add, Some(&form), term.as_ref(), &e.control)?
                .ok_or("数値核の式がない")?;
        }
        let value = variables
            .get_mut(&axis.name)
            .ok_or("relation適用域の数値変数がない")?;
        value.known_value = form.value(&e.control)?;
        value.scalar_scope = value.known_value.as_ref().map(|_| value.scope.clone());
        value.affine = Some(Box::new(form));
    }
    numeric_parameters::tuple_variables(e, params, variables)
}
// 移送先は自身のguardの解集合ではなく、sourceの適用域で読む。
pub(in crate::observed) fn on_numeric_domain(
    e: &Environment<'_>,
    declaration: &Declaration,
    bindings: Vec<(String, Scalar)>,
    domain: &change_affine::NumericGuard,
) -> Result<RelationInstance, ValidationFailure> {
    row(e, declaration, bindings, true, Some(domain))
}
pub(in crate::observed) fn at_numeric_point(
    e: &Environment<'_>,
    declaration: &Declaration,
    bindings: Vec<(String, Scalar)>,
) -> Result<RelationInstance, ValidationFailure> {
    row(e, declaration, bindings, true, None)
}
fn row_value(
    e: &Environment<'_>,
    declaration: &Declaration,
    bindings: Vec<(String, Scalar)>,
    numeric_families: bool,
    numeric_domain: Option<&change_affine::NumericGuard>,
) -> Result<RelationInstance, ValidationFailure> {
    let Signature::Relation {
        params,
        guard,
        left,
        right,
    } = &declaration.signature
    else {
        return Err("元relation署名がない".into());
    };
    let mut checks = owned_call::Checks::default();
    let mut values = BTreeMap::new();
    for p in params {
        let Some((_, v)) = bindings.iter().find(|(name, _)| name == &p.name) else {
            if numeric_families && numeric_parameters::numeric_width(&p.ty).is_some() {
                continue;
            }
            return Err("relation parameterの束縛がない".into());
        };
        e.tick()?;
        e.owned_call_value_check(
            &p.ty,
            &super::super::term::affine::Value::Known(v.clone()),
            &values,
            &declaration.reading,
            declaration.span,
            &mut checks,
        )?;
        values.insert(p.name.as_str(), Some(v));
    }
    let mut out = RelationInstance {
        declaration: declaration.name.clone(),
        bindings: bindings.clone(),
        numeric_parameters: params
            .iter()
            .filter(|p| !bindings.iter().any(|(name, _)| name == &p.name))
            .cloned()
            .collect(),
        numeric_domain: numeric_domain.cloned(),
        guard: None,
        guard_checked: false,
        left: None,
        right: None,
        left_checked: false,
        right_checked: false,
        state: RelationState::Pending,
        difference: None,
        missing: checks.missing,
        support: checks.support,
        scope: checks.scope,
    };
    out.scope.readings.insert(declaration.reading.clone());
    if checks.failure.is_some() {
        out.state = RelationState::OutsideDomain;
        return Ok(out);
    }
    if checks.blocked {
        return Ok(out);
    }
    let mut variables = bindings
        .iter()
        .cloned()
        .map(|(n, v)| known(e, v, &declaration.reading).map(|v| (n, v)))
        .collect::<Result<BTreeMap<_, _>, ValidationFailure>>()?;
    let mut axes = vec![];
    if numeric_families {
        let (mut symbolic, parameters) = numeric_parameters::law_variables(e, params, &bindings)?;
        for (name, value) in variables {
            let entry = symbolic.get_mut(&name).ok_or("relationの記号束縛がない")?;
            entry.scope = value.scope;
            entry.scalar_scope = value.scalar_scope;
            entry.support = value.support;
        }
        variables = symbolic;
        axes = parameters;
    }
    for value in variables.values() {
        out.support.extend(value.support.iter().cloned());
        out.scope.merge(&value.scope);
    }
    let base = out.scope.clone();
    if let Some(domain) = numeric_domain {
        restrict_variables(e, &mut variables, &axes, domain, params)?;
    }
    let mut g = guard
        .map(|id| e.scoped_ast(id, &variables, &base, &declaration.reading))
        .transpose()?;
    // 型全域で未知でも、数値等式の全解上で再評価できる。標本値は使わない。
    if numeric_domain.is_none()
        && numeric_families
        && !axes.is_empty()
        && axes.iter().all(|p| p.kind == axes[0].kind)
        && g.as_ref().is_none_or(|v| {
            v.known_value != Some(Scalar::Bool(false))
                && !v.condition_failed
                && !v.condition_pending
        })
    {
        let mut metadata = change_affine::Pending::default();
        let domain = change_affine::numeric_guard_domain(
            e,
            *guard,
            &variables,
            &axes,
            &declaration.reading,
            &mut metadata,
            &match axes[0].kind {
                affine::NumberType::Z => Type::Z,
                affine::NumberType::Q => Type::Q,
            },
        );
        out.support.extend(metadata.support);
        out.scope.merge(&metadata.scope);
        match domain {
            Ok(domain) => {
                if domain.particular.is_none() {
                    out.guard = Some(false);
                    out.guard_checked = true;
                    out.state = RelationState::Inactive;
                    out.numeric_domain = Some(domain);
                    return Ok(out);
                }
                restrict_variables(e, &mut variables, &axes, &domain, params)?;
                out.numeric_domain = Some(domain);
                g = guard
                    .map(|id| e.scoped_ast(id, &variables, &base, &declaration.reading))
                    .transpose()?;
            }
            Err(ValidationFailure::UnsupportedExpression { .. }) => {}
            Err(error) => return Err(error),
        }
    }
    out.guard = match &g {
        None => Some(true),
        Some(g) => match &g.known_value {
            Some(Scalar::Bool(v)) => Some(*v),
            None => None,
            _ => return Err("relation guardがBoolでない".into()),
        },
    };
    if let Some(g) = &g {
        out.support.extend(g.support.iter().cloned());
        out.scope.merge(&g.scope);
    }
    if g.as_ref().is_some_and(|g| g.condition_failed) {
        out.state = RelationState::ConditionFailed;
        return Ok(out);
    }
    if g.as_ref().is_some_and(|g| g.condition_pending) || out.guard.is_none() {
        return Ok(out);
    }
    out.guard_checked = true;
    if out.guard == Some(false) {
        out.state = RelationState::Inactive;
        return Ok(out);
    }
    let a = e.scoped_ast(*left, &variables, &base, &declaration.reading)?;
    let b = e.scoped_ast(*right, &variables, &base, &declaration.reading)?;
    for value in [&a, &b] {
        out.support.extend(value.support.iter().cloned());
        out.scope.merge(&value.scope);
    }
    out.left = a.known_value.clone();
    out.right = b.known_value.clone();
    out.left_checked = !a.condition_failed && !a.condition_pending;
    out.right_checked = !b.condition_failed && !b.condition_pending;
    if a.condition_failed || b.condition_failed {
        out.state = RelationState::ConditionFailed;
        return Ok(out);
    }
    if a.condition_pending || b.condition_pending {
        return Ok(out);
    }
    if let (Some(Scalar::Path(a)), Some(Scalar::Path(b))) = (&out.left, &out.right) {
        out.difference = difference(a, b, &e.control)?;
        out.state = if out.difference.is_some() {
            RelationState::Refuted
        } else {
            RelationState::Established
        };
    }
    out.support.sort();
    out.support.dedup();
    out.missing.sort();
    out.missing.dedup();
    e.tick()?;
    Ok(out)
}
fn row(
    e: &Environment<'_>,
    d: &Declaration,
    bindings: Vec<(String, Scalar)>,
    numeric_families: bool,
    numeric_domain: Option<&change_affine::NumericGuard>,
) -> Result<RelationInstance, ValidationFailure> {
    *e.state.missing_slot_reads.borrow_mut() = Some(BTreeSet::new());
    let result = row_value(e, d, bindings, numeric_families, numeric_domain);
    let missing = e
        .state
        .missing_slot_reads
        .borrow_mut()
        .take()
        .ok_or("relationの不足位置読取りがない")?;
    result.map(|mut row| {
        row.missing.extend(missing);
        row.missing.sort();
        row.missing.dedup();
        row.support.sort();
        row.support.dedup();
        row
    })
}
fn domain(
    e: &Environment<'_>,
    p: &crate::law::model::Param,
    bindings: &[(String, Scalar)],
    reading: &str,
) -> Result<Option<super::super::finite::FiniteDomain>, ValidationFailure> {
    super::super::finite::values_if_finite_with_owned(
        &p.ty,
        e.indexes.inputs.law(),
        &e.control,
        &mut |entity| e.indexes.reference_roster(&e.control, entity, &mut |_| {}),
        &mut |entity, name| {
            let value = bindings
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| v)
                .ok_or("relation parameterの元owner束縛がない")?;
            let owned = e.owned_members(entity, value, None, reading, &mut |_, _| {})?;
            Ok(super::super::finite::FiniteDomain {
                enumeration: owned.enumeration,
                missing: owned.missing,
            })
        },
        &mut |_| {},
    )
}
pub(in crate::observed) fn relation_instances(
    inputs: &CheckedInputs,
    reading: &str,
    c: &mut Control,
) -> Result<RelationInstances, RelationInstancesFailure> {
    instances(inputs, reading, c, false)
}
// 通常の有限relation照会を変えず、宣言移送だけで厳密な数値族を使う。
pub(in crate::observed) fn relation_transport_instances(
    inputs: &CheckedInputs,
    reading: &str,
    c: &mut Control,
) -> Result<RelationInstances, RelationInstancesFailure> {
    instances(inputs, reading, c, true)
}
fn instances(
    inputs: &CheckedInputs,
    reading: &str,
    c: &mut Control,
    numeric_families: bool,
) -> Result<RelationInstances, RelationInstancesFailure> {
    let mut out = RelationInstances {
        sources: inputs.sources().clone(),
        reading: reading.into(),
        declarations: vec![],
        instances: vec![],
        outside_finite: vec![],
        pending_domains: vec![],
        support: vec![],
        scope: Scope::default(),
        enumeration_complete: false,
        numeric_families,
    };
    let result = (|| -> Result<(), ValidationFailure> {
        tick(c)?;
        let mut exists = false;
        for info in inputs.law().infos() {
            tick(c)?;
            exists |= info.kind == "reading" && info.name == reading;
        }
        if !exists {
            return Err("relationの元readingがない".into());
        }
        out.scope.readings.insert(reading.into());
        let e = Environment::new(inputs, c)?;
        for d in inputs.law().declarations().values() {
            tick(c)?;
            if d.reading != reading || !matches!(d.signature, Signature::Relation { .. }) {
                continue;
            }
            out.declarations.push(d.clone());
        }
        for d in &out.declarations {
            let Signature::Relation { params, .. } = &d.signature else {
                return Err("relation族に別種の宣言がある".into());
            };
            // 他parameterの無限性で、独立した空型の0件を失わない。
            let mut empty = false;
            for p in params {
                tick(c)?;
                if p.ty == p.ty.erase() {
                    if let Some(domain) = e.dynamic_finite_values(&p.ty, &mut |_, _| {})? {
                        if domain.values.is_empty() {
                            out.support.extend(domain.support);
                            out.scope.merge(&domain.scope);
                            empty = true;
                            break;
                        }
                    }
                }
            }
            if empty {
                continue;
            }
            let mut bindings = vec![vec![]];
            for p in params {
                if numeric_families && numeric_parameters::numeric_width(&p.ty).is_some() {
                    continue;
                }
                let mut next = vec![];
                for prefix in bindings {
                    tick(c)?;
                    let Some(domain) = domain(&e, p, &prefix, &d.reading)? else {
                        let outside = OutsideFiniteRelation {
                            declaration: d.name.clone(),
                            parameter: p.name.clone(),
                            ty: p.ty.clone(),
                        };
                        if !out.outside_finite.contains(&outside) {
                            out.outside_finite.push(outside);
                        }
                        continue;
                    };
                    out.support.extend(domain.enumeration.support);
                    out.scope.merge(&domain.enumeration.scope);
                    if !domain.missing.is_empty() {
                        out.pending_domains.push(PendingRelationDomain {
                            declaration: d.name.clone(),
                            parameter: p.name.clone(),
                            bindings: prefix,
                            missing: domain.missing,
                        });
                        continue;
                    }
                    for value in domain.enumeration.values {
                        tick(c)?;
                        let mut row = prefix.clone();
                        row.push((p.name.clone(), value));
                        next.push(row);
                    }
                }
                bindings = next;
            }
            for bindings in bindings {
                tick(c)?;
                let r = row(&e, d, bindings, numeric_families, None)?;
                out.support.extend(r.support.iter().cloned());
                out.scope.merge(&r.scope);
                out.instances.push(r);
                tick(c)?;
            }
        }
        out.support.sort();
        out.support.dedup();
        out.enumeration_complete = out.outside_finite.is_empty() && out.pending_domains.is_empty();
        tick(c)?;
        Ok(())
    })();
    match result {
        Ok(()) => Ok(out),
        Err(cause) => {
            out.enumeration_complete = false;
            Err(RelationInstancesFailure {
                cause,
                partial: Box::new(out),
            })
        }
    }
}
#[cfg(test)]
mod tests;

pub(in crate::observed) mod congruence;

mod source_frames;
