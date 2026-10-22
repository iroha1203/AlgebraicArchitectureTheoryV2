//! 元instanceの適用条件と型条件を、共有D上の条件付き指示関数へ接続する。
use super::*;
use crate::construction::readings::{InstanceApplication, ObjectInstance};
fn select_tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone().checkpoint(Checkpoint::FiniteLawSelection)?;
    Ok(())
}

pub(in super::super) fn validate_selection(
    inputs: &CheckedInputs,
    objects: &Columns,
    column: usize,
    instance: usize,
    law: &str,
    bindings: &[(String, Scalar)],
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    select_tick(c)?;
    let object = objects
        .columns
        .get(column)
        .ok_or("元instanceの列対象がない")?;
    let original = objects
        .readings
        .instances()
        .get(instance)
        .ok_or("元Law instanceが範囲外")?;
    if original.declaration().kind != "law"
        || original.declaration().name != law
        || original.applications().get(object.object).is_none()
    {
        return Err("選択した列が元Law instance・対象の組でない".into());
    }
    let e = Environment::new(inputs, c)?;
    for fixed in original.bindings() {
        select_tick(c)?;
        let fact = fixed.subject();
        let subject = e.subject(&fact.snapshot, &fact.subject)?;
        let expected = Scalar::Subject {
            snapshot: fact.snapshot.clone(),
            subject: fact.subject.clone(),
            entity: subject.ty.clone(),
        };
        if bindings
            .iter()
            .find(|(name, _)| name == &fixed.parameter().name)
            .is_none_or(|(_, value)| value != &expected)
        {
            return Err("元Law instanceの参照束縛を差し替えた".into());
        }
    }
    Ok(())
}
/// ここで作る零は条件付き指示関数。未評価の左右値や原差を零へ書き替えない。
pub(in super::super) fn zero_indicator(
    e: &Environment<'_>,
    decl: &Declaration,
    row: &mut FiniteLawRow,
) -> Result<(), ValidationFailure> {
    let Signature::Law { body, .. } = decl.signature else {
        return Err("元Lawでない".into());
    };
    row.indicator = Some(0.into());
    if let Some(eq) = equation(e.inputs, body, &mut e.control.clone())? {
        let ExprKind::Binary { lhs, .. } = e.inputs.law().exprs[eq].kind else {
            return Err("元等式がない".into());
        };
        let ty = e.inputs.law().expr_type(lhs).ok_or("元等式の型がない")?;
        let mut leaves = components(e, ty, &None, &None, Some(false), false)?;
        for leaf in &mut leaves {
            tick(&e.control)?;
            // 条件不成立の指示関数だけを零と確定する。原値・等値性は未評価のまま。
            leaf.indicator = Some(0.into());
        }
        row.components = Some(leaves);
    }
    row.support.sort();
    row.support.dedup();
    row.application_missing.sort();
    row.application_missing.dedup();
    Ok(())
}
fn initial(
    e: &Environment<'_>,
    object: &Selection,
    original: &ObjectInstance,
    point: usize,
) -> Result<FiniteLawRow, ValidationFailure> {
    let mut row = FiniteLawRow {
        point,
        application: Some(true),
        application_missing: vec![],
        guard: None,
        predicate: None,
        operands: None,
        components: None,
        indicator: None,
        condition_failed: false,
        support: vec![],
        scope: Scope::default(),
    };
    for fact in std::iter::once(object.identity().root())
        .chain(std::iter::once(object.identity().subject()))
        .chain(original.bindings().iter().map(|binding| binding.subject()))
    {
        tick(&e.control)?;
        let subject = e.subject(&fact.snapshot, &fact.subject)?;
        row.scope
            .merge(&e.scope(subject, object.identity().reading(), None)?);
        row.support.push(fact.clone());
    }
    match original
        .applications()
        .get(object.object)
        .ok_or("元instanceの適用先がない")?
    {
        InstanceApplication::NotApplicable => row.application = Some(false),
        InstanceApplication::Applicable { conditions } => {
            let mut false_condition = false;
            let mut unknown = false;
            for condition in conditions {
                tick(&e.control)?;
                let position = condition.slot();
                let field = e.field(
                    &position.snapshot,
                    &position.subject,
                    position.field.as_deref().ok_or("元所属条件のfieldがない")?,
                )?;
                let subject = e.subject(&position.snapshot, &position.subject)?;
                let value = if let Some(value) = e
                    .primitive_valuation
                    .as_ref()
                    .and_then(|values| values.get(position))
                {
                    row.scope.assignments = true;
                    row.support.push(position.clone());
                    Some(value.clone())
                } else {
                    match &field.slot {
                        Slot::Known {
                            value,
                            atom,
                            origin,
                            ..
                        } => {
                            row.scope.merge(&e.scope(
                                subject,
                                object.identity().reading(),
                                Some(origin),
                            )?);
                            let mut fact = position.clone();
                            fact.atom = Some(atom.clone());
                            row.support.push(fact);
                            scalar_from(value, &field.ty, e.inputs.law(), &e.control)?
                        }
                        Slot::Missing => {
                            row.scope.completions = true;
                            row.application_missing.push(position.clone());
                            None
                        }
                    }
                };
                match &value {
                    Some(Scalar::Subject {
                        snapshot, subject, ..
                    }) => {
                        let expected = condition.owner();
                        false_condition |=
                            snapshot != &expected.snapshot || subject != &expected.subject;
                    }
                    Some(_) => return Err("元所属条件のownerがRefでない".into()),
                    None => unknown = true,
                }
            }
            row.application = if false_condition {
                Some(false)
            } else if unknown {
                None
            } else {
                Some(true)
            };
        }
    }
    row.support.sort();
    row.support.dedup();
    row.application_missing.sort();
    row.application_missing.dedup();
    Ok(row)
}
impl FiniteLawFamilyValuations {
    pub(in super::super) fn probe_column(
        &self,
        e: &Environment<'_>,
        column: usize,
        point: usize,
    ) -> Result<Probe, ValidationFailure> {
        let selected = self.columns.get(column).ok_or("元Lawの列がない")?;
        let Some(instance) = selected.source_instance else {
            return probe(e, &selected.declaration, &selected.bindings, point);
        };
        let object = self
            .column_objects
            .as_ref()
            .and_then(|objects| objects.columns.get(column))
            .ok_or("元Law列の対象がない")?;
        let original = object
            .readings
            .instances()
            .get(instance)
            .ok_or("元Law instanceがない")?;
        let mut row = initial(e, object, original, point)?;
        if row.application == Some(true) {
            let mut evaluated =
                probe_mode(e, &selected.declaration, &selected.bindings, point, true)?;
            evaluated.row.scope.merge(&row.scope);
            evaluated.row.support.extend(row.support);
            evaluated
                .row
                .application_missing
                .extend(row.application_missing);
            row = evaluated.row;
        }
        if row.application == Some(false) {
            zero_indicator(e, &selected.declaration, &mut row)?;
        }
        row.support.sort();
        row.support.dedup();
        row.application_missing.sort();
        row.application_missing.dedup();
        // 型条件はこの列の適用条件。別の列と共通のDから代入を削除しない。
        Ok(Probe {
            row,
            admissible: true,
            blocked: false,
        })
    }
    pub(in crate::observed) fn instance_source(
        &self,
        column: usize,
    ) -> Option<(&ObjectInstance, &InstanceApplication)> {
        let instance = self.columns.get(column)?.source_instance?;
        let object = self.column_objects.as_ref()?.columns.get(column)?;
        let original = object.readings.instances().get(instance)?;
        Some((original, original.applications().get(object.object)?))
    }
    pub(in crate::observed) fn recheck_on_instances(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        selected: &[(usize, usize)],
        c: &mut Control,
    ) -> Result<(), FiniteLawFamilyFailure> {
        if !self.instance_mode
            || self.columns.len() != selected.len()
            || self
                .columns
                .iter()
                .zip(selected)
                .any(|(column, (_, instance))| column.source_instance != Some(*instance))
        {
            return Err(FiniteLawFamilyFailure {
                cause: "元Law族が消費先instanceに由来しない".into(),
                partial: None,
            });
        }
        self.recheck_on_objects(
            inputs,
            readings,
            &selected
                .iter()
                .map(|(object, _)| *object)
                .collect::<Vec<_>>(),
            c,
        )
    }
}
/// 元instanceの参照束縛を固定し、完全束縛の型条件と適用条件を共有Dで評価する。
pub(in crate::observed) fn finite_instance_law_family_valuations(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    selected: &[(usize, usize, Vec<(String, Scalar)>)],
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    readings
        .recheck(inputs, c)
        .map_err(|cause| FiniteLawFamilyFailure {
            cause: failure(cause),
            partial: None,
        })?;
    let mut indices = vec![];
    let mut planned = vec![];
    for (object, instance, bindings) in selected {
        select_tick(c).map_err(|cause| FiniteLawFamilyFailure {
            cause,
            partial: None,
        })?;
        let original =
            readings
                .instances()
                .get(*instance)
                .ok_or_else(|| FiniteLawFamilyFailure {
                    cause: "元Law instanceの選択が範囲外".into(),
                    partial: None,
                })?;
        planned.push((
            *object,
            original.declaration().name.clone(),
            bindings.clone(),
        ));
        indices.push(*instance);
    }
    let (objects, laws) = multi_selection(inputs, readings, &planned, c)?;
    family_with_instances(inputs, &laws, None, Some(objects), Some(indices), c)
}
#[cfg(test)]
#[path = "finite_instance_law_tests.rs"]
mod tests;
