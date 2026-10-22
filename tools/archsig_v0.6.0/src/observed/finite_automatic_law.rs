//! 元parameter族の依存とbodyの依存を閉じ、共有Law列を自動構成する。
use super::*;

pub(in crate::observed) struct FiniteAutomaticLawFamily {
    parameters: FiniteParameterRealizations,
    family: Option<FiniteLawFamilyValuations>,
}
pub(in crate::observed) struct AutomaticLawFailure {
    pub cause: ValidationFailure,
    pub partial: Option<Box<FiniteAutomaticLawFamily>>,
}
impl std::fmt::Debug for AutomaticLawFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AutomaticLawFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
impl FiniteAutomaticLawFamily {
    pub(in crate::observed) fn parameters(&self) -> &FiniteParameterRealizations {
        &self.parameters
    }
    pub(in crate::observed) fn family(&self) -> Option<&FiniteLawFamilyValuations> {
        self.family.as_ref()
    }
    pub(in crate::observed) fn into_family(self) -> Option<FiniteLawFamilyValuations> {
        self.family
    }
    pub(in crate::observed) fn is_complete(&self) -> bool {
        self.parameters.is_complete()
            && self
                .family
                .as_ref()
                .is_some_and(FiniteLawFamilyValuations::is_complete)
    }
    pub(in crate::observed) fn recheck(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &mut Control,
    ) -> Result<(), AutomaticLawFailure> {
        let fail = |cause| AutomaticLawFailure {
            cause,
            partial: None,
        };
        if !self.parameters.law_dependencies {
            return Err(fail("自動Law族がparameter/bodyの共通依存を持たない".into()));
        }
        self.parameters
            .recheck(inputs, readings, c)
            .map_err(|e| fail(e.cause))?;
        if self.family.is_some() != self.parameters.is_complete() {
            return Err(fail(
                "自動Law族のparameter完成状態と評価族が対応しない".into(),
            ));
        }
        if let Some(family) = &self.family {
            if family.automatic_readings.as_deref() != Some(readings) {
                return Err(fail("自動Law族が消費先readingsに由来しない".into()));
            }
            family.recheck(inputs, c).map_err(|e| fail(e.cause))?;
        }
        Ok(())
    }
}
/// 候補を原始制約で枝刈りする前に、全typed parameter行の元bodyを同じ核で読む。
pub(super) fn discover_law_reads(
    inputs: &CheckedInputs,
    selections: &[Selection],
    objects: &[ObjectLawInstances],
    e: &mut Environment<'_>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    if selections.len() != objects.len() {
        return Err("自動Law依存の対象列が違う".into());
    }
    let mut failure = None;
    for (selection, object) in selections.iter().zip(objects) {
        tick(c)?;
        if e.object.as_deref() != Some(selection.domain.as_ref()) {
            e.scoped_values.borrow_mut().clear();
        }
        e.object = Some(Arc::clone(&selection.domain));
        for entry in object.entries() {
            let declaration = inputs
                .law()
                .declarations
                .get(&entry.source.declaration().name)
                .ok_or("元Lawの宣言がない")?;
            for row in &entry.rows {
                tick(c)?;
                match super::super::super::instance::probe_instance(
                    e,
                    selection,
                    &entry.source,
                    declaration,
                    &row.bindings,
                    0,
                ) {
                    Ok(_) => {}
                    Err(ValidationFailure::Stop(stop)) => return Err(stop.into()),
                    // 現在のbodyの非対応理由は後段の実評価へそのまま残す。
                    Err(ValidationFailure::UnsupportedExpression { .. }) => {}
                    Err(cause) if failure.is_none() => failure = Some(cause),
                    Err(_) => {}
                }
            }
        }
    }
    if let Some(cause) = failure {
        return Err(cause);
    }
    Ok(())
}
fn same_bindings(
    a: &[(String, Scalar)],
    b: &[(String, Scalar)],
    c: &mut Control,
) -> Result<bool, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for ((name, a), (other, b)) in a.iter().zip(b) {
        tick(c)?;
        if name != other || !validation_identity::scalar(a, b, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn selected_columns(
    parameters: &FiniteParameterRealizations,
    c: &mut Control,
) -> Result<Vec<(usize, usize, Vec<(String, Scalar)>)>, ValidationFailure> {
    let mut carriers = vec![];
    for (instance, original) in parameters.readings.instances().iter().enumerate() {
        tick(c)?;
        if original.declaration().kind != "law" {
            continue;
        }
        let mut bindings: Vec<Vec<(String, Scalar)>> = vec![];
        for point in &parameters.rows {
            for object in &point.objects {
                let entry = object
                    .entries()
                    .iter()
                    .find(|e| e.instance == instance)
                    .ok_or("自動Law族の元instanceがない")?;
                for row in &entry.rows {
                    tick(c)?;
                    let mut duplicate = false;
                    for previous in &bindings {
                        duplicate |= same_bindings(previous, &row.bindings, c)?;
                    }
                    if !duplicate {
                        bindings.push(row.bindings.clone());
                    }
                }
            }
        }
        for binding in bindings {
            carriers.push((instance, binding));
        }
    }
    let mut selected = vec![];
    for object in 0..parameters.readings.objects().len() {
        for (instance, bindings) in &carriers {
            tick(c)?;
            selected.push((object, *instance, bindings.clone()));
        }
    }
    Ok(selected)
}
pub(in crate::observed) fn finite_automatic_law_family(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    c: &mut Control,
) -> Result<FiniteAutomaticLawFamily, AutomaticLawFailure> {
    let parameters = match compute(inputs, readings, true, c) {
        Ok(p) => p,
        Err(error) => {
            return Err(AutomaticLawFailure {
                cause: error.cause,
                partial: error.partial.map(|p| {
                    Box::new(FiniteAutomaticLawFamily {
                        parameters: *p,
                        family: None,
                    })
                }),
            });
        }
    };
    let mut result = FiniteAutomaticLawFamily {
        parameters,
        family: None,
    };
    if !result.parameters.is_complete() {
        return Ok(result);
    }
    let built = (|| -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
        c.checkpoint(Checkpoint::FiniteLawAutomatic)
            .map_err(|cause| FiniteLawFamilyFailure {
                cause: cause.into(),
                partial: None,
            })?;
        let selected =
            selected_columns(&result.parameters, c).map_err(|cause| FiniteLawFamilyFailure {
                cause,
                partial: None,
            })?;
        let mut laws = vec![];
        let mut instances = vec![];
        for (object, instance, bindings) in selected {
            let original =
                readings
                    .instances()
                    .get(instance)
                    .ok_or_else(|| FiniteLawFamilyFailure {
                        cause: "自動Law列の元instanceがない".into(),
                        partial: None,
                    })?;
            laws.push((object, original.declaration().name.clone(), bindings));
            instances.push(instance);
        }
        let (objects, laws) = multi_selection(inputs, readings, &laws, c)?;
        family_with_instance_domain(
            inputs,
            &laws,
            None,
            Some(objects),
            Some(instances),
            &result.parameters.positions,
            Some(Arc::new(readings.clone())),
            c,
        )
    })();
    match built {
        Ok(family) => {
            if family.domain_complete()
                && (family.positions() != result.parameters.positions
                    || family.types() != result.parameters.types
                    || family.domain() != result.parameters.domain
                    || family.observed_point() != result.parameters.observed_point)
            {
                result.family = Some(family);
                return Err(AutomaticLawFailure {
                    cause: "自動Law列とparameter/body共通域が違う".into(),
                    partial: Some(Box::new(result)),
                });
            }
            result.family = Some(family);
            Ok(result)
        }
        Err(error) => {
            result.family = error.partial.map(|p| *p);
            Err(AutomaticLawFailure {
                cause: error.cause,
                partial: Some(Box::new(result)),
            })
        }
    }
}
#[cfg(test)]
#[path = "finite_automatic_law_tests.rs"]
mod tests;
