//! 元parameter族の依存とbodyの依存を閉じ、共有Law列を自動構成する。
use super::*;
use crate::construction::{
    maps::ObjectIdentity,
    readings::{InstanceApplication, ObjectInstance},
};
use crate::observed::{
    environment::finite_law_valuations::quotient::{
        FiniteIdealMembership, FiniteLawGenerator, FiniteLawQuotient,
    },
    finite_integer_function::{FiniteIntegerFunction, FiniteIntegerRing},
};

pub(in crate::observed) struct FiniteAutomaticLawFamily {
    parameters: FiniteParameterRealizations,
    family: Option<AutomaticLawValuations>,
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
    pub(in crate::observed) fn family(&self) -> Option<&AutomaticLawValuations> {
        self.family.as_ref()
    }
    pub(in crate::observed) fn into_family(self) -> Option<AutomaticLawValuations> {
        self.family
    }
    pub(in crate::observed) fn is_complete(&self) -> bool {
        self.parameters.is_complete()
            && self
                .family
                .as_ref()
                .is_some_and(AutomaticLawValuations::is_complete)
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
            family.recheck(inputs, readings, c).map_err(fail)?;
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
            c,
        )
    })();
    match built {
        Ok(value) => {
            let family = AutomaticLawValuations {
                readings: readings.clone(),
                value,
            };
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
            result.family = error.partial.map(|p| AutomaticLawValuations {
                readings: readings.clone(),
                value: *p,
            });
            Err(AutomaticLawFailure {
                cause: error.cause,
                partial: Some(Box::new(result)),
            })
        }
    }
}
/// 自動全列の消費では、この型と元readingsを保持する。明示選択族へは変換しない。
pub(in crate::observed) struct AutomaticLawValuations {
    readings: ObjectReadingInstances,
    value: FiniteLawFamilyValuations,
}
pub(in crate::observed) struct AutomaticLawQuotient<'a> {
    family: &'a AutomaticLawValuations,
    value: FiniteLawQuotient<'a>,
}
impl AutomaticLawValuations {
    pub(in crate::observed) fn columns(&self) -> &[FiniteLawColumn] {
        self.value.columns()
    }
    pub(in crate::observed) fn positions(&self) -> &[Fact] {
        self.value.positions()
    }
    pub(in crate::observed) fn types(&self) -> &[Type] {
        self.value.types()
    }
    pub(in crate::observed) fn domain(&self) -> &[Vec<Scalar>] {
        self.value.domain()
    }
    pub(in crate::observed) fn domain_complete(&self) -> bool {
        self.value.domain_complete()
    }
    pub(in crate::observed) fn observed_point(&self) -> Option<usize> {
        self.value.observed_point()
    }
    pub(in crate::observed) fn state(&self) -> &FiniteLawState {
        self.value.state()
    }
    pub(in crate::observed) fn is_complete(&self) -> bool {
        self.value.is_complete()
    }
    pub(in crate::observed) fn required_zero(&self) -> Option<&[usize]> {
        self.value.required_zero()
    }
    pub(in crate::observed) fn column_object_identity(
        &self,
        column: usize,
    ) -> Option<&ObjectIdentity> {
        self.value.column_object_identity(column)
    }
    pub(in crate::observed) fn instance_source(
        &self,
        column: usize,
    ) -> Option<(&ObjectInstance, &InstanceApplication)> {
        self.value.instance_source(column)
    }
    /// 補完代入を入れず、同じ元列のoperandとその読取りを現在の観測から得る。
    pub(in crate::observed) fn observed_indicator(
        &self,
        inputs: &CheckedInputs,
        column: usize,
        component: Option<&[usize]>,
        c: &mut Control,
    ) -> Result<(Option<BigInt>, Vec<Fact>), ValidationFailure> {
        tick(c)?;
        if &self.value.sources != inputs.sources() {
            return Err("有限Lawの実評価と元三入力が違う".into());
        }
        let mut e = Environment::new(inputs, c)?;
        *e.primitive_reads.borrow_mut() = Some(BTreeSet::new());
        self.value.select_column_object(&mut e, column)?;
        let reads = || -> Result<Vec<Fact>, ValidationFailure> {
            let tracked = e.primitive_reads.borrow();
            let mut positions = vec![];
            for position in tracked.as_ref().ok_or("有限Law実評価の読取り記録がない")?
            {
                tick(&mut e.control.clone())?;
                positions.push(position.clone());
            }
            Ok(positions)
        };
        let applied = self.value.probe_column(&e, column, 0)?;
        if applied.row.application != Some(true) || applied.row.condition_failed {
            return Ok((None, reads()?));
        }
        let selected = self
            .columns()
            .get(column)
            .ok_or("有限Lawの実評価列がない")?;
        // 条件付き指示値が零でも、元operandの欠測を恒値で置き換えない。
        let actual = probe(&e, selected.declaration(), selected.bindings(), 0)?.row;
        if actual.condition_failed || actual.guard.is_none() {
            return Ok((None, reads()?));
        }
        tick(c)?;
        let value = match component {
            Some(path) => {
                let mut value = None;
                for leaf in actual.components.as_deref().unwrap_or(&[]) {
                    tick(c)?;
                    if leaf.path == path && leaf.left.is_some() && leaf.right.is_some() {
                        value = leaf.indicator.clone();
                    }
                }
                value
            }
            None => actual.indicator,
        };
        Ok((value, reads()?))
    }
    pub(in crate::observed) fn integer_ring(
        &self,
        c: &mut Control,
    ) -> Result<FiniteIntegerRing<'_>, ValidationFailure> {
        self.value.integer_ring(c)
    }
    pub(in crate::observed) fn integer_function(
        &self,
        column: usize,
        component: Option<&[usize]>,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        self.value.integer_function(column, component, c)
    }
    pub(in crate::observed) fn required_generators(
        &self,
        c: &mut Control,
    ) -> Result<Vec<FiniteLawGenerator>, ValidationFailure> {
        self.value.required_generators(c)
    }
    pub(in crate::observed) fn required_quotient(
        &self,
        c: &mut Control,
    ) -> Result<AutomaticLawQuotient<'_>, ValidationFailure> {
        Ok(AutomaticLawQuotient {
            family: self,
            value: self.value.required_quotient(c)?,
        })
    }
    pub(in crate::observed) fn recheck(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        if &self.readings != readings {
            return Err("自動Law族が消費先の元readingsに由来しない".into());
        }
        let expected = finite_automatic_law_family(inputs, readings, c)
            .map_err(|failure| failure.cause)?
            .into_family()
            .ok_or("自動Law族の元parameter域が未完成")?;
        self.value
            .check_expected(expected.value, c)
            .map_err(|failure| failure.cause)
    }
}
impl AutomaticLawQuotient<'_> {
    pub(in crate::observed) fn points(&self) -> &[usize] {
        self.value.points()
    }
    pub(in crate::observed) fn integer_ring(
        &self,
        c: &mut Control,
    ) -> Result<FiniteIntegerRing<'_>, ValidationFailure> {
        self.value.integer_ring(c)
    }
    pub(in crate::observed) fn project(
        &self,
        f: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        self.value.project(f, c)
    }
    pub(in crate::observed) fn recheck(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        if !self.value.belongs_to(&self.family.value) {
            return Err("required商がこの自動Law族に由来しない".into());
        }
        self.family.recheck(inputs, readings, c)?;
        self.value.recheck_projection(c)
    }
    pub(in crate::observed) fn ideal_membership(
        &self,
        f: &FiniteIntegerFunction,
        c: &mut Control,
    ) -> Result<FiniteIdealMembership, ValidationFailure> {
        self.value.ideal_membership(f, c)
    }
    pub(in crate::observed) fn recheck_membership(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        f: &FiniteIntegerFunction,
        membership: &FiniteIdealMembership,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        self.recheck(inputs, readings, c)?;
        self.value.recheck_membership_value(f, membership, c)
    }
}

#[cfg(test)]
#[path = "finite_automatic_law_tests.rs"]
mod tests;

#[path = "finite_law_object_evaluation.rs"]
pub(in crate::observed) mod object_evaluation;

#[path = "finite_object_law_presentation.rs"]
pub(in crate::observed) mod presentation;

#[path = "finite_law_observation.rs"]
pub(in crate::observed) mod observation;

#[path = "finite_law_reading.rs"]
mod reading;
pub(in crate::observed) use reading::ObservedLawReading;
