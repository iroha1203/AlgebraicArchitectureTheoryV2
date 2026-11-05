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

pub(in crate::observed) struct FiniteAutomaticLawFamily<S = DetailedParameters> {
    parameters: FiniteParameterRealizations<S>,
    family: Option<AutomaticLawValuations>,
}
pub(in crate::observed) struct AutomaticLawFailure<S = DetailedParameters> {
    pub cause: ValidationFailure,
    pub partial: Option<Box<FiniteAutomaticLawFamily<S>>>,
}
impl<S> std::fmt::Debug for AutomaticLawFailure<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AutomaticLawFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
impl<S: ParameterSink> FiniteAutomaticLawFamily<S> {
    pub(in crate::observed) fn parameters(&self) -> &FiniteParameterRealizations<S> {
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
        c: &Control,
    ) -> Result<(), AutomaticLawFailure<S>> {
        let fail = |cause| AutomaticLawFailure {
            cause,
            partial: None,
        };
        if !self.parameters.law_dependencies {
            return Err(fail(
                internal!("自動Law族がparameter/bodyの共通依存を持たない").into(),
            ));
        }
        self.parameters
            .recheck(inputs, readings, c)
            .map_err(|e| fail(e.cause))?;
        if self.family.is_some() != self.parameters.is_complete() {
            return Err(fail(
                internal!("自動Law族のparameter完成状態と評価族が対応しない").into(),
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
    selections: &[Arc<Selection>],
    objects: &[ObjectLawInstances],
    e: &mut Environment<'_>,
    c: &Control,
) -> Result<(), ValidationFailure> {
    if selections.len() != objects.len() {
        return Err(internal!("自動Law依存の対象列が違う").into());
    }
    let mut failure = None;
    for (selection, object) in selections.iter().zip(objects) {
        tick(c)?;
        if e.indexes.object.as_deref() != Some(selection.domain.as_ref()) {
            e.results.scoped_values.borrow_mut().clear();
        }
        e.indexes.object = Some(Arc::clone(&selection.domain));
        for entry in object.entries() {
            let declaration = inputs
                .law()
                .declarations()
                .get(&entry.source.declaration().name)
                .ok_or(internal!("元Lawの宣言がない"))?;
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
fn selected_columns<S: ParameterSink>(
    parameters: &FiniteParameterRealizations<S>,
    c: &Control,
) -> Result<Vec<(usize, usize, Vec<(String, Scalar)>)>, ValidationFailure> {
    parameters.storage.columns(parameters.readings(), c)
}
pub(in crate::observed) fn finite_automatic_law_family(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    c: &Control,
) -> Result<FiniteAutomaticLawFamily, AutomaticLawFailure> {
    automatic_with_sink::<DetailedParameters>(inputs, readings, c)
}
pub(in crate::observed) fn finite_automatic_law_family_compact(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    c: &Control,
) -> Result<FiniteAutomaticLawFamily<ParameterCarriers>, AutomaticLawFailure<ParameterCarriers>> {
    automatic_with_sink::<ParameterCarriers>(inputs, readings, c)
}
fn automatic_with_sink<S: ParameterSink>(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    c: &Control,
) -> Result<FiniteAutomaticLawFamily<S>, AutomaticLawFailure<S>> {
    let parameters = match compute_sink::<S>(inputs, readings, true, c) {
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
                        cause: internal!("自動Law列の元instanceがない").into(),
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
                    cause: internal!("自動Law列とparameter/body共通域が違う").into(),
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
        c: &Control,
    ) -> Result<(Option<BigInt>, Vec<Fact>), ValidationFailure> {
        tick(c)?;
        if &self.value.sources != inputs.sources() {
            return Err(internal!("有限Lawの実評価と元三入力が違う").into());
        }
        let mut e = Environment::new(inputs, c)?;
        *e.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
        self.value.select_column_object(&mut e, column)?;
        let reads = || -> Result<Vec<Fact>, ValidationFailure> {
            let tracked = e.state.primitive_reads.borrow();
            let mut positions = vec![];
            for position in tracked
                .as_ref()
                .ok_or(internal!("有限Law実評価の読取り記録がない"))?
            {
                tick(&e.control)?;
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
            .ok_or(internal!("有限Lawの実評価列がない"))?;
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
        c: &Control,
    ) -> Result<FiniteIntegerRing<'_>, ValidationFailure> {
        self.value.integer_ring(c)
    }
    pub(in crate::observed) fn integer_function(
        &self,
        column: usize,
        component: Option<&[usize]>,
        c: &Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        self.value.integer_function(column, component, c)
    }
    pub(in crate::observed) fn required_generators(
        &self,
        c: &Control,
    ) -> Result<Vec<FiniteLawGenerator>, ValidationFailure> {
        self.value.required_generators(c)
    }
    pub(in crate::observed) fn required_quotient(
        &self,
        c: &Control,
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
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        if &self.readings != readings {
            return Err(internal!("自動Law族が消費先の元readingsに由来しない").into());
        }
        let expected = finite_automatic_law_family(inputs, readings, c)
            .map_err(|failure| failure.cause)?
            .into_family()
            .ok_or(internal!("自動Law族の元parameter域が未完成"))?;
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
        c: &Control,
    ) -> Result<FiniteIntegerRing<'_>, ValidationFailure> {
        self.value.integer_ring(c)
    }
    pub(in crate::observed) fn project(
        &self,
        f: &FiniteIntegerFunction,
        c: &Control,
    ) -> Result<FiniteIntegerFunction, ValidationFailure> {
        self.value.project(f, c)
    }
    pub(in crate::observed) fn recheck(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        if !self.value.belongs_to(&self.family.value) {
            return Err(internal!("required商がこの自動Law族に由来しない").into());
        }
        self.family.recheck(inputs, readings, c)?;
        self.value.recheck_projection(c)
    }
    pub(in crate::observed) fn ideal_membership(
        &self,
        f: &FiniteIntegerFunction,
        c: &Control,
    ) -> Result<FiniteIdealMembership, ValidationFailure> {
        self.value.ideal_membership(f, c)
    }
    pub(in crate::observed) fn recheck_membership(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        f: &FiniteIntegerFunction,
        membership: &FiniteIdealMembership,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        self.recheck(inputs, readings, c)?;
        self.value.recheck_membership_value(f, membership, c)
    }
}

#[cfg(test)]
mod tests;

pub(in crate::observed) mod object_evaluation;

pub(in crate::observed) mod presentation;

pub(in crate::observed) mod observation;

mod reading;
pub(in crate::observed) use reading::ObservedLawReading;
