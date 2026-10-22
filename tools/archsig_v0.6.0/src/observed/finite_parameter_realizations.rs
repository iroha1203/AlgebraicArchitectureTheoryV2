//! 同じ原始代入ごとに、全対象の元Law parameter域を読む。
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum ParameterRealizationState {
    Pending,
    Ready,
    Incomplete,
    OutsideFinite { position: Fact, ty: Type },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct ParameterRealization {
    pub point: usize,
    /// 元readingsのobjects順。各行は元instanceと実parameter直積を保持する。
    pub objects: Vec<ObjectLawInstances>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct FiniteParameterRealizations {
    sources: InputSources,
    readings: ObjectReadingInstances,
    law_dependencies: bool,
    pub positions: Vec<Fact>,
    pub types: Vec<Type>,
    pub domain: Vec<Vec<Scalar>>,
    pub domain_complete: bool,
    pub observed_point: Option<usize>,
    pub rows: Vec<ParameterRealization>,
    pub state: ParameterRealizationState,
}
pub(in crate::observed) struct ParameterRealizationFailure {
    pub cause: ValidationFailure,
    pub partial: Option<Box<FiniteParameterRealizations>>,
}
impl std::fmt::Debug for ParameterRealizationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ParameterRealizationFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
impl FiniteParameterRealizations {
    pub(in crate::observed) fn is_complete(&self) -> bool {
        self.domain_complete && self.state == ParameterRealizationState::Ready
    }
    pub(in crate::observed) fn readings(&self) -> &ObjectReadingInstances {
        &self.readings
    }
    pub(in crate::observed) fn recheck(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        c: &mut Control,
    ) -> Result<(), ParameterRealizationFailure> {
        if inputs.sources() != &self.sources || readings != &self.readings {
            return Err(ParameterRealizationFailure {
                cause: "parameter代入族の元三入力またはreadingsが違う".into(),
                partial: None,
            });
        }
        let expected = compute(inputs, readings, self.law_dependencies, c)?;
        if self != &expected {
            return Err(ParameterRealizationFailure {
                cause: "parameter代入族が元対象・instance・型域・直積と違う".into(),
                partial: None,
            });
        }
        Ok(())
    }
}
fn evaluated_objects(
    inputs: &CheckedInputs,
    selections: &[Selection],
    values: &[(Fact, Scalar)],
    e: &Environment<'_>,
    c: &mut Control,
) -> Result<Vec<ObjectLawInstances>, ValidationFailure> {
    let mut objects = vec![];
    for selection in selections {
        tick(c)?;
        let mut object = ObjectLawInstances {
            sources: inputs.sources().clone(),
            selection: selection.clone(),
            valuation: Some(values.to_vec()),
            entries: vec![],
            complete: false,
        };
        populate_with_environment(inputs, &mut object, c, e)?;
        objects.push(object);
    }
    Ok(objects)
}
fn populate_realizations(
    inputs: &CheckedInputs,
    result: &mut FiniteParameterRealizations,
    selections: &[Selection],
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let template = Environment::new(inputs, c)?;
    let mut positions: BTreeSet<Fact> = BTreeSet::new();
    loop {
        tick(c)?;
        loop {
            let mut expanded = positions.clone();
            for p in &positions {
                let field = template.field(
                    &p.snapshot,
                    &p.subject,
                    p.field.as_deref().ok_or("parameter依存位置のfieldがない")?,
                )?;
                type_dependencies(&template, p, &field.ty, &mut expanded)?;
            }
            if expanded == positions {
                break;
            }
            positions = expanded;
        }
        result.positions = positions.iter().cloned().collect();
        let Some((types, candidates)) = domains(&template, &result.positions)? else {
            for p in &result.positions {
                if domains(&template, std::slice::from_ref(p))?.is_none() {
                    let field = template.field(
                        &p.snapshot,
                        &p.subject,
                        p.field.as_deref().ok_or("parameter依存fieldがない")?,
                    )?;
                    result.state = ParameterRealizationState::OutsideFinite {
                        position: p.clone(),
                        ty: field.ty.clone(),
                    };
                    return Ok(());
                }
            }
            return Err("parameter代入族の非有限位置が特定できない".into());
        };
        let mut discovered = positions.clone();
        let mut admissible = vec![];
        let mut failure = None;
        for candidate in candidates {
            c.checkpoint(Checkpoint::FiniteIteration)?;
            let values: Vec<_> = result
                .positions
                .iter()
                .cloned()
                .zip(candidate.iter().cloned())
                .collect();
            let mut e = Environment::primitive_dependency_probe(inputs, &values, c)?;
            *e.primitive_reads.borrow_mut() = Some(BTreeSet::new());
            let mut evaluated = evaluated_objects(inputs, selections, &values, &e, c);
            if result.law_dependencies {
                if let Ok(objects) = &evaluated {
                    if let Err(cause) =
                        automatic::discover_law_reads(inputs, selections, objects, &mut e, c)
                    {
                        evaluated = Err(cause);
                    }
                }
            }
            if let Some(reads) = e.primitive_reads.borrow().as_ref() {
                discovered.extend(reads.iter().cloned());
            }
            if let Err(ValidationFailure::Stop(stop)) = evaluated {
                return Err(stop.into());
            }
            // 依存発見passの未固定値で、候補やparameter行を枝刈りしない。
            if Environment::try_primitive_valuation(inputs, &values, c)?.is_some() {
                match evaluated {
                    Ok(_) => admissible.push(candidate),
                    Err(cause) if failure.is_none() => failure = Some(cause),
                    Err(_) => {}
                }
            }
        }
        if discovered != positions {
            positions = discovered;
            continue;
        }
        if let Some(cause) = failure {
            return Err(cause);
        }
        result.types = types;
        result.domain = admissible;
        result.domain_complete = true;
        break;
    }
    let mut observed = vec![];
    let mut all_known = true;
    for p in &result.positions {
        tick(c)?;
        let field = template.field(
            &p.snapshot,
            &p.subject,
            p.field.as_deref().ok_or("元parameter依存fieldがない")?,
        )?;
        match &field.slot {
            Slot::Known { value, .. } => observed.push(
                scalar_from(value, &field.ty, inputs.law(), c)?
                    .ok_or("元parameter依存値が読めない")?,
            ),
            Slot::Missing => all_known = false,
        }
    }
    if all_known {
        for (point, values) in result.domain.iter().enumerate() {
            tick(c)?;
            let mut equal = values.len() == observed.len();
            for (a, b) in values.iter().zip(&observed) {
                equal &= data::equal(a, b, c)?;
            }
            if equal && result.observed_point.replace(point).is_some() {
                return Err("parameter代入族の元観測点が重複".into());
            }
        }
    }
    for (point, candidate) in result.domain.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
        let values: Vec<_> = result
            .positions
            .iter()
            .cloned()
            .zip(candidate.iter().cloned())
            .collect();
        let e = Environment::with_primitive_valuation(inputs, &values, c)?;
        let objects = evaluated_objects(inputs, selections, &values, &e, c)?;
        result.rows.push(ParameterRealization { point, objects });
        c.checkpoint(Checkpoint::FiniteLawRequired)?;
    }
    tick(c)?;
    result.state = if result
        .rows
        .iter()
        .all(|row| row.objects.iter().all(ObjectLawInstances::is_complete))
    {
        ParameterRealizationState::Ready
    } else {
        ParameterRealizationState::Incomplete
    };
    Ok(())
}
pub(in crate::observed) fn finite_parameter_realizations(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    c: &mut Control,
) -> Result<FiniteParameterRealizations, ParameterRealizationFailure> {
    compute(inputs, readings, false, c)
}
fn compute(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    law_dependencies: bool,
    c: &mut Control,
) -> Result<FiniteParameterRealizations, ParameterRealizationFailure> {
    let fail = |cause| ParameterRealizationFailure {
        cause,
        partial: None,
    };
    readings
        .recheck(inputs, c)
        .map_err(|cause| fail(super::super::failure(cause)))?;
    let mut selections = vec![];
    for object in 0..readings.objects().len() {
        selections.push(Selection::compute(inputs, readings, object, c).map_err(fail)?);
    }
    let mut result = FiniteParameterRealizations {
        sources: inputs.sources().clone(),
        readings: readings.clone(),
        law_dependencies,
        positions: vec![],
        types: vec![],
        domain: vec![],
        domain_complete: false,
        observed_point: None,
        rows: vec![],
        state: ParameterRealizationState::Pending,
    };
    if let Err(cause) = populate_realizations(inputs, &mut result, &selections, c) {
        return Err(ParameterRealizationFailure {
            cause,
            partial: Some(Box::new(result)),
        });
    }
    Ok(result)
}
#[cfg(test)]
#[path = "finite_parameter_realizations_tests.rs"]
mod tests;

#[path = "finite_automatic_law.rs"]
pub(in crate::observed) mod automatic;
