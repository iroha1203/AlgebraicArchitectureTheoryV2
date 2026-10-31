//! 元Law instanceの参照束縛・適用条件と、残parameter全域の有限座標。
use super::*;
use crate::{
    construction::readings::{InstanceApplication, ObjectInstance},
    input::InputSources,
    law::{ast::QuantKind, model::Param},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum ParameterFamilyState {
    Pending,
    Ready,
    NotApplicable,
    Undetermined,
    OutsideFinite,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct ParameterDomain {
    pub parameter: Param,
    /// Noneは非有限域。Some([])は既知の空有限域。
    pub values: Option<Vec<Scalar>>,
    pub missing: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct BoundInstance {
    pub coordinates: Vec<usize>,
    pub bindings: Vec<(String, Scalar)>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct InstanceParameters {
    pub instance: usize,
    pub source: ObjectInstance,
    pub application: InstanceApplication,
    /// Noneは観測入口、Someはこの原始代入で検査した適用値。
    pub application_value: Option<Option<bool>>,
    pub domains: Vec<ParameterDomain>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub rows: Vec<BoundInstance>,
    pub state: ParameterFamilyState,
}
/// 元Law instanceの適用条件と残parameterの完全束縛族。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct ObjectLawInstances {
    sources: InputSources,
    selection: Selection,
    valuation: Option<Vec<(Fact, Scalar)>>,
    entries: Vec<InstanceParameters>,
    complete: bool,
}
pub(in crate::observed) struct InstanceFamilyFailure {
    pub cause: ValidationFailure,
    pub partial: Option<Box<ObjectLawInstances>>,
}
impl std::fmt::Debug for InstanceFamilyFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InstanceFamilyFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
impl ObjectLawInstances {
    pub(in crate::observed) fn object_identity(&self) -> &ObjectIdentity {
        self.selection.identity()
    }
    pub(in crate::observed) fn entries(&self) -> &[InstanceParameters] {
        &self.entries
    }
    /// 全適用instanceの完全束縛族が有限かつ確定している。
    pub(in crate::observed) fn is_complete(&self) -> bool {
        self.complete
    }
    pub(in crate::observed) fn recheck(
        &self,
        inputs: &CheckedInputs,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        if inputs.sources() != &self.sources {
            return Err("Law instance添字族の元三入力が違う".into());
        }
        self.selection.recheck(inputs, c)?;
        let mut expected = ObjectLawInstances {
            sources: inputs.sources().clone(),
            selection: self.selection.clone(),
            valuation: self.valuation.clone(),
            entries: vec![],
            complete: false,
        };
        let env = match &self.valuation {
            Some(values) => Environment::with_primitive_valuation(inputs, values, c)?,
            None => Environment::new(inputs, c)?,
        };
        populate_with_environment(inputs, &mut expected, c, &env)?;
        if self != &expected {
            return Err("Law instance添字族が元宣言・参照束縛・parameter域と違う".into());
        }
        Ok(())
    }
    pub(in crate::observed) fn recheck_on_object(
        &self,
        inputs: &CheckedInputs,
        readings: &ObjectReadingInstances,
        object: usize,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        let selected = Selection::compute(inputs, readings, object, c)?;
        if selected != self.selection {
            return Err("Law instance添字族が消費先の対象に由来しない".into());
        }
        self.recheck(inputs, c)
    }
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawSelection)
        .map_err(Into::into)
}
fn populate(
    inputs: &CheckedInputs,
    result: &mut ObjectLawInstances,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let env = Environment::new(inputs, c)?;
    populate_with_environment(inputs, result, c, &env)
}
fn populate_with_environment(
    inputs: &CheckedInputs,
    result: &mut ObjectLawInstances,
    c: &mut Control,
    env: &Environment<'_>,
) -> Result<(), ValidationFailure> {
    for (index, original) in result.selection.readings.instances().iter().enumerate() {
        tick(c)?;
        if original.declaration().kind != "law" {
            continue;
        }
        let application = original
            .applications()
            .get(result.selection.object)
            .ok_or("Law instanceの対象別適用行がない")?
            .clone();
        result.entries.push(InstanceParameters {
            instance: index,
            source: original.clone(),
            application,
            application_value: None,
            domains: vec![],
            support: vec![],
            scope: Scope::default(),
            rows: vec![],
            state: ParameterFamilyState::Pending,
        });
        let entry = result
            .entries
            .last_mut()
            .ok_or("追加したLaw instanceがない")?;
        let mut fixed = vec![
            result.selection.identity().root(),
            result.selection.identity().subject(),
        ];
        fixed.extend(original.bindings().iter().map(|b| b.subject()));
        for position in fixed {
            tick(c)?;
            let subject = env.subject(&position.snapshot, &position.subject)?;
            entry
                .scope
                .merge(&env.scope(subject, result.selection.identity().reading(), None)?);
            entry.support.push(position.clone());
        }
        entry.support.sort();
        entry.support.dedup();
        entry.scope.completions = matches!(&entry.application,InstanceApplication::Applicable{conditions} if !conditions.is_empty());
        if result.valuation.is_some() {
            let evaluated = super::instance::initial(env, &result.selection, original, 0)?;
            entry.application_value = Some(evaluated.application);
            entry.scope.merge(&evaluated.scope);
            entry.support.extend(evaluated.support);
            entry.support.sort();
            entry.support.dedup();
        }
        if matches!(entry.application_value, Some(Some(false)))
            || (entry.application_value.is_none()
                && matches!(entry.application, InstanceApplication::NotApplicable))
        {
            entry.state = ParameterFamilyState::NotApplicable;
            continue;
        }
        for p in original.parameters() {
            c.checkpoint(Checkpoint::FiniteLawDomain)?;
            let domain = env.object_parameter_domain(p, original)?;
            let mut scope = Scope::default();
            scope
                .readings
                .insert(result.selection.identity().reading().into());
            scope.quantifiers.push(Quantifier {
                kind: QuantKind::Forall,
                name: p.name.clone(),
                ty: p.ty.clone(),
                domain: None,
                occurrence: p.span,
                context: None,
            });
            scope.merge(&domain.scope);
            let values = domain.values;
            let mut missing = domain.missing;
            let mut support = domain.support;
            missing.sort();
            missing.dedup();
            support.sort();
            support.dedup();
            entry.scope.merge(&scope);
            entry.support.extend(support.iter().cloned());
            entry.support.sort();
            entry.support.dedup();
            entry.domains.push(ParameterDomain {
                parameter: p.clone(),
                values,
                missing,
                support,
                scope,
            });
        }
        // 独立した一因子が既知空なら、非有限・未観測の他因子を含む直積も空。
        // 各因子の元型域・missingと元適用条件は保持する。
        if entry
            .domains
            .iter()
            .any(|d| d.missing.is_empty() && d.values.as_ref().is_some_and(|v| v.is_empty()))
        {
            entry.state = ParameterFamilyState::Ready;
            continue;
        }
        if matches!(entry.application_value, Some(None))
            || (entry.application_value.is_none()
                && matches!(&entry.application, InstanceApplication::Applicable {conditions} if !conditions.is_empty()))
            || entry.domains.iter().any(|d| !d.missing.is_empty())
        {
            entry.state = ParameterFamilyState::Undetermined;
            continue;
        }
        if entry.domains.iter().any(|d| d.values.is_none()) {
            entry.state = ParameterFamilyState::OutsideFinite;
            continue;
        }
        let mut product = vec![vec![]];
        for d in &entry.domains {
            let mut next = vec![];
            for previous in product {
                for index in 0..d.values.as_ref().ok_or("有限parameter域がない")?.len() {
                    c.checkpoint(Checkpoint::FiniteIteration)?;
                    let mut coordinates = previous.clone();
                    coordinates.push(index);
                    next.push(coordinates);
                }
            }
            product = next;
        }
        let declaration = inputs
            .law()
            .declarations
            .get(&original.declaration().name)
            .ok_or("Law instanceの元宣言がない")?;
        let Signature::Law { params, .. } = &declaration.signature else {
            return Err("Law instanceの署名がLawでない".into());
        };
        for coordinates in product {
            c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
            let mut bindings = vec![];
            for p in params {
                tick(c)?;
                let value = if let Some(binding) =
                    original.bindings().iter().find(|b| b.parameter() == p)
                {
                    let f = binding.subject();
                    let subject = env.subject(&f.snapshot, &f.subject)?;
                    Scalar::Subject {
                        snapshot: f.snapshot.clone(),
                        subject: f.subject.clone(),
                        entity: subject.ty.clone(),
                    }
                } else {
                    let index = entry
                        .domains
                        .iter()
                        .position(|d| &d.parameter == p)
                        .ok_or("元Law parameterの域がない")?;
                    entry.domains[index]
                        .values
                        .as_ref()
                        .ok_or("元Law parameterが有限でない")?[coordinates[index]]
                        .clone()
                };
                bindings.push((p.name.clone(), value));
            }
            entry.rows.push(BoundInstance {
                coordinates,
                bindings,
            });
        }
        entry.state = ParameterFamilyState::Ready;
    }
    result.complete = result.entries.iter().all(|e| {
        matches!(
            e.state,
            ParameterFamilyState::Ready | ParameterFamilyState::NotApplicable
        )
    });
    tick(c)
}
pub(in crate::observed) fn finite_object_law_instances(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    object: usize,
    c: &mut Control,
) -> Result<ObjectLawInstances, InstanceFamilyFailure> {
    let selection =
        Selection::compute(inputs, readings, object, c).map_err(|cause| InstanceFamilyFailure {
            cause,
            partial: None,
        })?;
    let mut result = ObjectLawInstances {
        sources: inputs.sources().clone(),
        selection,
        valuation: None,
        entries: vec![],
        complete: false,
    };
    if let Err(cause) = populate(inputs, &mut result, c) {
        return Err(InstanceFamilyFailure {
            cause,
            partial: Some(Box::new(result)),
        });
    }
    Ok(result)
}
#[cfg(test)]
#[path = "finite_object_law_instances_tests.rs"]
mod tests;

#[path = "finite_parameter_realizations.rs"]
pub(in crate::observed) mod realizations;
