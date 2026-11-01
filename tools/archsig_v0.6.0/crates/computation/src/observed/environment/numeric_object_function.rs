//! 数値Law/viewの元式を同じ対象・引数環境で読み、実引数で再代入する。
use super::*;
use crate::observed::{
    affine,
    object_evaluate::ObjectDomain,
    term::affine::{self as terms, Value},
};
use crate::{
    construction::{
        ConstructionFailure,
        readings::{InstanceApplication, ObjectReadingInstances},
    },
    observed::object_evaluation_table::ObjectEvaluationPosition,
};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum Reading {
    Outside,
    Value(Value),
    Unknown(Vec<Fact>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Counterexample {
    pub bindings: Vec<(String, Scalar)>,
    pub left: Scalar,
    pub right: Scalar,
    pub facts: Vec<Fact>,
}
pub(super) enum Source {
    Outside,
    Value(Box<SourceValue>),
    Unknown,
}
fn invalid(e: ValidationFailure) -> ConstructionFailure {
    match e {
        ValidationFailure::Stop(s) => s.into(),
        e => {
            ConstructionFailure::Inconsistent(e.internal_context(format!("数値viewの元式: {e:?}")))
        }
    }
}
pub(super) fn fixed_bindings(
    row: &crate::construction::readings::ObjectInstance,
    c: &Control,
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let mut bindings = vec![];
    for binding in row.bindings() {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)?;
        let Type::Ref(entity) = &binding.parameter().ty.erase() else {
            return Err(internal!("数値viewの固定束縛が参照でない").into());
        };
        bindings.push((
            binding.parameter().name.clone(),
            Scalar::Subject {
                snapshot: binding.subject().snapshot.clone(),
                subject: binding.subject().subject.clone(),
                entity: entity.clone(),
            },
        ));
    }
    Ok(bindings)
}
fn source(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    position: ObjectEvaluationPosition,
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &Control,
) -> Result<Source, ConstructionFailure> {
    expression(
        inputs,
        readings,
        (position, None),
        names,
        target,
        assignments,
        c,
    )
}
pub(super) fn expression(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    selection: (ObjectEvaluationPosition, Option<usize>),
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &Control,
) -> Result<Source, ConstructionFailure> {
    expression_inner(
        inputs,
        readings,
        (selection.0, selection.1, None),
        names,
        target,
        assignments,
        c,
    )
}
pub(super) fn guard(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    selection: (ObjectEvaluationPosition, Option<usize>),
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &Control,
) -> Result<(Source, super::numeric_guard::Analysis), ConstructionFailure> {
    let mut forms = super::numeric_guard::Analysis::default();
    let source = expression_inner(
        inputs,
        readings,
        (selection.0, selection.1, Some(&mut forms)),
        names,
        target,
        assignments,
        c,
    )?;
    Ok((source, forms))
}
fn expression_inner(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    selection: (
        ObjectEvaluationPosition,
        Option<usize>,
        Option<&mut super::numeric_guard::Analysis>,
    ),
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &Control,
) -> Result<Source, ConstructionFailure> {
    let (position, expression, forms) = selection;
    let row = readings
        .instances()
        .get(position.instance)
        .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("数値viewのinstanceがない")))?;
    match row.applications().get(position.object) {
        Some(InstanceApplication::NotApplicable) => return Ok(Source::Outside),
        Some(InstanceApplication::Applicable { conditions }) if conditions.is_empty() => {}
        Some(_) => return Ok(Source::Unknown),
        None => {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "数値viewの対象別適用がない"
            )));
        }
    }
    let declaration = inputs
        .law()
        .declarations()
        .get(&row.declaration().name)
        .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("数値viewの宣言がない")))?;
    let (params, body) = match &declaration.signature {
        archsig_input::law::model::Signature::View { params, body, .. }
        | archsig_input::law::model::Signature::Law { params, body, .. } => (params, *body),
        _ => {
            return Err(ConstructionFailure::InvalidSelection(
                "数値のLaw/viewを選択する".into(),
            ));
        }
    };
    let expression = expression.unwrap_or(body);
    let selected =
        inputs.law().exprs().get(expression).ok_or_else(|| {
            ConstructionFailure::Inconsistent(internal!("数値読取りの元式がない"))
        })?;
    if selected.span.0 < declaration.span.0 || selected.span.1 > declaration.span.1 {
        return Err(ConstructionFailure::Inconsistent(internal!(
            "数値読取りの元式が別宣言に属する"
        )));
    }
    let mut env = Environment::new(inputs, c).map_err(ConstructionFailure::from)?;
    env.indexes.object = Some(Arc::new(
        ObjectDomain::from_readings(inputs, readings, position.object, c).map_err(invalid)?,
    ));
    env.indexes.object_instance = Some(row);
    let mut bindings = fixed_bindings(row, c).map_err(invalid)?;
    for (name, value) in assignments {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        let parameter = row
            .parameters()
            .iter()
            .find(|p| &p.name == name)
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent(internal!("数値反例の引数が元viewにない"))
            })?;
        if value.ty() != parameter.ty || bindings.iter().any(|(n, _)| n == name) {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "数値反例の引数型または一意性が違う"
            )));
        }
        bindings.push((name.clone(), value.clone()));
    }
    let (mut variables, _) =
        numeric_parameters::law_variables(&env, params, &bindings).map_err(invalid)?;
    for p in params
        .iter()
        .filter(|p| !bindings.iter().any(|(name, _)| name == &p.name))
    {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        let argument = names
            .iter()
            .position(|(a, z)| if target { z == &p.name } else { a == &p.name })
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent(internal!("数値viewの引数対応がない"))
            })?;
        let Some(values) = terms::domain(&p.ty, argument, &[], inputs.law(), c).map_err(invalid)?
        else {
            return Ok(Source::Unknown);
        };
        let [value] = values.as_slice() else {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "数値引数の記号域が一つでない"
            )));
        };
        let variable = variables.get_mut(&p.name).ok_or_else(|| {
            ConstructionFailure::Inconsistent(internal!("数値viewの元変数がない"))
        })?;
        variable.known_value = value.known(c).map_err(invalid)?;
        variable.affine = value.number(c).map_err(invalid)?.map(Box::new);
        variable.symbolic = Some(Box::new(value.clone()));
    }
    if let Some(forms) = forms {
        *forms = super::numeric_guard::analyze(
            &env,
            expression,
            &variables,
            &Scope::default(),
            &declaration.reading,
        )
        .map_err(invalid)?;
    }
    Ok(Source::Value(Box::new(
        env.scoped_ast(
            expression,
            &variables,
            &Scope::default(),
            &declaration.reading,
        )
        .map_err(invalid)?,
    )))
}

pub(in crate::observed) fn read(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    object: usize,
    instance: usize,
    names: &[(String, String)],
    target: bool,
    c: &Control,
) -> Result<Reading, ConstructionFailure> {
    let value = match source(
        inputs,
        readings,
        ObjectEvaluationPosition { object, instance },
        names,
        target,
        &[],
        c,
    )? {
        Source::Outside => return Ok(Reading::Outside),
        Source::Unknown => return Ok(Reading::Unknown(vec![])),
        Source::Value(v) => *v,
    };
    if value.condition_failed {
        return Ok(Reading::Outside);
    }
    if value.condition_pending {
        return Ok(Reading::Unknown(vec![]));
    }
    let symbolic = value
        .known_value
        .map(Value::Known)
        .or_else(|| value.affine.map(|v| Value::Number(*v)))
        .or_else(|| value.symbolic.map(|v| *v));
    let Some(value) = symbolic else {
        return Ok(Reading::Unknown(vec![]));
    };
    if value.unsupported(c).map_err(invalid)? {
        return Ok(Reading::Unknown(vec![]));
    }
    let mut pending = vec![&value];
    let mut missing = vec![];
    while let Some(part) = pending.pop() {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        match part {
            Value::Number(form) => missing.extend(form.missing_facts()),
            Value::Tuple(items) => pending.extend(items),
            _ => {}
        }
    }
    missing.sort();
    missing.dedup();
    Ok(if missing.is_empty() {
        Reading::Value(value)
    } else {
        Reading::Unknown(missing)
    })
}
fn concrete(
    inputs: &CheckedInputs,
    readings: &ObjectReadingInstances,
    position: ObjectEvaluationPosition,
    names: &[(String, String)],
    target: bool,
    assignments: &[(String, Scalar)],
    c: &Control,
) -> Result<(Scalar, Vec<Fact>), ConstructionFailure> {
    let Source::Value(value) = source(inputs, readings, position, names, target, assignments, c)?
    else {
        return Err(ConstructionFailure::Inconsistent(internal!(
            "数値反例の元viewが適用されない"
        )));
    };
    if value.condition_failed || value.condition_pending {
        return Err(ConstructionFailure::Inconsistent(internal!(
            "数値反例の再代入条件が成立しない"
        )));
    }
    let value_scalar = value.known_value.ok_or_else(|| {
        ConstructionFailure::Inconsistent(internal!("数値反例の元bodyへの再代入値がない"))
    })?;
    Ok((value_scalar, value.support))
}
pub(in crate::observed) fn counterexample(
    inputs: &CheckedInputs,
    source_readings: &ObjectReadingInstances,
    target_readings: &ObjectReadingInstances,
    positions: [ObjectEvaluationPosition; 2],
    names: &[(String, String)],
    unit: Option<&affine::TermArgument>,
    c: &Control,
) -> Result<Counterexample, ConstructionFailure> {
    let row = &source_readings.instances()[positions[0].instance];
    let mut assignments = vec![];
    let mut target_assignments = vec![];
    for p in row.parameters() {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        let argument = names
            .iter()
            .position(|(a, _)| a == &p.name)
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent(internal!("数値反例の元引数対応がない"))
            })?;
        let Some(values) = terms::domain(&p.ty, argument, &[], inputs.law(), c).map_err(invalid)?
        else {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "数値反例の全型域がない"
            )));
        };
        let [value] = values.as_slice() else {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "数値反例の記号引数が一つでない"
            )));
        };
        let scalar = value.at(unit, c).map_err(invalid)?;
        assignments.push((p.name.clone(), scalar.clone()));
        target_assignments.push((names[argument].1.clone(), scalar));
    }
    let (left, mut facts) = concrete(
        inputs,
        source_readings,
        positions[0],
        names,
        false,
        &assignments,
        c,
    )?;
    let (right, target_facts) = concrete(
        inputs,
        target_readings,
        positions[1],
        names,
        true,
        &target_assignments,
        c,
    )?;
    if crate::observed::data::equal(&left, &right, c).map_err(invalid)? {
        return Err(ConstructionFailure::Inconsistent(internal!(
            "数値viewの係数反例が元bodyへの再代入で相違しない"
        )));
    }
    facts.extend(target_facts);
    facts.sort();
    facts.dedup();
    let mut values = fixed_bindings(row, c).map_err(invalid)?;
    values.extend(assignments);
    let mut bindings = vec![];
    for (name, _) in &row.declaration().parameters {
        c.checkpoint(Checkpoint::ObjectViewTransportFamily)
            .map_err(ConstructionFailure::from)?;
        let value = values
            .iter()
            .find(|(actual, _)| actual == name)
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent(internal!("数値反例の全引数が揃わない"))
            })?;
        bindings.push(value.clone());
    }
    Ok(Counterexample {
        bindings,
        left,
        right,
        facts,
    })
}
