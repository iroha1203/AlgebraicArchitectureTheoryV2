//! 元の整数change・guard・Lawから、範囲に依存しない全fiberを一度生成する。
use super::super::change_affine;
use super::*;
use num_bigint::BigInt as Z;
use std::sync::Arc;
#[derive(Debug)]
pub(in crate::observed) struct Compiled {
    pub linear: Arc<change_affine::Linear>,
    pub subjects: Vec<Scalar>,
    pub requirements: Vec<(String, Vec<(String, Scalar)>)>,
    pub bindings: Vec<(String, Scalar)>,
    pub fixed: Vec<(Fact, Scalar)>,
    pub baselines: Vec<Option<Z>>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub change: String,
}
pub(in crate::observed) enum Preparation {
    Ready(Arc<Compiled>),
    Pending {
        missing: Vec<Fact>,
        unsupported: bool,
    },
}
#[cfg(test)]
thread_local! {static GENERATED:std::cell::Cell<usize>=const{std::cell::Cell::new(0)};}
#[cfg(test)]
pub(in crate::observed) fn generated() -> usize {
    GENERATED.with(std::cell::Cell::get)
}
pub(in crate::observed) fn compile(
    original: &Environment<'_>,
    g: &Graph,
    witness: &ArchitectureWitness,
    r: &crate::observed::request::Request,
    c: &Control,
) -> Result<Preparation, ValidationFailure> {
    let mut env = original
        .try_primitive_valuation_from(&original.fixed_values(), c)?
        .ok_or(internal!("整数修復の基準代入が不適合"))?;
    env.select_local_object(witness, c)?;
    let selected = change_search::selection(original, &env, g, witness, r, &[], c)?;
    let Some(mut subjects) = selected.subjects else {
        return Ok(Preparation::Pending {
            missing: selected.missing,
            unsupported: false,
        });
    };
    subjects.sort_by_key(|s| match s {
        Scalar::Subject {
            snapshot, subject, ..
        } => (snapshot.clone(), subject.clone()),
        _ => unreachable!("選択済みentity"),
    });
    let change_name = r
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "using" {
                match &a.value {
                    crate::observed::request::Selector::Declaration { name } => Some(name.clone()),
                    _ => None,
                }
            } else {
                None
            }
        })
        .ok_or(internal!("整数修復のchangeがない"))?;
    let change = &env.indexes.inputs.law().declarations()[&change_name];
    let mut pending = change_affine::Pending::default();
    let linear = match change_affine::compute(
        &env,
        change,
        &subjects,
        &selected.requirements,
        &mut pending,
    ) {
        Ok(linear) => linear,
        Err(ValidationFailure::UnsupportedExpression { .. }) => {
            return Ok(Preparation::Pending {
                unsupported: pending.unsupported.is_some() || pending.facts.is_empty(),
                missing: pending.facts,
            });
        }
        Err(e) => return Err(e),
    };
    let mut support = pending.support.into_iter().collect::<BTreeSet<_>>();
    let mut scope = pending.scope;
    scope.readings.insert(change.reading.clone());
    let mut baselines = Vec::with_capacity(linear.slots.len());
    for slot in &linear.slots {
        tick(c)?;
        let field = slot
            .field
            .as_ref()
            .ok_or(internal!("整数更新先のfieldがない"))?;
        let subject = env.indexes.subject(&slot.snapshot, &slot.subject)?;
        let value = Scalar::Subject {
            snapshot: slot.snapshot.clone(),
            subject: slot.subject.clone(),
            entity: subject.ty.to_string(),
        };
        let read = env.scoped_field(
            change_evaluation::known(value),
            field,
            &Scope::default(),
            &change.reading,
            change.span,
        )?;
        support.extend(read.support.iter().cloned());
        scope.merge(&read.scope);
        baselines.push(match read.known_value.as_ref() {
            Some(Scalar::Z(z)) => Some(z.clone()),
            None => None,
            _ => return Err(internal!("整数更新先の基準値がZでない").into()),
        });
    }
    #[cfg(test)]
    GENERATED.with(|n| n.set(n.get() + 1));
    Ok(Preparation::Ready(Arc::new(Compiled {
        linear: Arc::new(linear),
        subjects,
        requirements: selected.requirements,
        bindings: selected.bindings,
        fixed: original.fixed_values(),
        baselines,
        support: support.into_iter().collect(),
        scope,
        change: change_name,
    })))
}
