//! 元の整数change・guard・Lawから、範囲に依存しない全fiberを一度生成する。
use super::super::change_affine;
use super::*;
use num_bigint::BigInt as Z;
use std::sync::Arc;
#[derive(Debug)]
pub(in crate::observed) struct Compiled {
    pub linear: Arc<change_affine::Linear>,
    object: Arc<crate::observed::object_evaluate::ObjectDomain>,
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
        details: Box<change_affine::Pending>,
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
    compile_inner(original, g, witness, r, c, None)
}
/// 既存solveの公開済み表示を、同じparameter/核の順序のまま引き継ぐ。
pub(in crate::observed) fn from_linear(
    original: &Environment<'_>,
    g: &Graph,
    witness: &ArchitectureWitness,
    r: &crate::observed::request::Request,
    c: &Control,
    linear: Arc<change_affine::Linear>,
) -> Result<Preparation, ValidationFailure> {
    compile_inner(original, g, witness, r, c, Some(linear))
}
fn compile_inner(
    original: &Environment<'_>,
    g: &Graph,
    witness: &ArchitectureWitness,
    r: &crate::observed::request::Request,
    c: &Control,
    prior: Option<Arc<change_affine::Linear>>,
) -> Result<Preparation, ValidationFailure> {
    let mut env = original
        .try_primitive_valuation_from(&original.fixed_values(), c)?
        .ok_or(internal!("整数修復の基準代入が不適合"))?;
    env.select_local_object(witness, c)?;
    let selected = change_search::selection(original, &env, g, witness, r, &[], c)?;
    let Some(mut subjects) = selected.subjects else {
        return Ok(Preparation::Pending {
            details: Box::new(change_affine::Pending {
                facts: selected.missing,
                ..Default::default()
            }),
            unsupported: false,
        });
    };
    if prior.is_none() {
        subjects.sort_by_key(|s| match s {
            Scalar::Subject {
                snapshot, subject, ..
            } => (snapshot.clone(), subject.clone()),
            _ => unreachable!("選択済みentity"),
        });
    }
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
    let linear = if let Some(linear) = prior {
        linear
    } else {
        let generated = match change_affine::compute(
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
                    details: Box::new(pending),
                });
            }
            Err(e) => return Err(e),
        };
        #[cfg(test)]
        GENERATED.with(|n| n.set(n.get() + 1));
        Arc::new(generated)
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
    Ok(Preparation::Ready(Arc::new(Compiled {
        linear,
        object: env
            .object_domain()
            .ok_or(internal!("整数修復の参照域がない"))?,
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

impl Compiled {
    #[cfg(test)]
    pub(in crate::observed) fn assert_object_shared(&self, current: &Environment<'_>) {
        assert!(Arc::ptr_eq(&self.object, &current.object_domain().unwrap()));
    }

    /// 同じ固定入力の参照域だけを共有し、評価状態は毎回新しくする。
    pub(in crate::observed) fn environment<'i>(
        &self,
        original: &Environment<'i>,
        c: &Control,
    ) -> Result<Environment<'i>, ValidationFailure> {
        let mut current = original
            .try_primitive_valuation_from(&self.fixed, c)?
            .ok_or(internal!("整数候補の基準代入が不適合"))?;
        current.indexes.object = Some(self.object.clone());
        Ok(current)
    }
}
