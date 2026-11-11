//! 元の整数change・guard・Lawから、範囲に依存しない全fiberを一度生成する。
use super::super::change_affine;
use super::*;
use num_bigint::BigInt as Z;
use std::sync::Arc;
#[derive(Debug)]
pub(in crate::observed) struct Compiled {
    pub linear: Arc<change_affine::Linear>,
    pub family: Option<Arc<InputFamily>>,
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
#[derive(Debug)]
pub(in crate::observed) struct InputFamily {
    pub view: String,
    pub bindings: Vec<(String, Scalar)>,
    pub fields: Vec<Fact>,
    pub system: change_affine::InputSystem,
}
pub(in crate::observed) enum Preparation {
    Ready(Arc<Compiled>),
    Rejected,
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
    let selected = change_search::selection(original, &env, g, witness, r, &[], true, c)?;
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
    let input = r.arguments.iter().find_map(|a| match (&*a.name, &a.value) {
        ("inputs", crate::observed::request::Selector::Declaration { name }) => Some(name.clone()),
        _ => None,
    });
    let mut input_data = None;
    if let Some(name) = input {
        let Signature::View {
            params,
            body,
            returns,
        } = &env.indexes.inputs.law().declarations()[&name].signature
        else {
            unreachable!("入力view")
        };
        let mut bindings = vec![];
        for p in params {
            let a = r
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or(internal!("整数入力viewの束縛がない"))?;
            bindings.push((
                p.name.clone(),
                change_search::selector(original, g, &a.value)?,
            ));
        }
        let mut details = change_affine::Pending {
            expression: Some(*body),
            coefficient_type: Some(returns.clone()),
            bindings: bindings.clone(),
            ..Default::default()
        };
        let read = match super::family::read(&env, &name, &bindings) {
            Ok(read) => read,
            Err(ValidationFailure::UnsupportedExpression { .. }) => {
                return Ok(Preparation::Pending {
                    details: Box::new(details),
                    unsupported: true,
                });
            }
            Err(e) => return Err(e),
        };
        if read.failed {
            return Ok(Preparation::Rejected);
        }
        details.facts = read.missing.clone();
        if read.blocked {
            return Ok(Preparation::Pending {
                unsupported: details.facts.is_empty(),
                details: Box::new(details),
            });
        }
        for fact in &read.missing {
            env.tick()?;
            let field = env.indexes.field(
                &env.state,
                &fact.snapshot,
                &fact.subject,
                fact.field
                    .as_deref()
                    .ok_or(internal!("整数入力位置のfieldがない"))?,
            )?;
            if field.ty != Type::Z || fact.field.as_ref().is_some_and(|f| f.is_owner()) {
                return Ok(Preparation::Pending {
                    details: Box::new(details),
                    unsupported: true,
                });
            }
        }
        input_data = Some((name, bindings, read));
    }
    let mut pending = change_affine::Pending::default();
    let (linear, family) = if let Some(linear) = prior {
        (linear, None)
    } else {
        let generated = if let Some((_, _, read)) = &input_data {
            change_affine::compute_inputs(
                &env,
                change,
                &subjects,
                &selected.requirements,
                &mut pending,
                &read.missing,
            )
            .map(|(linear, system)| (linear, Some(system)))
        } else {
            change_affine::compute(
                &env,
                change,
                &subjects,
                &selected.requirements,
                &mut pending,
            )
            .map(|linear| (linear, None))
        };
        let (linear, system) = match generated {
            Ok(generated) => generated,
            Err(ValidationFailure::UnsupportedExpression { .. }) => {
                return Ok(Preparation::Pending {
                    unsupported: pending.unsupported.is_some()
                        || pending.facts.is_empty()
                        || input_data.as_ref().is_some_and(|(_, _, read)| {
                            pending.facts.iter().any(|fact| read.missing.contains(fact))
                        }),
                    details: Box::new(pending),
                });
            }
            Err(e) => return Err(e),
        };
        let family = if let Some((name, bindings, read)) = input_data {
            pending.support.extend(read.support);
            pending.scope.merge(&read.scope);
            pending.scope.completions = !read.missing.is_empty();
            Some(Arc::new(InputFamily {
                view: name,
                bindings,
                fields: read.missing,
                system: system.ok_or(internal!("整数入力の同時系がない"))?,
            }))
        } else {
            None
        };
        #[cfg(test)]
        GENERATED.with(|n| n.set(n.get() + 1));
        (Arc::new(linear), family)
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
        family,
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
