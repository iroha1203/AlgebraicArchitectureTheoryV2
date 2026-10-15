//! Atom 定義の登録済み namespace・dependency・原始型の静的検査。
use super::*;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use std::collections::BTreeSet;

pub(super) fn check<E: InputError>(
    defs: &mut CheckedDefinitions,
    control: &mut Control,
) -> Result<(), E> {
    let mut done = BTreeSet::new();
    for n in defs.vocabularies.keys() {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        dag::<E>(n, defs, &mut BTreeSet::new(), &mut done, control)?;
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    for v in defs.vocabularies.values() {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        for b in &v.dependencies {
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            defs.check_binding(b)?;
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    for d in defs.declarations.values() {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        let v = &defs.vocabularies[&d.namespace];
        for (at, target) in &d.references {
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
            let ns = target.split('.').next().expect("完全名の字句を確認済み");
            let mut declared_dependency = ns == d.namespace;
            if !declared_dependency {
                let mut bindings = v.dependencies.iter().peekable();
                while let Some(binding) = bindings.next() {
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                    declared_dependency |= binding.namespace == ns;
                    if !declared_dependency && bindings.peek().is_none() {
                        return E::finish(
                            Err(Box::new(Issue {
                                code: Code::Reference,
                                message: format!("namespace `{ns}` の dependency がない"),
                                location: at.clone(),
                                details: Details::Empty,
                            })
                            .into()),
                            control,
                            Checkpoint::DefinitionDependency,
                        );
                    }
                    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
                    if declared_dependency {
                        break;
                    }
                }
            }
            if !declared_dependency {
                return Err((Box::new(Issue {
                    code: Code::Reference,
                    message: format!("namespace `{ns}` の dependency がない"),
                    location: at.clone(),
                    details: Details::Empty,
                }))
                .into());
            }
            E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    super::primitive::check::<E>(defs, control)?;
    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    Ok(())
}
fn dag<E: InputError>(
    n: &str,
    defs: &CheckedDefinitions,
    active: &mut BTreeSet<String>,
    done: &mut BTreeSet<String>,
    control: &mut Control,
) -> Result<(), E> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        dag_inner::<E>(n, defs, active, done, control)
    })
}
fn dag_inner<E: InputError>(
    n: &str,
    defs: &CheckedDefinitions,
    active: &mut BTreeSet<String>,
    done: &mut BTreeSet<String>,
    control: &mut Control,
) -> Result<(), E> {
    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    if done.contains(n) {
        return Ok(());
    }
    active.insert(n.into());
    let Some(v) = defs.vocabularies.get(n) else {
        return Ok(());
    };
    for b in &v.dependencies {
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
        if active.contains(&b.namespace) {
            return Err((Box::new(Issue {
                code: Code::Cycle,
                message: "Atom 定義の依存が循環している".into(),
                location: b.location.clone(),
                details: Details::Empty,
            }))
            .into());
        }
        if defs.vocabularies.contains_key(&b.namespace) {
            dag::<E>(&b.namespace, defs, active, done, control)?
        }
        E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    }
    active.remove(n);
    done.insert(n.into());
    E::checkpoint(control, Checkpoint::DefinitionDependency)?;
    Ok(())
}
