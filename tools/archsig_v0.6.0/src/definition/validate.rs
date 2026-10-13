//! Atom 定義の登録済み namespace・dependency・原始型の静的検査。
use super::*;
use std::collections::BTreeSet;

pub(super) fn check(defs: &mut CheckedDefinitions) -> Result<(), Box<Issue>> {
    let mut done = BTreeSet::new();
    for n in defs.vocabularies.keys() {
        dag(n, defs, &mut BTreeSet::new(), &mut done)?;
    }
    for v in defs.vocabularies.values() {
        for b in &v.dependencies {
            defs.check_binding(b)?;
        }
    }
    for d in defs.declarations.values() {
        let v = &defs.vocabularies[&d.namespace];
        for (at, target) in &d.references {
            let ns = target.split('.').next().expect("完全名の字句を確認済み");
            if ns != d.namespace && !v.dependencies.iter().any(|b| b.namespace == ns) {
                return Err(Box::new(Issue {
                    code: Code::Reference,
                    message: format!("namespace `{ns}` の dependency がない"),
                    location: at.clone(),
                    details: Details::Empty,
                }));
            }
        }
    }
    super::primitive::check(defs)
}
fn dag(
    n: &str,
    defs: &CheckedDefinitions,
    active: &mut BTreeSet<String>,
    done: &mut BTreeSet<String>,
) -> Result<(), Box<Issue>> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        dag_inner(n, defs, active, done)
    })
}
fn dag_inner(
    n: &str,
    defs: &CheckedDefinitions,
    active: &mut BTreeSet<String>,
    done: &mut BTreeSet<String>,
) -> Result<(), Box<Issue>> {
    if done.contains(n) {
        return Ok(());
    }
    active.insert(n.into());
    let Some(v) = defs.vocabularies.get(n) else {
        return Ok(());
    };
    for b in &v.dependencies {
        if active.contains(&b.namespace) {
            return Err(Box::new(Issue {
                code: Code::Cycle,
                message: "Atom 定義の依存が循環している".into(),
                location: b.location.clone(),
                details: Details::Empty,
            }));
        }
        if defs.vocabularies.contains_key(&b.namespace) {
            dag(&b.namespace, defs, active, done)?
        }
    }
    active.remove(n);
    done.insert(n.into());
    Ok(())
}
