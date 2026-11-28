//! Atom 定義ファイルの複数エラー一括収集。

use super::*;
use archsig_common::control::{CheckFailure, Checkpoint, Control};
use archsig_common::issue::Issue;
use std::collections::BTreeSet;

/// 複数エラー収集時の Atom 定義失敗。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionBatchFailure {
    pub issues: Vec<Issue>,
    pub inputs: Vec<DefinitionIdentity>,
}

/// 全 Atom 定義ファイルを走査し、独立したエラーを最大 `max_errors` 件まで収集する。
#[allow(clippy::result_large_err)]
pub fn check_definitions_batch_controlled(
    files: &[(&str, &[u8])],
    control: &Control,
    max_errors: usize,
) -> Result<CheckedDefinitions, CheckFailure<DefinitionBatchFailure>> {
    let max_errors = max_errors.max(1);
    let mut checked = CheckedDefinitions::empty();
    let mut issues: Vec<Issue> = Vec::new();

    for (input, bytes) in files {
        control
            .checkpoint(Checkpoint::DefinitionCanonical)
            .map_err(CheckFailure::Stopped)?;
        checked.inputs.push(DefinitionIdentity {
            input: (*input).into(),
            bytes_digest: sha256_digest(bytes),
            model_digest: None,
        });
        control
            .checkpoint(Checkpoint::DefinitionCanonical)
            .map_err(CheckFailure::Stopped)?;
    }

    for (i, (input, bytes)) in files.iter().enumerate() {
        control
            .checkpoint(Checkpoint::DefinitionIteration)
            .map_err(CheckFailure::Stopped)?;
        let node = match archsig_common::json::parse_definition_inner::<CheckFailure<Box<Issue>>>(
            bytes, input, control,
        ) {
            Ok(node) => node,
            Err(CheckFailure::Stopped(reason)) => return Err(CheckFailure::Stopped(reason)),
            Err(CheckFailure::Input(issue)) => {
                if issues.len() < max_errors {
                    issues.push(*issue);
                }
                continue;
            }
        };
        let (vs, ds, normalized) =
            match reader::read::<CheckFailure<Box<Issue>>>(&node, input, control) {
                Ok(parsed) => parsed,
                Err(CheckFailure::Stopped(reason)) => return Err(CheckFailure::Stopped(reason)),
                Err(CheckFailure::Input(issue)) => {
                    if issues.len() < max_errors {
                        issues.push(*issue);
                    }
                    continue;
                }
            };
        let canonical = match normalized.canonical_controlled::<CheckFailure<Box<Issue>>>(
            control,
            Checkpoint::DefinitionCanonical,
        ) {
            Ok(text) => text,
            Err(CheckFailure::Stopped(reason)) => return Err(CheckFailure::Stopped(reason)),
            Err(CheckFailure::Input(issue)) => {
                if issues.len() < max_errors {
                    issues.push(*issue);
                }
                continue;
            }
        };
        control
            .checkpoint(Checkpoint::DefinitionCanonical)
            .map_err(CheckFailure::Stopped)?;
        checked.inputs[i].model_digest = Some(sha256_digest(canonical.as_bytes()));
        control
            .checkpoint(Checkpoint::DefinitionCanonical)
            .map_err(CheckFailure::Stopped)?;

        let mut dup_ns = false;
        for v in vs {
            control
                .checkpoint(Checkpoint::DefinitionIteration)
                .map_err(CheckFailure::Stopped)?;
            if checked.vocabularies.contains_key(&v.namespace) {
                let mut issue = error(
                    Code::DuplicateId,
                    input,
                    "",
                    format!("duplicate namespace `{}`", v.namespace),
                );
                issue.location = v.location;
                if issues.len() < max_errors {
                    issues.push(*issue);
                }
                dup_ns = true;
                break;
            }
            checked.vocabularies.insert(v.namespace.clone(), v);
        }
        if dup_ns {
            continue;
        }
        for d in ds {
            control
                .checkpoint(Checkpoint::DefinitionIteration)
                .map_err(CheckFailure::Stopped)?;
            checked.declarations.insert(d.name.clone(), d);
        }
    }

    if !issues.is_empty() {
        control
            .checkpoint(Checkpoint::DefinitionCanonical)
            .map_err(CheckFailure::Stopped)?;
        return Err(CheckFailure::Input(DefinitionBatchFailure {
            issues,
            inputs: checked.inputs,
        }));
    }

    match validate_batch(&mut checked, control, max_errors) {
        Ok(()) => {
            if let Err(err) = control.checkpoint(Checkpoint::DefinitionCanonical) {
                return Err(CheckFailure::Stopped(err));
            }
            Ok(checked)
        }
        Err(CheckFailure::Stopped(reason)) => Err(CheckFailure::Stopped(reason)),
        Err(CheckFailure::Input(issues)) => {
            if let Err(err) = control.checkpoint(Checkpoint::DefinitionCanonical) {
                return Err(CheckFailure::Stopped(err));
            }
            Err(CheckFailure::Input(DefinitionBatchFailure {
                issues,
                inputs: checked.inputs,
            }))
        }
    }
}

fn push_unique_issue(issues: &mut Vec<Issue>, issue: Issue, max_errors: usize) {
    if issues.len() >= max_errors {
        return;
    }
    if issues.iter().any(|existing| {
        existing.code == issue.code
            && existing.location == issue.location
            && existing.message == issue.message
    }) {
        return;
    }
    issues.push(issue);
}

#[allow(clippy::result_large_err)]
fn validate_batch(
    defs: &mut CheckedDefinitions,
    control: &Control,
    max_errors: usize,
) -> Result<(), CheckFailure<Vec<Issue>>> {
    let mut dep_issues: Vec<Issue> = Vec::new();
    let mut done = BTreeSet::new();
    let vocab_names: Vec<String> = defs.vocabularies.keys().cloned().collect();
    for n in &vocab_names {
        control
            .checkpoint(Checkpoint::DefinitionDependency)
            .map_err(CheckFailure::Stopped)?;
        let mut active = BTreeSet::new();
        match validate::dag::<CheckFailure<Box<Issue>>>(n, defs, &mut active, &mut done, control) {
            Ok(()) => {}
            Err(CheckFailure::Stopped(reason)) => return Err(CheckFailure::Stopped(reason)),
            Err(CheckFailure::Input(issue)) => {
                push_unique_issue(&mut dep_issues, *issue, max_errors);
            }
        }
        control
            .checkpoint(Checkpoint::DefinitionDependency)
            .map_err(CheckFailure::Stopped)?;
    }

    for v in defs.vocabularies.values() {
        control
            .checkpoint(Checkpoint::DefinitionDependency)
            .map_err(CheckFailure::Stopped)?;
        for b in &v.dependencies {
            control
                .checkpoint(Checkpoint::DefinitionDependency)
                .map_err(CheckFailure::Stopped)?;
            if let Err(issue) = defs.check_binding(b) {
                push_unique_issue(&mut dep_issues, *issue, max_errors);
            }
            control
                .checkpoint(Checkpoint::DefinitionDependency)
                .map_err(CheckFailure::Stopped)?;
        }
        control
            .checkpoint(Checkpoint::DefinitionDependency)
            .map_err(CheckFailure::Stopped)?;
    }

    for d in defs.declarations.values() {
        control
            .checkpoint(Checkpoint::DefinitionDependency)
            .map_err(CheckFailure::Stopped)?;
        let v = &defs.vocabularies[&d.namespace];
        for (at, target) in &d.references {
            control
                .checkpoint(Checkpoint::DefinitionDependency)
                .map_err(CheckFailure::Stopped)?;
            let ns = target.split('.').next().expect("完全名の字句を確認済み");
            let declared_dependency =
                ns == d.namespace || v.dependencies.iter().any(|b| b.namespace == ns);
            if !declared_dependency {
                push_unique_issue(
                    &mut dep_issues,
                    Issue {
                        code: Code::Reference,
                        message: format!("missing dependency for namespace `{ns}`"),
                        location: at.clone(),
                        details: Details::Empty,
                    },
                    max_errors,
                );
            }
            control
                .checkpoint(Checkpoint::DefinitionDependency)
                .map_err(CheckFailure::Stopped)?;
        }
        control
            .checkpoint(Checkpoint::DefinitionDependency)
            .map_err(CheckFailure::Stopped)?;
    }

    if !dep_issues.is_empty() {
        return Err(CheckFailure::Input(dep_issues));
    }

    match super::primitive::check::<CheckFailure<Box<Issue>>>(defs, control) {
        Ok(()) => {
            control
                .checkpoint(Checkpoint::DefinitionDependency)
                .map_err(CheckFailure::Stopped)?;
            Ok(())
        }
        Err(CheckFailure::Stopped(reason)) => Err(CheckFailure::Stopped(reason)),
        Err(CheckFailure::Input(first)) => {
            let mut issues = Vec::new();
            push_unique_issue(&mut issues, *first, max_errors);
            for d in defs.declarations.values() {
                if issues.len() >= max_errors {
                    break;
                }
                if let Some((parameters, fields)) = d.signature.record_fields() {
                    let mut earlier = Vec::new();
                    for p in parameters {
                        control
                            .checkpoint(Checkpoint::DefinitionSemantics)
                            .map_err(CheckFailure::Stopped)?;
                        if let Err(issue) = defs.check_primitive_type(
                            &p.ty,
                            &super::primitive::child(&p.location, "type"),
                            &earlier,
                        ) {
                            push_unique_issue(&mut issues, *issue, max_errors);
                        }
                        earlier.push((p.name.as_str(), &p.ty));
                        if issues.len() >= max_errors {
                            break;
                        }
                    }
                    for f in fields {
                        if issues.len() >= max_errors {
                            break;
                        }
                        control
                            .checkpoint(Checkpoint::DefinitionSemantics)
                            .map_err(CheckFailure::Stopped)?;
                        if let Err(issue) = defs.check_primitive_type(
                            &f.ty,
                            &super::primitive::child(&f.location, "type"),
                            &earlier,
                        ) {
                            push_unique_issue(&mut issues, *issue, max_errors);
                        }
                    }
                } else if let super::model::PrimitiveSignature::Data { constructors } = &d.signature
                {
                    for c in constructors {
                        if issues.len() >= max_errors {
                            break;
                        }
                        let args_at = super::primitive::child(&c.location, "arguments");
                        for (i, t) in c.arguments.iter().enumerate() {
                            if issues.len() >= max_errors {
                                break;
                            }
                            control
                                .checkpoint(Checkpoint::DefinitionSemantics)
                                .map_err(CheckFailure::Stopped)?;
                            if let Err(issue) = defs.check_primitive_type(
                                t,
                                &super::primitive::child(&args_at, &i.to_string()),
                                &[],
                            ) {
                                push_unique_issue(&mut issues, *issue, max_errors);
                            }
                        }
                    }
                }
            }
            Err(CheckFailure::Input(issues))
        }
    }
}
