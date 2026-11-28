//! Atom 定義ファイルの複数エラー一括収集。

use super::*;
use archsig_common::control::{CheckFailure, Checkpoint, Control};
use archsig_common::issue::Issue;

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

    let validate_result = validate::check::<CheckFailure<Box<Issue>>>(&mut checked, control);
    if let Err(err) = control.checkpoint(Checkpoint::DefinitionCanonical) {
        return Err(CheckFailure::Stopped(err));
    }
    match validate_result {
        Ok(()) => Ok(checked),
        Err(CheckFailure::Stopped(reason)) => Err(CheckFailure::Stopped(reason)),
        Err(CheckFailure::Input(issue)) => Err(CheckFailure::Input(DefinitionBatchFailure {
            issues: vec![*issue],
            inputs: checked.inputs,
        })),
    }
}
