//! ArchMap の複数エラー一括収集。

use super::*;
use archsig_common::control::{CheckFailure, Checkpoint, Control};
use archsig_common::issue::{Code, Details, Issue, Location};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, BTreeSet, HashMap};

type E = CheckFailure<Box<Issue>>;

/// 複数エラー収集時の ArchMap 失敗。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchMapBatchFailure {
    pub issues: Vec<Issue>,
    pub bytes_digest: String,
}

/// ArchMap を検証し、独立した参照・由来・型・語彙エラーを最大 `max_errors` 件まで収集する。
#[allow(clippy::result_large_err)]
pub fn check_archmap_batch_controlled(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &Control,
    max_errors: usize,
) -> Result<CheckedArchMap, CheckFailure<ArchMapBatchFailure>> {
    let max_errors = max_errors.max(1);
    control
        .checkpoint(Checkpoint::BeforeArchMap)
        .map_err(CheckFailure::Stopped)?;
    #[cfg(test)]
    entry_control_tests::BYTES_DIGEST_STARTS.with(|count| count.set(count.get() + 1));
    let bytes_digest = sha256_digest(bytes);
    let wrap_single = |e: E| -> CheckFailure<ArchMapBatchFailure> {
        match e {
            CheckFailure::Stopped(reason) => CheckFailure::Stopped(reason),
            CheckFailure::Input(issue) => CheckFailure::Input(ArchMapBatchFailure {
                issues: vec![*issue],
                bytes_digest: bytes_digest.clone(),
            }),
        }
    };

    let root = archsig_common::json::parse_inner::<E>(bytes, control, Checkpoint::ArchMapIteration)
        .map_err(wrap_single)?;
    let raw = read_document::<E>(&root, control).map_err(wrap_single)?;

    E::checkpoint(control, Checkpoint::ArchMapSchema).map_err(wrap_single)?;

    let res = check_document_batch(raw, definitions, control, max_errors);
    let mut checked = match (res, control.checkpoint(Checkpoint::ArchMapSchema)) {
        (_, Err(stop)) => return Err(CheckFailure::Stopped(stop)),
        (Err(CheckFailure::Stopped(stop)), Ok(())) => return Err(CheckFailure::Stopped(stop)),
        (Err(CheckFailure::Input(issues)), Ok(())) => {
            return Err(CheckFailure::Input(ArchMapBatchFailure {
                issues,
                bytes_digest,
            }));
        }
        (Ok(checked), Ok(())) => checked,
    };

    checked.bytes_digest = bytes_digest.clone();
    let model = canonical::model_json_controlled::<E>(&checked, control).map_err(wrap_single)?;
    let canonical = model
        .canonical_controlled::<E>(control, Checkpoint::ArchMapCanonical)
        .map_err(wrap_single)?;
    control
        .checkpoint(Checkpoint::ArchMapCanonical)
        .map_err(CheckFailure::Stopped)?;
    checked.model_digest = sha256_digest(canonical.as_bytes());
    control
        .checkpoint(Checkpoint::ArchMapCanonical)
        .map_err(CheckFailure::Stopped)?;
    control
        .checkpoint(Checkpoint::ArchMapIteration)
        .map_err(CheckFailure::Stopped)?;
    Ok(checked)
}

fn push_issue(issues: &mut Vec<Issue>, max_errors: usize, iss: Box<Issue>) {
    if issues.len() < max_errors {
        issues.push(*iss);
    }
}

fn check_document_batch(
    raw: RawDocument,
    definitions: &CheckedDefinitions,
    control: &Control,
    max_errors: usize,
) -> Result<CheckedArchMap, CheckFailure<Vec<Issue>>> {
    let mut issues: Vec<Issue> = Vec::new();
    let mut sources: HashMap<&str, &Source> = HashMap::new();
    for (source, _) in &raw.sources {
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
        sources.insert(source.id.as_str(), source);
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
    }

    for (o, ptr) in &raw.origins {
        control
            .checkpoint(Checkpoint::ArchMapIteration)
            .map_err(CheckFailure::Stopped)?;
        for (i, l) in o.locations.iter().enumerate() {
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
            if !sources.contains_key(l.source.as_str()) {
                push_issue(
                    &mut issues,
                    max_errors,
                    issue(
                        Code::Reference,
                        &format!("{ptr}/locations/{i}/source"),
                        format!("source `{}` does not exist", l.source),
                    ),
                );
            }
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
        }
        control
            .checkpoint(Checkpoint::ArchMapIteration)
            .map_err(CheckFailure::Stopped)?;
    }

    let mut origins: HashMap<&str, &Origin> = HashMap::new();
    for (origin, _) in &raw.origins {
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
        origins.insert(origin.id.as_str(), origin);
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
    }

    let mut subject_types = BTreeSet::new();
    for snap in &raw.snapshots {
        control
            .checkpoint(Checkpoint::ArchMapIteration)
            .map_err(CheckFailure::Stopped)?;
        let snap_mode = match origins.get(snap.origin.as_str()) {
            Some(o) => Some(o.mode),
            None => {
                push_issue(
                    &mut issues,
                    max_errors,
                    issue(
                        Code::Reference,
                        &format!("{}/origin", snap.pointer),
                        format!("origin `{}` does not exist", snap.origin),
                    ),
                );
                None
            }
        };

        for s in &snap.subjects {
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
            match origins.get(s.origin.as_str()) {
                Some(o) => {
                    if let Some(m) = snap_mode
                        && o.mode != m
                    {
                        push_issue(
                            &mut issues,
                            max_errors,
                            issue(
                                Code::Reference,
                                &format!("{}/origin", s.pointer),
                                "subject origin.mode differs from snapshot",
                            ),
                        );
                    }
                }
                None => {
                    push_issue(
                        &mut issues,
                        max_errors,
                        issue(
                            Code::Reference,
                            &format!("{}/origin", s.pointer),
                            format!("origin `{}` does not exist", s.origin),
                        ),
                    );
                }
            }
            match definitions
                .declarations
                .get(&s.ty)
                .map(|d| d.signature.kind())
            {
                Some("entity" | "arrow" | "correspondence") => {
                    subject_types.insert(s.ty.clone());
                }
                _ => {
                    push_issue(
                        &mut issues,
                        max_errors,
                        issue(
                            Code::Reference,
                            &format!("{}/type", s.pointer),
                            format!(
                                "`{}` is not an entity, arrow, or correspondence declaration",
                                s.ty
                            ),
                        ),
                    );
                }
            }
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
        }

        for a in &snap.atoms {
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
            match origins.get(a.origin.as_str()) {
                Some(o) => {
                    if let Some(m) = snap_mode
                        && o.mode != m
                    {
                        push_issue(
                            &mut issues,
                            max_errors,
                            issue(
                                Code::Reference,
                                &format!("{}/origin", a.pointer),
                                "Atom origin.mode differs from snapshot",
                            ),
                        );
                    }
                }
                None => {
                    push_issue(
                        &mut issues,
                        max_errors,
                        issue(
                            Code::Reference,
                            &format!("{}/origin", a.pointer),
                            format!("origin `{}` does not exist", a.origin),
                        ),
                    );
                }
            }
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
        }
        control
            .checkpoint(Checkpoint::ArchMapIteration)
            .map_err(CheckFailure::Stopped)?;
    }

    let mut bound = BTreeMap::new();
    let mut vocab_had_errors = false;
    for (i, binding) in raw.vocabularies.iter().enumerate() {
        control
            .checkpoint(Checkpoint::ArchMapIteration)
            .map_err(CheckFailure::Stopped)?;
        let ptr = format!("/vocabularies/{i}");
        if let Err(mut error) = definitions.check_binding(binding) {
            vocab_had_errors = true;
            let field = if error.code == Code::Reference {
                "namespace"
            } else if matches!(&error.details, Details::VocabularyUnavailable { .. }) {
                "version"
            } else {
                "digest"
            };
            if error.code == Code::VocabularyMismatch {
                bound.insert(binding.namespace.clone(), binding.clone());
            }
            error.location = Location::ArchMap {
                pointer: format!("{ptr}/{field}"),
                span: None,
            };
            push_issue(&mut issues, max_errors, error);
        } else {
            bound.insert(binding.namespace.clone(), binding.clone());
        }
        control
            .checkpoint(Checkpoint::ArchMapIteration)
            .map_err(CheckFailure::Stopped)?;
    }

    if !vocab_had_errors {
        let req_ns = match required_namespaces::<E>(definitions, &subject_types, control) {
            Ok(ns) => ns,
            Err(CheckFailure::Stopped(r)) => return Err(CheckFailure::Stopped(r)),
            Err(CheckFailure::Input(i)) => return Err(CheckFailure::Input(vec![*i])),
        };
        for namespace in req_ns {
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
            if !bound.contains_key(&namespace) {
                let vocabulary = &definitions.vocabularies[&namespace];
                push_issue(
                    &mut issues,
                    max_errors,
                    Box::new(Issue {
                        code: Code::VocabularyMismatch,
                        message: format!(
                            "missing binding for vocabulary `{namespace}` version `{}`; expected digest {}",
                            vocabulary.version, vocabulary.digest
                        ),
                        location: Location::ArchMap {
                            pointer: "/vocabularies".into(),
                            span: None,
                        },
                        details: Details::Vocabulary {
                            namespace,
                            version: vocabulary.version.clone(),
                            found_digest: None,
                            expected_digest: vocabulary.digest.clone(),
                        },
                    }),
                );
            }
            control
                .checkpoint(Checkpoint::ArchMapIteration)
                .map_err(CheckFailure::Stopped)?;
        }
    }

    if !issues.is_empty() {
        return Err(CheckFailure::Input(issues));
    }

    let snapshots = match value::check_snapshots::<E>(&raw.snapshots, definitions, control) {
        Ok(s) => s,
        Err(CheckFailure::Stopped(r)) => return Err(CheckFailure::Stopped(r)),
        Err(CheckFailure::Input(i)) => return Err(CheckFailure::Input(vec![*i])),
    };
    if let Err(err) = complete::check_completion::<E>(&snapshots, definitions, control) {
        return match err {
            CheckFailure::Stopped(r) => Err(CheckFailure::Stopped(r)),
            CheckFailure::Input(i) => Err(CheckFailure::Input(vec![*i])),
        };
    }

    let mut sources_out = Vec::new();
    for (source, _) in raw.sources {
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
        sources_out.push(source);
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
    }
    let mut origins_out = Vec::new();
    for (origin, _) in raw.origins {
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
        origins_out.push(origin);
        control
            .checkpoint(Checkpoint::ArchMapSchema)
            .map_err(CheckFailure::Stopped)?;
    }
    Ok(CheckedArchMap {
        bytes_digest: String::new(),
        model_digest: String::new(),
        vocabularies: bound,
        sources: sources_out,
        origins: origins_out,
        snapshots,
    })
}
