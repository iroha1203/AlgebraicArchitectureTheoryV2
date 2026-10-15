//! 共通 Atom 定義の schema、namespace 登録、依存と原始型の検査。
pub mod model;
mod primitive;
mod reader;
mod validate;
use crate::json::InputError;
use crate::observed::control::{CheckFailure, Checkpoint, Control};
use crate::{
    canonical::sha256_digest,
    issue::{Code, Details, Issue, Location},
};
pub use model::*;

pub const FORMAT: &str = "archsig.atom-definition/1";
pub const SEMANTICS: &str = "archsig/0.6.0";
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionFailure {
    pub issue: Issue,
    pub inputs: Vec<DefinitionIdentity>,
}
pub(crate) fn location(input: &str, pointer: &str) -> Location {
    Location::Definition {
        input: input.into(),
        pointer: pointer.into(),
        span: None,
    }
}
pub(crate) fn error(
    code: Code,
    input: &str,
    pointer: &str,
    message: impl Into<String>,
) -> Box<Issue> {
    Box::new(Issue {
        code,
        message: message.into(),
        location: location(input, pointer),
        details: Details::Empty,
    })
}
/// 全ファイルを登録してから依存 DAG、binding、原始型を検査する。
#[allow(clippy::result_large_err)]
pub fn check_definitions(files: &[(&str, &[u8])]) -> Result<CheckedDefinitions, DefinitionFailure> {
    check_definitions_inner::<Box<Issue>>(files, &mut Control::unlimited()).map_err(
        |(issue, inputs)| DefinitionFailure {
            issue: *issue,
            inputs,
        },
    )
}

#[allow(clippy::result_large_err)]
pub fn check_definitions_controlled(
    files: &[(&str, &[u8])],
    control: &mut Control,
) -> Result<CheckedDefinitions, CheckFailure<DefinitionFailure>> {
    check_definitions_inner::<CheckFailure<Box<Issue>>>(files, control).map_err(
        |(failure, inputs)| match failure {
            CheckFailure::Input(issue) => CheckFailure::Input(DefinitionFailure {
                issue: *issue,
                inputs,
            }),
            CheckFailure::Stopped(reason) => CheckFailure::Stopped(reason),
        },
    )
}
fn check_definitions_inner<E: InputError>(
    files: &[(&str, &[u8])],
    control: &mut Control,
) -> Result<CheckedDefinitions, (E, Vec<DefinitionIdentity>)> {
    let mut checked = CheckedDefinitions::default();
    checked.inputs = files
        .iter()
        .map(|(input, bytes)| DefinitionIdentity {
            input: (*input).into(),
            bytes_digest: sha256_digest(bytes),
            model_digest: None,
        })
        .collect();
    let result = (|| -> Result<(), E> {
        for (i, (input, bytes)) in files.iter().enumerate() {
            E::checkpoint(control, Checkpoint::DefinitionIteration)?;
            let node = crate::json::parse_definition_inner::<E>(bytes, input, control)?;
            let (vs, ds, normalized) = reader::read::<E>(&node, input, control)?;
            checked.inputs[i].model_digest = Some(sha256_digest(normalized.canonical().as_bytes()));
            for v in vs {
                E::checkpoint(control, Checkpoint::DefinitionIteration)?;
                if checked.vocabularies.contains_key(&v.namespace) {
                    let mut issue = error(
                        Code::DuplicateId,
                        input,
                        "",
                        format!("namespace `{}` が重複している", v.namespace),
                    );
                    issue.location = v.location;
                    return Err(issue.into());
                }
                checked.vocabularies.insert(v.namespace.clone(), v);
            }
            for d in ds {
                E::checkpoint(control, Checkpoint::DefinitionIteration)?;
                checked.declarations.insert(d.name.clone(), d);
            }
        }
        validate::check::<E>(&mut checked, control)
    })();
    result.map_err(|issue| (issue, checked.inputs.clone()))?;
    Ok(checked)
}

impl CheckedDefinitions {
    pub fn check_binding(&self, binding: &Binding) -> Result<(), Box<Issue>> {
        let code = match self.vocabularies.get(&binding.namespace) {
            None => Code::Reference,
            Some(v) if v.version == binding.version && v.digest == binding.digest => return Ok(()),
            Some(_) => Code::VocabularyMismatch,
        };
        Err(Box::new(Issue {
            code,
            message: format!("語彙 `{}` の binding を解決できない", binding.namespace),
            location: binding.location.clone(),
            details: Details::Empty,
        }))
    }
}
