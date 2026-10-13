//! 共通 Atom 定義の schema、namespace 登録、依存と原始型の検査。
pub mod model;
mod primitive;
mod reader;
mod validate;
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
    let mut checked = CheckedDefinitions::default();
    checked.inputs = files
        .iter()
        .map(|(input, bytes)| DefinitionIdentity {
            input: (*input).into(),
            bytes_digest: sha256_digest(bytes),
            model_digest: None,
        })
        .collect();
    let result = (|| {
        for (i, (input, bytes)) in files.iter().enumerate() {
            let node = crate::json::parse_definition(bytes, input)?;
            let (vs, ds, normalized) = reader::read(&node, input)?;
            checked.inputs[i].model_digest = Some(sha256_digest(normalized.canonical().as_bytes()));
            for v in vs {
                if checked.vocabularies.contains_key(&v.namespace) {
                    let mut issue = error(
                        Code::DuplicateId,
                        input,
                        "",
                        format!("namespace `{}` が重複している", v.namespace),
                    );
                    issue.location = v.location;
                    return Err(issue);
                }
                checked.vocabularies.insert(v.namespace.clone(), v);
            }
            for d in ds {
                checked.declarations.insert(d.name.clone(), d);
            }
        }
        validate::check(&mut checked)
    })();
    result.map_err(|issue| DefinitionFailure {
        issue: *issue,
        inputs: checked.inputs.clone(),
    })?;
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
