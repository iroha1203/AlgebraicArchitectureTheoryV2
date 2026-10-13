//! ArchMap の静的検査(入力仕様 §§1–6)。版・schema・ID・由来・語彙 binding・原始値の型・
//! 参照・補完の存在を検査し、既知値と欠測 slot を持つ内部表現を返す。

mod canonical;
mod complete;
mod model;
mod schema;
pub mod value;

use crate::canonical::{Json, sha256_digest};
use crate::definition::model::{Binding, CheckedDefinitions, PrimitiveSignature};
use crate::issue::{Code, Details, Issue, Location};
use crate::types::Type;
pub use canonical::model_json;
pub use model::{
    ArchMapFailure, CheckedArchMap, Field, Mode, Origin, Slot, Snapshot, Source, SourceLocation,
    Subject,
};
use schema::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};
pub use value::Value;

pub const FORMAT: &str = "archsig.archmap/2";
pub const SEMANTICS: &str = "archsig/0.6.0";

pub(crate) fn issue(code: Code, pointer: &str, message: impl Into<String>) -> Box<Issue> {
    Box::new(Issue {
        code,
        message: message.into(),
        location: Location::ArchMap {
            pointer: pointer.to_owned(),
            span: None,
        },
        details: Details::Empty,
    })
}

pub(crate) type AResult<T> = Result<T, Box<Issue>>;

/// ArchMap を共通 Atom 定義の語彙で検査する。深い入れ子の値でも呼出し側のスタックを使い切らないよう、
/// 再帰は stacker を通す。
#[allow(clippy::result_large_err)]
pub fn check_archmap(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
) -> Result<CheckedArchMap, ArchMapFailure> {
    let bytes_digest = sha256_digest(bytes);
    let fail = |i: Box<Issue>| ArchMapFailure {
        issue: *i,
        bytes_digest: bytes_digest.clone(),
    };
    let root = crate::json::parse(bytes).map_err(fail)?;
    let raw = read_document(&root).map_err(fail)?;
    let mut checked = check_document(raw, definitions).map_err(fail)?;
    checked.bytes_digest = bytes_digest.clone();
    checked.model_digest = sha256_digest(model_json(&checked).canonical().as_bytes());
    Ok(checked)
}

/// subject と、その field 型から推移的に参照する宣言の namespace。
fn required_namespaces(
    definitions: &CheckedDefinitions,
    types: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<String> = types.iter().cloned().collect();
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(decl) = definitions.declarations.get(&name) else {
            continue;
        };
        let mut field_types: Vec<&Type> = Vec::new();
        match &decl.signature {
            PrimitiveSignature::Data { constructors } => {
                field_types.extend(constructors.iter().flat_map(|c| c.arguments.iter()))
            }
            sig => {
                if let Some((p, m)) = sig.record_fields() {
                    field_types.extend(p.iter().chain(m).map(|f| &f.ty));
                }
            }
        }
        for t in field_types {
            t.any(&mut |t| {
                match t {
                    Type::Ref(n) | Type::Owned(n, _) | Type::Data(n) => stack.push(n.clone()),
                    Type::Path(a, b) => {
                        stack.push(a.clone());
                        stack.push(b.clone());
                    }
                    _ => {}
                }
                false
            });
        }
    }
    seen.iter()
        .map(|n| definitions.declarations[n].namespace.clone())
        .collect()
}

fn check_document(raw: RawDocument, definitions: &CheckedDefinitions) -> AResult<CheckedArchMap> {
    // 由来の参照と mode。
    let sources: HashMap<&str, &Source> = raw
        .sources
        .iter()
        .map(|s| (s.0.id.as_str(), &s.0))
        .collect();
    for (o, ptr) in &raw.origins {
        for (i, l) in o.locations.iter().enumerate() {
            if !sources.contains_key(l.source.as_str()) {
                return Err(issue(
                    Code::Reference,
                    &format!("{ptr}/locations/{i}/source"),
                    format!("source `{}` がない", l.source),
                ));
            }
        }
    }
    let origins: HashMap<&str, &Origin> = raw
        .origins
        .iter()
        .map(|o| (o.0.id.as_str(), &o.0))
        .collect();
    let mode_of = |id: &str, ptr: &str| -> AResult<Mode> {
        origins
            .get(id)
            .map(|o| o.mode)
            .ok_or_else(|| issue(Code::Reference, ptr, format!("origin `{id}` がない")))
    };
    // subject の型と、語彙 binding。
    let mut subject_types = BTreeSet::new();
    for snap in &raw.snapshots {
        let mode = mode_of(&snap.origin, &format!("{}/origin", snap.pointer))?;
        for s in &snap.subjects {
            let sm = mode_of(&s.origin, &format!("{}/origin", s.pointer))?;
            if sm != mode {
                return Err(issue(
                    Code::Reference,
                    &format!("{}/origin", s.pointer),
                    "subject の origin.mode が snapshot と異なる",
                ));
            }
            match definitions
                .declarations
                .get(&s.ty)
                .map(|d| d.signature.kind())
            {
                Some("entity" | "arrow" | "correspondence") => {}
                _ => {
                    return Err(issue(
                        Code::Reference,
                        &format!("{}/type", s.pointer),
                        format!("`{}` は entity・arrow・correspondence の宣言ではない", s.ty),
                    ));
                }
            }
            subject_types.insert(s.ty.clone());
        }
        for a in &snap.atoms {
            let am = mode_of(&a.origin, &format!("{}/origin", a.pointer))?;
            if am != mode {
                return Err(issue(
                    Code::Reference,
                    &format!("{}/origin", a.pointer),
                    "Atom の origin.mode が snapshot と異なる",
                ));
            }
        }
    }
    let mut bound = BTreeMap::new();
    for (i, binding) in raw.vocabularies.iter().enumerate() {
        let ptr = format!("/vocabularies/{i}");
        let Some(vocabulary) = definitions.vocabularies.get(&binding.namespace) else {
            return Err(issue(
                Code::Reference,
                &format!("{ptr}/namespace"),
                format!("namespace `{}` の定義がない", binding.namespace),
            ));
        };
        if vocabulary.version != binding.version {
            return Err(issue(
                Code::VocabularyMismatch,
                &format!("{ptr}/version"),
                format!(
                    "namespace `{}` の語彙 version が定義と異なる",
                    binding.namespace
                ),
            ));
        }
        if vocabulary.digest != binding.digest {
            return Err(issue(
                Code::VocabularyMismatch,
                &format!("{ptr}/digest"),
                format!(
                    "namespace `{}` の語彙 digest が定義と異なる",
                    binding.namespace
                ),
            ));
        }
        bound.insert(binding.namespace.clone(), binding.clone());
    }
    for namespace in required_namespaces(definitions, &subject_types) {
        if !bound.contains_key(&namespace) {
            return Err(issue(
                Code::VocabularyMismatch,
                "/vocabularies",
                format!("namespace `{namespace}` の binding がない"),
            ));
        }
    }
    let snapshots = value::check_snapshots(&raw.snapshots, definitions)?;
    complete::check_completion(&snapshots, definitions)?;
    Ok(CheckedArchMap {
        bytes_digest: String::new(),
        model_digest: String::new(),
        vocabularies: bound,
        sources: raw.sources.into_iter().map(|s| s.0).collect(),
        origins: raw.origins.into_iter().map(|o| o.0).collect(),
        snapshots,
    })
}
