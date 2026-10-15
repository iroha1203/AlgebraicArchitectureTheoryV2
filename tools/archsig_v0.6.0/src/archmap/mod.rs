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
use crate::json::InputError;
use crate::observed::control::{CheckFailure, Checkpoint, Control};
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
    check_archmap_inner::<Box<Issue>>(bytes, definitions, &mut Control::unlimited()).map_err(
        |(issue, bytes_digest)| ArchMapFailure {
            issue: *issue,
            bytes_digest,
        },
    )
}
#[allow(clippy::result_large_err)]
pub fn check_archmap_controlled(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<CheckedArchMap, CheckFailure<ArchMapFailure>> {
    check_archmap_inner::<CheckFailure<Box<Issue>>>(bytes, definitions, control).map_err(
        |(failure, bytes_digest)| match failure {
            CheckFailure::Input(issue) => CheckFailure::Input(ArchMapFailure {
                issue: *issue,
                bytes_digest,
            }),
            CheckFailure::Stopped(reason) => CheckFailure::Stopped(reason),
        },
    )
}
fn check_archmap_inner<E: InputError>(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<CheckedArchMap, (E, String)> {
    let bytes_digest = sha256_digest(bytes);
    let fail = |issue| (issue, bytes_digest.clone());
    let root = crate::json::parse_inner::<E>(bytes, control, Checkpoint::ArchMapIteration)
        .map_err(fail)?;
    let raw = read_document::<E>(&root, control).map_err(fail)?;
    let mut checked = check_document::<E>(raw, definitions, control).map_err(fail)?;
    checked.bytes_digest = bytes_digest.clone();
    let model = canonical::model_json_controlled::<E>(&checked, control).map_err(fail)?;
    let canonical = model
        .canonical_controlled::<E>(control, Checkpoint::ArchMapCanonical)
        .map_err(fail)?;
    E::checkpoint(control, Checkpoint::ArchMapCanonical).map_err(fail)?;
    checked.model_digest = sha256_digest(canonical.as_bytes());
    E::checkpoint(control, Checkpoint::ArchMapCanonical).map_err(fail)?;
    E::checkpoint(control, Checkpoint::ArchMapIteration).map_err(fail)?;
    Ok(checked)
}

/// subject と、その field 型から推移的に参照する宣言の namespace。
fn required_namespaces<E: InputError>(
    definitions: &CheckedDefinitions,
    types: &BTreeSet<String>,
    control: &mut Control,
) -> Result<BTreeSet<String>, E> {
    let point = Checkpoint::ArchMapSchema;
    E::checkpoint(control, point)?;
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut stack = Vec::new();
    for ty in types {
        E::checkpoint(control, point)?;
        stack.push(ty.clone());
        E::checkpoint(control, point)?;
    }
    while let Some(name) = stack.pop() {
        E::checkpoint(control, point)?;
        if seen.insert(name.clone())
            && let Some(declaration) = definitions.declarations.get(&name)
        {
            let mut field_types: Vec<&Type> = Vec::new();
            match &declaration.signature {
                PrimitiveSignature::Data { constructors } => {
                    for constructor in constructors {
                        E::checkpoint(control, point)?;
                        for argument in &constructor.arguments {
                            E::checkpoint(control, point)?;
                            field_types.push(argument);
                            E::checkpoint(control, point)?;
                        }
                        E::checkpoint(control, point)?;
                    }
                }
                signature => {
                    if let Some((parameters, members)) = signature.record_fields() {
                        for field in parameters.iter().chain(members) {
                            E::checkpoint(control, point)?;
                            field_types.push(&field.ty);
                            E::checkpoint(control, point)?;
                        }
                    }
                }
            }
            for ty in field_types {
                E::checkpoint(control, point)?;
                ty.any_controlled::<E>(
                    &mut |ty| {
                        match ty {
                            Type::Ref(name) | Type::Owned(name, _) | Type::Data(name) => {
                                stack.push(name.clone())
                            }
                            Type::Path(source, target) => {
                                stack.push(source.clone());
                                stack.push(target.clone());
                            }
                            _ => {}
                        }
                        false
                    },
                    control,
                    point,
                )?;
                E::checkpoint(control, point)?;
            }
        }
        E::checkpoint(control, point)?;
    }
    let mut namespaces = BTreeSet::new();
    for name in seen {
        E::checkpoint(control, point)?;
        namespaces.insert(definitions.declarations[&name].namespace.clone());
        E::checkpoint(control, point)?;
    }
    E::checkpoint(control, point)?;
    Ok(namespaces)
}

fn check_document<E: InputError>(
    raw: RawDocument,
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<CheckedArchMap, E> {
    E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    let result = check_document_inner::<E>(raw, definitions, control);
    E::finish(result, control, Checkpoint::ArchMapSchema)
}

fn check_document_inner<E: InputError>(
    raw: RawDocument,
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<CheckedArchMap, E> {
    // 由来の参照と mode。
    let mut sources: HashMap<&str, &Source> = HashMap::new();
    for (source, _) in &raw.sources {
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
        sources.insert(source.id.as_str(), source);
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    }
    for (o, ptr) in &raw.origins {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        for (i, l) in o.locations.iter().enumerate() {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            if !sources.contains_key(l.source.as_str()) {
                return Err((issue(
                    Code::Reference,
                    &format!("{ptr}/locations/{i}/source"),
                    format!("source `{}` がない", l.source),
                ))
                .into());
            }
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        }
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
    }
    let mut origins: HashMap<&str, &Origin> = HashMap::new();
    for (origin, _) in &raw.origins {
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
        origins.insert(origin.id.as_str(), origin);
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    }
    let mode_of = |id: &str, ptr: &str| -> AResult<Mode> {
        origins
            .get(id)
            .map(|o| o.mode)
            .ok_or_else(|| issue(Code::Reference, ptr, format!("origin `{id}` がない")))
    };
    // subject の型と、語彙 binding。
    let mut subject_types = BTreeSet::new();
    for snap in &raw.snapshots {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let mode = mode_of(&snap.origin, &format!("{}/origin", snap.pointer))?;
        for s in &snap.subjects {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            let sm = mode_of(&s.origin, &format!("{}/origin", s.pointer))?;
            if sm != mode {
                return Err((issue(
                    Code::Reference,
                    &format!("{}/origin", s.pointer),
                    "subject の origin.mode が snapshot と異なる",
                ))
                .into());
            }
            match definitions
                .declarations
                .get(&s.ty)
                .map(|d| d.signature.kind())
            {
                Some("entity" | "arrow" | "correspondence") => {}
                _ => {
                    return Err((issue(
                        Code::Reference,
                        &format!("{}/type", s.pointer),
                        format!("`{}` は entity・arrow・correspondence の宣言ではない", s.ty),
                    ))
                    .into());
                }
            }
            subject_types.insert(s.ty.clone());
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        }
        for a in &snap.atoms {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            let am = mode_of(&a.origin, &format!("{}/origin", a.pointer))?;
            if am != mode {
                return Err((issue(
                    Code::Reference,
                    &format!("{}/origin", a.pointer),
                    "Atom の origin.mode が snapshot と異なる",
                ))
                .into());
            }
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        }
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
    }
    let mut bound = BTreeMap::new();
    for (i, binding) in raw.vocabularies.iter().enumerate() {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let ptr = format!("/vocabularies/{i}");
        let Some(vocabulary) = definitions.vocabularies.get(&binding.namespace) else {
            return Err((issue(
                Code::Reference,
                &format!("{ptr}/namespace"),
                format!("namespace `{}` の定義がない", binding.namespace),
            ))
            .into());
        };
        if vocabulary.version != binding.version {
            return Err((issue(
                Code::VocabularyMismatch,
                &format!("{ptr}/version"),
                format!(
                    "namespace `{}` の語彙 version が定義と異なる",
                    binding.namespace
                ),
            ))
            .into());
        }
        if vocabulary.digest != binding.digest {
            return Err((issue(
                Code::VocabularyMismatch,
                &format!("{ptr}/digest"),
                format!(
                    "namespace `{}` の語彙 digest が定義と異なる",
                    binding.namespace
                ),
            ))
            .into());
        }
        bound.insert(binding.namespace.clone(), binding.clone());
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
    }
    for namespace in required_namespaces::<E>(definitions, &subject_types, control)? {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        if !bound.contains_key(&namespace) {
            return Err((issue(
                Code::VocabularyMismatch,
                "/vocabularies",
                format!("namespace `{namespace}` の binding がない"),
            ))
            .into());
        }
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
    }
    let snapshots = value::check_snapshots::<E>(&raw.snapshots, definitions, control)?;
    complete::check_completion::<E>(&snapshots, definitions, control)?;
    let mut sources = Vec::new();
    for (source, _) in raw.sources {
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
        sources.push(source);
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    }
    let mut origins = Vec::new();
    for (origin, _) in raw.origins {
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
        origins.push(origin);
        E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    }
    Ok(CheckedArchMap {
        bytes_digest: String::new(),
        model_digest: String::new(),
        vocabularies: bound,
        sources,
        origins,
        snapshots,
    })
}
