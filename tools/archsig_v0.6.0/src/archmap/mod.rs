//! ArchMap の静的検査(入力仕様 §§1–6)。版・schema・ID・由来・語彙 binding・原始値の型・
//! 参照・補完の存在を検査し、既知値と欠測 slot を持つ内部表現を返す。

mod complete;
mod schema;
pub mod value;

use crate::canonical::{Json, sha256_digest};
use crate::issue::{Code, Details, Issue, Location};
use crate::law::CheckedLaw;
use crate::law::model::Signature;
use crate::types::Type;
use schema::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};
pub use value::Value;

pub const FORMAT: &str = "archsig.archmap/1";
pub const SEMANTICS: &str = "archsig/0.6.0";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Observed,
    Proposed,
    Specification,
}

impl Mode {
    pub fn wire(self) -> &'static str {
        match self {
            Mode::Observed => "observed",
            Mode::Proposed => "proposed",
            Mode::Specification => "specification",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    pub id: String,
    pub uri: String,
    pub revision: String,
    pub digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLocation {
    pub source: String,
    pub path: String,
    pub span: Option<(u64, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    pub id: String,
    pub mode: Mode,
    pub method: String,
    pub locations: Vec<SourceLocation>,
    pub note: Option<String>,
}

/// subject の一つの field の slot。Atom がなければ欠測で、identity と型を保持する。
#[derive(Debug, PartialEq)]
pub enum Slot {
    Known {
        atom: String,
        origin: String,
        value: Value,
        pointer: String,
    },
    Missing,
}

#[derive(Debug, PartialEq)]
pub struct Field {
    /// field の完全名。
    pub name: String,
    pub ty: Type,
    pub slot: Slot,
}

#[derive(Debug, PartialEq)]
pub struct Subject {
    pub snapshot: String,
    pub id: String,
    /// 宣言の完全名。
    pub ty: String,
    pub origin: String,
    /// 宣言順(括弧内、body の順)の全 field。
    pub fields: Vec<Field>,
    pub pointer: String,
}

impl Subject {
    pub fn field(&self, name: &str) -> Option<&Field> {
        self.fields
            .iter()
            .find(|f| f.name.rsplit('.').next() == Some(name))
    }
}

#[derive(Debug, PartialEq)]
pub struct Snapshot {
    pub id: String,
    pub origin: String,
    pub subjects: Vec<Subject>,
}

/// 検査を通った ArchMap。
#[derive(Debug)]
pub struct CheckedArchMap {
    pub bytes_digest: String,
    pub model_digest: String,
    pub vocabularies: BTreeMap<String, String>,
    pub sources: Vec<Source>,
    pub origins: Vec<Origin>,
    pub snapshots: Vec<Snapshot>,
}

impl CheckedArchMap {
    /// 欠測 slot の identity `(snapshot, subject, field)` と型。
    pub fn missing_slots(&self) -> Vec<(&str, &str, &str, &Type)> {
        let mut out = Vec::new();
        for s in &self.snapshots {
            for sub in &s.subjects {
                for f in &sub.fields {
                    if f.slot == Slot::Missing {
                        out.push((s.id.as_str(), sub.id.as_str(), f.name.as_str(), &f.ty));
                    }
                }
            }
        }
        out
    }

    pub fn subject(&self, snapshot: &str, id: &str) -> Option<&Subject> {
        self.snapshots
            .iter()
            .find(|s| s.id == snapshot)?
            .subjects
            .iter()
            .find(|s| s.id == id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchMapFailure {
    pub issue: Issue,
    pub bytes_digest: String,
}


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

/// ArchMap を Law の語彙で検査する。深い入れ子の値でも呼出し側のスタックを使い切らないよう、
/// 再帰は stacker を通す。
#[allow(clippy::result_large_err)]
pub fn check_archmap(bytes: &[u8], law: &CheckedLaw) -> Result<CheckedArchMap, ArchMapFailure> {
    let bytes_digest = sha256_digest(bytes);
    let fail = |i: Box<Issue>| ArchMapFailure {
        issue: *i,
        bytes_digest: bytes_digest.clone(),
    };
    let root = crate::json::parse(bytes).map_err(fail)?;
    let raw = read_document(&root).map_err(fail)?;
    let mut checked = check_document(raw, law).map_err(fail)?;
    checked.bytes_digest = bytes_digest.clone();
    checked.model_digest = sha256_digest(model_json(&checked).canonical().as_bytes());
    Ok(checked)
}

/// 集合表を ID・reading 名順へ、Set・Map の値を canonical 値順へ並べた ArchMap。
pub fn model_json(a: &CheckedArchMap) -> Json {
    let mut sources: Vec<&Source> = a.sources.iter().collect();
    sources.sort_by(|x, y| x.id.cmp(&y.id));
    let mut origins: Vec<&Origin> = a.origins.iter().collect();
    origins.sort_by(|x, y| x.id.cmp(&y.id));
    let mut snapshots: Vec<&Snapshot> = a.snapshots.iter().collect();
    snapshots.sort_by(|x, y| x.id.cmp(&y.id));
    let vocabularies = a
        .vocabularies
        .iter()
        .map(|(r, d)| {
            Json::obj([
                ("reading", Json::str(r.clone())),
                ("digest", Json::str(d.clone())),
            ])
        })
        .collect();
    let sources = sources
        .into_iter()
        .map(|s| {
            Json::obj([
                ("id", Json::str(s.id.clone())),
                ("uri", Json::str(s.uri.clone())),
                ("revision", Json::str(s.revision.clone())),
                ("digest", Json::str(s.digest.clone())),
            ])
        })
        .collect();
    let origins = origins
        .into_iter()
        .map(|o| {
            let mut m = BTreeMap::new();
            m.insert("id".to_owned(), Json::str(o.id.clone()));
            m.insert("mode".to_owned(), Json::str(o.mode.wire()));
            m.insert("method".to_owned(), Json::str(o.method.clone()));
            m.insert(
                "locations".to_owned(),
                Json::Arr(
                    o.locations
                        .iter()
                        .map(|l| {
                            let mut m = BTreeMap::new();
                            m.insert("source".to_owned(), Json::str(l.source.clone()));
                            m.insert("path".to_owned(), Json::str(l.path.clone()));
                            if let Some((s, e)) = l.span {
                                m.insert(
                                    "span".to_owned(),
                                    Json::Arr(vec![Json::Nat(s), Json::Nat(e)]),
                                );
                            }
                            Json::Obj(m)
                        })
                        .collect(),
                ),
            );
            if let Some(n) = &o.note {
                m.insert("note".to_owned(), Json::str(n.clone()));
            }
            Json::Obj(m)
        })
        .collect();
    let snapshots = snapshots
        .into_iter()
        .map(|s| {
            let mut subjects: Vec<&Subject> = s.subjects.iter().collect();
            subjects.sort_by(|x, y| x.id.cmp(&y.id));
            let mut atoms: Vec<(String, Json)> = Vec::new();
            for sub in &s.subjects {
                for f in &sub.fields {
                    if let Slot::Known {
                        atom,
                        origin,
                        value,
                        ..
                    } = &f.slot
                    {
                        atoms.push((
                            atom.clone(),
                            Json::obj([
                                ("id", Json::str(atom.clone())),
                                ("subject", Json::str(sub.id.clone())),
                                ("field", Json::str(f.name.clone())),
                                ("value", value.canonical_json()),
                                ("origin", Json::str(origin.clone())),
                            ]),
                        ));
                    }
                }
            }
            atoms.sort_by(|x, y| x.0.cmp(&y.0));
            Json::obj([
                ("id", Json::str(s.id.clone())),
                ("origin", Json::str(s.origin.clone())),
                (
                    "subjects",
                    Json::Arr(
                        subjects
                            .into_iter()
                            .map(|x| {
                                Json::obj([
                                    ("id", Json::str(x.id.clone())),
                                    ("type", Json::str(x.ty.clone())),
                                    ("origin", Json::str(x.origin.clone())),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "atoms",
                    Json::Arr(atoms.into_iter().map(|(_, j)| j).collect()),
                ),
            ])
        })
        .collect();
    Json::obj([
        ("format", Json::str(FORMAT)),
        ("semantics", Json::str(SEMANTICS)),
        ("vocabularies", Json::Arr(vocabularies)),
        ("sources", Json::Arr(sources)),
        ("origins", Json::Arr(origins)),
        ("snapshots", Json::Arr(snapshots)),
    ])
}

/// 宣言の reading と、型から推移的に参照する宣言の reading。
fn required_readings(law: &CheckedLaw, types: &BTreeSet<String>) -> BTreeSet<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<String> = types.iter().cloned().collect();
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(decl) = law.declarations.get(&name) else {
            continue;
        };
        let mut field_types: Vec<&Type> = Vec::new();
        match &decl.signature {
            Signature::Data { constructors } => {
                field_types.extend(constructors.iter().flat_map(|c| c.args.iter()))
            }
            sig => {
                if let Some((p, m)) = sig.record_fields() {
                    field_types.extend(p.iter().chain(m).map(|f| &f.ty));
                }
            }
        }
        for t in field_types {
            t.clone().any(&mut |t| {
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
        .map(|n| law.declarations[n].reading.clone())
        .collect()
}

fn check_document(raw: RawDocument, law: &CheckedLaw) -> AResult<CheckedArchMap> {
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
            match law.declarations.get(&s.ty).map(|d| d.signature.kind()) {
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
    let manifests: HashMap<&str, &str> = law
        .vocabularies
        .iter()
        .map(|v| (v.reading.as_str(), v.digest.as_str()))
        .collect();
    let mut bound = BTreeMap::new();
    for (i, (reading, digest)) in raw.vocabularies.iter().enumerate() {
        let ptr = format!("/vocabularies/{i}");
        match manifests.get(reading.as_str()) {
            None => {
                return Err(issue(
                    Code::VocabularyMismatch,
                    &format!("{ptr}/reading"),
                    format!("Law に reading `{reading}` がない"),
                ));
            }
            Some(d) if d != digest => {
                return Err(issue(
                    Code::VocabularyMismatch,
                    &format!("{ptr}/digest"),
                    format!("reading `{reading}` の語彙 digest が Law の manifest と異なる"),
                ));
            }
            _ => {}
        }
        bound.insert(reading.clone(), digest.clone());
    }
    for reading in required_readings(law, &subject_types) {
        if !bound.contains_key(&reading) {
            return Err(issue(
                Code::VocabularyMismatch,
                "/vocabularies",
                format!("reading `{reading}` の binding がない"),
            ));
        }
    }
    let snapshots = value::check_snapshots(&raw.snapshots, law)?;
    complete::check_completion(&snapshots, law)?;
    Ok(CheckedArchMap {
        bytes_digest: String::new(),
        model_digest: String::new(),
        vocabularies: bound,
        sources: raw.sources.into_iter().map(|s| s.0).collect(),
        origins: raw.origins.into_iter().map(|o| o.0).collect(),
        snapshots,
    })
}
