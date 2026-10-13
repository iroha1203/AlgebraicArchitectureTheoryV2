//! `check` の result.json(結果仕様 §1、§6)。

use crate::canonical::Json;
use crate::definition::{PrimitiveDeclaration, PrimitiveSignature, Vocabulary};
use crate::issue::{Code, Details, Issue, Location};
use crate::law::ast::Role;
use crate::law::model::{DeclarationInfo, ExpressionKind, SuppliedRule};
use std::collections::{BTreeMap, BTreeSet};

/// RunStatus と終了コード(実行仕様 §6)。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Complete,
    Invalid,
    Unsupported,
    Interrupted,
    Error,
}

impl Status {
    pub fn wire(self) -> &'static str {
        match self {
            Status::Complete => "complete",
            Status::Invalid => "invalid",
            Status::Unsupported => "unsupported",
            Status::Interrupted => "interrupted",
            Status::Error => "error",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Signal {
    Int,
    Term,
}

impl Signal {
    pub fn wire(self) -> &'static str {
        match self {
            Signal::Int => "SIGINT",
            Signal::Term => "SIGTERM",
        }
    }
}

/// 入力の不正のほか、CLI・I/O・内部障害・中断の理由。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResultIssue {
    Input(Issue),
    Usage {
        argument: String,
        message: String,
    },
    Io {
        operation: &'static str,
        path: String,
        message: String,
    },
    Internal {
        operation: String,
        message: String,
    },
    Cancelled(Signal),
}

impl ResultIssue {
    pub fn code(&self) -> &'static str {
        match self {
            ResultIssue::Input(i) => code_name(i.code),
            ResultIssue::Usage { .. } => "usage",
            ResultIssue::Io { .. } => "io",
            ResultIssue::Internal { .. } => "internal",
            ResultIssue::Cancelled(_) => "cancelled",
        }
    }

    /// issues の並び(結果仕様 §6): code、location.input、pointer または span 開始。
    fn sort_key(&self) -> (String, String, String, usize) {
        let (input, pointer, start) = match self {
            ResultIssue::Input(i) => match &i.location {
                Location::Law { span } => ("law".to_owned(), String::new(), span.0),
                Location::ArchMap { pointer, span } => (
                    "archmap".to_owned(),
                    pointer.clone(),
                    span.map_or(0, |s| s.0),
                ),
                Location::Definition {
                    input,
                    pointer,
                    span,
                } => (input.clone(), pointer.clone(), span.map_or(0, |s| s.0)),
            },
            _ => (String::new(), String::new(), 0),
        };
        (self.code().to_owned(), input, pointer, start)
    }

    pub fn wire(&self) -> Json {
        let mut m = BTreeMap::new();
        m.insert("code".to_owned(), Json::str(self.code()));
        m.insert("dependencies".to_owned(), Json::Arr(vec![]));
        m.insert("missing".to_owned(), Json::Arr(vec![]));
        let (message, details) = match self {
            ResultIssue::Input(i) => {
                m.insert("location".to_owned(), location_wire(&i.location));
                let details = match &i.details {
                    Details::Empty => Json::Obj(BTreeMap::new()),
                    Details::Type { expected, actual } => {
                        Json::obj([("expected", expected.wire()), ("actual", actual.wire())])
                    }
                    Details::Version {
                        found_format,
                        found_semantics,
                    } => {
                        let mut d = BTreeMap::new();
                        d.insert("found_format".to_owned(), Json::str(found_format.clone()));
                        if let Some(s) = found_semantics {
                            d.insert("found_semantics".to_owned(), Json::str(s.clone()));
                        }
                        Json::Obj(d)
                    }
                };
                (i.message.clone(), details)
            }
            ResultIssue::Usage { argument, message } => (
                message.clone(),
                Json::obj([("argument", Json::str(argument.clone()))]),
            ),
            ResultIssue::Io {
                operation,
                path,
                message,
            } => (
                message.clone(),
                Json::obj([
                    ("operation", Json::str(*operation)),
                    ("path", Json::str(path.clone())),
                ]),
            ),
            ResultIssue::Internal { operation, message } => (
                message.clone(),
                Json::obj([("operation", Json::str(operation.clone()))]),
            ),
            ResultIssue::Cancelled(s) => (
                "シグナルを受けて中断した".to_owned(),
                Json::obj([("signal", Json::str(s.wire()))]),
            ),
        };
        m.insert("message".to_owned(), Json::Str(message));
        m.insert("details".to_owned(), details);
        Json::Obj(m)
    }
}

pub fn code_name(code: Code) -> &'static str {
    match code {
        Code::Syntax => "syntax",
        Code::DuplicateKey => "duplicate_key",
        Code::DuplicateId => "duplicate_id",
        Code::DuplicateFact => "duplicate_fact",
        Code::Type => "type",
        Code::Reference => "reference",
        Code::Cycle => "cycle",
        Code::VocabularyMismatch => "vocabulary_mismatch",
        Code::InconsistentObservation => "inconsistent_observation",
        Code::UnsupportedVersion => "unsupported_version",
    }
}

pub fn location_wire(l: &Location) -> Json {
    match l {
        Location::Law { span } => {
            Json::obj([("input", Json::str("law")), ("span", span_wire(*span))])
        }
        Location::ArchMap { pointer, span } => {
            let mut m = BTreeMap::new();
            m.insert("input".to_owned(), Json::str("archmap"));
            m.insert("pointer".to_owned(), Json::str(pointer.clone()));
            if let Some(s) = span {
                m.insert("span".to_owned(), span_wire(*s));
            }
            Json::Obj(m)
        }
        Location::Definition {
            input,
            pointer,
            span,
        } => {
            let mut m = BTreeMap::new();
            m.insert("input".to_owned(), Json::str(input.clone()));
            m.insert("pointer".to_owned(), Json::str(pointer.clone()));
            if let Some(s) = span {
                m.insert("span".to_owned(), span_wire(*s));
            }
            Json::Obj(m)
        }
    }
}

fn span_wire(span: (usize, usize)) -> Json {
    Json::Arr(vec![Json::Nat(span.0 as u64), Json::Nat(span.1 as u64)])
}

fn law_location(span: (usize, usize)) -> Json {
    location_wire(&Location::Law { span })
}

fn params_wire(ps: &[(String, crate::types::Type)]) -> Json {
    Json::Arr(
        ps.iter()
            .map(|(n, t)| Json::obj([("name", Json::str(n.clone())), ("type", t.wire())]))
            .collect(),
    )
}

pub fn declaration_wire(d: &DeclarationInfo) -> Json {
    let mut m = BTreeMap::new();
    m.insert("name".to_owned(), Json::str(d.name.clone()));
    m.insert("kind".to_owned(), Json::str(d.kind));
    m.insert("parameters".to_owned(), params_wire(&d.parameters));
    m.insert("fields".to_owned(), params_wire(&d.fields));
    m.insert(
        "vocabularies".to_owned(),
        Json::Arr(d.vocabularies.iter().map(|b| b.wire()).collect()),
    );
    if let Some(t) = &d.returns {
        m.insert("returns".to_owned(), t.wire());
    }
    if let Some(r) = d.role {
        m.insert(
            "role".to_owned(),
            Json::str(match r {
                Role::Required => "required",
                Role::Optional => "optional",
            }),
        );
    }
    m.insert("location".to_owned(), law_location(d.span));
    m.insert(
        "dependencies".to_owned(),
        Json::Arr(d.dependencies.iter().cloned().map(Json::Str).collect()),
    );
    let references = d
        .references
        .iter()
        .map(|(s, n)| {
            Json::obj([
                ("location", law_location(*s)),
                ("name", Json::str(n.clone())),
            ])
        })
        .collect();
    let expressions = d
        .expressions
        .iter()
        .map(|e| {
            let kind = match e.kind {
                ExpressionKind::Guard => "guard",
                ExpressionKind::Body => "body",
                ExpressionKind::Read => "read",
                ExpressionKind::RelationLeft => "relation_left",
                ExpressionKind::RelationRight => "relation_right",
            };
            Json::obj([
                ("kind", Json::str(kind)),
                ("location", law_location(e.span)),
                ("type", e.ty.wire()),
            ])
        })
        .collect();
    let supplied = d
        .supplied
        .iter()
        .map(|r| match r {
            SuppliedRule::GuardTrue { span } => Json::obj([
                ("rule", Json::str("guard_true")),
                ("location", law_location(*span)),
            ]),
            SuppliedRule::LocalDeclared { span } => Json::obj([
                ("rule", Json::str("local_declared")),
                ("location", law_location(*span)),
            ]),
            SuppliedRule::LocalSupport { span } => Json::obj([
                ("rule", Json::str("local_support")),
                ("location", law_location(*span)),
            ]),
            SuppliedRule::SameNameAlignment { span, pairs } => Json::obj([
                ("rule", Json::str("same_name_alignment")),
                ("location", law_location(*span)),
                (
                    "pairs",
                    Json::Arr(
                        pairs
                            .iter()
                            .map(|(a, b)| {
                                Json::Arr(vec![Json::str(a.clone()), Json::str(b.clone())])
                            })
                            .collect(),
                    ),
                ),
            ]),
        })
        .collect();
    m.insert(
        "resolution".to_owned(),
        Json::obj([
            ("references", Json::Arr(references)),
            ("expressions", Json::Arr(expressions)),
            ("supplied", Json::Arr(supplied)),
        ]),
    );
    Json::Obj(m)
}

fn declaration_name(j: &Json) -> &str {
    let Json::Obj(m) = j else {
        unreachable!("宣言serializerはobjectを作る")
    };
    let Json::Str(name) = &m["name"] else {
        unreachable!("宣言名は文字列")
    };
    name
}

/// 独立原始表の表示用metadata。位置は定義のPointerをそのまま使う。
pub fn primitive_declarations_wire(d: &PrimitiveDeclaration) -> Vec<Json> {
    let row = |name: &str,
               kind: &str,
               params: Vec<(String, crate::types::Type)>,
               fields: Vec<(String, crate::types::Type)>,
               location: &Location,
               references: &[(Location, String)],
               supplied: Vec<Json>| {
        let mut references = references.to_vec();
        references.sort_by(|a, b| location_pointer(&a.0).cmp(location_pointer(&b.0)));
        let dependencies: BTreeSet<_> = references.iter().map(|(_, n)| n.clone()).collect();
        Json::obj([
            ("name", Json::str(name)),
            ("kind", Json::str(kind)),
            ("parameters", params_wire(&params)),
            ("fields", params_wire(&fields)),
            ("location", location_wire(location)),
            (
                "dependencies",
                Json::Arr(dependencies.into_iter().map(Json::Str).collect()),
            ),
            ("vocabularies", Json::Arr(vec![])),
            (
                "resolution",
                Json::obj([
                    (
                        "references",
                        Json::Arr(
                            references
                                .iter()
                                .map(|(l, n)| {
                                    Json::obj([
                                        ("location", location_wire(l)),
                                        ("name", Json::str(n.clone())),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                    ("expressions", Json::Arr(vec![])),
                    ("supplied", Json::Arr(supplied)),
                ]),
            ),
        ])
    };
    let pairs = |fields: &[crate::definition::Field]| {
        fields
            .iter()
            .map(|f| (f.name.clone(), f.ty.clone()))
            .collect()
    };
    let (params, fields) = d
        .signature
        .record_fields()
        .map(|(p, f)| (pairs(p), pairs(f)))
        .unwrap_or_default();
    let supplied = match &d.signature {
        PrimitiveSignature::Correspondence { implicit, .. } if !implicit.is_empty() => {
            vec![Json::obj([
                ("rule", Json::str("same_name_alignment")),
                ("location", location_wire(&d.location)),
                (
                    "pairs",
                    Json::Arr(
                        implicit
                            .iter()
                            .map(|(a, b)| {
                                Json::Arr(vec![Json::str(a.clone()), Json::str(b.clone())])
                            })
                            .collect(),
                    ),
                ),
            ])]
        }
        _ => vec![],
    };
    let mut rows = vec![row(
        &d.name,
        d.signature.kind(),
        params,
        fields,
        &d.location,
        &d.references,
        supplied,
    )];
    if let PrimitiveSignature::Data { constructors } = &d.signature {
        for c in constructors {
            let prefix = format!("{}/", location_pointer(&c.location));
            let references: Vec<_> = d
                .references
                .iter()
                .filter(|(l, _)| location_pointer(l).starts_with(&prefix))
                .cloned()
                .collect();
            rows.push(row(
                &format!("{}.{}", d.name, c.name),
                "data",
                c.arguments
                    .iter()
                    .enumerate()
                    .map(|(i, t)| (format!("arg{i}"), t.clone()))
                    .collect(),
                vec![],
                &c.location,
                &references,
                vec![],
            ));
        }
    }
    rows
}

fn location_pointer(l: &Location) -> &str {
    match l {
        Location::Definition { pointer, .. } | Location::ArchMap { pointer, .. } => pointer,
        Location::Law { .. } => "",
    }
}

/// 開始時に読んだ入力の識別。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputIdentity {
    pub id: String,
    pub kind: &'static str,
    pub read: bool,
    pub bytes_digest: Option<String>,
    pub model_digest: Option<String>,
    pub path: Option<String>,
}

impl InputIdentity {
    fn wire(&self) -> Json {
        let mut m = BTreeMap::new();
        m.insert("id".to_owned(), Json::str(self.id.clone()));
        m.insert("kind".to_owned(), Json::str(self.kind));
        m.insert(
            "state".to_owned(),
            Json::str(if self.read { "read" } else { "unread" }),
        );
        if let Some(d) = &self.bytes_digest {
            m.insert("bytes_digest".to_owned(), Json::str(d.clone()));
        }
        if let Some(d) = &self.model_digest {
            m.insert("model_digest".to_owned(), Json::str(d.clone()));
        }
        if let Some(p) = &self.path {
            m.insert("path".to_owned(), Json::str(p.clone()));
        }
        Json::Obj(m)
    }
}

/// result.json の内容。
#[derive(Debug)]
pub struct CheckResult {
    pub status: Status,
    pub exit_code: u8,
    pub inputs: Vec<InputIdentity>,
    pub declarations: Vec<DeclarationInfo>,
    pub primitives: Vec<PrimitiveDeclaration>,
    pub vocabularies: Vec<Vocabulary>,
    pub issues: Vec<ResultIssue>,
    pub elapsed_ms: u128,
    pub peak_bytes: u64,
}

pub fn exit_code(status: Status, signal: Option<Signal>, issues: &[ResultIssue]) -> u8 {
    match status {
        Status::Interrupted => match signal {
            Some(Signal::Term) => 143,
            _ => 130,
        },
        Status::Error => {
            if issues.iter().any(|i| matches!(i, ResultIssue::Io { .. })) {
                74
            } else {
                70
            }
        }
        Status::Invalid => {
            if issues
                .iter()
                .any(|i| matches!(i, ResultIssue::Usage { .. }))
            {
                64
            } else {
                65
            }
        }
        Status::Unsupported => 69,
        Status::Complete => 0,
    }
}

impl CheckResult {
    pub fn wire(&self) -> Json {
        let mut inputs: Vec<&InputIdentity> = self.inputs.iter().collect();
        inputs.sort_by(|a, b| a.id.cmp(&b.id));
        let mut issues: Vec<&ResultIssue> = self.issues.iter().collect();
        issues.sort_by_key(|i| i.sort_key());
        let mut declarations: Vec<Json> = self
            .primitives
            .iter()
            .flat_map(primitive_declarations_wire)
            .collect();
        declarations.extend(self.declarations.iter().map(declaration_wire));
        declarations.sort_by(|a, b| declaration_name(a).cmp(declaration_name(b)));
        let mut vocabularies: Vec<_> = self.vocabularies.iter().collect();
        vocabularies.sort_by(|a, b| a.namespace.cmp(&b.namespace));
        Json::obj([
            ("format", Json::str("archsig.result/2")),
            ("semantics", Json::str(crate::law::SEMANTICS)),
            (
                "producer",
                Json::obj([
                    ("version", Json::str(env!("CARGO_PKG_VERSION"))),
                    (
                        "build",
                        Json::str(concat!(
                            env!("CARGO_PKG_NAME"),
                            "-",
                            env!("CARGO_PKG_VERSION")
                        )),
                    ),
                ]),
            ),
            ("command", Json::str("check")),
            ("status", Json::str(self.status.wire())),
            ("exit_code", Json::Nat(u64::from(self.exit_code))),
            (
                "inputs",
                Json::Arr(inputs.into_iter().map(InputIdentity::wire).collect()),
            ),
            ("declarations", Json::Arr(declarations)),
            (
                "vocabularies",
                Json::Arr(
                    vocabularies
                        .into_iter()
                        .map(|v| {
                            Json::obj([
                                ("manifest", v.manifest.clone()),
                                ("digest", Json::str(v.digest.clone())),
                                ("location", location_wire(&v.location)),
                            ])
                        })
                        .collect(),
                ),
            ),
            ("requests", Json::Arr(vec![])),
            ("answers", Json::Arr(vec![])),
            ("nodes", Json::Arr(vec![])),
            (
                "issues",
                Json::Arr(issues.into_iter().map(ResultIssue::wire).collect()),
            ),
            (
                "reuse",
                Json::obj([
                    ("requested", Json::Bool(false)),
                    ("accepted_nodes", Json::Nat(0)),
                    ("recomputed_nodes", Json::Nat(0)),
                    ("rejected", Json::Arr(vec![])),
                ]),
            ),
            (
                "usage",
                Json::obj([
                    ("elapsed_ms", Json::str(self.elapsed_ms.to_string())),
                    ("peak_bytes", Json::str(self.peak_bytes.to_string())),
                ]),
            ),
            ("limits", Json::Obj(BTreeMap::new())),
        ])
    }
}
