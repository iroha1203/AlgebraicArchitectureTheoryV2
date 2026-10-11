//! 検査済み Law の内部表現。後続の評価へメモリ上で渡す。

use super::ast::{ExprId, Role, Span};
use crate::canonical::Json;
use crate::issue::Location;
use crate::types::Type;
use std::collections::BTreeMap;

/// 型付きの field・parameter。`span` は名前の出現。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtorSig {
    pub name: String,
    pub args: Vec<Type>,
    pub span: Span,
}

/// 宣言の型付き署名と原式。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Signature {
    Entity {
        params: Vec<Param>,
        members: Vec<Param>,
        owner: Option<String>,
    },
    Arrow {
        params: Vec<Param>,
        members: Vec<Param>,
        owner: String,
        endpoint: String,
    },
    Correspondence {
        params: Vec<Param>,
        members: Vec<Param>,
        from: String,
        to: String,
        /// 対応表の field 名と、その始域・終域の宣言。
        maps: Vec<(String, String, String)>,
        /// 明記した align(source, target の field 完全名)。
        alignments: Vec<(String, String)>,
        /// 同じ型間の同名 field の対応。
        implicit: Vec<(String, String)>,
    },
    Data {
        constructors: Vec<CtorSig>,
    },
    View {
        params: Vec<Param>,
        returns: Type,
        body: ExprId,
    },
    Law {
        role: Role,
        params: Vec<Param>,
        guard: Option<ExprId>,
        body: ExprId,
    },
    Local {
        params: Vec<Param>,
        guard: Option<ExprId>,
        reads: Vec<ExprId>,
    },
    Change {
        params: Vec<Param>,
        guard: Option<ExprId>,
        body: ExprId,
    },
    Relation {
        params: Vec<Param>,
        guard: Option<ExprId>,
        left: ExprId,
        right: ExprId,
    },
}

impl Signature {
    pub fn kind(&self) -> &'static str {
        match self {
            Signature::Entity { .. } => "entity",
            Signature::Arrow { .. } => "arrow",
            Signature::Correspondence { .. } => "correspondence",
            Signature::Data { .. } => "data",
            Signature::View { .. } => "view",
            Signature::Law { .. } => "law",
            Signature::Local { .. } => "local",
            Signature::Change { .. } => "change",
            Signature::Relation { .. } => "relation",
        }
    }

    /// entity/arrow/correspondence の括弧内と body の field。
    pub fn record_fields(&self) -> Option<(&[Param], &[Param])> {
        match self {
            Signature::Entity {
                params, members, ..
            }
            | Signature::Arrow {
                params, members, ..
            }
            | Signature::Correspondence {
                params, members, ..
            } => Some((params, members)),
            _ => None,
        }
    }

    pub fn field(&self, name: &str) -> Option<&Param> {
        let (params, members) = self.record_fields()?;
        params.iter().chain(members).find(|p| p.name == name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub name: String,
    pub reading: String,
    pub signature: Signature,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExpressionKind {
    Guard,
    Body,
    Read,
    RelationLeft,
    RelationRight,
}

impl ExpressionKind {
    fn wire(self) -> &'static str {
        match self {
            ExpressionKind::Guard => "guard",
            ExpressionKind::Body => "body",
            ExpressionKind::Read => "read",
            ExpressionKind::RelationLeft => "relation_left",
            ExpressionKind::RelationRight => "relation_right",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedExpression {
    pub kind: ExpressionKind,
    pub span: Span,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SuppliedRule {
    GuardTrue {
        span: Span,
    },
    SameNameAlignment {
        span: Span,
        pairs: Vec<(String, String)>,
    },
    LocalDeclared {
        span: Span,
    },
    LocalSupport {
        span: Span,
    },
}

impl SuppliedRule {
    fn rule(&self) -> &'static str {
        match self {
            SuppliedRule::GuardTrue { .. } => "guard_true",
            SuppliedRule::SameNameAlignment { .. } => "same_name_alignment",
            SuppliedRule::LocalDeclared { .. } => "local_declared",
            SuppliedRule::LocalSupport { .. } => "local_support",
        }
    }

    fn wire(&self) -> Json {
        let (span, pairs) = match self {
            SuppliedRule::GuardTrue { span }
            | SuppliedRule::LocalDeclared { span }
            | SuppliedRule::LocalSupport { span } => (*span, None),
            SuppliedRule::SameNameAlignment { span, pairs } => (*span, Some(pairs)),
        };
        let mut m = BTreeMap::new();
        m.insert("rule".to_owned(), Json::str(self.rule()));
        m.insert("location".to_owned(), Location::Law { span }.wire());
        if let Some(pairs) = pairs {
            m.insert(
                "pairs".to_owned(),
                Json::Arr(
                    pairs
                        .iter()
                        .map(|(a, b)| Json::Arr(vec![Json::str(a.clone()), Json::str(b.clone())]))
                        .collect(),
                ),
            );
        }
        Json::Obj(m)
    }
}

/// 結果仕様 §1 の DeclarationInfo。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationInfo {
    pub name: String,
    pub kind: &'static str,
    pub parameters: Vec<(String, Type)>,
    pub fields: Vec<(String, Type)>,
    pub returns: Option<Type>,
    pub role: Option<Role>,
    pub span: Span,
    pub dependencies: Vec<String>,
    pub references: Vec<(Span, String)>,
    pub expressions: Vec<ResolvedExpression>,
    pub supplied: Vec<SuppliedRule>,
}

fn params_wire(ps: &[(String, Type)]) -> Json {
    Json::Arr(
        ps.iter()
            .map(|(n, t)| Json::obj([("name", Json::str(n.clone())), ("type", t.wire())]))
            .collect(),
    )
}

impl DeclarationInfo {
    pub fn wire(&self) -> Json {
        let mut m = BTreeMap::new();
        m.insert("name".to_owned(), Json::str(self.name.clone()));
        m.insert("kind".to_owned(), Json::str(self.kind));
        m.insert("parameters".to_owned(), params_wire(&self.parameters));
        m.insert("fields".to_owned(), params_wire(&self.fields));
        if let Some(t) = &self.returns {
            m.insert("returns".to_owned(), t.wire());
        }
        if let Some(r) = self.role {
            m.insert(
                "role".to_owned(),
                Json::str(match r {
                    Role::Required => "required",
                    Role::Optional => "optional",
                }),
            );
        }
        m.insert(
            "location".to_owned(),
            Location::Law { span: self.span }.wire(),
        );
        m.insert(
            "dependencies".to_owned(),
            Json::Arr(self.dependencies.iter().cloned().map(Json::Str).collect()),
        );
        let references = self
            .references
            .iter()
            .map(|(s, n)| {
                Json::obj([
                    ("location", Location::Law { span: *s }.wire()),
                    ("name", Json::str(n.clone())),
                ])
            })
            .collect();
        let expressions = self
            .expressions
            .iter()
            .map(|e| {
                Json::obj([
                    ("kind", Json::str(e.kind.wire())),
                    ("location", Location::Law { span: e.span }.wire()),
                    ("type", e.ty.wire()),
                ])
            })
            .collect();
        m.insert(
            "resolution".to_owned(),
            Json::obj([
                ("references", Json::Arr(references)),
                ("expressions", Json::Arr(expressions)),
                (
                    "supplied",
                    Json::Arr(self.supplied.iter().map(SuppliedRule::wire).collect()),
                ),
            ]),
        );
        Json::Obj(m)
    }
}

/// 入力仕様 §4 の語彙 manifest と、その canonical JSON の digest。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vocabulary {
    pub reading: String,
    pub manifest: Json,
    pub digest: String,
}
