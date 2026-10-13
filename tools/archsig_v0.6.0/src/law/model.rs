//! 検査済み Law の内部表現。後続の評価へメモリ上で渡す。

use super::ast::{ExprId, Role, Span};
use crate::types::Type;

/// 型付きの field・parameter。Law parameter の `span` は名前の出現。
/// 式検査内部の原始 field は入力 span を持たず、位置の出力には共通定義を使う。
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
    /// 検査済み共通署名を式検査の lookup へ接続する。原始型の検査・位置は定義側が所有する。
    pub(crate) fn from_primitive(sig: &crate::definition::PrimitiveSignature) -> Self {
        use crate::definition::PrimitiveSignature as P;
        let fields = |fs: &[crate::definition::Field]| {
            fs.iter()
                .map(|f| Param {
                    name: f.name.clone(),
                    ty: f.ty.clone(),
                    // 原始 field は Law の出現を持たない。この値を Location に出力しない。
                    span: (0, 0),
                })
                .collect()
        };
        match sig {
            P::Entity {
                parameters,
                fields: fs,
                owner,
            } => Self::Entity {
                params: fields(parameters),
                members: fields(fs),
                owner: owner.clone(),
            },
            P::Arrow {
                parameters,
                fields: fs,
                owner,
                endpoint,
            } => Self::Arrow {
                params: fields(parameters),
                members: fields(fs),
                owner: owner.clone(),
                endpoint: endpoint.clone(),
            },
            P::Correspondence {
                parameters,
                fields: fs,
                from,
                to,
                maps,
                alignments,
                implicit,
            } => Self::Correspondence {
                params: fields(parameters),
                members: fields(fs),
                from: from.clone(),
                to: to.clone(),
                maps: maps.clone(),
                alignments: alignments
                    .iter()
                    .map(|a| (a.source.clone(), a.target.clone()))
                    .collect(),
                implicit: implicit.clone(),
            },
            P::Data { constructors } => Self::Data {
                constructors: constructors
                    .iter()
                    .map(|c| CtorSig {
                        name: c.name.clone(),
                        args: c.arguments.clone(),
                    })
                    .collect(),
            },
        }
    }

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

/// 結果仕様 §1 の DeclarationInfo。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationInfo {
    pub vocabularies: Vec<crate::definition::Binding>,
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
