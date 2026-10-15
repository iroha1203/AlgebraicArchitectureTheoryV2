//! Law ファイルの静的検査。構文・版・名前・型・再帰・純粋性を検査し、
//! 共通定義を参照する型付き宣言、原式と出現位置、名前参照を返す。

pub mod ast;
mod body;
pub(crate) mod check;
mod expr;
pub mod lexer;
mod metadata;
pub mod model;
pub mod parser;

use crate::canonical::{Json, sha256_digest};
use crate::definition::CheckedDefinitions;
use crate::issue::{Code, Details, Issue, Location};
use crate::json::InputError;
use crate::observed::control::{CheckFailure, Checkpoint, Control};
use crate::types::Type;
use ast::{Expr, ExprId};
use check::Checker;
use model::{Declaration, DeclarationInfo};
use std::collections::BTreeMap;

pub const FORMAT: &str = "archsig.law/2";
pub const SEMANTICS: &str = "archsig/0.6.0";

/// 検査を通った Law。
#[derive(Debug)]
pub struct CheckedLaw {
    pub bytes_digest: String,
    pub model_digest: String,
    /// 完全名から宣言へ。
    pub declarations: BTreeMap<String, Declaration>,
    /// 原式の arena と、各出現の解決した型。
    pub exprs: Vec<Expr>,
    pub expr_types: Vec<Option<Type>>,
    pub infos: Vec<DeclarationInfo>,
    pub definitions: CheckedDefinitions,
}

/// 検査した観測 Term の本体。
#[derive(Debug)]
pub struct TermBody {
    pub exprs: Vec<Expr>,
    pub root: ExprId,
    pub types: Vec<Option<Type>>,
}

impl CheckedLaw {
    pub fn expr_type(&self, id: ExprId) -> Option<&Type> {
        self.expr_types.get(id).and_then(Option::as_ref)
    }
}

/// 定義元と依存 namespace の scope で、観測した Term の純粋な本体を検査する。
/// 位置は本体文字列中の byte span。ArchMap reader が該当 JSON Pointer へ接続する。
pub fn check_definition_term_body(
    definitions: &CheckedDefinitions,
    namespace: &str,
    params: &[(String, Type)],
    ret: &Type,
    body: &str,
) -> Result<TermBody, Box<Issue>> {
    if !definitions.vocabularies.contains_key(namespace) {
        return Err(Box::new(Issue::law(
            Code::Reference,
            (0, body.len()),
            format!("namespace `{namespace}` が登録されていない"),
        )));
    }
    let tokens = lexer::lex(body.as_bytes())?;
    let mut parser = parser::Parser::new(tokens, body.len());
    let root = parser.parse_expr(ast::Flags::default())?;
    parser.expect_end()?;
    let mut checker = Checker::with_definitions(parser, Vec::new(), definitions);
    checker.term_namespace = Some(namespace.to_owned());
    let mut env = expr::Env::default();
    for (name, ty) in params {
        let id = ast::Ident {
            name: name.clone(),
            span: (0, 0),
            tok: 0,
        };
        checker.bind(&mut env, &id, ty.clone(), expr::Origin::Other)?;
    }
    let ctx = expr::Ctx {
        reading: 0,
        decl: String::new(),
        is_view: false,
        rec: None,
        term: true,
    };
    checker.check(root, Some(ret), &mut env, &ctx)?;
    let mut types = std::mem::take(&mut checker.expr_types);
    types.resize(checker.parser.exprs.len(), None);
    Ok(TermBody {
        exprs: std::mem::take(&mut checker.parser.exprs),
        root,
        types,
    })
}

/// 検査の失敗。読めた byte 列の digest と、字句列が得られた場合の model_digest を持つ。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawFailure {
    pub issue: Issue,
    pub bytes_digest: String,
    pub model_digest: Option<String>,
}

/// 字句列の正規化(Law 仕様 §1)。`{semantics, tokens}` の canonical JSON。
pub fn model_canonical(tokens: &[lexer::Token]) -> String {
    let toks = tokens
        .iter()
        .map(|t| {
            Json::obj([
                ("kind", Json::str(t.kind.wire())),
                ("text", Json::str(t.text.clone())),
            ])
        })
        .collect();
    Json::obj([
        ("semantics", Json::str(SEMANTICS)),
        ("tokens", Json::Arr(toks)),
    ])
    .canonical()
}

pub fn model_digest(tokens: &[lexer::Token]) -> String {
    sha256_digest(model_canonical(tokens).as_bytes())
}

/// Law を検査する。深い入れ子でも呼出し側のスタックを使い切らないよう、再帰は stacker を通す。
#[allow(clippy::result_large_err)]
pub fn check_law(bytes: &[u8], definitions: &CheckedDefinitions) -> Result<CheckedLaw, LawFailure> {
    check_law_inner::<Box<Issue>>(bytes, definitions, &mut Control::unlimited()).map_err(
        |(issue, bytes_digest, model_digest)| LawFailure {
            issue: *issue,
            bytes_digest,
            model_digest,
        },
    )
}
#[allow(clippy::result_large_err)]
pub fn check_law_controlled(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<CheckedLaw, CheckFailure<LawFailure>> {
    check_law_inner::<CheckFailure<Box<Issue>>>(bytes, definitions, control).map_err(
        |(failure, bytes_digest, model_digest)| match failure {
            CheckFailure::Input(issue) => CheckFailure::Input(LawFailure {
                issue: *issue,
                bytes_digest,
                model_digest,
            }),
            CheckFailure::Stopped(reason) => CheckFailure::Stopped(reason),
        },
    )
}
fn check_law_inner<E: InputError>(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<CheckedLaw, (E, String, Option<String>)> {
    let bytes_digest = sha256_digest(bytes);
    let fail = |issue: E, model_digest: Option<String>| (issue, bytes_digest.clone(), model_digest);
    // 検査順: UTF-8、header の版、残りの字句と宣言の文法、名前・型・参照。
    let head = lexer::lex_inner::<E>(bytes, 5, control).map_err(|i| fail(i, None))?;
    let header = parser::Parser::<E>::with_error(head, bytes.len(), control.clone())
        .header()
        .map_err(|i| fail(i, None))?;
    if header.format != FORMAT || header.semantics != SEMANTICS {
        let issue = Issue {
            code: Code::UnsupportedVersion,
            message: "未対応の format または semantics".into(),
            location: Location::Law { span: header.span },
            details: Details::Version {
                found_format: header.format.clone(),
                found_semantics: Some(header.semantics.clone()),
            },
        };
        return Err(fail(Box::new(issue).into(), None));
    }
    let tokens = lexer::lex_inner::<E>(bytes, usize::MAX, control).map_err(|i| fail(i, None))?;
    let digest = model_digest(&tokens);
    let mut parser = parser::Parser::<E>::with_error(tokens, bytes.len(), control.clone());
    parser.header().map_err(|i| fail(i, Some(digest.clone())))?;
    let readings = parser
        .readings()
        .map_err(|i| fail(i, Some(digest.clone())))?;
    let mut checker = Checker::with_definitions(parser.into_uncontrolled(), readings, definitions);
    let result = (|| -> Result<(), E> {
        checker.collect_names_controlled::<E>(control)?;
        checker.check_bodies_controlled::<E>(control)
    })();
    result.map_err(|i| fail(i, Some(digest.clone())))?;
    let infos = checker.declaration_infos();
    let mut declarations = BTreeMap::new();
    for r in checker.ast.iter() {
        E::checkpoint(control, Checkpoint::LawIteration)
            .map_err(|i| fail(i, Some(digest.clone())))?;
        for d in &r.decls {
            E::checkpoint(control, Checkpoint::LawIteration)
                .map_err(|i| fail(i, Some(digest.clone())))?;
            let name = check::full(&r.name.name, &[&d.name.name]);
            let signature = checker.sigs[&name].clone();
            declarations.insert(
                name.clone(),
                Declaration {
                    name,
                    reading: r.name.name.clone(),
                    signature,
                    span: d.span,
                },
            );
        }
    }
    let mut expr_types = std::mem::take(&mut checker.expr_types);
    expr_types.resize(checker.parser.exprs.len(), None);
    Ok(CheckedLaw {
        bytes_digest,
        model_digest: digest,
        declarations,
        exprs: std::mem::take(&mut checker.parser.exprs),
        expr_types,
        infos,
        definitions: definitions.clone(),
    })
}
