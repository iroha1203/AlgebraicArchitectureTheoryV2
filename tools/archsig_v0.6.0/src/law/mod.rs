//! Law ファイルの静的検査。構文・版・名前・型・再帰・純粋性を検査し、
//! 型付き宣言、原式と出現位置、参照、語彙 manifest を返す。

pub mod ast;
mod body;
mod check;
mod expr;
pub mod lexer;
pub mod model;
pub mod parser;

use crate::canonical::{Json, sha256_digest};
use crate::issue::{Code, Details, Issue, Location};
use crate::types::Type;
use ast::{Expr, ExprId, Header, Reading};
use check::Checker;
use model::{Declaration, DeclarationInfo, Vocabulary};
use std::collections::BTreeMap;

pub const FORMAT: &str = "archsig.law/1";
pub const SEMANTICS: &str = "archsig/0.6.0";

/// 検査を通った Law。
#[derive(Debug)]
pub struct CheckedLaw {
    pub bytes_digest: String,
    pub model_digest: String,
    pub header: Header,
    pub readings: Vec<Reading>,
    /// 完全名から宣言へ。
    pub declarations: BTreeMap<String, Declaration>,
    /// 原式の arena と、各出現の解決した型。
    pub exprs: Vec<Expr>,
    pub expr_types: Vec<Option<Type>>,
    pub infos: Vec<DeclarationInfo>,
    pub vocabularies: Vec<Vocabulary>,
}

impl CheckedLaw {
    pub fn expr_type(&self, id: ExprId) -> Option<&Type> {
        self.expr_types.get(id).and_then(Option::as_ref)
    }
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
pub fn check_law(bytes: &[u8]) -> Result<CheckedLaw, LawFailure> {
    let bytes_digest = sha256_digest(bytes);
    let fail = |issue: Issue, model_digest: Option<String>| LawFailure {
        issue,
        bytes_digest: bytes_digest.clone(),
        model_digest,
    };
    // 検査順: UTF-8、header の版、残りの字句と宣言の文法、名前・型・参照。
    let head = lexer::lex_up_to(bytes, 5).map_err(|i| fail(*i, None))?;
    let header = parser::Parser::new(head, bytes.len())
        .header()
        .map_err(|i| fail(*i, None))?;
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
        return Err(fail(issue, None));
    }
    let tokens = lexer::lex(bytes).map_err(|i| fail(*i, None))?;
    let digest = model_digest(&tokens);
    let mut parser = parser::Parser::new(tokens, bytes.len());
    parser
        .header()
        .map_err(|i| fail(*i, Some(digest.clone())))?;
    let readings = parser
        .readings()
        .map_err(|i| fail(*i, Some(digest.clone())))?;
    let mut checker = Checker::new(parser, readings);
    let result = (|| {
        checker.collect_names()?;
        checker.check_primitives()?;
        checker.check_bodies()
    })();
    result.map_err(|i| fail(*i, Some(digest.clone())))?;
    let infos = checker.declaration_infos();
    let vocabularies = checker.vocabularies();
    let mut declarations = BTreeMap::new();
    for r in checker.ast.iter() {
        for d in &r.decls {
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
        header,
        readings: checker.ast.as_ref().clone(),
        declarations,
        exprs: std::mem::take(&mut checker.parser.exprs),
        expr_types,
        infos,
        vocabularies,
    })
}
