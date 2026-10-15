//! Law の構文解析(Law 仕様 §§2–4)。
//!
//! 深い入れ子でも落ちないよう、再帰する関数は `stacker` で必要に応じてスタックを伸ばす。

use super::ast::*;
use super::lexer::{Token, TokenKind};
use crate::issue::{Code, Issue};
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use std::collections::HashMap;

pub use crate::names::RESERVED;

pub fn is_reserved(name: &str) -> bool {
    RESERVED.contains(&name)
}

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

type PResult<T, E> = Result<T, E>;

pub struct Parser<E = Box<Issue>> {
    control: Control,
    point: Checkpoint,
    error: std::marker::PhantomData<E>,
    pub toks: Vec<Token>,
    pub exprs: Vec<Expr>,
    src_len: usize,
    pos: usize,
    limit: usize,
    memo: HashMap<(usize, usize, Flags), (ExprId, usize)>,
}

impl<E: InputError> Parser<E> {
    pub(super) fn with_error(toks: Vec<Token>, src_len: usize, control: Control) -> Self {
        let limit = toks.len();
        Parser {
            control,
            point: Checkpoint::LawIteration,
            error: std::marker::PhantomData,
            toks,
            exprs: Vec::new(),
            src_len,
            pos: 0,
            limit,
            memo: HashMap::new(),
        }
    }

    /// Cover every Result exit (including `?` inside an iteration) before its caller
    /// can start another operation or retry a speculative candidate.
    fn checked<T>(&mut self, parse: impl FnOnce(&mut Self) -> PResult<T, E>) -> PResult<T, E> {
        E::checkpoint(&mut self.control, self.point)?;
        let result = parse(self);
        E::finish(result, &mut self.control, self.point)
    }

    // ---- 字句の参照 ----

    fn peek(&self) -> Option<&Token> {
        (self.pos < self.limit).then(|| &self.toks[self.pos])
    }

    fn peek_at(&self, k: usize) -> Option<&Token> {
        (self.pos + k < self.limit).then(|| &self.toks[self.pos + k])
    }

    fn is_sym(&self, s: &str) -> bool {
        self.peek()
            .is_some_and(|t| t.kind == TokenKind::Sym && t.text == s)
    }

    fn is_kw(&self, s: &str) -> bool {
        self.peek()
            .is_some_and(|t| t.kind == TokenKind::Name && t.text == s)
    }

    fn here(&self) -> Span {
        match self.peek() {
            Some(t) => t.span,
            None if self.limit < self.toks.len() => self.toks[self.limit].span,
            None => (self.src_len, self.src_len),
        }
    }

    fn prev_end(&self) -> usize {
        if self.pos == 0 {
            0
        } else {
            self.toks[self.pos - 1].span.1
        }
    }

    fn err<T>(&self, message: impl Into<String>) -> PResult<T, E> {
        Err((Box::new(Issue::law(Code::Syntax, self.here(), message))).into())
    }

    fn eat_sym(&mut self, s: &str) -> bool {
        if self.is_sym(s) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, s: &str) -> bool {
        if self.is_kw(s) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_sym(&mut self, s: &str) -> PResult<Span, E> {
        if self.is_sym(s) {
            self.pos += 1;
            Ok(self.toks[self.pos - 1].span)
        } else {
            self.err(format!("`{s}` が必要"))
        }
    }

    fn expect_kw(&mut self, s: &str) -> PResult<Span, E> {
        if self.is_kw(s) {
            self.pos += 1;
            Ok(self.toks[self.pos - 1].span)
        } else {
            self.err(format!("`{s}` が必要"))
        }
    }

    fn ident(&mut self) -> PResult<Ident, E> {
        match self.peek() {
            Some(t) if t.kind == TokenKind::Name && !is_reserved(&t.text) => {
                let id = Ident {
                    name: t.text.clone(),
                    span: t.span,
                    tok: self.pos,
                };
                self.pos += 1;
                Ok(id)
            }
            Some(t) if t.kind == TokenKind::Name => {
                self.err(format!("予約語 `{}` は名前に使えない", t.text))
            }
            _ => self.err("名前が必要"),
        }
    }

    fn string(&mut self) -> PResult<String, E> {
        match self.peek() {
            Some(t) if t.kind == TokenKind::Str => {
                let s = t.text.clone();
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("文字列が必要"),
        }
    }

    /// `.` に続く名前を貪欲に読む。
    fn qname(&mut self) -> PResult<QName, E> {
        // Embedded ArchMap Term parsers retain their caller's checkpoint.
        let point = if self.point == Checkpoint::LawIteration {
            Checkpoint::LawName
        } else {
            self.point
        };
        E::checkpoint(&mut self.control, point)?;
        let first = self.ident();
        let mut parts = vec![E::finish(first, &mut self.control, point)?];
        while self.is_sym(".")
            && self
                .peek_at(1)
                .is_some_and(|t| t.kind == TokenKind::Name && !is_reserved(&t.text))
        {
            E::checkpoint(&mut self.control, point)?;
            self.pos += 1;
            let next = self.ident();
            parts.push(E::finish(next, &mut self.control, point)?);
        }
        E::checkpoint(&mut self.control, point)?;
        Ok(QName { parts })
    }

    fn push(&mut self, kind: ExprKind, span: Span) -> ExprId {
        self.exprs.push(Expr { kind, span });
        self.exprs.len() - 1
    }

    /// 字句列を読み切ったことを確かめる。
    pub fn expect_end(&self) -> PResult<(), E> {
        if self.peek().is_some() {
            self.err("式の後に余分な字句がある")
        } else {
            Ok(())
        }
    }

    // ---- 文書 ----

    pub fn header(&mut self) -> PResult<Header, E> {
        let start = self.here().0;
        self.expect_kw("law")?;
        let format = self.string()?;
        self.expect_kw("semantics")?;
        let semantics = self.string()?;
        self.expect_sym(";")?;
        Ok(Header {
            format,
            semantics,
            span: (start, self.prev_end()),
        })
    }

    pub fn readings(&mut self) -> PResult<Vec<Reading>, E> {
        self.checked(|parser| {
            let mut readings = Vec::new();
            loop {
                E::checkpoint(&mut parser.control, parser.point)?;
                readings.push(parser.reading()?);
                if parser.peek().is_none() {
                    return Ok(readings);
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
        })
    }

    fn reading(&mut self) -> PResult<Reading, E> {
        self.checked(|parser| {
            let start = parser.here().0;
            parser.expect_kw("reading")?;
            let name = parser.ident()?;
            parser.expect_sym("{")?;
            let mut uses = Vec::new();
            let mut vocabularies = Vec::new();
            let mut decls = Vec::new();
            while !parser.is_sym("}") {
                E::checkpoint(&mut parser.control, parser.point)?;
                if parser.eat_kw("use") {
                    let use_start = parser.toks[parser.pos - 1].span.0;
                    if parser.eat_kw("vocabulary") {
                        let namespace = parser.ident()?;
                        parser.expect_kw("version")?;
                        let version_span = parser.here();
                        let version = parser.string()?;
                        if version.is_empty() {
                            return Err((Box::new(Issue::law(
                                Code::Syntax,
                                version_span,
                                "語彙の version は空文字列にできない",
                            )))
                            .into());
                        }
                        parser.expect_kw("digest")?;
                        let digest_span = parser.here();
                        let digest = parser.string()?;
                        if digest.len() != 71
                            || !digest.starts_with("sha256:")
                            || !digest.as_bytes()[7..]
                                .iter()
                                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
                        {
                            return Err((Box::new(Issue::law(
                                Code::Syntax,
                                digest_span,
                                "digest は sha256: と小文字16進64桁",
                            )))
                            .into());
                        }
                        parser.expect_sym(";")?;
                        vocabularies.push(VocabularyUse {
                            namespace,
                            version,
                            digest,
                            span: (use_start, parser.prev_end()),
                        });
                    } else {
                        let reading = parser.ident()?;
                        parser.expect_kw("as")?;
                        let alias = parser.ident()?;
                        parser.expect_sym(";")?;
                        uses.push(Use { reading, alias });
                    }
                } else {
                    decls.push(parser.decl()?);
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            parser.expect_sym("}")?;
            Ok(Reading {
                name,
                uses,
                vocabularies,
                decls,
                span: (start, parser.prev_end()),
            })
        })
    }

    fn decl(&mut self) -> PResult<Decl, E> {
        self.checked(|parser| {
            let start = parser.here().0;
            let Some(t) = parser.peek() else {
                return parser.err("宣言または `}` が必要");
            };
            let keyword = if t.kind == TokenKind::Name {
                t.text.clone()
            } else {
                String::new()
            };
            let (name, kind) = match keyword.as_str() {
                "entity" | "arrow" | "correspondence" | "data" => {
                    return parser.err("原始宣言は Atom 定義ファイルに置く");
                }
                "view" => {
                    parser.pos += 1;
                    let name = parser.ident()?;
                    let params = parser.fields()?;
                    parser.expect_sym(":")?;
                    let returns = parser.ty()?;
                    parser.expect_sym("=")?;
                    let body = parser.parse_expr(Flags::default())?;
                    parser.expect_sym(";")?;
                    (
                        name,
                        DeclKind::View {
                            params,
                            returns,
                            body,
                        },
                    )
                }
                "law" => {
                    parser.pos += 1;
                    let role = if parser.eat_kw("required") {
                        Role::Required
                    } else if parser.eat_kw("optional") {
                        Role::Optional
                    } else {
                        return parser.err("`required` または `optional` が必要");
                    };
                    let name = parser.ident()?;
                    let params = parser.fields()?;
                    let guard = parser.guard()?;
                    parser.expect_sym(":")?;
                    let body = parser.parse_expr(Flags::default())?;
                    parser.expect_sym(";")?;
                    (
                        name,
                        DeclKind::Law {
                            role,
                            params,
                            guard,
                            body,
                        },
                    )
                }
                "local" => {
                    parser.pos += 1;
                    let name = parser.ident()?;
                    let params = parser.fields()?;
                    let guard = parser.guard()?;
                    parser.expect_kw("reads")?;
                    let mut reads = vec![parser.parse_expr(Flags::default())?];
                    while parser.is_sym(",") {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        parser.pos += 1;
                        reads.push(parser.parse_expr(Flags::default())?);

                        E::checkpoint(&mut parser.control, parser.point)?;
                    }
                    parser.expect_sym(";")?;
                    (
                        name,
                        DeclKind::Local {
                            params,
                            guard,
                            reads,
                        },
                    )
                }
                "change" => {
                    parser.pos += 1;
                    let name = parser.ident()?;
                    let params = parser.fields()?;
                    let (guard, body) = parser.change_tail()?;
                    (
                        name,
                        DeclKind::Change {
                            params,
                            guard,
                            body,
                        },
                    )
                }
                "relation" => {
                    parser.pos += 1;
                    let name = parser.ident()?;
                    let params = parser.fields()?;
                    let guard = parser.guard()?;
                    parser.expect_sym(":")?;
                    let body = parser.parse_expr(Flags::default())?;
                    parser.expect_sym(";")?;
                    (
                        name,
                        DeclKind::Relation {
                            params,
                            guard,
                            body,
                        },
                    )
                }
                _ => return parser.err("宣言または `}` が必要"),
            };
            Ok(Decl {
                name,
                kind,
                span: (start, parser.prev_end()),
            })
        })
    }

    fn guard(&mut self) -> PResult<Option<ExprId>, E> {
        if self.eat_kw("when") {
            Ok(Some(self.parse_expr(Flags::default())?))
        } else {
            Ok(None)
        }
    }

    /// change の guard と body は、宣言の最上位の `=` を後ろから試し、両方が読める位置で区切る。
    fn change_tail(&mut self) -> PResult<(Option<ExprId>, ExprId), E> {
        self.checked(|parser| {
            if !parser.eat_kw("when") {
                parser.expect_sym("=")?;
                let body = parser.parse_expr(Flags::default())?;
                parser.expect_sym(";")?;
                return Ok((None, body));
            }
            let start = parser.pos;
            let mut depth = 0isize;
            let mut eqs = Vec::new();
            let mut end = None;
            for i in parser.pos..parser.limit {
                E::checkpoint(&mut parser.control, parser.point)?;
                let t = &parser.toks[i];
                if t.kind != TokenKind::Sym {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    continue;
                }
                match t.text.as_str() {
                    "(" | "[" | "{" => depth += 1,
                    ")" | "]" | "}" => {
                        depth -= 1;
                        if depth < 0 {
                            E::checkpoint(&mut parser.control, parser.point)?;
                            break;
                        }
                    }
                    "=" if depth == 0 => eqs.push(i),
                    ";" if depth == 0 => {
                        end = Some(i);

                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }
                    _ => {}
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            let Some(end) = end else {
                return parser.err("change の guard の後に `=` と body が必要");
            };
            // 最上位の `=` を後ろから順に試し、guard と body がどちらも読める位置で区切る。
            let mut first_error = None;
            for (candidate_index, &eq) in eqs.iter().rev().enumerate() {
                E::checkpoint(&mut parser.control, parser.point)?;
                parser.pos = start;
                let parsed = parser
                    .parse_until(eq, |p| p.parse_expr(Flags::default()))
                    .and_then(|guard| {
                        parser.pos = eq + 1;
                        parser
                            .parse_until(end, |p| p.parse_expr(Flags::default()))
                            .map(|body| (guard, body))
                    });
                match parsed {
                    Ok((guard, body)) => {
                        parser.pos = end + 1;
                        return Ok((Some(guard), body));
                    }
                    Err(e) => {
                        if e.is_stopped() {
                            return Err(e);
                        }
                        first_error.get_or_insert(e);
                        // Every split has failed. Let `checked` finish the
                        // established Syntax before consulting a latched budget.
                        // An earlier candidate's failure cannot establish this.
                        if candidate_index + 1 == eqs.len() {
                            break;
                        }
                    }
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            parser.pos = start;
            Err(first_error.unwrap_or_else(|| {
                Box::new(Issue::law(
                    Code::Syntax,
                    parser.here(),
                    "change の guard の後に `=` と body が必要",
                ))
                .into()
            }))
        })
    }

    /// `limit` までの字句をちょうど読み切る。
    fn parse_until<T>(
        &mut self,
        limit: usize,
        f: impl FnOnce(&mut Self) -> PResult<T, E>,
    ) -> PResult<T, E> {
        let saved = self.limit;
        self.limit = limit;
        let result = f(self).and_then(|v| {
            if self.pos == limit {
                Ok(v)
            } else {
                self.err("式の終わりが必要")
            }
        });
        self.limit = saved;
        result
    }

    fn fields(&mut self) -> PResult<Vec<Field>, E> {
        self.checked(|parser| {
            parser.expect_sym("(")?;
            let mut fields = Vec::new();
            if !parser.is_sym(")") {
                loop {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    let name = parser.ident()?;
                    parser.expect_sym(":")?;
                    fields.push(Field {
                        name,
                        ty: parser.ty()?,
                    });
                    if !parser.eat_sym(",") {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }

                    E::checkpoint(&mut parser.control, parser.point)?;
                }
            }
            parser.expect_sym(")")?;
            Ok(fields)
        })
    }

    pub fn ty(&mut self) -> PResult<TypeAst, E> {
        self.checked(|parser| stacker::maybe_grow(RED_ZONE, STACK_STEP, || parser.ty_inner()))
    }

    fn ty_inner(&mut self) -> PResult<TypeAst, E> {
        self.checked(|parser| {
            let start = parser.here().0;
            let Some(t) = parser.peek().cloned() else {
                return parser.err("型が必要");
            };
            let builtin = |b| Ok(TypeAst::Builtin(b, t.span));
            if t.kind == TokenKind::Name {
                match t.text.as_str() {
                    "Unit" => {
                        parser.pos += 1;
                        return builtin(Builtin::Unit);
                    }
                    "Bool" => {
                        parser.pos += 1;
                        return builtin(Builtin::Bool);
                    }
                    "Z" => {
                        parser.pos += 1;
                        return builtin(Builtin::Z);
                    }
                    "Q" => {
                        parser.pos += 1;
                        return builtin(Builtin::Q);
                    }
                    "Text" => {
                        parser.pos += 1;
                        return builtin(Builtin::Text);
                    }
                    "Fp" => {
                        parser.pos += 1;
                        parser.expect_sym("(")?;
                        let modulus = match parser.peek() {
                            Some(t) if t.kind == TokenKind::Int => t.text.clone(),
                            _ => return parser.err("Fp の法は10進整数"),
                        };
                        parser.pos += 1;
                        parser.expect_sym(")")?;
                        return Ok(TypeAst::Fp {
                            modulus,
                            span: (start, parser.prev_end()),
                        });
                    }
                    "List" | "Set" | "Option" => {
                        parser.pos += 1;
                        parser.expect_sym("<")?;
                        let inner = Box::new(parser.ty()?);
                        parser.expect_sym(">")?;
                        let span = (start, parser.prev_end());
                        return Ok(match t.text.as_str() {
                            "List" => TypeAst::List(inner, span),
                            "Set" => TypeAst::Set(inner, span),
                            _ => TypeAst::Option(inner, span),
                        });
                    }
                    "Map" => {
                        parser.pos += 1;
                        parser.expect_sym("<")?;
                        let a = Box::new(parser.ty()?);
                        parser.expect_sym(",")?;
                        let b = Box::new(parser.ty()?);
                        parser.expect_sym(">")?;
                        return Ok(TypeAst::Map(a, b, (start, parser.prev_end())));
                    }
                    "Term" => {
                        parser.pos += 1;
                        parser.expect_sym("<")?;
                        parser.expect_sym("(")?;
                        let mut args = Vec::new();
                        if !parser.is_sym(")") {
                            loop {
                                E::checkpoint(&mut parser.control, parser.point)?;
                                args.push(parser.ty()?);
                                if !parser.eat_sym(",") {
                                    E::checkpoint(&mut parser.control, parser.point)?;
                                    break;
                                }

                                E::checkpoint(&mut parser.control, parser.point)?;
                            }
                        }
                        parser.expect_sym(")")?;
                        parser.expect_sym("->")?;
                        let ret = Box::new(parser.ty()?);
                        parser.expect_sym(">")?;
                        return Ok(TypeAst::Term(args, ret, (start, parser.prev_end())));
                    }
                    "Path" => {
                        parser.pos += 1;
                        parser.expect_sym("<")?;
                        let a = parser.qname()?;
                        parser.expect_sym(",")?;
                        let b = parser.qname()?;
                        parser.expect_sym(">")?;
                        return Ok(TypeAst::Path(a, b, (start, parser.prev_end())));
                    }
                    _ => {}
                }
            }
            if parser.eat_sym("(") {
                let mut items = vec![parser.ty()?];
                while parser.is_sym(",") {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    parser.pos += 1;
                    items.push(parser.ty()?);

                    E::checkpoint(&mut parser.control, parser.point)?;
                }
                parser.expect_sym(")")?;
                if items.len() < 2 {
                    return Err((Box::new(Issue::law(
                        Code::Syntax,
                        (start, parser.prev_end()),
                        "組の型は二つ以上の成分を持つ",
                    )))
                    .into());
                }
                return Ok(TypeAst::Tuple(items, (start, parser.prev_end())));
            }
            let name = parser.qname()?;
            let index = if parser.eat_sym("[") {
                let i = parser.ident()?;
                parser.expect_sym("]")?;
                Some(i)
            } else {
                None
            };
            Ok(TypeAst::Named {
                name,
                index,
                span: (start, parser.prev_end()),
            })
        })
    }

    // ---- 式 ----

    pub fn parse_expr(&mut self, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            stacker::maybe_grow(RED_ZONE, STACK_STEP, || parser.expr_inner(flags))
        })
    }

    /// 字句位置 `start` から `limit` の手前までで一つの式を読む。量化の区切りを決め直すときに使う。
    pub fn parse_expr_at(
        &mut self,
        start: usize,
        limit: usize,
        flags: Flags,
    ) -> PResult<(ExprId, usize), E> {
        if let Some(hit) = self.memo.get(&(start, limit, flags)) {
            return Ok(*hit);
        }
        let (saved_pos, saved_limit) = (self.pos, self.limit);
        self.pos = start;
        self.limit = limit;
        let result = self.parse_expr(flags).map(|id| (id, self.pos));
        self.pos = saved_pos;
        self.limit = saved_limit;
        let result = result?;
        self.memo.insert((start, limit, flags), result);
        Ok(result)
    }

    fn expr_inner(&mut self, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            let start = parser.here().0;
            if parser.eat_kw("let") {
                let name = parser.ident()?;
                parser.expect_sym("=")?;
                let value = parser.parse_expr(Flags { no_in: true })?;
                parser.expect_kw("in")?;
                let body = parser.parse_expr(flags)?;
                return Ok(parser.push(
                    ExprKind::Let { name, value, body },
                    (start, parser.prev_end()),
                ));
            }
            if parser.eat_kw("if") {
                let cond = parser.parse_expr(Flags::default())?;
                parser.expect_kw("then")?;
                let then_branch = parser.parse_expr(Flags::default())?;
                parser.expect_kw("else")?;
                let else_branch = parser.parse_expr(flags)?;
                return Ok(parser.push(
                    ExprKind::If {
                        cond,
                        then_branch,
                        else_branch,
                    },
                    (start, parser.prev_end()),
                ));
            }
            if parser.eat_kw("match") {
                let scrutinee = parser.parse_expr(Flags::default())?;
                parser.expect_sym("{")?;
                let mut arms = Vec::new();
                loop {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    let pattern = parser.pattern()?;
                    parser.expect_sym("=>")?;
                    let body = parser.parse_expr(Flags::default())?;
                    parser.expect_sym(";")?;
                    arms.push(Arm { pattern, body });
                    if parser.is_sym("}") {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }

                    E::checkpoint(&mut parser.control, parser.point)?;
                }
                parser.expect_sym("}")?;
                return Ok(parser.push(
                    ExprKind::Match { scrutinee, arms },
                    (start, parser.prev_end()),
                ));
            }
            let quant = if parser.is_kw("forall") {
                Some(QuantKind::Forall)
            } else if parser.is_kw("exists") {
                Some(QuantKind::Exists)
            } else {
                None
            };
            if let Some(kind) = quant {
                parser.pos += 1;
                return parser.quantifier(kind, start, flags);
            }
            parser.binary(0, flags)
        })
    }

    /// 量化の `.` は字句の上では射影の `.` と区別できない。最上位の `.` を全て候補にし、
    /// 域(型)と本体がどちらも読め、本体が最も遠くまで読める候補を残す。選ぶのは核の型検査。
    fn quantifier(&mut self, kind: QuantKind, start: usize, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            let var = parser.ident()?;
            let typed = if parser.eat_kw("in") {
                false
            } else {
                parser.expect_sym(":")?;
                true
            };
            let from = parser.pos;
            let limit = parser.limit;
            let mut depth = 0isize;
            let mut dots = Vec::new();
            for i in from..limit {
                E::checkpoint(&mut parser.control, parser.point)?;
                let t = &parser.toks[i];
                if t.kind != TokenKind::Sym {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    continue;
                }
                match t.text.as_str() {
                    "(" | "[" | "{" => depth += 1,
                    ")" | "]" | "}" => {
                        depth -= 1;
                        if depth < 0 {
                            E::checkpoint(&mut parser.control, parser.point)?;
                            break;
                        }
                    }
                    ";" if depth == 0 => {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }
                    "." if depth == 0 => dots.push(i),
                    _ => {}
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            let mut candidates = Vec::new();
            let mut end = None;
            let mut first_error = None;
            let candidate_count = dots.len();
            for (candidate_index, c) in dots.into_iter().enumerate() {
                E::checkpoint(&mut parser.control, parser.point)?;
                let domain = if typed {
                    parser.parse_type_at(from, c).map(QuantDomain::Type)
                } else {
                    parser.parse_expr_at(from, c, flags).and_then(|(d, e)| {
                        if e == c {
                            Ok(QuantDomain::In(d))
                        } else {
                            Err(parser.err_at(e, "量化の域の終わりが必要"))
                        }
                    })
                };
                let domain = match domain {
                    Ok(d) => d,
                    Err(e) => {
                        if e.is_stopped() {
                            return Err(e);
                        }
                        first_error.get_or_insert(e);

                        if candidate_index + 1 == candidate_count && candidates.is_empty() {
                            break;
                        }

                        E::checkpoint(&mut parser.control, parser.point)?;
                        continue;
                    }
                };
                match parser.parse_expr_at(c + 1, limit, flags) {
                    Ok((body, e)) => {
                        end = end.max(Some(e));
                        candidates.push((domain, body, e));
                    }
                    Err(e) => {
                        if e.is_stopped() {
                            return Err(e);
                        }
                        first_error.get_or_insert(e);
                        if candidate_index + 1 == candidate_count && candidates.is_empty() {
                            break;
                        }
                    }
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            // 本体が最も遠くまで読める候補だけを残す。手前で終わる本体は、続く字句を読めなかった。
            let mut selected = Vec::new();
            for (domain, body, candidate_end) in candidates {
                E::checkpoint(&mut parser.control, parser.point)?;
                if Some(candidate_end) == end {
                    selected.push((domain, body));
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            let mut candidates = selected;
            let Some(end) = end else {
                return Err(first_error.unwrap_or_else(|| {
                    Box::new(Issue::law(
                        Code::Syntax,
                        parser.here(),
                        "量化の域と本体を区切る `.` が必要",
                    ))
                    .into()
                }));
            };
            parser.pos = end;
            let split = if candidates.len() == 1 {
                let (domain, body) = candidates.pop().expect("一つの候補");
                QuantSplit::Fixed { domain, body }
            } else {
                QuantSplit::Candidates(candidates)
            };
            Ok(parser.push(
                ExprKind::Quant { kind, var, split },
                (start, parser.prev_end()),
            ))
        })
    }

    fn err_at(&self, tok: usize, message: &str) -> E {
        let span = if tok < self.toks.len() {
            self.toks[tok].span
        } else {
            (self.src_len, self.src_len)
        };
        Box::new(Issue::law(Code::Syntax, span, message)).into()
    }

    /// 字句位置 `start` から `limit` の手前までをちょうど一つの型として読む。
    fn parse_type_at(&mut self, start: usize, limit: usize) -> PResult<TypeAst, E> {
        let (saved_pos, saved_limit) = (self.pos, self.limit);
        self.pos = start;
        self.limit = limit;
        let result = self.ty().and_then(|t| {
            if self.pos == limit {
                Ok(t)
            } else {
                self.err("量化の型の終わりが必要")
            }
        });
        self.pos = saved_pos;
        self.limit = saved_limit;
        result
    }

    fn binop(&self, flags: Flags) -> Option<(BinOp, u8)> {
        let t = self.peek()?;
        let op = match (t.kind, t.text.as_str()) {
            (TokenKind::Name, "implies") => (BinOp::Implies, 0),
            (TokenKind::Name, "or") => (BinOp::Or, 1),
            (TokenKind::Name, "and") => (BinOp::And, 2),
            (TokenKind::Sym, "=") => (BinOp::Eq, 3),
            (TokenKind::Sym, "!=") => (BinOp::Ne, 3),
            (TokenKind::Sym, "<") => (BinOp::Lt, 3),
            (TokenKind::Sym, "<=") => (BinOp::Le, 3),
            (TokenKind::Sym, ">") => (BinOp::Gt, 3),
            (TokenKind::Sym, ">=") => (BinOp::Ge, 3),
            (TokenKind::Name, "in") if !flags.no_in => (BinOp::In, 3),
            (TokenKind::Sym, "+") => (BinOp::Add, 4),
            (TokenKind::Sym, "-") => (BinOp::Sub, 4),
            (TokenKind::Sym, "*") => (BinOp::Mul, 5),
            _ => return None,
        };
        Some(op)
    }

    fn binary(&mut self, min_prec: u8, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
                let mut lhs = parser.unary(flags)?;
                let mut compared = false;
                while let Some((op, prec)) = parser.binop(flags) {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    if prec < min_prec {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }
                    if prec == 3 && compared {
                        return parser.err("比較は連鎖できない");
                    }
                    parser.pos += 1;
                    let rhs = if op == BinOp::Implies {
                        parser.binary(prec, flags)?
                    } else {
                        parser.binary(prec + 1, flags)?
                    };
                    let span = (parser.exprs[lhs].span.0, parser.exprs[rhs].span.1);
                    lhs = parser.push(ExprKind::Binary { op, lhs, rhs }, span);
                    compared = prec == 3;

                    E::checkpoint(&mut parser.control, parser.point)?;
                }
                Ok(lhs)
            })
        })
    }

    fn unary(&mut self, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
                let start = parser.here().0;
                let op = if parser.is_kw("not") {
                    UnOp::Not
                } else if parser.is_sym("-") {
                    UnOp::Neg
                } else {
                    return parser.postfix(flags);
                };
                parser.pos += 1;
                let operand = parser.unary(flags)?;
                let span = (start, parser.exprs[operand].span.1);
                Ok(parser.push(ExprKind::Unary { op, operand }, span))
            })
        })
    }

    fn postfix(&mut self, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            let mut base = parser.primary(flags)?;
            loop {
                E::checkpoint(&mut parser.control, parser.point)?;
                if parser.is_sym(".") {
                    let dot_tok = parser.pos;
                    match parser.peek_at(1) {
                        Some(t) if t.kind == TokenKind::Int => {
                            let index_span = t.span;
                            let index = t.text.parse::<usize>().map_err(|_| {
                                Box::new(Issue::law(
                                    Code::Syntax,
                                    index_span,
                                    "組の位置が大きすぎる",
                                ))
                            })?;
                            parser.pos += 2;
                            let span = (parser.exprs[base].span.0, index_span.1);
                            base = parser.push(
                                ExprKind::Index {
                                    base,
                                    index,
                                    index_span,
                                    dot_tok,
                                },
                                span,
                            );
                        }
                        Some(t) if t.kind == TokenKind::Name && !is_reserved(&t.text) => {
                            parser.pos += 1;
                            let name = parser.ident()?;
                            let span = (parser.exprs[base].span.0, name.span.1);
                            base = parser.push(ExprKind::Field { base, name }, span);
                        }
                        _ => {
                            E::checkpoint(&mut parser.control, parser.point)?;
                            break;
                        }
                    }
                } else if parser.is_sym("(") {
                    parser.pos += 1;
                    let mut args = Vec::new();
                    if !parser.is_sym(")") {
                        loop {
                            E::checkpoint(&mut parser.control, parser.point)?;
                            args.push(parser.parse_expr(Flags::default())?);
                            if !parser.eat_sym(",") {
                                E::checkpoint(&mut parser.control, parser.point)?;
                                break;
                            }

                            E::checkpoint(&mut parser.control, parser.point)?;
                        }
                    }
                    parser.expect_sym(")")?;
                    let span = (parser.exprs[base].span.0, parser.prev_end());
                    base = parser.push(ExprKind::Call { callee: base, args }, span);
                } else {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    break;
                }

                E::checkpoint(&mut parser.control, parser.point)?;
            }
            if parser.eat_kw("with") {
                parser.expect_sym("{")?;
                let mut updates = Vec::new();
                loop {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    let name = parser.ident()?;
                    parser.expect_sym("=")?;
                    updates.push((name, parser.parse_expr(Flags::default())?));
                    if !parser.eat_sym(",") {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }

                    E::checkpoint(&mut parser.control, parser.point)?;
                }
                parser.expect_sym("}")?;
                let span = (parser.exprs[base].span.0, parser.prev_end());
                base = parser.push(ExprKind::With { base, updates }, span);
            }
            let _ = flags;
            Ok(base)
        })
    }

    fn primary(&mut self, flags: Flags) -> PResult<ExprId, E> {
        self.checked(|parser| {
            let start = parser.here().0;
            let Some(t) = parser.peek().cloned() else {
                return parser.err("式が必要");
            };
            match t.kind {
                TokenKind::Int => {
                    parser.pos += 1;
                    return Ok(parser.push(ExprKind::Int(t.text), t.span));
                }
                TokenKind::Str => {
                    parser.pos += 1;
                    return Ok(parser.push(ExprKind::Str(t.text), t.span));
                }
                TokenKind::Sym if t.text == "(" => {
                    parser.pos += 1;
                    let first = parser.parse_expr(Flags::default())?;
                    if parser.eat_sym(",") {
                        let mut items = vec![first];
                        loop {
                            E::checkpoint(&mut parser.control, parser.point)?;
                            items.push(parser.parse_expr(Flags::default())?);
                            if !parser.eat_sym(",") {
                                E::checkpoint(&mut parser.control, parser.point)?;
                                break;
                            }

                            E::checkpoint(&mut parser.control, parser.point)?;
                        }
                        parser.expect_sym(")")?;
                        return Ok(parser.push(ExprKind::Tuple(items), (start, parser.prev_end())));
                    }
                    parser.expect_sym(")")?;
                    return Ok(parser.push(ExprKind::Group(first), (start, parser.prev_end())));
                }
                TokenKind::Sym => return parser.err("式が必要"),
                TokenKind::Name => {}
            }
            match t.text.as_str() {
                "true" | "false" => {
                    parser.pos += 1;
                    Ok(parser.push(ExprKind::Bool(t.text == "true"), t.span))
                }
                "unit" => {
                    parser.pos += 1;
                    Ok(parser.push(ExprKind::Unit, t.span))
                }
                "then" => {
                    if !parser
                        .peek_at(1)
                        .is_some_and(|n| n.kind == TokenKind::Sym && n.text == "(")
                    {
                        return parser.err("予約語 `then` は合成演算の適用位置だけで使える");
                    }
                    parser.pos += 1;
                    Ok(parser.push(ExprKind::ThenOp, t.span))
                }
                "list" => {
                    parser.pos += 1;
                    parser.expect_sym("<")?;
                    let ty = parser.ty()?;
                    parser.expect_sym(">")?;
                    parser.expect_sym("[")?;
                    let items = parser.items("]")?;
                    Ok(parser.push(ExprKind::ListLit { ty, items }, (start, parser.prev_end())))
                }
                "set" => {
                    parser.pos += 1;
                    if parser.eat_sym("<") {
                        let ty = parser.ty()?;
                        parser.expect_sym(">")?;
                        parser.expect_sym("{")?;
                        let items = parser.items("}")?;
                        return Ok(
                            parser.push(ExprKind::SetLit { ty, items }, (start, parser.prev_end()))
                        );
                    }
                    parser.expect_sym("{")?;
                    let elem = parser.parse_expr(Flags::default())?;
                    parser.expect_sym("|")?;
                    let var = parser.ident()?;
                    parser.expect_kw("in")?;
                    let domain = parser.parse_expr(Flags::default())?;
                    let filter = if parser.eat_kw("where") {
                        Some(parser.parse_expr(Flags::default())?)
                    } else {
                        None
                    };
                    parser.expect_sym("}")?;
                    Ok(parser.push(
                        ExprKind::SetComp {
                            elem,
                            var,
                            domain,
                            filter,
                        },
                        (start, parser.prev_end()),
                    ))
                }
                "none" => {
                    parser.pos += 1;
                    parser.expect_sym("<")?;
                    let ty = parser.ty()?;
                    parser.expect_sym(">")?;
                    Ok(parser.push(ExprKind::None(ty), (start, parser.prev_end())))
                }
                "some" => {
                    parser.pos += 1;
                    parser.expect_sym("(")?;
                    let inner = parser.parse_expr(Flags::default())?;
                    parser.expect_sym(")")?;
                    Ok(parser.push(ExprKind::Some(inner), (start, parser.prev_end())))
                }
                "fn" => {
                    parser.pos += 1;
                    let params = parser.fields()?;
                    parser.expect_sym("=>")?;
                    let body = parser.parse_expr(flags)?;
                    Ok(parser.push(ExprKind::Fn { params, body }, (start, parser.prev_end())))
                }
                _ => {
                    let name = parser.qname()?;
                    if parser.eat_sym("[") {
                        let owner = parser.parse_expr(Flags::default())?;
                        parser.expect_sym("]")?;
                        return Ok(parser
                            .push(ExprKind::Family { name, owner }, (start, parser.prev_end())));
                    }
                    let span = name.span();
                    Ok(parser.push(ExprKind::Dotted(name.parts), span))
                }
            }
        })
    }

    fn items(&mut self, close: &str) -> PResult<Vec<ExprId>, E> {
        self.checked(|parser| {
            let mut items = Vec::new();
            if !parser.is_sym(close) {
                loop {
                    E::checkpoint(&mut parser.control, parser.point)?;
                    items.push(parser.parse_expr(Flags::default())?);
                    if !parser.eat_sym(",") {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        break;
                    }

                    E::checkpoint(&mut parser.control, parser.point)?;
                }
            }
            parser.expect_sym(close)?;
            Ok(items)
        })
    }

    fn pattern(&mut self) -> PResult<Pattern, E> {
        self.checked(|parser| {
            stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
                if parser.is_sym("_") {
                    let span = parser.here();
                    parser.pos += 1;
                    return Ok(Pattern::Wild(span));
                }
                let name = parser.qname()?;
                if parser.eat_sym("(") {
                    let mut args = vec![parser.pattern()?];
                    while parser.is_sym(",") {
                        E::checkpoint(&mut parser.control, parser.point)?;
                        parser.pos += 1;
                        args.push(parser.pattern()?);

                        E::checkpoint(&mut parser.control, parser.point)?;
                    }
                    parser.expect_sym(")")?;
                    let span = (name.span().0, parser.prev_end());
                    return Ok(Pattern::Ctor { name, args, span });
                }
                if name.parts.len() == 1 {
                    return Ok(Pattern::Name(
                        name.parts.into_iter().next().expect("一つの名前"),
                    ));
                }
                let span = name.span();
                Ok(Pattern::Ctor {
                    name,
                    args: Vec::new(),
                    span,
                })
            })
        })
    }
}

impl Parser {
    pub fn new(toks: Vec<Token>, src_len: usize) -> Self {
        Self::with_error(toks, src_len, Control::unlimited())
    }
}
impl<E: InputError> Parser<E> {
    pub(super) fn at_checkpoint(mut self, point: Checkpoint) -> Self {
        self.point = point;
        self
    }
}

#[cfg(test)]
mod qname_interruption_tests {
    use super::*;
    use crate::observed::control::{CheckFailure, Limits, Resource, StopReason, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};

    #[test]
    fn qname_components_check_their_own_boundaries_without_lexing_or_outer_loops() {
        for text in ["alpha", "alpha.beta", "alpha.beta.gamma.delta"] {
            let tokens = super::super::lexer::lex(text.as_bytes()).unwrap();
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let control = Control::new(Limits::default(), move |point| {
                assert_eq!(point, Checkpoint::LawName);
                seen.set(seen.get() + 1);
                Usage::default()
            });
            let mut parser =
                Parser::<CheckFailure<Box<Issue>>>::with_error(tokens.clone(), text.len(), control);
            let name = parser.qname().unwrap();
            assert_eq!(name.parts.len(), text.split('.').count());
            parser.expect_end().unwrap();
            // Entry and first component, two boundaries per dot, then exit.
            let total = count.get();
            assert_eq!(total, 2 * name.parts.len() + 1);
            for at in 1..=total {
                for kind in 0..3 {
                    let mut visits = 0;
                    let control = Control::new(
                        Limits {
                            time_ms: (kind == 1).then_some(1),
                            memory_mib: (kind == 2).then_some(1),
                        },
                        move |point| {
                            assert_eq!(point, Checkpoint::LawName);
                            visits += 1;
                            let stop = visits == at;
                            Usage {
                                signal: (stop && kind == 0).then_some(Signal::Int),
                                elapsed_ms: u128::from(stop && kind == 1),
                                memory_mib: u128::from(stop && kind == 2),
                            }
                        },
                    );
                    let expected = match kind {
                        0 => StopReason::Cancelled(Signal::Int),
                        1 => StopReason::BudgetExhausted {
                            resource: Resource::TimeMs,
                            limit: 1,
                            observed: 1,
                        },
                        _ => StopReason::BudgetExhausted {
                            resource: Resource::MemoryMib,
                            limit: 1,
                            observed: 1,
                        },
                    };
                    let mut parser = Parser::<CheckFailure<Box<Issue>>>::with_error(
                        tokens.clone(),
                        text.len(),
                        control,
                    );
                    let stopped = parser.qname().unwrap_err();
                    assert!(
                        matches!(stopped, CheckFailure::Stopped(ref r) if r == &expected),
                        "{text} {at}: {stopped:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn malformed_first_qname_component_checks_after_error_before_returning_it() {
        let tokens = super::super::lexer::lex(b"(").unwrap();
        let mut ordinary = Parser::new(tokens.clone(), 1);
        assert_eq!(ordinary.qname().unwrap_err().code, Code::Syntax);
        for at in [1, 2] {
            let mut visits = 0;
            let control = Control::new(Limits::default(), move |point| {
                assert_eq!(point, Checkpoint::LawName);
                visits += 1;
                Usage {
                    signal: (visits == at).then_some(Signal::Term),
                    ..Usage::default()
                }
            });
            let mut controlled =
                Parser::<CheckFailure<Box<Issue>>>::with_error(tokens.clone(), 1, control);
            assert!(matches!(
                controlled.qname(),
                Err(CheckFailure::Stopped(StopReason::Cancelled(Signal::Term)))
            ));
        }
    }

    #[test]
    fn parser_loop_post_boundaries_cover_success_errors_and_speculative_candidates() {
        type Failure = CheckFailure<Box<Issue>>;
        let run = |text: &str, kind: u8, control: Control| -> Result<(), Failure> {
            // Lex independently: only parser iteration boundaries trigger the probe.
            let tokens = super::super::lexer::lex(text.as_bytes()).unwrap();
            let mut parser = Parser::<Failure>::with_error(tokens, text.len(), control);
            match kind {
                0 => parser.fields().map(|_| ()),
                1 => parser.readings().map(|_| ()),
                2 => parser.parse_expr(Flags::default()).map(|_| ()),
                _ => parser.change_tail().map(|_| ()),
            }
        };
        for (text, operation, valid) in [
            ("(x: Z,y:(Z,Q),f:Term<(Z,Q)->Z>)", 0, true),
            (
                "reading R { view f(x: Z,y: Z): Z = x + y; local C(x: Z) reads x,x; }",
                1,
                true,
            ),
            ("match x { A(a,b) => (a,b); B => list<Z>[1,2]; }", 2, true),
            ("f(1,2).x with {a=1,b=2}", 2, true),
            ("forall x: Z . exists y: Z . x = y", 2, true),
            ("when x = 1 = x;", 3, true),
            ("(x: Z,)", 0, false),
            ("f(1,)", 2, false),
            ("forall x: Z .", 2, false),
            ("when x = ;", 3, false),
        ] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let control = Control::new(Limits::default(), move |point| {
                if point == Checkpoint::LawIteration {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            });
            assert_eq!(run(text, operation, control).is_ok(), valid, "{text}");
            let total = count.get();
            assert!(total > 2, "{text}");
            for at in [1, total / 2, total - 1, total] {
                for mode in 0..3 {
                    let mut visits = 0;
                    let control = Control::new(
                        Limits {
                            time_ms: (mode == 1).then_some(1),
                            memory_mib: (mode == 2).then_some(1),
                        },
                        move |point| {
                            if point == Checkpoint::LawIteration {
                                visits += 1;
                            }
                            let stop = visits == at;
                            Usage {
                                signal: (stop && mode == 0).then_some(Signal::Term),
                                elapsed_ms: u128::from(stop && mode == 1),
                                memory_mib: u128::from(stop && mode == 2),
                            }
                        },
                    );
                    let expected = match mode {
                        0 => StopReason::Cancelled(Signal::Term),
                        1 => StopReason::BudgetExhausted {
                            resource: Resource::TimeMs,
                            limit: 1,
                            observed: 1,
                        },
                        _ => StopReason::BudgetExhausted {
                            resource: Resource::MemoryMib,
                            limit: 1,
                            observed: 1,
                        },
                    };
                    let stopped = run(text, operation, control.clone()).unwrap_err();
                    if !valid && mode > 0 && at == total {
                        assert!(
                            matches!(stopped, CheckFailure::Input(_)),
                            "final known Syntax must survive budget: {text}"
                        );
                    }
                    match stopped {
                        CheckFailure::Stopped(reason) => assert_eq!(reason, expected),
                        CheckFailure::Input(issue) => {
                            assert!(!valid && mode > 0, "{text} {at}/{total}");
                            assert_eq!(issue.code, Code::Syntax);
                        }
                    }
                    assert_eq!(control.stop_reason(), Some(expected));
                }
            }
        }
    }
}

#[cfg(test)]
pub(super) mod candidate_priority_tests {
    use super::*;
    use crate::{
        issue::Location,
        observed::control::{CheckFailure, Limits, StopReason, Usage},
        result::Signal,
    };
    use std::{
        cell::{Cell, RefCell},
        rc::Rc,
    };

    // Arm only after the selected diagnostic has actually been constructed.
    // Counting outer checkpoints cannot identify this candidate-local boundary.
    thread_local! {
        static ERROR_ARM: RefCell<Option<(Span, Rc<Cell<bool>>)>> = const { RefCell::new(None) };
    }
    #[derive(Debug)]
    pub(crate) struct Failure(pub CheckFailure<Box<Issue>>);
    impl From<Box<Issue>> for Failure {
        fn from(issue: Box<Issue>) -> Self {
            ERROR_ARM.with(|state| {
                if let Some((target, armed)) = state.borrow().as_ref()
                    && issue.location == (Location::Law { span: *target })
                {
                    armed.set(true);
                }
            });
            Self(CheckFailure::Input(issue))
        }
    }
    impl InputError for Failure {
        fn checkpoint(control: &mut Control, point: Checkpoint) -> Result<(), Self> {
            <CheckFailure<Box<Issue>> as InputError>::checkpoint(control, point).map_err(Self)
        }
        fn map_issue(self, map: impl FnOnce(Box<Issue>) -> Box<Issue>) -> Self {
            Self(self.0.map_issue(map))
        }
        fn is_stopped(&self) -> bool {
            self.0.is_stopped()
        }
        fn is_budget_stop(&self) -> bool {
            self.0.is_budget_stop()
        }
    }
    pub(crate) struct ErrorArm;
    impl Drop for ErrorArm {
        fn drop(&mut self) {
            ERROR_ARM.with(|state| *state.borrow_mut() = None);
        }
    }
    pub(crate) fn stop_after_issue(span: Span, mode: usize) -> (Control, ErrorArm, Rc<Cell<bool>>) {
        let armed = Rc::new(Cell::new(false));
        ERROR_ARM.with(|state| {
            assert!(state.borrow().is_none());
            *state.borrow_mut() = Some((span, armed.clone()));
        });
        let probe = armed.clone();
        let control = Control::new(
            Limits {
                time_ms: (mode == 1).then_some(1),
                memory_mib: (mode == 2).then_some(1),
            },
            move |_| Usage {
                signal: (probe.get() && mode == 0).then_some(Signal::Term),
                elapsed_ms: u128::from(probe.get() && mode == 1),
                memory_mib: u128::from(probe.get() && mode == 2),
            },
        );
        (control, ErrorArm, armed)
    }
    fn run(text: &str, change: bool, control: Control) -> Result<(), Failure> {
        let tokens = super::super::lexer::lex(text.as_bytes()).unwrap();
        let mut parser = Parser::<Failure>::with_error(tokens, text.len(), control);
        if change {
            parser.change_tail().map(|_| ())
        } else {
            parser.parse_expr(Flags::default()).map(|_| ())
        }
    }
    #[test]
    fn final_candidate_syntax_survives_budget_at_first_post_error_sample() {
        for (text, change, span) in [
            ("when true = ;", true, (12, 13)),
            ("forall x: Z .", false, (13, 13)),
            ("forall x: . true", false, (10, 11)),
        ] {
            let Failure(CheckFailure::Input(expected)) =
                run(text, change, Control::unlimited()).unwrap_err()
            else {
                panic!("ordinary Syntax expected")
            };
            assert_eq!(expected.code, Code::Syntax);
            assert_eq!(expected.location, Location::Law { span });
            for mode in 0..3 {
                let (control, _arm, observed) = stop_after_issue(span, mode);
                let failure = run(text, change, control.clone()).unwrap_err();
                assert!(observed.get(), "{text}: candidate error was not reached");
                if mode == 0 {
                    assert!(matches!(
                        failure.0,
                        CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
                    ));
                } else {
                    let CheckFailure::Input(actual) = failure.0 else {
                        panic!("{text}: final Syntax replaced by budget")
                    };
                    assert_eq!(actual, expected);
                    assert!(matches!(
                        control.stop_reason(),
                        Some(StopReason::BudgetExhausted { .. })
                    ));
                }
            }
        }
    }
    #[test]
    fn speculative_syntax_cannot_replace_untried_or_valid_candidates() {
        for (text, change, span) in [
            // The rightmost split fails; a leftward split remains untried.
            ("when true = false = ;", true, (20, 21)),
            // The earlier dot already has a syntactically valid domain/body.
            ("forall x: A . b.", false, (16, 16)),
        ] {
            for mode in 0..3 {
                let (control, _arm, observed) = stop_after_issue(span, mode);
                let failure = run(text, change, control.clone()).unwrap_err();
                assert!(observed.get(), "{text}: speculative error was not reached");
                assert!(
                    matches!(failure.0, CheckFailure::Stopped(_)),
                    "{text}: speculative Syntax became final"
                );
                assert!(control.stop_reason().is_some());
            }
        }
    }
}
