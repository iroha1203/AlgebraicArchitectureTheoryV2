//! Law の構文解析(Law 仕様 §§2–4)。
//!
//! 深い入れ子でも落ちないよう、再帰する関数は `stacker` で必要に応じてスタックを伸ばす。

use super::ast::*;
use super::lexer::{Token, TokenKind};
use crate::issue::{Code, Issue};
use std::collections::HashMap;

/// 予約語と組込み型名。識別子として使えない。
pub const RESERVED: &[&str] = &[
    "law",
    "semantics",
    "reading",
    "use",
    "as",
    "entity",
    "arrow",
    "correspondence",
    "align",
    "data",
    "view",
    "required",
    "optional",
    "local",
    "reads",
    "change",
    "relation",
    "when",
    "let",
    "in",
    "if",
    "then",
    "else",
    "match",
    "forall",
    "exists",
    "not",
    "implies",
    "or",
    "and",
    "with",
    "true",
    "false",
    "unit",
    "list",
    "set",
    "where",
    "none",
    "some",
    "fn",
    "Unit",
    "Bool",
    "Z",
    "Q",
    "Text",
    "Fp",
    "List",
    "Set",
    "Option",
    "Map",
    "Term",
    "Path",
];

pub fn is_reserved(name: &str) -> bool {
    RESERVED.contains(&name)
}

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

type PResult<T> = Result<T, Box<Issue>>;

pub struct Parser {
    pub toks: Vec<Token>,
    pub exprs: Vec<Expr>,
    src_len: usize,
    pos: usize,
    limit: usize,
    memo: HashMap<(usize, usize, Flags), (ExprId, usize)>,
}

impl Parser {
    pub fn new(toks: Vec<Token>, src_len: usize) -> Parser {
        let limit = toks.len();
        Parser {
            toks,
            exprs: Vec::new(),
            src_len,
            pos: 0,
            limit,
            memo: HashMap::new(),
        }
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

    fn err<T>(&self, message: impl Into<String>) -> PResult<T> {
        Err(Box::new(Issue::law(Code::Syntax, self.here(), message)))
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

    fn expect_sym(&mut self, s: &str) -> PResult<Span> {
        if self.is_sym(s) {
            self.pos += 1;
            Ok(self.toks[self.pos - 1].span)
        } else {
            self.err(format!("`{s}` が必要"))
        }
    }

    fn expect_kw(&mut self, s: &str) -> PResult<Span> {
        if self.is_kw(s) {
            self.pos += 1;
            Ok(self.toks[self.pos - 1].span)
        } else {
            self.err(format!("`{s}` が必要"))
        }
    }

    fn is_ident(&self) -> bool {
        self.peek()
            .is_some_and(|t| t.kind == TokenKind::Name && !is_reserved(&t.text))
    }

    fn ident(&mut self) -> PResult<Ident> {
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

    fn string(&mut self) -> PResult<String> {
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
    fn qname(&mut self) -> PResult<QName> {
        let mut parts = vec![self.ident()?];
        while self.is_sym(".")
            && self
                .peek_at(1)
                .is_some_and(|t| t.kind == TokenKind::Name && !is_reserved(&t.text))
        {
            self.pos += 1;
            parts.push(self.ident()?);
        }
        Ok(QName { parts })
    }

    fn push(&mut self, kind: ExprKind, span: Span) -> ExprId {
        self.exprs.push(Expr { kind, span });
        self.exprs.len() - 1
    }

    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id]
    }

    // ---- 文書 ----

    pub fn header(&mut self) -> PResult<Header> {
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

    pub fn readings(&mut self) -> PResult<Vec<Reading>> {
        let mut readings = Vec::new();
        loop {
            readings.push(self.reading()?);
            if self.peek().is_none() {
                return Ok(readings);
            }
        }
    }

    fn reading(&mut self) -> PResult<Reading> {
        let start = self.here().0;
        self.expect_kw("reading")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut uses = Vec::new();
        let mut decls = Vec::new();
        while !self.is_sym("}") {
            if self.eat_kw("use") {
                let reading = self.ident()?;
                self.expect_kw("as")?;
                let alias = self.ident()?;
                self.expect_sym(";")?;
                uses.push(Use { reading, alias });
            } else {
                decls.push(self.decl()?);
            }
        }
        self.expect_sym("}")?;
        Ok(Reading {
            name,
            uses,
            decls,
            span: (start, self.prev_end()),
        })
    }

    fn decl(&mut self) -> PResult<Decl> {
        let start = self.here().0;
        let Some(t) = self.peek() else {
            return self.err("宣言または `}` が必要");
        };
        let keyword = if t.kind == TokenKind::Name {
            t.text.clone()
        } else {
            String::new()
        };
        let (name, kind) = match keyword.as_str() {
            "entity" => {
                self.pos += 1;
                let name = self.ident()?;
                let params = if self.is_sym("(") {
                    self.fields()?
                } else {
                    Vec::new()
                };
                let members = self.members_or_semicolon()?;
                (name, DeclKind::Entity { params, members })
            }
            "arrow" => {
                self.pos += 1;
                let name = self.ident()?;
                let params = self.fields()?;
                let members = self.members_or_semicolon()?;
                (name, DeclKind::Arrow { params, members })
            }
            "correspondence" => {
                self.pos += 1;
                let name = self.ident()?;
                let params = self.fields()?;
                self.expect_sym("{")?;
                let mut members = Vec::new();
                let mut alignments = Vec::new();
                while !self.is_sym("}") {
                    if self.eat_kw("align") {
                        let source = self.qname()?;
                        self.expect_sym("=")?;
                        let target = self.qname()?;
                        self.expect_sym(";")?;
                        alignments.push(Alignment { source, target });
                    } else if alignments.is_empty() {
                        members.push(self.member()?);
                    } else {
                        return self.err("align の後に field は置けない");
                    }
                }
                self.expect_sym("}")?;
                (
                    name,
                    DeclKind::Correspondence {
                        params,
                        members,
                        alignments,
                    },
                )
            }
            "data" => {
                self.pos += 1;
                let name = self.ident()?;
                self.expect_sym("=")?;
                let mut constructors = vec![self.constructor()?];
                while self.eat_sym("|") {
                    constructors.push(self.constructor()?);
                }
                self.expect_sym(";")?;
                (name, DeclKind::Data { constructors })
            }
            "view" => {
                self.pos += 1;
                let name = self.ident()?;
                let params = self.fields()?;
                self.expect_sym(":")?;
                let returns = self.ty()?;
                self.expect_sym("=")?;
                let body = self.parse_expr(Flags::default())?;
                self.expect_sym(";")?;
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
                self.pos += 1;
                let role = if self.eat_kw("required") {
                    Role::Required
                } else if self.eat_kw("optional") {
                    Role::Optional
                } else {
                    return self.err("`required` または `optional` が必要");
                };
                let name = self.ident()?;
                let params = self.fields()?;
                let guard = self.guard()?;
                self.expect_sym(":")?;
                let body = self.parse_expr(Flags::default())?;
                self.expect_sym(";")?;
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
                self.pos += 1;
                let name = self.ident()?;
                let params = self.fields()?;
                let guard = self.guard()?;
                self.expect_kw("reads")?;
                let mut reads = vec![self.parse_expr(Flags::default())?];
                while self.eat_sym(",") {
                    reads.push(self.parse_expr(Flags::default())?);
                }
                self.expect_sym(";")?;
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
                self.pos += 1;
                let name = self.ident()?;
                let params = self.fields()?;
                let (guard, body) = self.change_tail()?;
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
                self.pos += 1;
                let name = self.ident()?;
                let params = self.fields()?;
                let guard = self.guard()?;
                self.expect_sym(":")?;
                let body = self.parse_expr(Flags::default())?;
                self.expect_sym(";")?;
                (
                    name,
                    DeclKind::Relation {
                        params,
                        guard,
                        body,
                    },
                )
            }
            _ => return self.err("宣言または `}` が必要"),
        };
        Ok(Decl {
            name,
            kind,
            span: (start, self.prev_end()),
        })
    }

    fn guard(&mut self) -> PResult<Option<ExprId>> {
        if self.eat_kw("when") {
            Ok(Some(self.parse_expr(Flags::default())?))
        } else {
            Ok(None)
        }
    }

    /// change の guard と body は、宣言の最上位にある最後の `=` で区切る。
    /// body は `with` 更新であり、その `=` は波括弧の内側にある。
    fn change_tail(&mut self) -> PResult<(Option<ExprId>, ExprId)> {
        if !self.eat_kw("when") {
            self.expect_sym("=")?;
            let body = self.parse_expr(Flags::default())?;
            self.expect_sym(";")?;
            return Ok((None, body));
        }
        let mut depth = 0isize;
        let mut last_eq = None;
        let mut end = None;
        for i in self.pos..self.limit {
            let t = &self.toks[i];
            if t.kind != TokenKind::Sym {
                continue;
            }
            match t.text.as_str() {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => {
                    depth -= 1;
                    if depth < 0 {
                        break;
                    }
                }
                "=" if depth == 0 => last_eq = Some(i),
                ";" if depth == 0 => {
                    end = Some(i);
                    break;
                }
                _ => {}
            }
        }
        let (Some(eq), Some(end)) = (last_eq, end) else {
            return self.err("change の guard の後に `=` と body が必要");
        };
        let guard = self.parse_until(eq, |p| p.parse_expr(Flags::default()))?;
        self.pos = eq + 1;
        let body = self.parse_until(end, |p| p.parse_expr(Flags::default()))?;
        self.pos = end + 1;
        Ok((Some(guard), body))
    }

    /// `limit` までの字句をちょうど読み切る。
    fn parse_until<T>(
        &mut self,
        limit: usize,
        f: impl FnOnce(&mut Self) -> PResult<T>,
    ) -> PResult<T> {
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

    fn fields(&mut self) -> PResult<Vec<Field>> {
        self.expect_sym("(")?;
        let mut fields = Vec::new();
        if !self.is_sym(")") {
            loop {
                let name = self.ident()?;
                self.expect_sym(":")?;
                fields.push(Field {
                    name,
                    ty: self.ty()?,
                });
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        Ok(fields)
    }

    fn member(&mut self) -> PResult<Field> {
        let name = self.ident()?;
        self.expect_sym(":")?;
        let ty = self.ty()?;
        self.expect_sym(";")?;
        Ok(Field { name, ty })
    }

    fn members_or_semicolon(&mut self) -> PResult<Vec<Field>> {
        if self.eat_sym(";") {
            return Ok(Vec::new());
        }
        self.expect_sym("{")?;
        let mut members = Vec::new();
        while !self.is_sym("}") {
            members.push(self.member()?);
        }
        self.expect_sym("}")?;
        Ok(members)
    }

    fn constructor(&mut self) -> PResult<Constructor> {
        let name = self.ident()?;
        let mut args = Vec::new();
        if self.eat_sym("(") {
            loop {
                args.push(self.ty()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym(")")?;
        }
        let span = (name.span.0, self.prev_end());
        Ok(Constructor { name, args, span })
    }

    // ---- 型 ----

    pub fn ty(&mut self) -> PResult<TypeAst> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || self.ty_inner())
    }

    fn ty_inner(&mut self) -> PResult<TypeAst> {
        let start = self.here().0;
        let Some(t) = self.peek().cloned() else {
            return self.err("型が必要");
        };
        let builtin = |b| Ok(TypeAst::Builtin(b, t.span));
        if t.kind == TokenKind::Name {
            match t.text.as_str() {
                "Unit" => {
                    self.pos += 1;
                    return builtin(Builtin::Unit);
                }
                "Bool" => {
                    self.pos += 1;
                    return builtin(Builtin::Bool);
                }
                "Z" => {
                    self.pos += 1;
                    return builtin(Builtin::Z);
                }
                "Q" => {
                    self.pos += 1;
                    return builtin(Builtin::Q);
                }
                "Text" => {
                    self.pos += 1;
                    return builtin(Builtin::Text);
                }
                "Fp" => {
                    self.pos += 1;
                    self.expect_sym("(")?;
                    let modulus = match self.peek() {
                        Some(t) if t.kind == TokenKind::Int => t.text.clone(),
                        _ => return self.err("Fp の法は10進整数"),
                    };
                    self.pos += 1;
                    self.expect_sym(")")?;
                    return Ok(TypeAst::Fp {
                        modulus,
                        span: (start, self.prev_end()),
                    });
                }
                "List" | "Set" | "Option" => {
                    self.pos += 1;
                    self.expect_sym("<")?;
                    let inner = Box::new(self.ty()?);
                    self.expect_sym(">")?;
                    let span = (start, self.prev_end());
                    return Ok(match t.text.as_str() {
                        "List" => TypeAst::List(inner, span),
                        "Set" => TypeAst::Set(inner, span),
                        _ => TypeAst::Option(inner, span),
                    });
                }
                "Map" => {
                    self.pos += 1;
                    self.expect_sym("<")?;
                    let a = Box::new(self.ty()?);
                    self.expect_sym(",")?;
                    let b = Box::new(self.ty()?);
                    self.expect_sym(">")?;
                    return Ok(TypeAst::Map(a, b, (start, self.prev_end())));
                }
                "Term" => {
                    self.pos += 1;
                    self.expect_sym("<")?;
                    self.expect_sym("(")?;
                    let mut args = Vec::new();
                    if !self.is_sym(")") {
                        loop {
                            args.push(self.ty()?);
                            if !self.eat_sym(",") {
                                break;
                            }
                        }
                    }
                    self.expect_sym(")")?;
                    self.expect_sym("->")?;
                    let ret = Box::new(self.ty()?);
                    self.expect_sym(">")?;
                    return Ok(TypeAst::Term(args, ret, (start, self.prev_end())));
                }
                "Path" => {
                    self.pos += 1;
                    self.expect_sym("<")?;
                    let a = self.qname()?;
                    self.expect_sym(",")?;
                    let b = self.qname()?;
                    self.expect_sym(">")?;
                    return Ok(TypeAst::Path(a, b, (start, self.prev_end())));
                }
                _ => {}
            }
        }
        if self.eat_sym("(") {
            let mut items = vec![self.ty()?];
            while self.eat_sym(",") {
                items.push(self.ty()?);
            }
            self.expect_sym(")")?;
            if items.len() < 2 {
                return Err(Box::new(Issue::law(
                    Code::Syntax,
                    (start, self.prev_end()),
                    "組の型は二つ以上の成分を持つ",
                )));
            }
            return Ok(TypeAst::Tuple(items, (start, self.prev_end())));
        }
        let name = self.qname()?;
        let index = if self.eat_sym("[") {
            let i = self.ident()?;
            self.expect_sym("]")?;
            Some(i)
        } else {
            None
        };
        Ok(TypeAst::Named {
            name,
            index,
            span: (start, self.prev_end()),
        })
    }

    // ---- 式 ----

    pub fn parse_expr(&mut self, flags: Flags) -> PResult<ExprId> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || self.expr_inner(flags))
    }

    /// 字句位置 `start` から `limit` の手前までで一つの式を読む。量化の区切りを決め直すときに使う。
    pub fn parse_expr_at(
        &mut self,
        start: usize,
        limit: usize,
        flags: Flags,
    ) -> PResult<(ExprId, usize)> {
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

    fn expr_inner(&mut self, flags: Flags) -> PResult<ExprId> {
        let start = self.here().0;
        if self.eat_kw("let") {
            let name = self.ident()?;
            self.expect_sym("=")?;
            let value = self.parse_expr(Flags { no_in: true })?;
            self.expect_kw("in")?;
            let body = self.parse_expr(flags)?;
            return Ok(self.push(
                ExprKind::Let { name, value, body },
                (start, self.prev_end()),
            ));
        }
        if self.eat_kw("if") {
            let cond = self.parse_expr(Flags::default())?;
            self.expect_kw("then")?;
            let then_branch = self.parse_expr(Flags::default())?;
            self.expect_kw("else")?;
            let else_branch = self.parse_expr(flags)?;
            return Ok(self.push(
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                },
                (start, self.prev_end()),
            ));
        }
        if self.eat_kw("match") {
            let scrutinee = self.parse_expr(Flags::default())?;
            self.expect_sym("{")?;
            let mut arms = Vec::new();
            loop {
                let pattern = self.pattern()?;
                self.expect_sym("=>")?;
                let body = self.parse_expr(Flags::default())?;
                self.expect_sym(";")?;
                arms.push(Arm { pattern, body });
                if self.is_sym("}") {
                    break;
                }
            }
            self.expect_sym("}")?;
            return Ok(self.push(
                ExprKind::Match { scrutinee, arms },
                (start, self.prev_end()),
            ));
        }
        let quant = if self.is_kw("forall") {
            Some(QuantKind::Forall)
        } else if self.is_kw("exists") {
            Some(QuantKind::Exists)
        } else {
            None
        };
        if let Some(kind) = quant {
            self.pos += 1;
            return self.quantifier(kind, start, flags);
        }
        self.binary(0, flags)
    }

    fn quantifier(&mut self, kind: QuantKind, start: usize, flags: Flags) -> PResult<ExprId> {
        let var = self.ident()?;
        let limit = self.limit;
        let split = if self.eat_kw("in") {
            let glued = self.parse_expr(flags)?;
            if self.eat_sym(".") {
                let body = self.parse_expr(flags)?;
                QuantSplit::Fixed {
                    domain: QuantDomain::In(glued),
                    body,
                }
            } else {
                QuantSplit::InGlued { glued }
            }
        } else {
            self.expect_sym(":")?;
            if self.is_ident() {
                let name = self.qname()?;
                if self.is_sym("[") {
                    self.pos += 1;
                    let index = self.ident()?;
                    self.expect_sym("]")?;
                    let span = (name.span().0, self.prev_end());
                    self.expect_sym(".")?;
                    let body = self.parse_expr(flags)?;
                    QuantSplit::Fixed {
                        domain: QuantDomain::Type(TypeAst::Named {
                            name,
                            index: Some(index),
                            span,
                        }),
                        body,
                    }
                } else if self.eat_sym(".") {
                    let span = name.span();
                    let body = self.parse_expr(flags)?;
                    QuantSplit::Fixed {
                        domain: QuantDomain::Type(TypeAst::Named {
                            name,
                            index: None,
                            span,
                        }),
                        body,
                    }
                } else if name.parts.len() > 1 {
                    // 本体は名前列の途中から始まる。最短の型名から読んだ本体で終わりを決める。
                    let (_, end) = self.parse_expr_at(name.parts[1].tok, limit, flags)?;
                    self.pos = end;
                    QuantSplit::TypedChain { parts: name.parts }
                } else {
                    return self.err("量化の型の後に `.` が必要");
                }
            } else {
                let ty = self.ty()?;
                self.expect_sym(".")?;
                let body = self.parse_expr(flags)?;
                QuantSplit::Fixed {
                    domain: QuantDomain::Type(ty),
                    body,
                }
            }
        };
        let end = self.pos;
        Ok(self.push(
            ExprKind::Quant {
                kind,
                var,
                split,
                flags,
                limit,
                end,
            },
            (start, self.prev_end()),
        ))
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

    fn binary(&mut self, min_prec: u8, flags: Flags) -> PResult<ExprId> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let mut lhs = self.unary(flags)?;
            let mut compared = false;
            while let Some((op, prec)) = self.binop(flags) {
                if prec < min_prec {
                    break;
                }
                if prec == 3 && compared {
                    return self.err("比較は連鎖できない");
                }
                self.pos += 1;
                let rhs = if op == BinOp::Implies {
                    self.binary(prec, flags)?
                } else {
                    self.binary(prec + 1, flags)?
                };
                let span = (self.exprs[lhs].span.0, self.exprs[rhs].span.1);
                lhs = self.push(ExprKind::Binary { op, lhs, rhs }, span);
                compared = prec == 3;
            }
            Ok(lhs)
        })
    }

    fn unary(&mut self, flags: Flags) -> PResult<ExprId> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let start = self.here().0;
            let op = if self.is_kw("not") {
                UnOp::Not
            } else if self.is_sym("-") {
                UnOp::Neg
            } else {
                return self.postfix(flags);
            };
            self.pos += 1;
            let operand = self.unary(flags)?;
            let span = (start, self.exprs[operand].span.1);
            Ok(self.push(ExprKind::Unary { op, operand }, span))
        })
    }

    fn postfix(&mut self, flags: Flags) -> PResult<ExprId> {
        let mut base = self.primary(flags)?;
        loop {
            if self.is_sym(".") {
                let dot_tok = self.pos;
                match self.peek_at(1) {
                    Some(t) if t.kind == TokenKind::Int => {
                        let index_span = t.span;
                        let index = t.text.parse::<usize>().map_err(|_| {
                            Box::new(Issue::law(Code::Syntax, index_span, "組の位置が大きすぎる"))
                        })?;
                        self.pos += 2;
                        let span = (self.exprs[base].span.0, index_span.1);
                        base = self.push(
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
                        self.pos += 1;
                        let name = self.ident()?;
                        let span = (self.exprs[base].span.0, name.span.1);
                        base = self.push(ExprKind::Field { base, name }, span);
                    }
                    _ => break,
                }
            } else if self.is_sym("(") {
                self.pos += 1;
                let mut args = Vec::new();
                if !self.is_sym(")") {
                    loop {
                        args.push(self.parse_expr(Flags::default())?);
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                }
                self.expect_sym(")")?;
                let span = (self.exprs[base].span.0, self.prev_end());
                base = self.push(ExprKind::Call { callee: base, args }, span);
            } else {
                break;
            }
        }
        if self.eat_kw("with") {
            self.expect_sym("{")?;
            let mut updates = Vec::new();
            loop {
                let name = self.ident()?;
                self.expect_sym("=")?;
                updates.push((name, self.parse_expr(Flags::default())?));
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym("}")?;
            let span = (self.exprs[base].span.0, self.prev_end());
            base = self.push(ExprKind::With { base, updates }, span);
        }
        let _ = flags;
        Ok(base)
    }

    fn primary(&mut self, flags: Flags) -> PResult<ExprId> {
        let start = self.here().0;
        let Some(t) = self.peek().cloned() else {
            return self.err("式が必要");
        };
        match t.kind {
            TokenKind::Int => {
                self.pos += 1;
                return Ok(self.push(ExprKind::Int(t.text), t.span));
            }
            TokenKind::Str => {
                self.pos += 1;
                return Ok(self.push(ExprKind::Str(t.text), t.span));
            }
            TokenKind::Sym if t.text == "(" => {
                self.pos += 1;
                let first = self.parse_expr(Flags::default())?;
                if self.eat_sym(",") {
                    let mut items = vec![first];
                    loop {
                        items.push(self.parse_expr(Flags::default())?);
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                    self.expect_sym(")")?;
                    return Ok(self.push(ExprKind::Tuple(items), (start, self.prev_end())));
                }
                self.expect_sym(")")?;
                return Ok(self.push(ExprKind::Group(first), (start, self.prev_end())));
            }
            TokenKind::Sym => return self.err("式が必要"),
            TokenKind::Name => {}
        }
        match t.text.as_str() {
            "true" | "false" => {
                self.pos += 1;
                Ok(self.push(ExprKind::Bool(t.text == "true"), t.span))
            }
            "unit" => {
                self.pos += 1;
                Ok(self.push(ExprKind::Unit, t.span))
            }
            "then" => {
                if !self
                    .peek_at(1)
                    .is_some_and(|n| n.kind == TokenKind::Sym && n.text == "(")
                {
                    return self.err("予約語 `then` は合成演算の適用位置だけで使える");
                }
                self.pos += 1;
                Ok(self.push(ExprKind::ThenOp, t.span))
            }
            "list" => {
                self.pos += 1;
                self.expect_sym("<")?;
                let ty = self.ty()?;
                self.expect_sym(">")?;
                self.expect_sym("[")?;
                let items = self.items("]")?;
                Ok(self.push(ExprKind::ListLit { ty, items }, (start, self.prev_end())))
            }
            "set" => {
                self.pos += 1;
                if self.eat_sym("<") {
                    let ty = self.ty()?;
                    self.expect_sym(">")?;
                    self.expect_sym("{")?;
                    let items = self.items("}")?;
                    return Ok(self.push(ExprKind::SetLit { ty, items }, (start, self.prev_end())));
                }
                self.expect_sym("{")?;
                let elem = self.parse_expr(Flags::default())?;
                self.expect_sym("|")?;
                let var = self.ident()?;
                self.expect_kw("in")?;
                let domain = self.parse_expr(Flags::default())?;
                let filter = if self.eat_kw("where") {
                    Some(self.parse_expr(Flags::default())?)
                } else {
                    None
                };
                self.expect_sym("}")?;
                Ok(self.push(
                    ExprKind::SetComp {
                        elem,
                        var,
                        domain,
                        filter,
                    },
                    (start, self.prev_end()),
                ))
            }
            "none" => {
                self.pos += 1;
                self.expect_sym("<")?;
                let ty = self.ty()?;
                self.expect_sym(">")?;
                Ok(self.push(ExprKind::None(ty), (start, self.prev_end())))
            }
            "some" => {
                self.pos += 1;
                self.expect_sym("(")?;
                let inner = self.parse_expr(Flags::default())?;
                self.expect_sym(")")?;
                Ok(self.push(ExprKind::Some(inner), (start, self.prev_end())))
            }
            "fn" => {
                self.pos += 1;
                let params = self.fields()?;
                self.expect_sym("=>")?;
                let body = self.parse_expr(flags)?;
                Ok(self.push(ExprKind::Fn { params, body }, (start, self.prev_end())))
            }
            _ => {
                let name = self.qname()?;
                if self.eat_sym("[") {
                    let owner = self.parse_expr(Flags::default())?;
                    self.expect_sym("]")?;
                    return Ok(
                        self.push(ExprKind::Family { name, owner }, (start, self.prev_end()))
                    );
                }
                let span = name.span();
                Ok(self.push(ExprKind::Dotted(name.parts), span))
            }
        }
    }

    fn items(&mut self, close: &str) -> PResult<Vec<ExprId>> {
        let mut items = Vec::new();
        if !self.is_sym(close) {
            loop {
                items.push(self.parse_expr(Flags::default())?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(close)?;
        Ok(items)
    }

    fn pattern(&mut self) -> PResult<Pattern> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            if self.is_sym("_") {
                let span = self.here();
                self.pos += 1;
                return Ok(Pattern::Wild(span));
            }
            let name = self.qname()?;
            if self.eat_sym("(") {
                let mut args = vec![self.pattern()?];
                while self.eat_sym(",") {
                    args.push(self.pattern()?);
                }
                self.expect_sym(")")?;
                let span = (name.span().0, self.prev_end());
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
    }
}
