use crate::{
    canonical,
    model::{Checked, Issue, Span, Type, location},
};
use num_bigint::BigUint;
use num_traits::Zero;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: String,
    pub text: String,
    pub span: Span,
}
fn syntax(message: impl Into<String>, span: Span) -> Issue {
    Issue::law("syntax", message, span)
}
pub fn lex(bytes: &[u8]) -> Checked<Vec<Token>> {
    let s = std::str::from_utf8(bytes).map_err(|e| {
        syntax(
            "不正 UTF-8",
            [e.valid_up_to(), (e.valid_up_to() + 1).min(bytes.len())],
        )
    })?;
    if s.starts_with('\u{feff}') {
        return Err(syntax("BOM は使用できない", [0, 3]));
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let start = i;
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if bytes[i..].starts_with(b"//") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let (kind, text) = if bytes[i].is_ascii_alphabetic() {
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            ("name", s[start..i].to_owned())
        } else if bytes[i].is_ascii_digit() {
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let n = &s[start..i];
            if n.len() > 1 && n.starts_with('0') {
                return Err(syntax("整数の先頭零", [start, i]));
            }
            ("integer", n.to_owned())
        } else if bytes[i] == b'"' {
            i += 1;
            let mut escaped = false;
            let mut closed = false;
            while i < bytes.len() {
                let c = bytes[i];
                i += 1;
                if !escaped && c == b'"' {
                    closed = true;
                    break;
                }
                if !escaped && c == b'\\' {
                    escaped = true;
                } else {
                    escaped = false;
                }
            }
            if !closed {
                return Err(syntax("文字列が閉じていない", [start, i]));
            }
            let text = serde_json::from_str::<String>(&s[start..i])
                .map_err(|_| syntax("不正な JSON 文字列", [start, i]))?;
            ("string", text)
        } else {
            let two = bytes.get(i..i + 2);
            if matches!(two, Some(b"->" | b"=>" | b"!=" | b"<=" | b">=")) {
                i += 2;
            } else if b"{}()[]<>:;,.=|+-*_".contains(&bytes[i]) {
                i += 1;
            } else {
                let n = s[i..].chars().next().map(char::len_utf8).unwrap_or(1);
                return Err(syntax("未知の文字", [i, i + n]));
            }
            ("symbol", s[start..i].to_owned())
        };
        out.push(Token {
            kind: kind.into(),
            text,
            span: [start, i],
        });
    }
    Ok(out)
}
const RESERVED: &str = "law semantics reading use as entity arrow correspondence align data view required optional local reads change relation when let in if then else match forall exists not implies or and with true false unit list set where none some fn Unit Bool Z Q Text Fp List Set Option Map Term Path rat count sum path identity source target";
fn reserved(s: &str) -> bool {
    RESERVED.split_whitespace().any(|x| x == s)
}
#[derive(Clone, Debug)]
pub struct RawType {
    pub kind: RawTypeKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub enum RawTypeKind {
    Named(String, Option<String>),
    Apply(String, Vec<RawType>),
    Fp(String),
    Term(Vec<RawType>, Box<RawType>),
}
#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub raw: RawType,
    pub ty: Option<Type>,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: String,
    pub arguments: Vec<RawType>,
    pub types: Vec<Type>,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Pattern {
    pub name: String,
    pub args: Vec<Pattern>,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub ty: Option<Type>,
}
#[derive(Clone, Debug)]
pub enum ExprKind {
    Group(Box<Expr>),
    Name(String),
    Integer(String),
    Text(String),
    Bool(bool),
    Unit,
    Tuple(Vec<Expr>),
    Select(Box<Expr>, String, Span),
    Apply(Box<Expr>, Vec<Expr>),
    Family(String, Span, Box<Expr>),
    Unary(String, Box<Expr>),
    Binary(String, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Quantify(String, String, Option<RawType>, Box<Expr>, Box<Expr>),
    Collection(String, RawType, Vec<Expr>),
    Comprehension(Box<Expr>, String, Box<Expr>, Option<Box<Expr>>),
    Alternatives(Vec<Expr>),
    None(RawType),
    Some(Box<Expr>),
    Fn(Vec<Field>, Box<Expr>),
    With(Box<Expr>, Vec<(String, Span, Expr)>),
}
#[derive(Clone, Debug)]
pub struct Declaration {
    pub name: String,
    pub reading: String,
    pub kind: String,
    pub span: Span,
    pub parameters: Vec<Field>,
    pub fields: Vec<Field>,
    pub constructors: Vec<Constructor>,
    pub alignments: Vec<(String, Span, String, Span)>,
    pub returns: Option<RawType>,
    pub ty: Option<Type>,
    pub role: Option<String>,
    pub guard: Option<Expr>,
    pub bodies: Vec<Expr>,
    pub references: Vec<(Span, String)>,
    pub supplied: Vec<Value>,
    pub dependencies: BTreeSet<String>,
}
#[derive(Clone, Debug)]
pub struct Reading {
    pub name: String,
    pub span: Span,
    pub aliases: BTreeMap<String, (String, Span)>,
    pub declarations: Vec<Declaration>,
}
#[derive(Clone, Debug)]
pub struct Program {
    pub tokens: Vec<Token>,
    pub readings: Vec<Reading>,
    pub declarations: Vec<Value>,
    pub vocabularies: Vec<Value>,
    pub model_digest: String,
}
#[derive(Clone)]
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    end: usize,
}
impl Parser {
    fn current(&self) -> &str {
        self.tokens
            .get(self.pos)
            .map(|t| {
                if t.kind == "string" {
                    "\0string"
                } else {
                    t.text.as_str()
                }
            })
            .unwrap_or("")
    }
    fn span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or([self.end, self.end])
    }
    fn last(&self) -> usize {
        self.tokens
            .get(self.pos.saturating_sub(1))
            .map(|t| t.span[1])
            .unwrap_or(0)
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.current() == s {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, s: &str) -> Checked<()> {
        if self.eat(s) {
            Ok(())
        } else {
            Err(syntax(format!("{s} を要求"), self.span()))
        }
    }
    fn name(&mut self) -> Checked<(String, Span)> {
        let t = self
            .tokens
            .get(self.pos)
            .ok_or_else(|| syntax("名前を要求", self.span()))?;
        if t.kind != "name"
            || (reserved(&t.text)
                && ![
                    "rat", "count", "sum", "path", "identity", "source", "target",
                ]
                .contains(&t.text.as_str()))
        {
            return Err(syntax("予約語または不正な名前", t.span));
        }
        self.pos += 1;
        Ok((t.text.clone(), t.span))
    }
    fn qname(&mut self) -> Checked<(String, Span)> {
        let (n, s) = self.name()?;
        let mut n = n;
        while self.eat(".") {
            n.push('.');
            n.push_str(&self.name()?.0);
        }
        Ok((n, [s[0], self.last()]))
    }
    fn string(&mut self) -> Checked<String> {
        let t = self
            .tokens
            .get(self.pos)
            .ok_or_else(|| syntax("文字列を要求", self.span()))?;
        if t.kind != "string" {
            return Err(syntax("文字列を要求", t.span));
        }
        self.pos += 1;
        Ok(t.text.clone())
    }
    fn ty(&mut self) -> Checked<RawType> {
        let start = self.span()[0];
        let n = self.current().to_owned();
        let kind = if self.eat("(") {
            let mut a = vec![self.ty()?];
            self.expect(",")?;
            a.push(self.ty()?);
            while self.eat(",") {
                a.push(self.ty()?);
            }
            self.expect(")")?;
            RawTypeKind::Apply("Tuple".into(), a)
        } else if self.eat("Fp") {
            self.expect("(")?;
            let p = self
                .tokens
                .get(self.pos)
                .ok_or_else(|| syntax("素数を要求", self.span()))?
                .clone();
            if p.kind != "integer" {
                return Err(syntax("10進素数を要求", p.span));
            }
            self.pos += 1;
            self.expect(")")?;
            RawTypeKind::Fp(p.text)
        } else if self.eat("Term") {
            self.expect("<")?;
            self.expect("(")?;
            let mut a = Vec::new();
            if !self.eat(")") {
                a.push(self.ty()?);
                while self.eat(",") {
                    a.push(self.ty()?);
                }
                self.expect(")")?;
            }
            self.expect("->")?;
            let b = self.ty()?;
            self.expect(">")?;
            RawTypeKind::Term(a, Box::new(b))
        } else if ["List", "Set", "Option", "Map", "Path"].contains(&n.as_str()) {
            self.pos += 1;
            self.expect("<")?;
            let mut a = vec![self.ty()?];
            if n == "Map" || n == "Path" {
                self.expect(",")?;
                a.push(self.ty()?);
            }
            self.expect(">")?;
            RawTypeKind::Apply(n, a)
        } else if ["Unit", "Bool", "Z", "Q", "Text"].contains(&n.as_str()) {
            self.pos += 1;
            RawTypeKind::Named(n, None)
        } else {
            let (n, _) = self.qname()?;
            let dep = if self.eat("[") {
                let p = self.name()?.0;
                self.expect("]")?;
                Some(p)
            } else {
                None
            };
            RawTypeKind::Named(n, dep)
        };
        Ok(RawType {
            kind,
            span: [start, self.last()],
        })
    }
    fn fields(&mut self) -> Checked<Vec<Field>> {
        self.expect("(")?;
        let mut out = Vec::new();
        if self.eat(")") {
            return Ok(out);
        }
        loop {
            let (n, s) = self.name()?;
            self.expect(":")?;
            let raw = self.ty()?;
            out.push(Field {
                name: n,
                span: [s[0], raw.span[1]],
                raw,
                ty: None,
            });
            if self.eat(")") {
                break;
            }
            self.expect(",")?;
        }
        Ok(out)
    }
    fn declaration(&mut self, reading: &str) -> Checked<Declaration> {
        let start = self.span()[0];
        let kind = self.current().to_owned();
        self.pos += 1;
        if ![
            "entity",
            "arrow",
            "correspondence",
            "data",
            "view",
            "law",
            "local",
            "change",
            "relation",
        ]
        .contains(&kind.as_str())
        {
            return Err(syntax("未知の宣言", [start, self.last()]));
        }
        let role = if kind == "law" {
            let r = self.current().to_owned();
            if !["required", "optional"].contains(&r.as_str()) {
                return Err(syntax("Law role を要求", self.span()));
            }
            self.pos += 1;
            Some(r)
        } else {
            None
        };
        let (short, ss) = self.name()?;
        if reserved(&short) {
            return Err(syntax("組込み演算を再定義できない", ss));
        }
        let mut d = Declaration {
            name: format!("{reading}.{short}"),
            reading: reading.into(),
            kind: kind.clone(),
            span: [start, 0],
            parameters: Vec::new(),
            fields: Vec::new(),
            constructors: Vec::new(),
            alignments: Vec::new(),
            returns: None,
            ty: None,
            role,
            guard: None,
            bodies: Vec::new(),
            references: Vec::new(),
            supplied: Vec::new(),
            dependencies: BTreeSet::new(),
        };
        if kind == "data" {
            self.expect("=")?;
            loop {
                let (n, s) = self.name()?;
                let mut arguments = Vec::new();
                if self.eat("(") {
                    arguments.push(self.ty()?);
                    while self.eat(",") {
                        arguments.push(self.ty()?);
                    }
                    self.expect(")")?;
                }
                d.constructors.push(Constructor {
                    name: n,
                    span: [s[0], self.last()],
                    arguments,
                    types: Vec::new(),
                });
                if !self.eat("|") {
                    break;
                }
            }
            self.expect(";")?;
        } else if ["entity", "arrow", "correspondence"].contains(&kind.as_str()) {
            if self.current() == "(" {
                d.parameters = self.fields()?;
            } else if kind != "entity" {
                return Err(syntax("parameter を要求", self.span()));
            }
            if self.eat("{") {
                while self.current() != "}" {
                    if self.eat("align") {
                        if kind != "correspondence" {
                            return Err(syntax(
                                "align は correspondence のみ",
                                self.tokens[self.pos - 1].span,
                            ));
                        }
                        let (a, sa) = self.qname()?;
                        self.expect("=")?;
                        let (b, sb) = self.qname()?;
                        self.expect(";")?;
                        d.alignments.push((a, sa, b, sb));
                    } else {
                        if !d.alignments.is_empty() {
                            return Err(syntax("align の後に field は置けない", self.span()));
                        }
                        let (n, s) = self.name()?;
                        self.expect(":")?;
                        let raw = self.ty()?;
                        self.expect(";")?;
                        d.fields.push(Field {
                            name: n,
                            span: [s[0], raw.span[1]],
                            raw,
                            ty: None,
                        });
                    }
                }
                self.expect("}")?;
            } else {
                if kind == "correspondence" {
                    return Err(syntax("correspondence body を要求", self.span()));
                }
                self.expect(";")?;
            }
        } else {
            d.parameters = self.fields()?;
            if kind == "view" {
                self.expect(":")?;
                d.returns = Some(self.ty()?);
                self.expect("=")?;
                d.bodies.push(self.expr(0)?);
            } else {
                if self.eat("when") {
                    d.guard = Some(self.expr(0)?);
                }
                if kind == "local" {
                    self.expect("reads")?;
                    d.bodies.push(self.expr(0)?);
                    while self.eat(",") {
                        d.bodies.push(self.expr(0)?);
                    }
                } else {
                    self.expect(if kind == "change" { "=" } else { ":" })?;
                    d.bodies.push(self.expr(0)?);
                }
            }
            self.expect(";")?;
        }
        d.span[1] = self.last();
        Ok(d)
    }
    fn pattern(&mut self) -> Checked<Pattern> {
        let start = self.span()[0];
        let name = if self.eat("_") {
            "_".into()
        } else {
            self.qname()?.0
        };
        let mut args = Vec::new();
        if self.eat("(") {
            args.push(self.pattern()?);
            while self.eat(",") {
                args.push(self.pattern()?);
            }
            self.expect(")")?;
        }
        Ok(Pattern {
            name,
            args,
            span: [start, self.last()],
        })
    }
    fn expr(&mut self, min: u8) -> Checked<Expr> {
        let start = self.span()[0];
        let mut left = self.prefix()?;
        let mut compared = false;
        loop {
            let op = self.current();
            let prec = match op {
                "implies" => 1,
                "or" => 2,
                "and" => 3,
                "=" | "!=" | "<" | "<=" | ">" | ">=" | "in" => 4,
                "+" | "-" => 5,
                "*" => 6,
                _ => 0,
            };
            if prec == 0 || prec < min {
                break;
            }
            if prec == 4 && compared {
                return Err(syntax("比較の連鎖", self.span()));
            }
            compared |= prec == 4;
            let op = op.to_owned();
            self.pos += 1;
            let right = self.expr(if op == "implies" { prec } else { prec + 1 })?;
            let end = right.span[1];
            left = Expr {
                kind: ExprKind::Binary(op, Box::new(left), Box::new(right)),
                span: [start, end],
                ty: None,
            };
        }
        Ok(left)
    }
    fn prefix(&mut self) -> Checked<Expr> {
        let start = self.span()[0];
        let kind = if self.eat("let") {
            let n = self.name()?.0;
            self.expect("=")?;
            return self.split_bound(start, n, None, None, "in");
        } else if self.eat("if") {
            let a = self.expr(0)?;
            self.expect("then")?;
            let b = self.expr(0)?;
            self.expect("else")?;
            ExprKind::If(Box::new(a), Box::new(b), Box::new(self.expr(0)?))
        } else if self.eat("match") {
            let a = self.expr(0)?;
            self.expect("{")?;
            let mut arms = Vec::new();
            while self.current() != "}" {
                let p = self.pattern()?;
                self.expect("=>")?;
                let e = self.expr(0)?;
                self.expect(";")?;
                arms.push((p, e));
            }
            self.expect("}")?;
            if arms.is_empty() {
                return Err(syntax("空 match", [start, self.last()]));
            }
            ExprKind::Match(Box::new(a), arms)
        } else if ["forall", "exists"].contains(&self.current()) {
            let k = self.current().to_owned();
            self.pos += 1;
            let n = self.name()?.0;
            if self.eat(":") {
                return self.split_typed_quantifier(start, n, k);
            } else {
                self.expect("in")?;
                return self.split_bound(start, n, Some(k), None, ".");
            }
        } else if ["not", "-"].contains(&self.current()) {
            let op = self.current().to_owned();
            self.pos += 1;
            ExprKind::Unary(op, Box::new(self.expr(7)?))
        } else if self.eat("fn") {
            let fields = self.fields()?;
            self.expect("=>")?;
            ExprKind::Fn(fields, Box::new(self.expr(0)?))
        } else {
            return self.postfix();
        };
        Ok(Expr {
            kind,
            span: [start, self.last()],
            ty: None,
        })
    }
    fn split_typed_quantifier(&mut self, start: usize, n: String, k: String) -> Checked<Expr> {
        let domain_start = self.pos;
        let mut depth = 0isize;
        let mut candidates = Vec::new();
        let mut end = None;
        for i in domain_start..self.tokens.len() {
            let token = &self.tokens[i];
            if depth == 0 && token.kind != "string" && token.text == "." {
                let mut lhs = Parser {
                    tokens: self.tokens[domain_start..i].to_vec(),
                    pos: 0,
                    end: token.span[0],
                };
                if let Ok(t) = lhs.ty() {
                    if lhs.pos == lhs.tokens.len() {
                        let mut rhs = self.clone();
                        rhs.pos = i + 1;
                        if let Ok(b) = rhs.expr(0) {
                            candidates.push(Expr {
                                kind: ExprKind::Quantify(
                                    k.clone(),
                                    n.clone(),
                                    Some(t),
                                    Box::new(Expr {
                                        kind: ExprKind::Unit,
                                        span: [start, start],
                                        ty: None,
                                    }),
                                    Box::new(b),
                                ),
                                span: [start, rhs.last()],
                                ty: None,
                            });
                            end = Some(rhs.pos);
                        }
                    }
                }
            }
            if token.kind != "string" {
                match token.text.as_str() {
                    "(" | "[" | "<" => depth += 1,
                    ")" | "]" | ">" => {
                        depth -= 1;
                        if depth < 0 {
                            break;
                        }
                    }
                    ";" | "}" | "=" if depth == 0 => break,
                    _ => {}
                }
            }
        }
        self.pos = end.ok_or_else(|| syntax("型付き量化の区切りを要求", self.span()))?;
        Ok(Expr {
            kind: ExprKind::Alternatives(candidates),
            span: [start, self.last()],
            ty: None,
        })
    }
    fn split_bound(
        &mut self,
        start: usize,
        n: String,
        k: Option<String>,
        _: Option<RawType>,
        separator: &str,
    ) -> Checked<Expr> {
        let domain_start = self.pos;
        let mut depth = 0isize;
        let mut candidates = Vec::new();
        let mut end = None;
        for i in domain_start..self.tokens.len() {
            let token = &self.tokens[i];
            if depth == 0 && token.kind != "string" && token.text == separator {
                let mut lhs = Parser {
                    tokens: self.tokens[domain_start..i].to_vec(),
                    pos: 0,
                    end: token.span[0],
                };
                if let Ok(a) = lhs.expr(0) {
                    if lhs.pos == lhs.tokens.len() {
                        let mut rhs = self.clone();
                        rhs.pos = i + 1;
                        if let Ok(b) = rhs.expr(0) {
                            let kind = if let Some(k) = &k {
                                ExprKind::Quantify(
                                    k.clone(),
                                    n.clone(),
                                    None,
                                    Box::new(a),
                                    Box::new(b),
                                )
                            } else {
                                ExprKind::Let(n.clone(), Box::new(a), Box::new(b))
                            };
                            candidates.push(Expr {
                                kind,
                                span: [start, rhs.last()],
                                ty: None,
                            });
                            end = Some(rhs.pos);
                        }
                    }
                }
            }
            if token.kind == "string" {
                continue;
            }
            match token.text.as_str() {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                ";" | "," if depth == 0 => break,
                _ => {}
            }
        }
        self.pos =
            end.ok_or_else(|| syntax(format!("{separator} の束縛区切りを要求"), self.span()))?;
        Ok(Expr {
            kind: ExprKind::Alternatives(candidates),
            span: [start, self.last()],
            ty: None,
        })
    }
    fn postfix(&mut self) -> Checked<Expr> {
        let start = self.span()[0];
        let text = self.current().to_owned();
        let kind = if self.eat("(") {
            let a = self.expr(0)?;
            if self.eat(",") {
                let mut xs = vec![a, self.expr(0)?];
                while self.eat(",") {
                    xs.push(self.expr(0)?);
                }
                self.expect(")")?;
                ExprKind::Tuple(xs)
            } else {
                self.expect(")")?;
                ExprKind::Group(Box::new(a))
            }
        } else if self.eat("true") {
            ExprKind::Bool(true)
        } else if self.eat("false") {
            ExprKind::Bool(false)
        } else if self.eat("unit") {
            ExprKind::Unit
        } else if self.eat("none") {
            self.expect("<")?;
            let t = self.ty()?;
            self.expect(">")?;
            ExprKind::None(t)
        } else if self.eat("some") {
            self.expect("(")?;
            let a = self.expr(0)?;
            self.expect(")")?;
            ExprKind::Some(Box::new(a))
        } else if self.eat("list") || self.eat("set") {
            let k = text;
            if k == "set" && self.eat("{") {
                let value = self.expr(0)?;
                self.expect("|")?;
                let n = self.name()?.0;
                self.expect("in")?;
                let domain = self.expr(0)?;
                let guard = if self.eat("where") {
                    Some(Box::new(self.expr(0)?))
                } else {
                    None
                };
                self.expect("}")?;
                ExprKind::Comprehension(Box::new(value), n, Box::new(domain), guard)
            } else {
                self.expect("<")?;
                let t = self.ty()?;
                self.expect(">")?;
                let (a, b) = if k == "list" { ("[", "]") } else { ("{", "}") };
                self.expect(a)?;
                let mut xs = Vec::new();
                if !self.eat(b) {
                    xs.push(self.expr(0)?);
                    while self.eat(",") {
                        xs.push(self.expr(0)?);
                    }
                    self.expect(b)?;
                }
                ExprKind::Collection(k, t, xs)
            }
        } else {
            let token = self
                .tokens
                .get(self.pos)
                .ok_or_else(|| syntax("式を要求", self.span()))?
                .clone();
            if token.kind == "integer" {
                self.pos += 1;
                ExprKind::Integer(token.text)
            } else if token.kind == "string" {
                self.pos += 1;
                ExprKind::Text(token.text)
            } else if token.kind == "name"
                && (!reserved(&token.text)
                    || [
                        "rat", "count", "sum", "path", "identity", "then", "source", "target",
                    ]
                    .contains(&token.text.as_str()))
            {
                self.pos += 1;
                ExprKind::Name(token.text)
            } else {
                return Err(syntax("式を要求", token.span));
            }
        };
        let mut e = Expr {
            kind,
            span: [start, self.last()],
            ty: None,
        };
        loop {
            if self.current() == "."
                && self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == "name" || t.kind == "integer")
            {
                self.pos += 1;
                let t = self.tokens[self.pos].clone();
                self.pos += 1;
                let span = [start, self.last()];
                e = Expr {
                    kind: ExprKind::Select(Box::new(e), t.text, t.span),
                    span,
                    ty: None,
                };
            } else if self.eat("(") {
                let mut xs = Vec::new();
                if !self.eat(")") {
                    xs.push(self.expr(0)?);
                    while self.eat(",") {
                        xs.push(self.expr(0)?);
                    }
                    self.expect(")")?;
                }
                e = Expr {
                    kind: ExprKind::Apply(Box::new(e), xs),
                    span: [start, self.last()],
                    ty: None,
                };
            } else if self.eat("[") {
                let n = expr_name(&e).ok_or_else(|| syntax("観測族の型名を要求", e.span))?;
                let a = self.expr(0)?;
                self.expect("]")?;
                e = Expr {
                    kind: ExprKind::Family(n, e.span, Box::new(a)),
                    span: [start, self.last()],
                    ty: None,
                };
            } else {
                break;
            }
        }
        if self.eat("with") {
            self.expect("{")?;
            let mut updates = Vec::new();
            loop {
                let (n, s) = self.name()?;
                self.expect("=")?;
                let a = self.expr(0)?;
                updates.push((n, s, a));
                if self.eat("}") {
                    break;
                }
                self.expect(",")?;
            }
            e = Expr {
                kind: ExprKind::With(Box::new(e), updates),
                span: [start, self.last()],
                ty: None,
            };
        }
        Ok(e)
    }
}
fn expr_name(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Group(a) => expr_name(a),
        ExprKind::Name(n) => Some(n.clone()),
        ExprKind::Select(a, n, _) => Some(format!("{}.{}", expr_name(a)?, n)),
        _ => None,
    }
}
pub fn parse(bytes: &[u8]) -> Checked<Program> {
    let tokens = lex(bytes)?;
    let mut p = Parser {
        tokens: tokens.clone(),
        pos: 0,
        end: bytes.len(),
    };
    p.expect("law")?;
    let format = p.string()?;
    p.expect("semantics")?;
    let semantics = p.string()?;
    p.expect(";")?;
    if format != "archsig.law/1" || semantics != "archsig/0.6.0" {
        let mut e = Issue::law("unsupported_version", "未知の版", [0, p.last()]);
        e.details = json!({"found_format":format,"found_semantics":semantics});
        return Err(e);
    }
    let mut readings = Vec::new();
    while p.pos < p.tokens.len() {
        let start = p.span()[0];
        p.expect("reading")?;
        let (name, _) = p.name()?;
        p.expect("{")?;
        let mut aliases = BTreeMap::new();
        let mut declarations = Vec::new();
        while p.current() != "}" {
            if p.eat("use") {
                let (other, s) = p.name()?;
                p.expect("as")?;
                let (alias, sa) = p.name()?;
                p.expect(";")?;
                if aliases.insert(alias, (other, s)).is_some() {
                    return Err(Issue::law("duplicate_id", "alias の重複", sa));
                }
            } else {
                declarations.push(p.declaration(&name)?);
            }
        }
        p.expect("}")?;
        readings.push(Reading {
            name,
            span: [start, p.last()],
            aliases,
            declarations,
        });
    }
    if readings.is_empty() {
        return Err(syntax("reading を要求", [p.end, p.end]));
    }
    let model = json!({"semantics":semantics,"tokens":tokens.iter().map(|t|json!({"kind":t.kind,"text":t.text})).collect::<Vec<_>>()});
    Ok(Program {
        tokens,
        readings,
        declarations: Vec::new(),
        vocabularies: Vec::new(),
        model_digest: canonical::model_digest(&model),
    })
}

#[derive(Clone)]
struct Symbols {
    declarations: BTreeMap<String, Declaration>,
    aliases: BTreeMap<String, BTreeMap<String, (String, Span)>>,
}
impl Symbols {
    fn resolve(&self, reading: &str, n: &str, span: Span) -> Checked<String> {
        let candidate = if let Some((first, rest)) = n.split_once('.') {
            if let Some((target, _)) = self.aliases.get(reading).and_then(|a| a.get(first)) {
                format!("{target}.{rest}")
            } else {
                n.into()
            }
        } else {
            format!("{reading}.{n}")
        };
        if self.declarations.contains_key(&candidate) {
            return Ok(candidate);
        }
        if let Some((data, ctor)) = candidate.rsplit_once('.') {
            if self
                .declarations
                .get(data)
                .is_some_and(|d| d.kind == "data" && d.constructors.iter().any(|c| c.name == ctor))
            {
                return Ok(candidate);
            }
        }
        if n.split('.').count() == 2 {
            let full = format!("{reading}.{n}");
            if let Some((data, ctor)) = full.rsplit_once('.') {
                if self.declarations.get(data).is_some_and(|d| {
                    d.kind == "data" && d.constructors.iter().any(|c| c.name == ctor)
                }) {
                    return Ok(full);
                }
            }
        }
        let mut constructors = Vec::new();
        if !n.contains('.') {
            for d in self
                .declarations
                .values()
                .filter(|d| d.reading == reading && d.kind == "data")
            {
                if d.constructors.iter().any(|c| c.name == n) {
                    constructors.push(format!("{}.{n}", d.name));
                }
            }
        }
        if constructors.len() == 1 {
            return Ok(constructors.remove(0));
        }
        Err(Issue::law(
            "reference",
            format!("名前を解決できない: {n}"),
            span,
        ))
    }
    fn ctor(&self, n: &str) -> Option<(&Declaration, &Constructor)> {
        let (d, c) = n.rsplit_once('.')?;
        let d = self.declarations.get(d)?;
        Some((d, d.constructors.iter().find(|x| x.name == c)?))
    }
}
fn type_error(expected: &Type, actual: &Type, span: Span) -> Issue {
    let mut e = Issue::law("type", "型が一致しない", span);
    e.details = json!({"expected":expected.wire(),"actual":actual.wire()});
    e
}
fn compatible(expected: &Type, actual: &Type) -> bool {
    match (expected, actual) {
        (Type::Ref(a), Type::Owned(b, _)) => a == b,
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| compatible(a, b))
        }
        (Type::List(a), Type::List(b))
        | (Type::Set(a), Type::Set(b))
        | (Type::Option(a), Type::Option(b)) => compatible(a, b),
        _ => expected == actual,
    }
}
fn ensure(expected: &Type, actual: &Type, span: Span) -> Checked<()> {
    if compatible(expected, actual) {
        Ok(())
    } else {
        Err(type_error(expected, actual, span))
    }
}
fn prime(p: &str) -> bool {
    let Some(p) = BigUint::parse_bytes(p.as_bytes(), 10) else {
        return false;
    };
    if p < BigUint::from(2u8) {
        return false;
    }
    if p == BigUint::from(2u8) {
        return true;
    }
    if (&p % 2u8).is_zero() {
        return false;
    }
    let mut d = BigUint::from(3u8);
    while &d * &d <= p {
        if (&p % &d).is_zero() {
            return false;
        }
        d += 2u8;
    }
    true
}
#[derive(Clone)]
struct Resolver<'a> {
    s: &'a Symbols,
    reading: &'a str,
    references: Vec<(Span, String)>,
}
impl Resolver<'_> {
    fn reference(&mut self, n: &str, span: Span) -> Checked<String> {
        let name = self.s.resolve(self.reading, n, span)?;
        self.references.push((span, name.clone()));
        Ok(name)
    }
    fn ty(&mut self, t: &RawType, env: &BTreeMap<String, Type>) -> Checked<Type> {
        let out = match &t.kind {
            RawTypeKind::Fp(p) => {
                if !prime(p) {
                    return Err(syntax("Fp の係数は素数でなければならない", t.span));
                }
                Type::Fp(p.clone())
            }
            RawTypeKind::Named(n, dep) => {
                if dep.is_none() {
                    match n.as_str() {
                        "Unit" => return Ok(Type::Unit),
                        "Bool" => return Ok(Type::Bool),
                        "Z" => return Ok(Type::Z),
                        "Q" => return Ok(Type::Q),
                        "Text" => return Ok(Type::Text),
                        _ => {}
                    }
                }
                let n = self.reference(n, t.span)?;
                let d = self
                    .s
                    .declarations
                    .get(&n)
                    .ok_or_else(|| syntax("型の宣言を要求", t.span))?;
                if d.kind == "data" {
                    if dep.is_some() {
                        return Err(syntax("data に owner はない", t.span));
                    }
                    Type::Data(n)
                } else if ["entity", "arrow", "correspondence"].contains(&d.kind.as_str()) {
                    if let Some(p) = dep {
                        let owner = env.get(p).ok_or_else(|| {
                            Issue::law("reference", "未束縛の依存 parameter", t.span)
                        })?;
                        let field = d
                            .parameters
                            .iter()
                            .chain(&d.fields)
                            .find(|f| f.name == "owner")
                            .ok_or_else(|| syntax("owner を持たない型", t.span))?;
                        let expect = if let Some(t) = &field.ty {
                            t.clone()
                        } else {
                            Resolver {
                                s: self.s,
                                reading: &d.reading,
                                references: Vec::new(),
                            }
                            .ty(&field.raw, &BTreeMap::new())?
                        };
                        ensure(&expect, owner, t.span)?;
                        Type::Owned(n, p.clone())
                    } else {
                        Type::Ref(n)
                    }
                } else {
                    return Err(syntax("型位置に値宣言は置けない", t.span));
                }
            }
            RawTypeKind::Apply(n, a) => {
                let types = a
                    .iter()
                    .map(|a| self.ty(a, env))
                    .collect::<Checked<Vec<_>>>()?;
                match n.as_str() {
                    "Tuple" => Type::Tuple(types),
                    "List" => Type::List(Box::new(types[0].clone())),
                    "Set" => Type::Set(Box::new(types[0].clone())),
                    "Option" => Type::Option(Box::new(types[0].clone())),
                    "Map" => {
                        if types.iter().any(|t| t.ref_name().is_none()) {
                            return Err(syntax("Map は参照型間に限定する", t.span));
                        }
                        Type::Map(Box::new(types[0].clone()), Box::new(types[1].clone()))
                    }
                    "Path" => {
                        if types.iter().any(|t| !matches!(t, Type::Ref(_))) {
                            return Err(syntax("Path の端点は entity 型", t.span));
                        }
                        let a = types[0].ref_name().unwrap();
                        let b = types[1].ref_name().unwrap();
                        if [a, b]
                            .iter()
                            .any(|n| self.s.declarations[*n].kind != "entity")
                        {
                            return Err(syntax("Path の端点は entity 型", t.span));
                        }
                        Type::Path(a.into(), b.into())
                    }
                    _ => unreachable!(),
                }
            }
            RawTypeKind::Term(a, b) => Type::Term(
                a.iter()
                    .map(|a| self.ty(a, env))
                    .collect::<Checked<Vec<_>>>()?,
                Box::new(self.ty(b, env)?),
            ),
        };
        Ok(out)
    }
}
fn children(t: &Type) -> Vec<&Type> {
    match t {
        Type::Tuple(a) => a.iter().collect(),
        Type::List(a) | Type::Set(a) | Type::Option(a) => vec![a],
        Type::Map(a, b) => vec![a, b],
        Type::Term(a, b) => a.iter().chain(std::iter::once(b.as_ref())).collect(),
        _ => Vec::new(),
    }
}
fn contains(t: &Type, s: &Symbols, p: fn(&Type) -> bool, seen: &mut BTreeSet<String>) -> bool {
    if p(t) {
        return true;
    }
    if let Type::Data(n) = t {
        if seen.insert(n.clone()) {
            if let Some(d) = s.declarations.get(n) {
                if d.constructors
                    .iter()
                    .flat_map(|c| &c.types)
                    .any(|t| contains(t, s, p, seen))
                {
                    return true;
                }
            }
        }
    }
    children(t).into_iter().any(|t| contains(t, s, p, seen))
}
fn has_ref(t: &Type, s: &Symbols) -> bool {
    contains(
        t,
        s,
        |t| t.ref_name().is_some() || matches!(t, Type::Path(..)),
        &mut BTreeSet::new(),
    )
}
fn has_path(t: &Type, s: &Symbols) -> bool {
    contains(t, s, |t| matches!(t, Type::Path(..)), &mut BTreeSet::new())
}
fn equality_type(t: &Type, s: &Symbols) -> bool {
    !contains(
        t,
        s,
        |t| matches!(t, Type::Term(..) | Type::Path(..)),
        &mut BTreeSet::new(),
    )
}
fn admissible(t: &Type, s: &Symbols, span: Span) -> Checked<()> {
    match t {
        Type::Set(a) if !equality_type(a, s) => {
            return Err(syntax("Set 要素に Term/Path を含められない", span));
        }
        Type::Term(a, b)
            if a.iter()
                .chain(std::iter::once(b.as_ref()))
                .any(|t| has_ref(t, s)) =>
        {
            return Err(syntax("Term の型に参照/Path を含められない", span));
        }
        _ => {}
    }
    for a in children(t) {
        admissible(a, s, span)?;
    }
    Ok(())
}
fn substitute(t: &Type, p: &str, by: &str) -> Type {
    match t {
        Type::Owned(n, x) if x == p => Type::Owned(n.clone(), by.into()),
        Type::Tuple(xs) => Type::Tuple(xs.iter().map(|t| substitute(t, p, by)).collect()),
        Type::List(t) => Type::List(Box::new(substitute(t, p, by))),
        Type::Set(t) => Type::Set(Box::new(substitute(t, p, by))),
        Type::Option(t) => Type::Option(Box::new(substitute(t, p, by))),
        Type::Map(a, b) => Type::Map(
            Box::new(substitute(a, p, by)),
            Box::new(substitute(b, p, by)),
        ),
        _ => t.clone(),
    }
}
fn instantiate(t: &Type, bindings: &BTreeMap<String, String>) -> Type {
    match t {
        Type::Owned(n, x) => Type::Owned(
            n.clone(),
            bindings.get(x).cloned().unwrap_or_else(|| x.clone()),
        ),
        Type::Tuple(a) => Type::Tuple(a.iter().map(|t| instantiate(t, bindings)).collect()),
        Type::List(a) => Type::List(Box::new(instantiate(a, bindings))),
        Type::Set(a) => Type::Set(Box::new(instantiate(a, bindings))),
        Type::Option(a) => Type::Option(Box::new(instantiate(a, bindings))),
        Type::Map(a, b) => Type::Map(
            Box::new(instantiate(a, bindings)),
            Box::new(instantiate(b, bindings)),
        ),
        _ => t.clone(),
    }
}
fn numeric(t: &Type) -> bool {
    match t {
        Type::Z | Type::Q | Type::Fp(_) => true,
        Type::Tuple(a) => a.iter().all(numeric),
        _ => false,
    }
}
#[derive(Clone)]
struct Binding {
    ty: Type,
    subterm: bool,
}
#[derive(Clone)]
struct Checker<'a> {
    r: Resolver<'a>,
    env: BTreeMap<String, Binding>,
    declaration: &'a Declaration,
    pure: bool,
    captures: BTreeSet<String>,
    change: bool,
    calls: BTreeSet<String>,
}
impl Checker<'_> {
    fn bind(&mut self, n: &str, ty: Type, subterm: bool, span: Span) -> Checked<()> {
        if reserved(n) || self.env.contains_key(n) || self.captures.contains(n) {
            return Err(syntax("束縛の重複または捕獲", span));
        }
        self.env.insert(n.into(), Binding { ty, subterm });
        Ok(())
    }
    fn raw_type(&mut self, t: &RawType) -> Checked<Type> {
        let env = self
            .env
            .iter()
            .map(|(n, b)| (n.clone(), b.ty.clone()))
            .collect();
        let ty = self.r.ty(t, &env)?;
        admissible(&ty, self.r.s, t.span)?;
        if self.pure && has_ref(&ty, self.r.s) {
            return Err(syntax("Term に参照型の域を含められない", t.span));
        }
        Ok(ty)
    }
    fn ctor_name(&mut self, n: &str, span: Span, expected: Option<&Type>) -> Checked<String> {
        if self.captures.contains(n.split('.').next().unwrap()) {
            return Err(syntax("Term は外側の束縛を捕獲できない", span));
        }
        if !n.contains('.') {
            if let Some(Type::Data(d)) = expected {
                if self.r.s.declarations[d]
                    .constructors
                    .iter()
                    .any(|c| c.name == n)
                {
                    let full = format!("{d}.{n}");
                    self.r.references.push((span, full.clone()));
                    return Ok(full);
                }
            }
        }
        self.r.reference(n, span)
    }
    fn qualified(&mut self, e: &Expr, expected: Option<&Type>) -> Checked<Option<(String, Type)>> {
        let Some(n) = expr_name(e) else {
            return Ok(None);
        };
        let first = n.split('.').next().unwrap();
        if self.captures.contains(first) {
            return Err(syntax("Term は外側の束縛を捕獲できない", e.span));
        }
        if self.env.contains_key(first) {
            return Ok(None);
        }
        let full = self.ctor_name(&n, e.span, expected)?;
        if let Some(d) = self.r.s.declarations.get(&full) {
            if matches!(d.kind.as_str(), "entity" | "arrow" | "correspondence") {
                if self.pure {
                    return Err(syntax("Term に観測族を含められない", e.span));
                }
                return Ok(Some((full.clone(), Type::Set(Box::new(Type::Ref(full))))));
            }
        }
        if let Some((d, c)) = self.r.s.ctor(&full) {
            if c.types.is_empty() {
                return Ok(Some((full, Type::Data(d.name.clone()))));
            }
        }
        Err(syntax("呼出しが必要な宣言", e.span))
    }
    fn expression(&mut self, e: &mut Expr, expected: Option<&Type>) -> Checked<Type> {
        let span = e.span;
        if let ExprKind::Alternatives(xs) = &e.kind {
            let original = self.clone();
            let mut last = None;
            for mut x in xs.clone() {
                *self = original.clone();
                match self.expression(&mut x, expected) {
                    Ok(t) => {
                        *e = x;
                        return Ok(t);
                    }
                    Err(err) => last = Some(err),
                }
            }
            *self = original;
            return Err(last.unwrap_or_else(|| syntax("束縛式を解決できない", span)));
        }
        if matches!(e.kind, ExprKind::Name(_) | ExprKind::Select(..))
            && expr_name(e).is_some_and(|n| !self.env.contains_key(n.split('.').next().unwrap()))
        {
            if let Some((_, ty)) = self.qualified(e, expected)? {
                e.ty = Some(ty.clone());
                if let Some(x) = expected {
                    ensure(x, &ty, span)?;
                }
                return Ok(ty);
            }
        }
        let ty = match &mut e.kind {
            ExprKind::Alternatives(_) => unreachable!(),
            ExprKind::Group(a) => self.expression(a, expected)?,
            ExprKind::Integer(n) => {
                let t = expected
                    .filter(|t| matches!(t, Type::Z | Type::Q | Type::Fp(_)))
                    .cloned()
                    .unwrap_or(Type::Z);
                if let Type::Fp(p) = &t {
                    let value = BigUint::parse_bytes(n.as_bytes(), 10).unwrap();
                    let p = BigUint::parse_bytes(p.as_bytes(), 10).unwrap();
                    if value >= p {
                        return Err(syntax("Fp literal の範囲外", span));
                    }
                }
                t
            }
            ExprKind::Text(_) => Type::Text,
            ExprKind::Bool(_) => Type::Bool,
            ExprKind::Unit => Type::Unit,
            ExprKind::Name(n) => self
                .env
                .get(n)
                .ok_or_else(|| Issue::law("reference", "未束縛の名前", span))?
                .ty
                .clone(),
            ExprKind::Tuple(a) => {
                let wants = if let Some(Type::Tuple(a)) = expected {
                    Some(a)
                } else {
                    None
                };
                let mut types = Vec::new();
                for (i, a) in a.iter_mut().enumerate() {
                    types.push(self.expression(a, wants.and_then(|t| t.get(i)))?);
                }
                Type::Tuple(types)
            }
            ExprKind::Select(a, n, s) => {
                let base = self.expression(a, None)?;
                if let Type::Tuple(xs) = &base {
                    let i = n
                        .parse::<usize>()
                        .map_err(|_| syntax("tuple は数値射影", *s))?;
                    xs.get(i)
                        .cloned()
                        .ok_or_else(|| syntax("tuple 射影の範囲外", *s))?
                } else {
                    if self.pure {
                        return Err(syntax("Term は field を読めない", span));
                    }
                    let d = base
                        .ref_name()
                        .ok_or_else(|| syntax("field を持たない型", span))?;
                    let decl = &self.r.s.declarations[d];
                    let field = decl
                        .parameters
                        .iter()
                        .chain(&decl.fields)
                        .find(|f| f.name == *n)
                        .ok_or_else(|| Issue::law("reference", "未知の field", *s))?;
                    self.r.references.push((*s, format!("{d}.{n}")));
                    let mut ty = field.ty.clone().unwrap();
                    let prefix = expr_name(a).unwrap_or_else(|| format!("@{}", a.span[0]));
                    for f in &decl.parameters {
                        ty = substitute(&ty, &f.name, &format!("{prefix}.{}", f.name));
                    }
                    ty
                }
            }
            ExprKind::Family(n, name_span, a) => {
                if self.pure {
                    return Err(syntax("Term に観測族を含められない", span));
                }
                let full = self.r.reference(n, *name_span)?;
                let d = self
                    .r
                    .s
                    .declarations
                    .get(&full)
                    .filter(|d| matches!(d.kind.as_str(), "entity" | "arrow"))
                    .ok_or_else(|| syntax("owner を持つ原始族を要求", *name_span))?;
                let owner = d
                    .parameters
                    .iter()
                    .chain(&d.fields)
                    .find(|f| f.name == "owner")
                    .ok_or_else(|| syntax("owner を持つ族を要求", span))?;
                self.expression(a, owner.ty.as_ref())?;
                Type::Set(Box::new(Type::Owned(
                    full,
                    expr_name(a).unwrap_or_else(|| format!("@{}", a.span[0])),
                )))
            }
            ExprKind::Unary(op, a) => {
                let ty = self.expression(
                    a,
                    if op == "not" {
                        Some(&Type::Bool)
                    } else {
                        expected
                    },
                )?;
                if op != "not" && !numeric(&ty) {
                    return Err(type_error(&Type::Z, &ty, span));
                }
                ty
            }
            ExprKind::Binary(op, a, b) => {
                if ["and", "or", "implies"].contains(&op.as_str()) {
                    self.expression(a, Some(&Type::Bool))?;
                    self.expression(b, Some(&Type::Bool))?;
                    Type::Bool
                } else if op == "in" {
                    let collection = self.expression(b, None)?;
                    let item = match collection {
                        Type::List(t) | Type::Set(t) => *t,
                        _ => return Err(syntax("所属先は List/Set", b.span)),
                    };
                    self.expression(a, Some(&item))?;
                    Type::Bool
                } else {
                    let want = if ["+", "-", "*"].contains(&op.as_str()) {
                        expected
                    } else {
                        None
                    };
                    let mut left = self.expression(a, want)?;
                    let right = if flexible_literal(a) && !flexible_literal(b) {
                        let right = self.expression(b, want)?;
                        left = self.expression(a, Some(&right))?;
                        right
                    } else {
                        self.expression(b, Some(&left))?
                    };
                    ensure(&left, &right, b.span)?;
                    if ["+", "-", "*"].contains(&op.as_str()) {
                        if !numeric(&left) {
                            return Err(type_error(&Type::Z, &left, span));
                        }
                        left
                    } else {
                        if ["<", "<=", ">", ">="].contains(&op.as_str())
                            && !matches!(left, Type::Z | Type::Q)
                        {
                            return Err(type_error(&Type::Z, &left, span));
                        }
                        Type::Bool
                    }
                }
            }
            ExprKind::Apply(fun, args) => {
                if let Some(n) =
                    expr_name(fun).filter(|n| !self.env.contains_key(n.split('.').next().unwrap()))
                {
                    match n.as_str() {
                        "rat" => {
                            if args.len() != 2
                                || !args.iter().all(integer_literal)
                                || !positive_literal(&args[1])
                            {
                                return Err(syntax("rat は整数 literal と正分母", span));
                            }
                            for a in args {
                                self.expression(a, Some(&Type::Z))?;
                            }
                            Type::Q
                        }
                        "count" | "sum" => {
                            if args.len() != 1 {
                                return Err(syntax("演算の arity", span));
                            }
                            let t = self.expression(&mut args[0], None)?;
                            let (Type::List(t) | Type::Set(t)) = t else {
                                return Err(syntax("有限 List/Set を要求", span));
                            };
                            if n == "sum" {
                                if !numeric(&t) {
                                    return Err(type_error(&Type::Z, &t, span));
                                }
                                *t
                            } else {
                                Type::Z
                            }
                        }
                        "path" | "identity" | "then" | "source" | "target" => {
                            if self.pure {
                                return Err(syntax("Term に Path は使えない", span));
                            }
                            self.path_call(&n, args, span)?
                        }
                        _ => {
                            let full = self.ctor_name(&n, fun.span, expected)?;
                            if let Some((d, c)) = self.r.s.ctor(&full) {
                                let types = c.types.clone();
                                let result = Type::Data(d.name.clone());
                                if args.len() != types.len() {
                                    return Err(syntax("constructor の arity", span));
                                }
                                for (a, t) in args.iter_mut().zip(&types) {
                                    self.expression(a, Some(t))?;
                                }
                                result
                            } else {
                                let d = self
                                    .r
                                    .s
                                    .declarations
                                    .get(&full)
                                    .ok_or_else(|| syntax("呼出せない名前", span))?
                                    .clone();
                                if self.pure || d.kind != "view" {
                                    return Err(syntax("view 呼出しを要求", span));
                                }
                                if args.len() != d.parameters.len() {
                                    return Err(syntax("view の arity", span));
                                }
                                if full == self.declaration.name {
                                    let index = self
                                        .declaration
                                        .parameters
                                        .iter()
                                        .position(|p| matches!(p.ty, Some(Type::Data(_))))
                                        .ok_or_else(|| {
                                            syntax("data parameter のない自己再帰", span)
                                        })?;
                                    let decrease = args
                                        .get(index)
                                        .and_then(expr_name)
                                        .and_then(|n| self.env.get(&n))
                                        .is_some_and(|b| b.subterm);
                                    if !decrease {
                                        return Err(syntax("直接の再帰 subterm を要求", span));
                                    }
                                }
                                self.calls.insert(full.clone());
                                let arg_names = args
                                    .iter()
                                    .map(|e| {
                                        expr_name(e).unwrap_or_else(|| format!("@{}", e.span[0]))
                                    })
                                    .collect::<Vec<_>>();
                                for (i, a) in args.iter_mut().enumerate() {
                                    let bindings = d.parameters[..i]
                                        .iter()
                                        .zip(&arg_names[..i])
                                        .map(|(p, n)| (p.name.clone(), n.clone()))
                                        .collect();
                                    let t = instantiate(
                                        d.parameters[i].ty.as_ref().unwrap(),
                                        &bindings,
                                    );
                                    self.expression(a, Some(&t))?;
                                }
                                let bindings = d
                                    .parameters
                                    .iter()
                                    .zip(&arg_names)
                                    .map(|(p, n)| (p.name.clone(), n.clone()))
                                    .collect();
                                instantiate(d.ty.as_ref().unwrap(), &bindings)
                            }
                        }
                    }
                } else {
                    let callable = self.expression(fun, None)?;
                    match callable {
                        Type::Map(a, b) => {
                            if args.len() != 1 {
                                return Err(syntax("Map の arity", span));
                            }
                            self.expression(&mut args[0], Some(&a))?;
                            *b
                        }
                        Type::Term(a, b) => {
                            if self.pure {
                                return Err(syntax("Term body は Term を呼べない", span));
                            }
                            if args.len() != a.len() {
                                return Err(syntax("Term の arity", span));
                            }
                            for (x, t) in args.iter_mut().zip(&a) {
                                self.expression(x, Some(t))?;
                            }
                            *b
                        }
                        _ => return Err(syntax("適用できない型", fun.span)),
                    }
                }
            }
            ExprKind::Let(n, a, b) => {
                let t = self.expression(a, None)?;
                let env = self.env.clone();
                self.bind(n, t, false, a.span)?;
                let t = self.expression(b, expected)?;
                self.env = env;
                t
            }
            ExprKind::If(a, b, c) => {
                self.expression(a, Some(&Type::Bool))?;
                let t = self.expression(b, expected)?;
                self.expression(c, Some(&t))?;
                t
            }
            ExprKind::Quantify(_, n, t, a, b) => {
                let t = if let Some(raw) = t {
                    self.raw_type(raw)?
                } else {
                    match self.expression(a, None)? {
                        Type::List(t) | Type::Set(t) => *t,
                        _ => return Err(syntax("量化域は List/Set", a.span)),
                    }
                };
                let env = self.env.clone();
                self.bind(n, t, false, span)?;
                self.expression(b, Some(&Type::Bool))?;
                self.env = env;
                Type::Bool
            }
            ExprKind::Collection(k, t, xs) => {
                let ty = self.raw_type(t)?;
                if k == "set" && !equality_type(&ty, self.r.s) {
                    return Err(syntax("Set 要素に Term/Path は使えない", span));
                }
                for x in xs {
                    self.expression(x, Some(&ty))?;
                }
                if k == "list" {
                    Type::List(Box::new(ty))
                } else {
                    Type::Set(Box::new(ty))
                }
            }
            ExprKind::Comprehension(value, n, domain, guard) => {
                let t = match self.expression(domain, None)? {
                    Type::List(t) | Type::Set(t) => *t,
                    _ => return Err(syntax("comprehension の域", domain.span)),
                };
                let env = self.env.clone();
                self.bind(n, t, false, span)?;
                if let Some(g) = guard {
                    self.expression(g, Some(&Type::Bool))?;
                }
                let t = self.expression(value, None)?;
                if !equality_type(&t, self.r.s) {
                    return Err(syntax("Set 要素に Term/Path は使えない", span));
                }
                self.env = env;
                Type::Set(Box::new(t))
            }
            ExprKind::None(t) => Type::Option(Box::new(self.raw_type(t)?)),
            ExprKind::Some(a) => {
                let expected = if let Some(Type::Option(t)) = expected {
                    Some(t.as_ref())
                } else {
                    None
                };
                Type::Option(Box::new(self.expression(a, expected)?))
            }
            ExprKind::Fn(fields, body) => {
                let old_env = self.env.clone();
                let was_pure = self.pure;
                let old_captures = self.captures.clone();
                let mut env = BTreeMap::new();
                let mut types = Vec::new();
                for f in fields {
                    if reserved(&f.name)
                        || old_env.contains_key(&f.name)
                        || old_captures.contains(&f.name)
                        || env.contains_key(&f.name)
                    {
                        return Err(syntax("fn parameter の捕獲または重複", f.span));
                    }
                    let t = self.r.ty(&f.raw, &BTreeMap::new())?;
                    admissible(&t, self.r.s, f.span)?;
                    if has_ref(&t, self.r.s) {
                        return Err(syntax("Term parameter の参照", f.span));
                    }
                    f.ty = Some(t.clone());
                    types.push(t.clone());
                    env.insert(
                        f.name.clone(),
                        Binding {
                            ty: t,
                            subterm: false,
                        },
                    );
                }
                self.captures.extend(old_env.keys().cloned());
                self.env = env;
                self.pure = true;
                let want = if let Some(Type::Term(_, b)) = expected {
                    Some(b.as_ref())
                } else {
                    None
                };
                let t = self.expression(body, want)?;
                if has_ref(&t, self.r.s) {
                    return Err(syntax("Term result の参照", body.span));
                }
                self.env = old_env;
                self.pure = was_pure;
                self.captures = old_captures;
                Type::Term(types, Box::new(t))
            }
            ExprKind::With(base, updates) => {
                if !self.change || self.pure {
                    return Err(syntax("with は change body のみ", span));
                }
                let ty = self.expression(base, None)?;
                let name = ty
                    .ref_name()
                    .ok_or_else(|| syntax("entity 更新を要求", base.span))?;
                if self.r.s.declarations[name].kind != "entity"
                    || expr_name(base).as_deref()
                        != self.declaration.parameters.first().map(|p| p.name.as_str())
                {
                    return Err(syntax("第1 parameter の entity 更新を要求", base.span));
                }
                let d = self.r.s.declarations[name].clone();
                let mut names = BTreeSet::new();
                for (n, s, x) in updates {
                    if !names.insert(n.clone()) {
                        return Err(Issue::law("duplicate_id", "更新 field の重複", *s));
                    }
                    let f = d
                        .parameters
                        .iter()
                        .chain(&d.fields)
                        .find(|f| f.name == *n)
                        .ok_or_else(|| Issue::law("reference", "未知の更新 field", *s))?;
                    let t = f.ty.as_ref().unwrap();
                    if n == "owner"
                        || has_ref(t, self.r.s)
                        || contains(
                            t,
                            self.r.s,
                            |t| matches!(t, Type::Map(..)),
                            &mut BTreeSet::new(),
                        )
                    {
                        return Err(syntax("参照/owner/Map は更新できない", *s));
                    }
                    self.r.references.push((*s, format!("{name}.{n}")));
                    self.expression(x, Some(t))?;
                }
                ty
            }
            ExprKind::Match(scrutinee, arms) => {
                let t = self.expression(scrutinee, None)?;
                let Type::Data(data) = &t else {
                    return Err(syntax("match の対象は data", scrutinee.span));
                };
                let d = self.r.s.declarations[data].clone();
                let mut seen = BTreeSet::new();
                let mut covered = BTreeSet::new();
                let mut wildcard = false;
                let mut result = expected.cloned();
                let is_root = expr_name(scrutinee).is_some_and(|n| {
                    self.declaration
                        .parameters
                        .iter()
                        .find(|p| matches!(p.ty, Some(Type::Data(_))))
                        .is_some_and(|p| p.name == n)
                });
                let arm_count = arms.len();
                for (i, (p, body)) in arms.iter_mut().enumerate() {
                    let env = self.env.clone();
                    if wildcard {
                        return Err(syntax("到達不能な分岐", p.span));
                    }
                    if p.name == "_" {
                        if !p.args.is_empty()
                            || i + 1 != arm_count
                            || covered.len() == d.constructors.len()
                        {
                            return Err(syntax("_ は末尾のみ", p.span));
                        }
                        wildcard = true;
                    } else {
                        if !p.name.contains('.') && self.env.contains_key(&p.name) {
                            return Err(syntax("constructor 短名と束縛名の衝突", p.span));
                        }
                        let full = self.ctor_name(&p.name, p.span, Some(&t))?;
                        let (owner, c) = self
                            .r
                            .s
                            .ctor(&full)
                            .ok_or_else(|| syntax("constructor pattern を要求", p.span))?;
                        if owner.name != *data || !seen.insert(c.name.clone()) {
                            return Err(syntax("重複または異なる constructor", p.span));
                        }
                        let constructor = c.name.clone();
                        let types = c.types.clone();
                        let mut irrefutable = true;
                        if p.args.len() != types.len() {
                            return Err(syntax("pattern の arity", p.span));
                        }
                        for (arg, ty) in p.args.iter().zip(types) {
                            irrefutable &= self.pattern_bind(
                                arg,
                                &ty,
                                is_root && matches!(&ty,Type::Data(n)if n==data),
                            )?;
                        }
                        if irrefutable {
                            covered.insert(constructor);
                        }
                    }
                    let ty = self.expression(body, result.as_ref())?;
                    if result.is_none() {
                        result = Some(ty);
                    }
                    self.env = env;
                }
                if !wildcard && covered.len() != d.constructors.len() {
                    return Err(syntax("match が全 constructor を覆わない", span));
                }
                result.ok_or_else(|| syntax("空 match", span))?
            }
        };
        if let Some(expected) = expected {
            ensure(expected, &ty, span)?;
        }
        e.ty = Some(ty.clone());
        Ok(ty)
    }
    fn pattern_bind(&mut self, p: &Pattern, ty: &Type, subterm: bool) -> Checked<bool> {
        if p.name == "_" {
            if !p.args.is_empty() {
                return Err(syntax("wildcard に引数は置けない", p.span));
            }
            return Ok(true);
        }
        let short_constructor = match ty {
            Type::Data(n) => self.r.s.declarations[n]
                .constructors
                .iter()
                .any(|c| c.name == p.name),
            _ => false,
        };
        if p.args.is_empty() && !p.name.contains('.') && !short_constructor {
            self.bind(&p.name, ty.clone(), subterm, p.span)?;
            return Ok(true);
        }
        if !p.name.contains('.') && self.env.contains_key(&p.name) {
            return Err(syntax("constructor 短名と束縛名の衝突", p.span));
        }
        let full = self.ctor_name(&p.name, p.span, Some(ty))?;
        let (d, c) = self
            .r
            .s
            .ctor(&full)
            .ok_or_else(|| syntax("constructor pattern", p.span))?;
        ensure(&Type::Data(d.name.clone()), ty, p.span)?;
        let mut irrefutable = d.constructors.len() == 1;
        let a = c.types.clone();
        if a.len() != p.args.len() {
            return Err(syntax("pattern arity", p.span));
        }
        for (p, t) in p.args.iter().zip(a) {
            irrefutable &= self.pattern_bind(p, &t, false)?;
        }
        Ok(irrefutable)
    }
    fn path_call(&mut self, n: &str, a: &mut [Expr], span: Span) -> Checked<Type> {
        let arity = if n == "then" { 2 } else { 1 };
        if a.len() != arity {
            return Err(syntax("Path 演算の arity", span));
        }
        let t = self.expression(&mut a[0], None)?;
        match n {
            "identity" => {
                let name = t
                    .ref_name()
                    .ok_or_else(|| syntax("entity 参照を要求", span))?;
                if self.r.s.declarations[name].kind != "entity" {
                    return Err(syntax("identity は entity", span));
                }
                Ok(Type::Path(name.into(), name.into()))
            }
            "path" => {
                let name = t.ref_name().ok_or_else(|| syntax("原始操作を要求", span))?;
                let d = &self.r.s.declarations[name];
                if !["arrow", "correspondence"].contains(&d.kind.as_str()) {
                    return Err(syntax("path は arrow/correspondence", span));
                }
                let fs = d.parameters.iter().chain(&d.fields).collect::<Vec<_>>();
                let get = |n| {
                    fs.iter()
                        .find(|f| f.name == n)
                        .and_then(|f| f.ty.as_ref())
                        .and_then(Type::ref_name)
                        .map(str::to_owned)
                };
                Ok(Type::Path(
                    get("from").ok_or_else(|| syntax("arrow の from を要求", span))?,
                    get("to").ok_or_else(|| syntax("arrow の to を要求", span))?,
                ))
            }
            "then" => {
                let Type::Path(x, y) = t else {
                    return Err(syntax("Path を要求", span));
                };
                let u = self.expression(&mut a[1], None)?;
                let Type::Path(z, w) = u else {
                    return Err(syntax("Path を要求", span));
                };
                if y != z {
                    return Err(syntax("Path 始終型の不一致", span));
                }
                Ok(Type::Path(x, w))
            }
            "source" | "target" => {
                let Type::Path(x, y) = t else {
                    return Err(syntax("Path を要求", span));
                };
                Ok(Type::Ref(if n == "source" { x } else { y }))
            }
            _ => unreachable!(),
        }
    }
}
fn flexible_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Integer(_) => true,
        ExprKind::Group(a) => flexible_literal(a),
        ExprKind::Unary(op, a) if op == "-" => flexible_literal(a),
        ExprKind::Tuple(a) => a.iter().all(flexible_literal),
        _ => false,
    }
}
fn integer_literal(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Integer(_))
        || matches!(&e.kind,ExprKind::Unary(op,x)if op=="-"&&matches!(x.kind,ExprKind::Integer(_)))
}
fn positive_literal(e: &Expr) -> bool {
    matches!(&e.kind,ExprKind::Integer(n)if n!="0")
}

fn acyclic(graph: &BTreeMap<String, BTreeSet<String>>, span: Span) -> Checked<()> {
    fn visit(
        n: &str,
        g: &BTreeMap<String, BTreeSet<String>>,
        active: &mut BTreeSet<String>,
        done: &mut BTreeSet<String>,
    ) -> bool {
        if done.contains(n) {
            return true;
        }
        if !active.insert(n.into()) {
            return false;
        }
        if let Some(xs) = g.get(n) {
            for x in xs {
                if !visit(x, g, active, done) {
                    return false;
                }
            }
        }
        active.remove(n);
        done.insert(n.into());
        true
    }
    let mut done = BTreeSet::new();
    for n in graph.keys() {
        if !visit(n, graph, &mut BTreeSet::new(), &mut done) {
            return Err(Issue::law("cycle", "依存循環", span));
        }
    }
    Ok(())
}
fn symbols(p: &Program) -> Symbols {
    Symbols {
        declarations: p
            .readings
            .iter()
            .flat_map(|r| r.declarations.iter().map(|d| (d.name.clone(), d.clone())))
            .collect(),
        aliases: p
            .readings
            .iter()
            .map(|r| (r.name.clone(), r.aliases.clone()))
            .collect(),
    }
}
fn root_type(t: &Type, s: &Symbols) -> bool {
    t.ref_name().is_some_and(|n| {
        s.declarations.get(n).is_some_and(|d| {
            d.kind == "entity"
                && !d
                    .parameters
                    .iter()
                    .chain(&d.fields)
                    .any(|f| f.name == "owner")
        })
    })
}
fn validate_structure(d: &mut Declaration, s: &Symbols) -> Checked<()> {
    let fs = d.parameters.iter().chain(&d.fields).collect::<Vec<_>>();
    let get = |n: &str| fs.iter().find(|f| f.name == n).copied();
    if let Some(owner) =
        get("owner").filter(|_| ["entity", "arrow", "correspondence"].contains(&d.kind.as_str()))
    {
        if !["entity", "arrow"].contains(&d.kind.as_str())
            || !root_type(owner.ty.as_ref().unwrap(), s)
        {
            return Err(syntax("owner は根 entity", owner.span));
        }
    }
    if d.kind == "arrow" {
        let owner = get("owner").ok_or_else(|| syntax("arrow に owner が必要", d.span))?;
        let from = get("from").ok_or_else(|| syntax("arrow に from が必要", d.span))?;
        let to = get("to").ok_or_else(|| syntax("arrow に to が必要", d.span))?;
        let Type::Owned(n, p) = from.ty.as_ref().unwrap() else {
            return Err(syntax("arrow の from は owner 依存型", from.span));
        };
        if p != "owner" || to.ty != from.ty || s.declarations[n].kind != "entity" {
            return Err(syntax("arrow の始終型", d.span));
        }
        let target_owner = s.declarations[n]
            .parameters
            .iter()
            .chain(&s.declarations[n].fields)
            .find(|f| f.name == "owner")
            .and_then(|f| f.ty.as_ref())
            .ok_or_else(|| syntax("owned entity を要求", from.span))?;
        ensure(owner.ty.as_ref().unwrap(), target_owner, from.span)?;
    }
    if d.kind == "correspondence" {
        let from = get("from").ok_or_else(|| syntax("correspondence に from が必要", d.span))?;
        let to = get("to").ok_or_else(|| syntax("correspondence に to が必要", d.span))?;
        if !root_type(from.ty.as_ref().unwrap(), s) || !root_type(to.ty.as_ref().unwrap(), s) {
            return Err(syntax("correspondence の端点は根 entity", d.span));
        }
        let source = from.ty.as_ref().unwrap().ref_name().unwrap();
        let target = to.ty.as_ref().unwrap().ref_name().unwrap();
        let owned = |root: &str| {
            s.declarations
                .values()
                .filter(|d| {
                    ["entity", "arrow"].contains(&d.kind.as_str())
                        && d.parameters.iter().chain(&d.fields).any(|f| {
                            f.name == "owner"
                                && f.ty.as_ref().and_then(Type::ref_name) == Some(root)
                        })
                })
                .map(|d| d.name.clone())
                .collect::<BTreeSet<_>>()
        };
        let mut domain = BTreeSet::new();
        let mut codomain = BTreeSet::new();
        let mut pairs = Vec::new();
        let mut maps = BTreeMap::new();
        for f in &d.fields {
            let Some(Type::Map(a, b)) = &f.ty else {
                return Err(syntax("correspondence body は Map", f.span));
            };
            let (Type::Owned(a, pa), Type::Owned(b, pb)) = (a.as_ref(), b.as_ref()) else {
                return Err(syntax("Map の型は端点依存族", f.span));
            };
            if pa != "from"
                || pb != "to"
                || !domain.insert(a.clone())
                || !codomain.insert(b.clone())
            {
                return Err(syntax("型対応の重複または依存先の不一致", f.span));
            }
            maps.insert(a.clone(), b.clone());
        }
        if domain != owned(source) || codomain != owned(target) {
            return Err(syntax("correspondence が owned 型を覆わない", d.span));
        }
        let mut explicit = BTreeMap::new();
        let mut targets = BTreeSet::new();
        for (a, sa, b, sb) in &mut d.alignments {
            let resolve_field = |n: &str, span: Span| -> Checked<String> {
                let (base, field) = n
                    .rsplit_once('.')
                    .ok_or_else(|| syntax("field 完全名を要求", span))?;
                let base = s.resolve(&d.reading, base, span)?;
                let declaration = s.declarations.get(&base).ok_or_else(|| {
                    Issue::law("reference", "align は原始宣言の field を要求", span)
                })?;
                if !declaration
                    .parameters
                    .iter()
                    .chain(&declaration.fields)
                    .any(|f| f.name == field)
                {
                    return Err(Issue::law("reference", "align の未知 field", span));
                }
                Ok(format!("{base}.{field}"))
            };
            *a = resolve_field(a, *sa)?;
            *b = resolve_field(b, *sb)?;
            let (da, _) = a.rsplit_once('.').unwrap();
            let (db, _) = b.rsplit_once('.').unwrap();
            if maps.get(da).map(String::as_str) != Some(db)
                || explicit.insert(a.clone(), b.clone()).is_some()
                || !targets.insert(b.clone())
            {
                return Err(syntax("align 対応の重複または不一致", *sa));
            }
            d.references.push((*sa, a.clone()));
            d.references.push((*sb, b.clone()));
        }
        for (a, b) in maps {
            let da = &s.declarations[&a];
            let db = &s.declarations[&b];
            let af = da.parameters.iter().chain(&da.fields).collect::<Vec<_>>();
            let bf = db.parameters.iter().chain(&db.fields).collect::<Vec<_>>();
            if af.len() != bf.len() {
                return Err(syntax("対応する field 数の不一致", d.span));
            }
            for f in af {
                let source = format!("{a}.{}", f.name);
                let target = if let Some(t) = explicit.get(&source) {
                    t.clone()
                } else if a == b {
                    let t = format!("{b}.{}", f.name);
                    if !targets.insert(t.clone()) {
                        return Err(syntax("暗黙 align の target 重複", d.span));
                    }
                    pairs.push(json!([source, t]));
                    t
                } else {
                    return Err(syntax("異なる型の全 field に align が必要", d.span));
                };
                let (_, name) = target.rsplit_once('.').unwrap();
                let g = bf.iter().find(|f| f.name == name).unwrap();
                let ft = f.ty.as_ref().unwrap();
                let gt = g.ty.as_ref().unwrap();
                let transported = transport_type(ft, &domain, &codomain, s, d)?;
                if !same_shape(&transported, gt) {
                    return Err(type_error(gt, &transported, d.span));
                }
            }
        }
        if !pairs.is_empty() {
            pairs.sort_by_key(canonical::bytes);
            d.supplied.push(
                json!({"rule":"same_name_alignment","location":location(d.span),"pairs":pairs}),
            );
        }
    }
    Ok(())
}
fn same_shape(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Owned(a, _), Type::Owned(b, _)) => a == b,
        _ => a == b,
    }
}
fn transport_type(
    t: &Type,
    _domain: &BTreeSet<String>,
    _codomain: &BTreeSet<String>,
    _s: &Symbols,
    d: &Declaration,
) -> Checked<Type> {
    let map_name = |n: &str| -> String {
        for f in &d.fields {
            if let Some(Type::Map(a, b)) = &f.ty {
                if a.ref_name() == Some(n) {
                    return b.ref_name().unwrap().into();
                }
            }
        }
        let from = d
            .parameters
            .iter()
            .find(|f| f.name == "from")
            .and_then(|f| f.ty.as_ref())
            .and_then(Type::ref_name);
        if from == Some(n) {
            return d
                .parameters
                .iter()
                .find(|f| f.name == "to")
                .and_then(|f| f.ty.as_ref())
                .and_then(Type::ref_name)
                .unwrap()
                .into();
        }
        n.into()
    };
    Ok(match t {
        Type::Ref(n) => Type::Ref(map_name(n)),
        Type::Owned(n, p) => Type::Owned(map_name(n), p.clone()),
        Type::Tuple(a) => Type::Tuple(
            a.iter()
                .map(|t| transport_type(t, _domain, _codomain, _s, d))
                .collect::<Checked<_>>()?,
        ),
        Type::List(a) => Type::List(Box::new(transport_type(a, _domain, _codomain, _s, d)?)),
        Type::Set(a) => Type::Set(Box::new(transport_type(a, _domain, _codomain, _s, d)?)),
        Type::Option(a) => Type::Option(Box::new(transport_type(a, _domain, _codomain, _s, d)?)),
        _ => t.clone(),
    })
}
fn ground(t: &Type, s: &Symbols, active: &mut BTreeSet<String>) -> bool {
    match t {
        Type::Data(n) => {
            if !active.insert(n.clone()) {
                return false;
            }
            let yes = s.declarations[n]
                .constructors
                .iter()
                .any(|c| c.types.iter().all(|t| ground(t, s, active)));
            active.remove(n);
            yes
        }
        Type::Tuple(a) => a.iter().all(|t| ground(t, s, active)),
        Type::Term(_, b) => ground(b, s, active),
        _ => true,
    }
}
fn data_references(t: &Type, out: &mut BTreeSet<String>) {
    if let Type::Data(n) = t {
        out.insert(n.clone());
    }
    for t in children(t) {
        data_references(t, out);
    }
}
fn positive_recursive(t: &Type, name: &str, allowed: bool) -> bool {
    match t {
        Type::Data(n) => n != name || allowed,
        Type::Tuple(a) => a.iter().all(|t| positive_recursive(t, name, allowed)),
        Type::List(a) | Type::Option(a) => positive_recursive(a, name, allowed),
        _ => children(t)
            .into_iter()
            .all(|t| positive_recursive(t, name, false)),
    }
}
pub fn check(bytes: &[u8]) -> Checked<Program> {
    let mut p = parse(bytes)?;
    let mut reading_names = BTreeSet::new();
    let mut decl_names = BTreeSet::new();
    for r in &p.readings {
        if !reading_names.insert(r.name.clone()) {
            return Err(Issue::law("duplicate_id", "reading の重複", r.span));
        }
        let mut scope = r.aliases.keys().cloned().collect::<BTreeSet<_>>();
        for d in &r.declarations {
            let short = d.name.rsplit('.').next().unwrap();
            if !scope.insert(short.into()) || !decl_names.insert(d.name.clone()) {
                return Err(Issue::law("duplicate_id", "宣言名の衝突", d.span));
            }
            let mut names = BTreeSet::new();
            for f in d.parameters.iter().chain(&d.fields) {
                if !names.insert(&f.name) {
                    return Err(Issue::law("duplicate_id", "field/parameter の重複", f.span));
                }
            }
            let mut ctors = BTreeSet::new();
            for c in &d.constructors {
                if reserved(&c.name) {
                    return Err(syntax("組込み演算を再定義できない", c.span));
                }
                if !ctors.insert(&c.name) {
                    return Err(Issue::law("duplicate_id", "constructor の重複", c.span));
                }
            }
        }
    }
    for r in &p.readings {
        for (other, span) in r.aliases.values() {
            if !reading_names.contains(other) {
                return Err(Issue::law("reference", "use 参照先がない", *span));
            }
        }
    }
    let s = symbols(&p);
    for r in &mut p.readings {
        for d in &mut r.declarations {
            let mut resolver = Resolver {
                s: &s,
                reading: &r.name,
                references: Vec::new(),
            };
            let mut env = BTreeMap::new();
            for f in &mut d.parameters {
                let ty = resolver.ty(&f.raw, &env)?;
                env.insert(f.name.clone(), ty.clone());
                f.ty = Some(ty);
            }
            for f in &mut d.fields {
                f.ty = Some(resolver.ty(&f.raw, &env)?);
            }
            for c in &mut d.constructors {
                for raw in &c.arguments {
                    c.types.push(resolver.ty(raw, &BTreeMap::new())?);
                }
            }
            if let Some(t) = &d.returns {
                d.ty = Some(resolver.ty(t, &env)?);
            }
            d.references = resolver.references;
        }
    }
    let s = symbols(&p);
    let mut data_graph = BTreeMap::new();
    for d in s.declarations.values() {
        for f in d.parameters.iter().chain(&d.fields) {
            let t = f.ty.as_ref().unwrap();
            admissible(t, &s, f.span)?;
            if ["entity", "arrow", "correspondence"].contains(&d.kind.as_str()) && has_path(t, &s) {
                return Err(syntax("原始 field に Path は使えない", f.span));
            }
        }
        if let Some(t) = &d.ty {
            admissible(t, &s, d.span)?;
        }
        if d.kind == "data" {
            let mut deps = BTreeSet::new();
            for c in &d.constructors {
                for t in &c.types {
                    admissible(t, &s, c.span)?;
                    if has_path(t, &s) || !positive_recursive(t, &d.name, true) {
                        return Err(syntax("data の不正再帰または Path", c.span));
                    }
                    data_references(t, &mut deps);
                }
            }
            deps.remove(&d.name);
            data_graph.insert(d.name.clone(), deps);
            if !ground(&Type::Data(d.name.clone()), &s, &mut BTreeSet::new()) {
                return Err(syntax("data に有限 ground value がない", d.span));
            }
        }
    }
    acyclic(&data_graph, [0, bytes.len()])?;
    let mut reading_graph = p
        .readings
        .iter()
        .map(|r| {
            (
                r.name.clone(),
                r.aliases
                    .values()
                    .map(|(n, _)| n.clone())
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for r in &mut p.readings {
        for d in &mut r.declarations {
            validate_structure(d, &s)?;
        }
    }
    let s = symbols(&p);
    let mut call_graph = BTreeMap::new();
    for r in &mut p.readings {
        for d in &mut r.declarations {
            let mut c = Checker {
                r: Resolver {
                    s: &s,
                    reading: &r.name,
                    references: Vec::new(),
                },
                env: BTreeMap::new(),
                declaration: &s.declarations[&d.name],
                pure: false,
                captures: BTreeSet::new(),
                change: false,
                calls: BTreeSet::new(),
            };
            for f in &d.parameters {
                c.bind(&f.name, f.ty.clone().unwrap(), false, f.span)?;
            }
            if let Some(g) = &mut d.guard {
                c.expression(g, Some(&Type::Bool))?;
            } else if ["law", "local", "change", "relation"].contains(&d.kind.as_str()) {
                d.supplied
                    .push(json!({"rule":"guard_true","location":location(d.span)}));
            }
            for e in &mut d.bodies {
                if d.kind == "relation" {
                    let ExprKind::Binary(op, a, b) = &mut e.kind else {
                        return Err(syntax("relation は最上位等号", e.span));
                    };
                    if op != "=" {
                        return Err(syntax("relation は最上位等号", e.span));
                    }
                    let left = c.expression(a, None)?;
                    if !matches!(left, Type::Path(..)) {
                        return Err(syntax("relation の両辺は Path", a.span));
                    }
                    c.expression(b, Some(&left))?;
                    e.ty = Some(Type::Bool);
                } else {
                    let want = if d.kind == "law" {
                        Some(Type::Bool)
                    } else {
                        d.ty.clone()
                    };
                    c.change = d.kind == "change";
                    let t = c.expression(e, want.as_ref())?;
                    c.change = false;
                    if d.kind == "change" {
                        let Some(f) = d.parameters.first() else {
                            return Err(syntax("change に entity parameter が必要", d.span));
                        };
                        ensure(f.ty.as_ref().unwrap(), &t, e.span)?;
                        if !matches!(e.kind, ExprKind::With(..)) {
                            return Err(syntax("change body は with 更新", e.span));
                        }
                        d.ty = Some(t);
                    }
                }
            }
            if d.kind == "change" {
                for f in d.parameters.iter().skip(1) {
                    if has_ref(f.ty.as_ref().unwrap(), &s) {
                        return Err(syntax("change の追加 parameter に参照は使えない", f.span));
                    }
                }
            }
            d.references.extend(c.r.references);
            for (_, n) in &d.references {
                let reading = n.split('.').next().unwrap();
                if reading != r.name {
                    reading_graph
                        .get_mut(&r.name)
                        .unwrap()
                        .insert(reading.into());
                }
                d.dependencies.insert(n.clone());
            }
            c.calls.remove(&d.name);
            call_graph.insert(d.name.clone(), c.calls);
        }
    }
    acyclic(&reading_graph, [0, bytes.len()])?;
    acyclic(&call_graph, [0, bytes.len()])?;
    for r in &mut p.readings {
        for d in &mut r.declarations {
            for (span, _) in &mut d.references {
                if let Some(token) = p.tokens.iter().find(|t| {
                    t.span[0] >= span[0]
                        && t.span[1] <= span[1]
                        && ["(", "["].contains(&t.text.as_str())
                }) {
                    if let Some(last) = p
                        .tokens
                        .iter()
                        .rev()
                        .find(|t| t.span[0] >= span[0] && t.span[1] <= token.span[0])
                    {
                        span[1] = last.span[1];
                    }
                }
            }
        }
    }
    for r in &p.readings {
        let rule = if r.declarations.iter().any(|d| d.kind == "local") {
            "local_declared"
        } else {
            "local_support"
        };
        let mut ordered_aliases = r.aliases.values().collect::<Vec<_>>();
        ordered_aliases.sort_by_key(|(_, span)| span[0]);
        let refs = ordered_aliases
            .into_iter()
            .map(|(name, span)| json!({"location":location(*span),"name":name}))
            .collect::<Vec<_>>();
        p.declarations.push(json!({"name":r.name,"kind":"reading","parameters":[],"fields":[],"location":location(r.span),"dependencies":r.aliases.values().map(|(n,_)|n).collect::<BTreeSet<_>>(),"resolution":{"references":refs,"expressions":[],"supplied":[{"rule":rule,"location":location(r.span)}]}}));
        let mut primitives = Vec::new();
        for d in &r.declarations {
            p.declarations.push(declaration_info(d));
            if ["entity", "arrow", "correspondence"].contains(&d.kind.as_str()) {
                primitives.push(json!({"kind":d.kind,"name":d.name,"parameters":d.parameters.iter().map(field_wire).collect::<Vec<_>>(),"fields":d.fields.iter().map(field_wire).collect::<Vec<_>>(),"alignments":({let mut a=d.alignments.iter().map(|(a,_,b,_)|json!({"source":a,"target":b})).collect::<Vec<_>>();a.sort_by_key(|a|(a["source"].as_str().unwrap().to_owned(),a["target"].as_str().unwrap().to_owned()));a})}));
            } else if d.kind == "data" {
                primitives.push(json!({"kind":"data","name":d.name,"constructors":d.constructors.iter().map(|c|json!({"name":c.name,"arguments":c.types.iter().map(Type::wire).collect::<Vec<_>>()})).collect::<Vec<_>>() }));
                for c in &d.constructors {
                    p.declarations.push(json!({"name":format!("{}.{}",d.name,c.name),"kind":"data","parameters":c.types.iter().enumerate().map(|(i,t)|json!({"name":format!("arg{i}"),"type":t.wire()})).collect::<Vec<_>>(),"fields":[],"location":location(c.span),"dependencies":d.references.iter().filter(|(s,_)|s[0]>=c.span[0]&&s[1]<=c.span[1]).map(|(_,n)|n).collect::<BTreeSet<_>>(),"resolution":{"references":d.references.iter().filter(|(s,_)|s[0]>=c.span[0]&&s[1]<=c.span[1]).map(|(s,n)|json!({"location":location(*s),"name":n})).collect::<Vec<_>>(),"expressions":[],"supplied":[]}}));
                }
            }
        }
        primitives.sort_by_key(|d| d["name"].as_str().unwrap().to_owned());
        let manifest =
            json!({"semantics":"archsig/0.6.0","reading":r.name,"declarations":primitives});
        let digest = canonical::model_digest(&manifest);
        p.vocabularies
            .push(json!({"manifest":manifest,"digest":digest}));
    }
    p.declarations
        .sort_by_key(|d| d["name"].as_str().unwrap().to_owned());
    p.vocabularies
        .sort_by_key(|d| d["manifest"]["reading"].as_str().unwrap().to_owned());
    Ok(p)
}
fn field_wire(f: &Field) -> Value {
    json!({"name":f.name,"type":f.ty.as_ref().unwrap().wire()})
}
fn declaration_info(d: &Declaration) -> Value {
    let mut refs = d.references.clone();
    refs.sort_by_key(|(s, _)| s[0]);
    let mut expressions = Vec::new();
    if let Some(g) = &d.guard {
        expressions.push(json!({"kind":"guard","location":location(g.span),"type":g.ty.as_ref().unwrap().wire()}));
    }
    for b in &d.bodies {
        if d.kind == "relation" {
            if let ExprKind::Binary(_, a, b) = &b.kind {
                for (kind, e) in [("relation_left", a), ("relation_right", b)] {
                    expressions.push(json!({"kind":kind,"location":location(e.span),"type":e.ty.as_ref().unwrap().wire()}));
                }
            }
        } else {
            expressions.push(json!({"kind":if d.kind=="local"{"read"}else{"body"},"location":location(b.span),"type":b.ty.as_ref().unwrap().wire()}));
        }
    }
    expressions.sort_by_key(|e| e["location"]["span"][0].as_u64().unwrap());
    let mut supplied = d.supplied.clone();
    supplied.sort_by_key(|r| r["rule"].as_str().unwrap().to_owned());
    let mut info = json!({"name":d.name,"kind":d.kind,"parameters":d.parameters.iter().map(field_wire).collect::<Vec<_>>(),"fields":d.fields.iter().map(field_wire).collect::<Vec<_>>(),"location":location(d.span),"dependencies":d.dependencies,"resolution":{"references":refs.iter().map(|(s,n)|json!({"location":location(*s),"name":n})).collect::<Vec<_>>(),"expressions":expressions,"supplied":supplied}});
    if let Some(t) = &d.ty {
        info["returns"] = t.wire();
    }
    if let Some(role) = &d.role {
        info["role"] = json!(role);
    }
    info
}
