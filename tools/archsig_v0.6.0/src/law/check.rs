//! 名前の解決と宣言の署名の検査(Law 仕様 §§1–3)。

use super::ast::*;
use super::model::*;
use super::parser::Parser;
use crate::issue::{Code, Issue};
use crate::prime::is_prime;
use crate::types::Type;
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

pub type CResult<T> = Result<T, Box<Issue>>;

/// 組込み演算名。宣言名・束縛名に使えない。
pub const BUILTIN_OPS: &[&str] = &[
    "rat", "count", "sum", "path", "identity", "then", "source", "target",
];

/// `.` 列の先頭からの最長一致で解決した宣言。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    Decl(String),
    Ctor { data: String, index: usize },
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DataProps {
    pub term_or_path: bool,
    pub reference: bool,
}

/// 型の解決で使う文脈。
pub struct TypeCtx<'a> {
    pub reading: usize,
    /// 依存型の添字に使える parameter と型。
    pub index: &'a [Param],
    pub allow_path: bool,
    /// 参照を含まない値型だけを許す(Term の中、change の値 parameter)。
    pub ref_free: bool,
    /// Set/Map/Term/Path の型適格性を確かめる。data の性質を計算する前の下読みでは偽。
    pub validate: bool,
}

pub struct Checker {
    pub parser: Parser,
    pub ast: Rc<Vec<Reading>>,
    pub reading_index: HashMap<String, usize>,
    pub aliases: Vec<HashMap<String, String>>,
    pub shorts: Vec<HashSet<String>>,
    pub decl_index: HashMap<String, (usize, usize)>,
    pub ctor_index: HashMap<String, (String, usize)>,
    pub sigs: HashMap<String, Signature>,
    pub data_props: HashMap<String, DataProps>,
    /// 現在の宣言で記録している名前の参照。
    pub refs: Vec<(Span, String)>,
    pub expr_types: Vec<Option<Type>>,
    pub view_edges: Vec<(String, String, Span)>,
    pub reading_edges: Vec<(usize, usize, Span)>,
    pub current_reading: usize,
    pub decl_refs: HashMap<String, Vec<(Span, String)>>,
    pub decl_exprs: HashMap<String, Vec<ResolvedExpression>>,
}

pub fn full(reading: &str, rest: &[&str]) -> String {
    let mut s = reading.to_owned();
    for r in rest {
        s.push('.');
        s.push_str(r);
    }
    s
}

pub fn syntax<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::Syntax, span, message)))
}

pub fn reference<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::Reference, span, message)))
}

pub fn duplicate<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::DuplicateId, span, message)))
}

pub fn cycle<T>(span: Span, message: impl Into<String>) -> CResult<T> {
    Err(Box::new(Issue::law(Code::Cycle, span, message)))
}

pub fn type_error<T>(
    span: Span,
    expected: &Type,
    actual: &Type,
    message: impl Into<String>,
) -> CResult<T> {
    Err(Box::new(Issue::law_type(span, expected, actual, message)))
}

impl Checker {
    pub fn new(parser: Parser, readings: Vec<Reading>) -> Checker {
        Checker {
            parser,
            ast: Rc::new(readings),
            reading_index: HashMap::new(),
            aliases: Vec::new(),
            shorts: Vec::new(),
            decl_index: HashMap::new(),
            ctor_index: HashMap::new(),
            sigs: HashMap::new(),
            data_props: HashMap::new(),
            refs: Vec::new(),
            expr_types: Vec::new(),
            view_edges: Vec::new(),
            reading_edges: Vec::new(),
            current_reading: 0,
            decl_refs: HashMap::new(),
            decl_exprs: HashMap::new(),
        }
    }

    pub fn reading_name(&self, r: usize) -> &str {
        &self.ast[r].name.name
    }

    pub fn decl_ast(&self, full: &str) -> Option<&Decl> {
        let (r, d) = *self.decl_index.get(full)?;
        Some(&self.ast[r].decls[d])
    }

    pub fn decl_kind(&self, full: &str) -> Option<&'static str> {
        self.decl_ast(full).map(|d| d.kind.name())
    }

    // ---- 名前の表 ----

    /// reading・alias・宣言・constructor・field の名前を集め、同じ scope での重複を拒否する。
    pub fn collect_names(&mut self) -> CResult<()> {
        let ast = self.ast.clone();
        for (ri, r) in ast.iter().enumerate() {
            if self.reading_index.insert(r.name.name.clone(), ri).is_some() {
                return duplicate(
                    r.name.span,
                    format!("reading `{}` が重複している", r.name.name),
                );
            }
        }
        for (ri, r) in ast.iter().enumerate() {
            let mut scope: HashSet<String> = HashSet::new();
            let mut shorts = HashSet::new();
            let mut aliases = HashMap::new();
            for u in &r.uses {
                if !scope.insert(u.alias.name.clone()) {
                    return duplicate(
                        u.alias.span,
                        format!("名前 `{}` が重複している", u.alias.name),
                    );
                }
                let Some(&target) = self.reading_index.get(&u.reading.name) else {
                    return reference(
                        u.reading.span,
                        format!("reading `{}` が同梱されていない", u.reading.name),
                    );
                };
                if target == ri {
                    return cycle(u.reading.span, "reading が自分自身を use している");
                }
                self.reading_edges.push((ri, target, u.reading.span));
                aliases.insert(u.alias.name.clone(), u.reading.name.clone());
            }
            for (di, d) in r.decls.iter().enumerate() {
                check_decl_name(&d.name)?;
                if !scope.insert(d.name.name.clone()) {
                    return duplicate(
                        d.name.span,
                        format!("名前 `{}` が重複している", d.name.name),
                    );
                }
                shorts.insert(d.name.name.clone());
                let name = full(&r.name.name, &[&d.name.name]);
                self.decl_index.insert(name.clone(), (ri, di));
                match &d.kind {
                    DeclKind::Data { constructors } => {
                        let mut seen = HashSet::new();
                        for (ci, c) in constructors.iter().enumerate() {
                            if !seen.insert(c.name.name.clone()) {
                                return duplicate(
                                    c.name.span,
                                    format!("constructor `{}` が重複している", c.name.name),
                                );
                            }
                            self.ctor_index
                                .insert(full(&name, &[&c.name.name]), (name.clone(), ci));
                        }
                    }
                    DeclKind::Entity { params, members }
                    | DeclKind::Arrow { params, members }
                    | DeclKind::Correspondence {
                        params, members, ..
                    } => {
                        let mut seen = HashSet::new();
                        for f in params.iter().chain(members) {
                            if !seen.insert(f.name.name.clone()) {
                                return duplicate(
                                    f.name.span,
                                    format!("field `{}` が重複している", f.name.name),
                                );
                            }
                        }
                    }
                    DeclKind::View { params, .. }
                    | DeclKind::Law { params, .. }
                    | DeclKind::Local { params, .. }
                    | DeclKind::Change { params, .. }
                    | DeclKind::Relation { params, .. } => {
                        let mut seen = HashSet::new();
                        for f in params {
                            check_binding_name(&f.name)?;
                            if !seen.insert(f.name.name.clone()) {
                                return duplicate(
                                    f.name.span,
                                    format!("parameter `{}` が重複している", f.name.name),
                                );
                            }
                        }
                    }
                }
            }
            self.aliases.push(aliases);
            self.shorts.push(shorts);
        }
        Ok(())
    }

    /// `.` 列の先頭を、別名・自分の宣言の短名・reading 名の順に展開した候補。
    fn expand(&self, reading: usize, parts: &[Ident]) -> Vec<String> {
        let head = &parts[0].name;
        let rest: Vec<&str> = parts[1..].iter().map(|p| p.name.as_str()).collect();
        let mut out = Vec::new();
        if let Some(target) = self.aliases[reading].get(head) {
            out.push(full(target, &rest));
        }
        if self.shorts[reading].contains(head) {
            let mut all = vec![head.as_str()];
            all.extend(rest.iter().copied());
            out.push(full(self.reading_name(reading), &all));
        }
        if self.reading_index.contains_key(head) {
            out.push(full(head, &rest));
        }
        out
    }

    /// alias 展開後の宣言完全名を最長一致で解決する。返す数は宣言名に使った名前の数。
    pub fn resolve_prefix(&mut self, reading: usize, parts: &[Ident]) -> Option<(Target, usize)> {
        for k in (1..=parts.len()).rev() {
            for name in self.expand(reading, &parts[..k]) {
                let target = if self.decl_index.contains_key(&name) {
                    Target::Decl(name.clone())
                } else if let Some((data, index)) = self.ctor_index.get(&name) {
                    Target::Ctor {
                        data: data.clone(),
                        index: *index,
                    }
                } else {
                    continue;
                };
                self.note_reading_edge(reading, &name, (parts[0].span.0, parts[k - 1].span.1));
                return Some((target, k));
            }
        }
        None
    }

    /// 別の reading の宣言を参照したら、reading 間の依存辺に加える。
    pub fn note_reading_edge(&mut self, reading: usize, name: &str, span: Span) {
        let head = name.split('.').next().unwrap_or(name);
        if let Some(&target) = self.reading_index.get(head)
            && target != reading
        {
            self.reading_edges.push((reading, target, span));
        }
    }

    pub fn record(&mut self, span: Span, name: String) {
        self.refs.push((span, name));
    }

    // ---- 所属 ----

    fn owner_field_ast(d: &Decl) -> Option<&Field> {
        match &d.kind {
            DeclKind::Entity { params, members } => params
                .iter()
                .chain(members)
                .find(|f| f.name.name == "owner"),
            DeclKind::Arrow { params, members } => params
                .iter()
                .chain(members)
                .find(|f| f.name.name == "owner"),
            _ => None,
        }
    }

    pub fn is_root_entity(&self, name: &str) -> bool {
        self.decl_ast(name).is_some_and(|d| {
            matches!(d.kind, DeclKind::Entity { .. }) && Self::owner_field_ast(d).is_none()
        })
    }

    /// entity/arrow の所属先の根 entity。owner の型が根 entity の名前でなければ None。
    pub fn owner_root(&mut self, name: &str) -> Option<String> {
        let (ri, _) = *self.decl_index.get(name)?;
        let field = self.decl_ast(name).and_then(Self::owner_field_ast).cloned();

        match field.as_ref().map(|f| &f.ty) {
            Some(TypeAst::Named {
                name: q,
                index: None,
                ..
            }) => match self.resolve_prefix_silent(ri, &q.parts) {
                Some((Target::Decl(n), k)) if k == q.parts.len() && self.is_root_entity(&n) => {
                    Some(n)
                }
                _ => None,
            },
            _ => None,
        }
    }

    pub fn resolve_prefix_silent(
        &mut self,
        reading: usize,
        parts: &[Ident],
    ) -> Option<(Target, usize)> {
        let edges = self.reading_edges.len();
        let hit = self.resolve_prefix(reading, parts);
        self.reading_edges.truncate(edges);
        hit
    }

    // ---- 型 ----

    pub fn resolve_type(&mut self, ast: &TypeAst, ctx: &TypeCtx) -> CResult<Type> {
        let t = stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.resolve_type_inner(ast, ctx)
        })?;
        if ctx.validate && ctx.ref_free && self.has_reference(&t) {
            return syntax(ast.span(), "ここには参照・Map・Path を含まない値型が必要");
        }
        Ok(t)
    }

    fn resolve_type_inner(&mut self, ast: &TypeAst, ctx: &TypeCtx) -> CResult<Type> {
        Ok(match ast {
            TypeAst::Builtin(b, _) => match b {
                Builtin::Unit => Type::Unit,
                Builtin::Bool => Type::Bool,
                Builtin::Z => Type::Z,
                Builtin::Q => Type::Q,
                Builtin::Text => Type::Text,
            },
            TypeAst::Fp { modulus, span } => {
                let n: BigUint = modulus.parse().expect("字句で10進整数を確認済み");
                if !is_prime(&n) {
                    return syntax(*span, format!("Fp の法 {modulus} は素数でない"));
                }
                Type::Fp(modulus.clone())
            }
            TypeAst::Named { name, index, span } => {
                self.resolve_named_type(name, index.as_ref(), *span, ctx)?
            }
            TypeAst::Tuple(items, _) => Type::Tuple(
                items
                    .iter()
                    .map(|t| self.resolve_type(t, ctx))
                    .collect::<CResult<_>>()?,
            ),
            TypeAst::List(t, _) => Type::List(Box::new(self.resolve_type(t, ctx)?)),
            TypeAst::Option(t, _) => Type::Option(Box::new(self.resolve_type(t, ctx)?)),
            TypeAst::Set(t, span) => {
                let inner = self.resolve_type(t, ctx)?;
                if ctx.validate && self.has_term_or_path(&inner) {
                    return syntax(*span, "Set の要素型は Term・Path を含まない");
                }
                Type::Set(Box::new(inner))
            }
            TypeAst::Map(a, b, span) => {
                let a = self.resolve_type(a, ctx)?;
                let b = self.resolve_type(b, ctx)?;
                if ctx.validate && (a.ref_target().is_none() || b.ref_target().is_none()) {
                    return syntax(*span, "Map の定義域・値域は参照型");
                }
                Type::Map(Box::new(a), Box::new(b))
            }
            TypeAst::Term(args, ret, span) => {
                let inner = TypeCtx {
                    reading: ctx.reading,
                    index: &[],
                    allow_path: false,
                    ref_free: false,
                    validate: ctx.validate,
                };
                let args = args
                    .iter()
                    .map(|t| self.resolve_type(t, &inner))
                    .collect::<CResult<Vec<_>>>()?;
                let ret = self.resolve_type(ret, &inner)?;
                if ctx.validate
                    && (args.iter().any(|t| self.has_reference(t)) || self.has_reference(&ret))
                {
                    return syntax(*span, "Term の引数・戻り型は参照・Map・Path を含まない値型");
                }
                Type::Term(args, Box::new(ret))
            }
            TypeAst::Path(a, b, span) => {
                if ctx.validate && !ctx.allow_path {
                    return syntax(*span, "Path は原始 field・data・Term の型に置けない");
                }
                let a = self.resolve_entity_name(a, ctx.reading)?;
                let b = self.resolve_entity_name(b, ctx.reading)?;
                Type::Path(a, b)
            }
        })
    }

    fn resolve_entity_name(&mut self, q: &QName, reading: usize) -> CResult<String> {
        match self.resolve_prefix(reading, &q.parts) {
            Some((Target::Decl(n), k)) if k == q.parts.len() => {
                if self.decl_kind(&n) != Some("entity") {
                    return syntax(q.span(), format!("Path の端点 `{}` は entity", q.text()));
                }
                self.record(q.span(), n.clone());
                Ok(n)
            }
            _ => reference(q.span(), format!("型名 `{}` を解決できない", q.text())),
        }
    }

    fn resolve_named_type(
        &mut self,
        q: &QName,
        index: Option<&Ident>,
        span: Span,
        ctx: &TypeCtx,
    ) -> CResult<Type> {
        let target = match self.resolve_prefix(ctx.reading, &q.parts) {
            Some((Target::Decl(n), k)) if k == q.parts.len() => n,
            _ => return reference(q.span(), format!("型名 `{}` を解決できない", q.text())),
        };
        let kind = self.decl_kind(&target).expect("解決済みの宣言");
        self.record(q.span(), target.clone());
        match (kind, index) {
            ("data", None) => Ok(Type::Data(target)),
            ("data", Some(_)) => syntax(span, "data 型に所属の添字は付けられない"),
            ("entity" | "arrow" | "correspondence", None) => Ok(Type::Ref(target)),
            ("entity" | "arrow", Some(i)) => {
                let Some(root) = self.owner_root(&target) else {
                    return syntax(span, format!("`{}` は所属先を持たない", q.text()));
                };
                let Some(p) = ctx.index.iter().find(|p| p.name == i.name) else {
                    return reference(
                        i.span,
                        format!("添字 `{}` は左にある parameter を指す", i.name),
                    );
                };
                let expected = Type::Ref(root);
                if p.ty.erase() != expected {
                    return type_error(
                        i.span,
                        &expected,
                        &p.ty,
                        "添字の parameter は所属先の根 entity の参照",
                    );
                }
                Ok(Type::Owned(target, i.name.clone()))
            }
            ("correspondence", Some(_)) => {
                syntax(span, "correspondence に所属の添字は付けられない")
            }
            _ => reference(q.span(), format!("`{}` は型ではない", q.text())),
        }
    }

    pub fn has_term_or_path(&self, t: &Type) -> bool {
        t.any(&mut |t| match t {
            Type::Term(..) | Type::Path(..) => true,
            Type::Data(d) => self.data_props.get(d).is_some_and(|p| p.term_or_path),
            _ => false,
        })
    }

    /// 参照・Map・Path を、data の定義を通して含むか。
    pub fn has_reference(&self, t: &Type) -> bool {
        t.any(&mut |t| match t {
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => true,
            Type::Data(d) => self.data_props.get(d).is_some_and(|p| p.reference),
            _ => false,
        })
    }

    // ---- 原始宣言の署名 ----

    pub fn check_primitives(&mut self) -> CResult<()> {
        let ast = self.ast.clone();
        // data の構成子の型を下読みし、Term/Path・参照を含むかを計算する。
        let mut raw: BTreeMap<String, Vec<Vec<Type>>> = BTreeMap::new();
        for (ri, r) in ast.iter().enumerate() {
            for d in &r.decls {
                if let DeclKind::Data { constructors } = &d.kind {
                    let ctx = TypeCtx {
                        reading: ri,
                        index: &[],
                        allow_path: true,
                        ref_free: false,
                        validate: false,
                    };
                    let mut args = Vec::new();
                    for c in constructors {
                        args.push(
                            c.args
                                .iter()
                                .map(|t| self.resolve_type(t, &ctx))
                                .collect::<CResult<Vec<_>>>()?,
                        );
                    }
                    raw.insert(full(&r.name.name, &[&d.name.name]), args);
                }
            }
        }
        self.refs.clear();
        loop {
            let mut changed = false;
            for (name, ctors) in &raw {
                let mut props = DataProps::default();
                for t in ctors.iter().flatten() {
                    props.term_or_path |= self.has_term_or_path(t);
                    props.reference |= self.has_reference(t);
                }
                let old = self.data_props.get(name).copied().unwrap_or_default();
                if old.term_or_path != props.term_or_path || old.reference != props.reference {
                    self.data_props.insert(name.clone(), props);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for (ri, r) in ast.iter().enumerate() {
            for d in &r.decls {
                let name = full(&r.name.name, &[&d.name.name]);
                let sig = match &d.kind {
                    DeclKind::Data { constructors } => self.check_data(ri, constructors)?,
                    DeclKind::Entity { params, members } => {
                        let (params, members) = self.record_fields(ri, params, members)?;
                        let owner = self.check_owner_field(&name, &params, &members)?;
                        Signature::Entity {
                            params,
                            members,
                            owner,
                        }
                    }
                    DeclKind::Arrow { params, members } => {
                        let (params, members) = self.record_fields(ri, params, members)?;
                        self.check_arrow(&name, d, params, members)?
                    }
                    DeclKind::Correspondence {
                        params, members, ..
                    } => {
                        let (params, members) = self.record_fields(ri, params, members)?;
                        Signature::Correspondence {
                            params,
                            members,
                            from: String::new(),
                            to: String::new(),
                            maps: Vec::new(),
                            alignments: Vec::new(),
                            implicit: Vec::new(),
                        }
                    }
                    _ => continue,
                };
                let refs = std::mem::take(&mut self.refs);
                self.decl_refs.insert(name.clone(), refs);
                self.sigs.insert(name, sig);
            }
        }
        self.check_data_recursion(&raw)?;
        for (ri, r) in ast.iter().enumerate() {
            for d in &r.decls {
                if let DeclKind::Correspondence { alignments, .. } = &d.kind {
                    let name = full(&r.name.name, &[&d.name.name]);
                    self.refs = self.decl_refs.remove(&name).unwrap_or_default();
                    self.check_correspondence(ri, &name, d, alignments)?;
                    let refs = std::mem::take(&mut self.refs);
                    self.decl_refs.insert(name, refs);
                }
            }
        }
        Ok(())
    }

    fn record_fields(
        &mut self,
        ri: usize,
        params: &[Field],
        members: &[Field],
    ) -> CResult<(Vec<Param>, Vec<Param>)> {
        let mut ps: Vec<Param> = Vec::new();
        for f in params {
            let ctx = TypeCtx {
                reading: ri,
                index: &ps,
                allow_path: false,
                ref_free: false,
                validate: true,
            };
            let ty = self.resolve_type(&f.ty, &ctx)?;
            ps.push(Param {
                name: f.name.name.clone(),
                ty,
                span: f.name.span,
            });
        }
        let mut ms = Vec::new();
        for f in members {
            let ctx = TypeCtx {
                reading: ri,
                index: &ps,
                allow_path: false,
                ref_free: false,
                validate: true,
            };
            let ty = self.resolve_type(&f.ty, &ctx)?;
            ms.push(Param {
                name: f.name.name.clone(),
                ty,
                span: f.name.span,
            });
        }
        Ok((ps, ms))
    }

    fn check_owner_field(
        &mut self,
        name: &str,
        params: &[Param],
        members: &[Param],
    ) -> CResult<Option<String>> {
        let Some(owner) = params.iter().chain(members).find(|p| p.name == "owner") else {
            return Ok(None);
        };
        match &owner.ty {
            Type::Ref(r) if self.is_root_entity(r) => {
                let root = self.owner_root(name);
                debug_assert_eq!(root.as_deref(), Some(r.as_str()));
                Ok(Some(r.clone()))
            }
            t => syntax(
                owner.span,
                format!(
                    "owner の型は所属先を持たない entity(実際は {:?})",
                    t.wire().canonical()
                ),
            ),
        }
    }

    fn check_arrow(
        &mut self,
        name: &str,
        d: &Decl,
        params: Vec<Param>,
        members: Vec<Param>,
    ) -> CResult<Signature> {
        let get = |n: &str| params.iter().chain(&members).find(|p| p.name == n).cloned();
        let (Some(owner), Some(from), Some(to)) = (get("owner"), get("from"), get("to")) else {
            return syntax(d.name.span, "arrow は owner・from・to の field を持つ");
        };
        let root = match &owner.ty {
            Type::Ref(r) if self.is_root_entity(r) => r.clone(),
            _ => return syntax(owner.span, "arrow の owner の型は根 entity"),
        };
        let endpoint = match (&from.ty, &to.ty) {
            (Type::Owned(e, p), Type::Owned(f, q)) if e == f && p == "owner" && q == "owner" => {
                e.clone()
            }
            _ => return syntax(from.span, "arrow の from・to は同じ entity の E[owner]"),
        };
        if self.decl_kind(&endpoint) != Some("entity")
            || self.owner_root(&endpoint).as_deref() != Some(root.as_str())
        {
            return syntax(from.span, "arrow の端点は owner に所属する entity");
        }
        let _ = name;
        Ok(Signature::Arrow {
            params,
            members,
            owner: root,
            endpoint,
        })
    }

    fn check_data(&mut self, ri: usize, constructors: &[Constructor]) -> CResult<Signature> {
        let ctx = TypeCtx {
            reading: ri,
            index: &[],
            allow_path: false,
            ref_free: false,
            validate: true,
        };
        let mut out = Vec::new();
        for c in constructors {
            let args = c
                .args
                .iter()
                .map(|t| self.resolve_type(t, &ctx))
                .collect::<CResult<Vec<_>>>()?;
            out.push(CtorSig {
                name: c.name.name.clone(),
                args,
                span: c.span,
            });
        }
        Ok(Signature::Data { constructors: out })
    }

    /// 自己参照は直接または Tuple/List/Option を通る正の出現だけ。相互再帰と空の data を拒否する。
    fn check_data_recursion(&mut self, raw: &BTreeMap<String, Vec<Vec<Type>>>) -> CResult<()> {
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (name, ctors) in raw {
            let decl = self.decl_ast(name).cloned().expect("data 宣言");
            let DeclKind::Data { constructors } = &decl.kind else {
                unreachable!()
            };
            for (c, args) in constructors.iter().zip(ctors) {
                for (ast, t) in c.args.iter().zip(args) {
                    if !positive_self(t, name, true) {
                        return syntax(
                            ast.span(),
                            "data の自己参照は直接または Tuple・List・Option を通る",
                        );
                    }
                    t.clone().any(&mut |t| {
                        if let Type::Data(other) = t
                            && other != name
                        {
                            edges.entry(name.clone()).or_default().insert(other.clone());
                        }
                        false
                    });
                }
            }
        }
        if let Some(looped) = find_cycle(&edges) {
            let decl = self.decl_ast(&looped).expect("data 宣言");
            return cycle(
                decl.name.span,
                format!("data `{looped}` が相互再帰している"),
            );
        }
        let mut inhabited: HashSet<String> = HashSet::new();
        loop {
            let mut changed = false;
            for (name, ctors) in raw {
                if inhabited.contains(name) {
                    continue;
                }
                if ctors
                    .iter()
                    .any(|args| args.iter().all(|t| type_inhabited(t, &inhabited)))
                {
                    inhabited.insert(name.clone());
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for name in raw.keys() {
            if !inhabited.contains(name) {
                let decl = self.decl_ast(name).expect("data 宣言");
                return syntax(
                    decl.name.span,
                    format!("data `{name}` は有限の値を持たない"),
                );
            }
        }
        Ok(())
    }

    /// reading と、それが use・完全名で参照する reading(推移的)。
    fn reading_closure(&self, ri: usize) -> HashSet<usize> {
        let mut seen = HashSet::from([ri]);
        let mut stack = vec![ri];
        while let Some(r) = stack.pop() {
            for (a, b, _) in &self.reading_edges {
                if *a == r && seen.insert(*b) {
                    stack.push(*b);
                }
            }
        }
        seen
    }

    /// correspondence の reading から見える、所属先が root の entity・arrow。
    fn owned_types(&mut self, root: &str, ri: usize) -> BTreeSet<String> {
        let visible = self.reading_closure(ri);
        let names: Vec<String> = self.decl_index.keys().cloned().collect();
        names
            .into_iter()
            .filter(|n| {
                visible.contains(&self.decl_index[n].0)
                    && matches!(self.decl_kind(n), Some("entity" | "arrow"))
                    && self.owner_root(n).as_deref() == Some(root)
            })
            .collect()
    }

    fn check_correspondence(
        &mut self,
        ri: usize,
        name: &str,
        d: &Decl,
        alignments: &[Alignment],
    ) -> CResult<()> {
        let Some(Signature::Correspondence {
            params, members, ..
        }) = self.sigs.get(name).cloned()
        else {
            unreachable!()
        };
        let get = |n: &str| params.iter().find(|p| p.name == n).cloned();
        let (Some(from), Some(to)) = (get("from"), get("to")) else {
            return syntax(d.name.span, "correspondence は括弧内に from・to を持つ");
        };
        let root = |t: &Type, me: &Self| match t {
            Type::Ref(r) if me.is_root_entity(r) => Some(r.clone()),
            _ => None,
        };
        let Some(source) = root(&from.ty, self) else {
            return syntax(from.span, "correspondence の from は根 entity");
        };
        let Some(target) = root(&to.ty, self) else {
            return syntax(to.span, "correspondence の to は根 entity");
        };
        let mut maps = Vec::new();
        let mut domain = BTreeMap::new();
        let mut codomain = BTreeSet::new();
        for m in &members {
            let (e, f) = match &m.ty {
                Type::Map(a, b) => match (a.as_ref(), b.as_ref()) {
                    (Type::Owned(e, p), Type::Owned(f, q)) if p == "from" && q == "to" => {
                        (e.clone(), f.clone())
                    }
                    _ => return syntax(m.span, "correspondence の field は Map<E[from], F[to]>"),
                },
                _ => return syntax(m.span, "correspondence の field は Map<E[from], F[to]>"),
            };
            if self.decl_kind(&e) != self.decl_kind(&f) {
                return syntax(m.span, "対応表は entity どうし・arrow どうしを対応させる");
            }
            if self.owner_root(&e).as_deref() != Some(&source)
                || self.owner_root(&f).as_deref() != Some(&target)
            {
                return syntax(m.span, "対応表の型は from・to の根に所属する");
            }
            if domain.insert(e.clone(), f.clone()).is_some() || !codomain.insert(f.clone()) {
                return duplicate(m.span, "同じ型の対応表が重複している");
            }
            maps.push((m.name.clone(), e, f));
        }
        let covered: BTreeSet<String> = domain.keys().cloned().collect();
        if covered != self.owned_types(&source, ri) || codomain != self.owned_types(&target, ri) {
            return syntax(
                d.name.span,
                "correspondence は from・to の根に所属する全ての entity・arrow を一度ずつ覆う",
            );
        }
        // 型の運搬: 根は from→to、対応表の型は始域→終域。
        let mut mu: BTreeMap<String, String> = domain.clone();
        mu.insert(source.clone(), target.clone());
        let mut explicit: BTreeMap<String, String> = BTreeMap::new();
        let mut targets: BTreeSet<String> = BTreeSet::new();
        let mut resolved_aligns = Vec::new();
        for a in alignments {
            let (se, sf) = self.resolve_field_name(ri, &a.source)?;
            let (te, tf) = self.resolve_field_name(ri, &a.target)?;
            if domain.get(&se) != Some(&te) {
                return reference(
                    a.source.span(),
                    "align の両辺は同じ対応表の始域と終域の field",
                );
            }
            let s = full(&se, &[&sf]);
            let t = full(&te, &[&tf]);
            if explicit.insert(s.clone(), t.clone()).is_some() {
                return duplicate(a.source.span(), format!("`{s}` の align が重複している"));
            }
            if !targets.insert(t.clone()) {
                return duplicate(a.target.span(), format!("`{t}` への align が重複している"));
            }
            resolved_aligns.push((s, t));
        }
        let mut implicit = Vec::new();
        for (_, e, f) in &maps {
            let es = self.sigs.get(e).cloned().expect("原始宣言");
            let fs = self.sigs.get(f).cloned().expect("原始宣言");
            let (ep, em) = es.record_fields().expect("record");
            let (fp, fm) = fs.record_fields().expect("record");
            let source_fields: Vec<&Param> = ep.iter().chain(em).collect();
            let target_fields: Vec<&Param> = fp.iter().chain(fm).collect();
            if source_fields.len() != target_fields.len() {
                return syntax(d.name.span, format!("`{e}` と `{f}` の field 数が異なる"));
            }
            let mut alpha: BTreeMap<String, String> = BTreeMap::new();
            for sfield in &source_fields {
                let s = full(e, &[&sfield.name]);
                let t = if let Some(t) = explicit.get(&s) {
                    t.clone()
                } else if e == f {
                    let t = full(f, &[&sfield.name]);
                    if !targets.insert(t.clone()) {
                        return duplicate(
                            d.name.span,
                            format!("`{t}` が同名の対応と align で重複している"),
                        );
                    }
                    implicit.push((s.clone(), t.clone()));
                    t
                } else {
                    return syntax(d.name.span, format!("`{s}` の対応先を align で明記する"));
                };
                alpha.insert(
                    sfield.name.clone(),
                    t.rsplit('.').next().expect("field 名").to_owned(),
                );
            }
            for sfield in &source_fields {
                let tname = &alpha[&sfield.name];
                let tfield = target_fields
                    .iter()
                    .find(|p| &p.name == tname)
                    .expect("解決済み field");
                // 所属・参照は対応表に沿って運び、量の field は位置だけを対応させる。
                let refs = self.has_reference(&sfield.ty) || self.has_reference(&tfield.ty);
                let moved = transport(&sfield.ty, &mu, &alpha);
                if refs && moved != tfield.ty {
                    return type_error(
                        tfield.span,
                        &moved,
                        &tfield.ty,
                        format!("`{e}.{}` と `{f}.{tname}` の型が対応しない", sfield.name),
                    );
                }
            }
        }
        implicit.sort();
        resolved_aligns.sort();
        self.sigs.insert(
            name.to_owned(),
            Signature::Correspondence {
                params,
                members,
                from: source,
                to: target,
                maps,
                alignments: resolved_aligns,
                implicit,
            },
        );
        Ok(())
    }

    /// `Decl.field` の形の名前を、宣言完全名と field 名へ解決する。
    fn resolve_field_name(&mut self, ri: usize, q: &QName) -> CResult<(String, String)> {
        if q.parts.len() >= 2 {
            let (head, last) = q.parts.split_at(q.parts.len() - 1);
            if let Some((Target::Decl(n), k)) = self.resolve_prefix(ri, head)
                && k == head.len()
                && let Some(sig) = self.sigs.get(&n)
                && sig.field(&last[0].name).is_some()
            {
                let name = full(&n, &[&last[0].name]);
                self.record(q.span(), name);
                return Ok((n, last[0].name.clone()));
            }
        }
        reference(q.span(), format!("field `{}` を解決できない", q.text()))
    }
}

/// 宣言名の規則。組込み演算名は宣言名に使えない。
pub fn check_decl_name(id: &Ident) -> CResult<()> {
    if BUILTIN_OPS.contains(&id.name.as_str()) {
        return syntax(
            id.span,
            format!("組込み演算名 `{}` は宣言名に使えない", id.name),
        );
    }
    Ok(())
}

pub fn check_binding_name(id: &Ident) -> CResult<()> {
    if BUILTIN_OPS.contains(&id.name.as_str()) {
        return syntax(
            id.span,
            format!("組込み演算名 `{}` は束縛名に使えない", id.name),
        );
    }
    Ok(())
}

fn positive_self(t: &Type, me: &str, positive: bool) -> bool {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        positive_self_inner(t, me, positive)
    })
}

fn positive_self_inner(t: &Type, me: &str, positive: bool) -> bool {
    match t {
        Type::Data(d) if d == me => positive,
        Type::Tuple(items) => items.iter().all(|t| positive_self(t, me, positive)),
        Type::List(t) | Type::Option(t) => positive_self(t, me, positive),
        Type::Set(t) => positive_self(t, me, false),
        Type::Map(a, b) => positive_self(a, me, false) && positive_self(b, me, false),
        Type::Term(args, ret) => {
            args.iter().all(|t| positive_self(t, me, false)) && positive_self(ret, me, false)
        }
        _ => true,
    }
}

fn type_inhabited(t: &Type, inhabited: &HashSet<String>) -> bool {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        type_inhabited_inner(t, inhabited)
    })
}

fn type_inhabited_inner(t: &Type, inhabited: &HashSet<String>) -> bool {
    match t {
        Type::Data(d) => inhabited.contains(d),
        Type::Tuple(items) => items.iter().all(|t| type_inhabited(t, inhabited)),
        _ => true,
    }
}

fn transport(t: &Type, mu: &BTreeMap<String, String>, alpha: &BTreeMap<String, String>) -> Type {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        transport_inner(t, mu, alpha)
    })
}

fn transport_inner(
    t: &Type,
    mu: &BTreeMap<String, String>,
    alpha: &BTreeMap<String, String>,
) -> Type {
    let map = |n: &String| mu.get(n).cloned().unwrap_or_else(|| n.clone());
    match t {
        Type::Ref(n) => Type::Ref(map(n)),
        Type::Owned(n, p) => {
            Type::Owned(map(n), alpha.get(p).cloned().unwrap_or_else(|| p.clone()))
        }
        Type::Tuple(items) => Type::Tuple(items.iter().map(|t| transport(t, mu, alpha)).collect()),
        Type::List(t) => Type::List(Box::new(transport(t, mu, alpha))),
        Type::Set(t) => Type::Set(Box::new(transport(t, mu, alpha))),
        Type::Option(t) => Type::Option(Box::new(transport(t, mu, alpha))),
        Type::Map(a, b) => Type::Map(
            Box::new(transport(a, mu, alpha)),
            Box::new(transport(b, mu, alpha)),
        ),
        t => t.clone(),
    }
}

/// 有向グラフの閉路の一点。自己辺は含まない。
pub fn find_cycle(edges: &BTreeMap<String, BTreeSet<String>>) -> Option<String> {
    fn visit(
        n: &str,
        edges: &BTreeMap<String, BTreeSet<String>>,
        state: &mut HashMap<String, u8>,
    ) -> Option<String> {
        match state.get(n) {
            Some(1) => return Some(n.to_owned()),
            Some(2) => return None,
            _ => {}
        }
        state.insert(n.to_owned(), 1);
        if let Some(next) = edges.get(n) {
            for m in next {
                if let Some(c) = visit(m, edges, state) {
                    return Some(c);
                }
            }
        }
        state.insert(n.to_owned(), 2);
        None
    }
    let mut state = HashMap::new();
    for n in edges.keys() {
        if let Some(c) = visit(n, edges, &mut state) {
            return Some(c);
        }
    }
    None
}
